// Lean compiler output
// Module: Lean.Meta.Tactic.Rewrites
// Imports: Lean.Meta.LazyDiscrTree Lean.Meta.Tactic.Rewrite Lean.Meta.Tactic.Refl Lean.Meta.Tactic.SolveByElim Lean.Meta.Tactic.TryThis Lean.Util.Heartbeats
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_fswap,
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_to_list, lean_array_uget,
    lean_array_uget_borrowed, lean_array_uset, lean_infer_type, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_ptr_addr, lean_st_mk_ref,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_dec_eq, lean_string_hash,
    lean_string_memcmp, lean_string_utf8_byte_size, lean_uint64_lor, lean_uint64_shift_left,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_reverse___redArg};
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_num___override, l_Lean_Name_str___override,
};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::LOption::l_Option_toLOption___redArg;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isMetaprogramming;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_contains, l_Lean_NameSet_empty, l_Lean_NameSet_insert,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Declaration::{l_Lean_ConstantInfo_isUnsafe, l_Lean_ConstantInfo_type};
use crate::r#gen::Lean::Elab::Tactic::Basic::l_Lean_Elab_Tactic_saveState___redArg;
use crate::r#gen::Lean::Environment::l_Lean_registerEnvExtension___redArg;
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_forallE___override, l_Lean_Expr_fvarId_x21,
    l_Lean_Expr_getAppFnArgs, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_getRevArg_x21,
    l_Lean_Expr_hasMVar, l_Lean_Expr_isAppOfArity, l_Lean_Expr_lam___override,
    l_Lean_Expr_letE___override, l_Lean_Expr_mdata___override, l_Lean_Expr_mvarId_x21,
    l_Lean_Expr_proj___override, l_Lean_instBEqBinderInfo_beq, l_Lean_instBEqFVarId_beq,
};
use crate::r#gen::Lean::Linter::Deprecated::l_Lean_Linter_isDeprecated;
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_isImplementationDetail, l_Lean_LocalDecl_toExpr,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofList,
    l_Lean_MessageData_ofName, l_Lean_MessageData_paren, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp, l_Lean_Meta_Context_config,
    l_Lean_Meta_Context_configKey, l_Lean_Meta_SavedState_restore___redArg,
    l_Lean_Meta_TransparencyMode_toUInt64, l_Lean_Meta_forallMetaTelescopeReducing,
    l_Lean_Meta_mkConstWithFreshMVarLevels, l_Lean_Meta_mkFreshExprMVar, l_Lean_Meta_ppExpr,
    l_Lean_Meta_saveState___redArg, l_Lean_Meta_whnfR,
};
use crate::r#gen::Lean::Meta::CompletionName::l_Lean_Meta_allowCompletion;
use crate::r#gen::Lean::Meta::LazyDiscrTree::{
    initialize_Lean_Meta_LazyDiscrTree, l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg,
    l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg,
    l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg, runtime_initialize_Lean_Meta_LazyDiscrTree,
};
use crate::r#gen::Lean::Meta::Tactic::Assumption::l_Lean_MVarId_assumption;
use crate::r#gen::Lean::Meta::Tactic::Refl::{
    initialize_Lean_Meta_Tactic_Refl, l_Lean_MVarId_refl, runtime_initialize_Lean_Meta_Tactic_Refl,
};
use crate::r#gen::Lean::Meta::Tactic::Rewrite::{
    initialize_Lean_Meta_Tactic_Rewrite, l_Lean_MVarId_rewrite,
    runtime_initialize_Lean_Meta_Tactic_Rewrite,
};
use crate::r#gen::Lean::Meta::Tactic::SolveByElim::{
    initialize_Lean_Meta_Tactic_SolveByElim, l_Lean_Meta_SolveByElim_mkAssumptionSet,
    l_Lean_Meta_SolveByElim_solveByElim, runtime_initialize_Lean_Meta_Tactic_SolveByElim,
};
use crate::r#gen::Lean::Meta::Tactic::TryThis::{
    initialize_Lean_Meta_Tactic_TryThis, l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion,
    runtime_initialize_Lean_Meta_Tactic_TryThis,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::Heartbeats::{
    initialize_Lean_Util_Heartbeats, l_Lean_getMaxHeartbeats___redArg,
    l_Lean_getRemainingHeartbeats___redArg, runtime_initialize_Lean_Util_Heartbeats,
};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [114, 101, 119, 114, 105, 116, 101, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5416787921777642938 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11570849125384100776 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__3_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__3_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__3_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__3_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__6_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__6_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__6_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__7_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__7_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__7_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__8_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__6_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__7_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13556645696814629918 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__8_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__8_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__9_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__8_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,18261494228143523011 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__9_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__9_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__10_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [82, 101, 119, 114, 105, 116, 101, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__10_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__10_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__11_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__9_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__10_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2309225253354524358 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__11_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__11_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__12_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__11_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,8183885787141467727 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__12_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__12_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__13_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__12_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8609101547001652322 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__13_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__13_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__14_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__13_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__7_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10223271670319187318 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__14_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__14_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__15_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__14_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__10_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4929826666449082423 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__15_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__15_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__16_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__16_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__16_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__17_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__15_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__16_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15078368743364075526 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__17_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__17_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__18_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__18_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__18_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__19_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__17_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__18_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13720124707547987895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__19_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__19_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__20_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__19_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2848172960897170250 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__20_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__20_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__21_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__20_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__7_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2892769173969267310 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__21_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__21_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__22_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__21_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3197819759381581203 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__22_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__22_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__23_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__22_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__10_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1329115827935803990 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__23_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__23_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__24_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__24_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__25_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__25_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__25_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__26_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__26_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__27_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__27_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__27_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__28_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__28_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__29_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__29_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 101, 109, 109, 97, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5416787921777642938 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11570849125384100776 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9383325351095173650 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__23_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 414759425 as usize) << 1) | 1) as *mut leanh::LeanObject,8352205217020885888 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__3_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__25_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11250309528255385175 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__3_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__3_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__3_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__27_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17997709671831549887 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,3419483318661945850 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Rewrites_rewriteResultLemma___closed__0_value:
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
    m_data: [99, 111, 110, 103, 114, 65, 114, 103, 0],
};
static mut l_Lean_Meta_Rewrites_rewriteResultLemma___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_rewriteResultLemma___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Rewrites_rewriteResultLemma___closed__1_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Rewrites_rewriteResultLemma___closed__0_value)
            as *mut leanh::LeanObject,
        2642306550782628284 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Rewrites_rewriteResultLemma___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_rewriteResultLemma___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Rewrites_forwardWeight: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Rewrites_backwardWeight: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [73, 102, 102, 0]};
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [95, 105, 110, 106, 39, 0]};
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 110, 106, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [115, 105, 122, 101, 79, 102, 95, 115, 112, 101, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 105, 110, 106, 0]};
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__4_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Rewrites_localHypotheses___closed__0_value: leanh::LeanArrayObject<
    0,
> = leanh::LeanArrayObject {
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
static mut l_Lean_Meta_Rewrites_localHypotheses___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_localHypotheses___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Rewrites_droppedKeys___closed__0_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((3 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Rewrites_droppedKeys___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_droppedKeys___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Rewrites_droppedKeys___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1_value) as *mut leanh::LeanObject,16122875713692181903 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Rewrites_droppedKeys___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_droppedKeys___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Rewrites_droppedKeys___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Rewrites_droppedKeys___closed__1_value)
                as *mut leanh::LeanObject,
            (((3 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Rewrites_droppedKeys___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_droppedKeys___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Rewrites_droppedKeys___closed__3_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((3 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Rewrites_droppedKeys___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Rewrites_droppedKeys___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_droppedKeys___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Rewrites_droppedKeys___closed__4_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((3 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Rewrites_droppedKeys___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Rewrites_droppedKeys___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_droppedKeys___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Rewrites_droppedKeys___closed__5_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Rewrites_droppedKeys___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Rewrites_droppedKeys___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Rewrites_droppedKeys___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_droppedKeys___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Rewrites_droppedKeys___closed__6_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Rewrites_droppedKeys___closed__5_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Rewrites_droppedKeys___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_droppedKeys___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Rewrites_droppedKeys___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Rewrites_droppedKeys___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Rewrites_droppedKeys___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Rewrites_droppedKeys___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_droppedKeys___closed__7_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Rewrites_droppedKeys: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_droppedKeys___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ExtState_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___lam__0_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ext:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Rewrites_rwFindDecls___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_Rewrites_incPrio as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Rewrites_rwFindDecls___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_rwFindDecls___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0: u64 = 0;
pub static l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__0_value:
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
    m_data: [102, 97, 105, 108, 101, 100, 0],
};
static mut l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Rewrites_solveByElim___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_Rewrites_solveByElim___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Rewrites_solveByElim___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_solveByElim___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Rewrites_solveByElim___closed__1_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_Rewrites_solveByElim___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Rewrites_solveByElim___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_solveByElim___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Rewrites_solveByElim___closed__2_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_Rewrites_solveByElim___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Rewrites_solveByElim___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_solveByElim___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Rewrites_solveByElim___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [16777472 as *mut leanh::LeanObject],
    };
static mut l_Lean_Meta_Rewrites_solveByElim___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_solveByElim___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Rewrites_solveByElim___closed__4_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_Rewrites_solveByElim___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_solveByElim___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__1_value:
    leanh::LeanStringObject<1> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__2_value:
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
static mut l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__0_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [115, 121, 109, 109, 0],
};
static mut l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1_value) as *mut leanh::LeanObject,16122875713692181903 as *mut leanh::LeanObject] };
pub static l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
        15643637366941324764 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__2_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        258 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__3_value: leanh::LeanStringObject<
    6,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__3_value)
            as *mut leanh::LeanObject,
        14231257465488249300 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__6_value: leanh::LeanStringObject<
    13,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [99, 111, 110, 115, 105, 100, 101, 114, 105, 110, 103, 32, 0],
};
static mut l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__8_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 2,
    m_data: [226, 134, 144, 32, 0],
};
static mut l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___closed__0_value:
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
static mut l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__0_value
) as *mut leanh::LeanObject;
pub static l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__0_value) as *mut leanh::LeanObject] };
static mut l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__1_value
) as *mut leanh::LeanObject;
static mut l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__4_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 97, 108, 115, 101, 0]};
static mut l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__4_value
) as *mut leanh::LeanObject;
pub static l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__5_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Rewrites_rewriteCandidates___closed__0_value: leanh::LeanArrayObject<
    0,
> = leanh::LeanArrayObject {
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
static mut l_Lean_Meta_Rewrites_rewriteCandidates___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_rewriteCandidates___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Rewrites_rewriteCandidates___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Rewrites_rewriteCandidates___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Rewrites_rewriteCandidates___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Rewrites_rewriteCandidates___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Rewrites_rewriteCandidates___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Rewrites_rewriteCandidates___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Rewrites_rewriteCandidates___closed__4_value:
    leanh::LeanStringObject<27> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        67, 97, 110, 100, 105, 100, 97, 116, 101, 32, 114, 101, 119, 114, 105, 116, 101, 32, 108,
        101, 109, 109, 97, 115, 58, 10, 0,
    ],
};
static mut l_Lean_Meta_Rewrites_rewriteCandidates___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Rewrites_rewriteCandidates___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Rewrites_rewriteCandidates___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Rewrites_rewriteCandidates___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Rewrites_findRewrites___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Rewrites_findRewrites___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Rewrites_findRewrites___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Rewrites_findRewrites___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__24_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4107_ = leanh::lean_unsigned_to_nat(2316440083);
    v___x_4108_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__23_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
    v___x_4109_ = l_Lean_Name_num___override(v___x_4108_, v___x_4107_);
    return v___x_4109_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__26_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4111_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__25_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
    v___x_4112_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__24_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__24_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__24_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
    v___x_4113_ = l_Lean_Name_str___override(v___x_4112_, v___x_4111_);
    return v___x_4113_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__28_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4115_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__27_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
    v___x_4116_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__26_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__26_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__26_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
    v___x_4117_ = l_Lean_Name_str___override(v___x_4116_, v___x_4115_);
    return v___x_4117_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__29_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4118_ = leanh::lean_unsigned_to_nat(2);
    v___x_4119_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__28_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__28_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__28_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
    v___x_4120_ = l_Lean_Name_num___override(v___x_4119_, v___x_4118_);
    return v___x_4120_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: u8 = 0;
    let mut v___x_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4122_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
    v___x_4123_ = 0;
    v___x_4124_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__29_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__29_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__29_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
    v___x_4125_ = l_Lean_registerTraceClass(v___x_4122_, v___x_4123_, v___x_4124_);
    return v___x_4125_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2____boxed(
    mut v_a_4126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4127_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
    return v_res_4127_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: u8 = 0;
    let mut v___x_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4146_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_;
    v___x_4147_ = 0;
    v___x_4148_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_;
    v___x_4149_ = l_Lean_registerTraceClass(v___x_4146_, v___x_4147_, v___x_4148_);
    return v___x_4149_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2____boxed(
    mut v_a_4150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4151_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_();
    return v_res_4151_;
}
pub unsafe fn l_Lean_Meta_Rewrites_rewriteResultLemma(
    mut v_r_4155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_eqProof_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: u8 = 0;
    v_eqProof_4156_ = leanh::lean_ctor_get(v_r_4155_, 1);
    v___x_4157_ = l_Lean_Meta_Rewrites_rewriteResultLemma___closed__1;
    v___x_4158_ = leanh::lean_unsigned_to_nat(6);
    v___x_4159_ = l_Lean_Expr_isAppOfArity(v_eqProof_4156_, v___x_4157_, v___x_4158_);
    if v___x_4159_ == 0 {
        let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4160_ = leanh::lean_box(0);
        return v___x_4160_;
    } else {
        let mut v___x_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4161_ = leanh::lean_unsigned_to_nat(5);
        v___x_4162_ = l_Lean_Expr_getAppNumArgs(v_eqProof_4156_);
        v___x_4163_ = lean_nat_sub(v___x_4162_, v___x_4161_);
        leanh::lean_dec(v___x_4162_);
        v___x_4164_ = leanh::lean_unsigned_to_nat(1);
        v___x_4165_ = lean_nat_sub(v___x_4163_, v___x_4164_);
        leanh::lean_dec(v___x_4163_);
        v___x_4166_ = l_Lean_Expr_getRevArg_x21(v_eqProof_4156_, v___x_4165_);
        v___x_4167_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4167_, 0, v___x_4166_);
        return v___x_4167_;
    }
}
pub unsafe fn l_Lean_Meta_Rewrites_rewriteResultLemma___boxed(
    mut v_r_4168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4169_ = l_Lean_Meta_Rewrites_rewriteResultLemma(v_r_4168_);
    leanh::lean_dec_ref(v_r_4168_);
    return v_res_4169_;
}
pub unsafe fn _init_l_Lean_Meta_Rewrites_forwardWeight() -> *mut leanh::LeanObject {
    let mut v___x_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4170_ = leanh::lean_unsigned_to_nat(2);
    return v___x_4170_;
}
pub unsafe fn _init_l_Lean_Meta_Rewrites_backwardWeight() -> *mut leanh::LeanObject {
    let mut v___x_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4171_ = leanh::lean_unsigned_to_nat(1);
    return v___x_4171_;
}
pub unsafe fn l_Lean_Meta_Rewrites_RwDirection_ctorIdx(
    mut v_x_4172_: u8,
) -> *mut leanh::LeanObject {
    if v_x_4172_ == 0 {
        let mut v___x_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4173_ = leanh::lean_unsigned_to_nat(0);
        return v___x_4173_;
    } else {
        let mut v___x_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4174_ = leanh::lean_unsigned_to_nat(1);
        return v___x_4174_;
    }
}
pub unsafe fn l_Lean_Meta_Rewrites_RwDirection_ctorIdx___boxed(
    mut v_x_4175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_4176_: u8 = 0;
    let mut v_res_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_4176_ = (leanh::lean_unbox(v_x_4175_) as u8);
    v_res_4177_ = l_Lean_Meta_Rewrites_RwDirection_ctorIdx(v_x_boxed_4176_);
    return v_res_4177_;
}
pub unsafe fn l_Lean_Meta_Rewrites_RwDirection_toCtorIdx(
    mut v_x_4178_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4179_ = l_Lean_Meta_Rewrites_RwDirection_ctorIdx(v_x_4178_);
    return v___x_4179_;
}
pub unsafe fn l_Lean_Meta_Rewrites_RwDirection_toCtorIdx___boxed(
    mut v_x_4180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_4181_: u8 = 0;
    let mut v_res_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_4181_ = (leanh::lean_unbox(v_x_4180_) as u8);
    v_res_4182_ = l_Lean_Meta_Rewrites_RwDirection_toCtorIdx(v_x_4__boxed_4181_);
    return v_res_4182_;
}
pub unsafe fn l_Lean_Meta_Rewrites_RwDirection_ctorElim___redArg(
    mut v_k_4183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_4183_);
    return v_k_4183_;
}
pub unsafe fn l_Lean_Meta_Rewrites_RwDirection_ctorElim___redArg___boxed(
    mut v_k_4184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4185_ = l_Lean_Meta_Rewrites_RwDirection_ctorElim___redArg(v_k_4184_);
    leanh::lean_dec(v_k_4184_);
    return v_res_4185_;
}
pub unsafe fn l_Lean_Meta_Rewrites_RwDirection_ctorElim(
    mut v_motive_4186_: *mut leanh::LeanObject,
    mut v_ctorIdx_4187_: *mut leanh::LeanObject,
    mut v_t_4188_: u8,
    mut v_h_4189_: *mut leanh::LeanObject,
    mut v_k_4190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_4190_);
    return v_k_4190_;
}
pub unsafe fn l_Lean_Meta_Rewrites_RwDirection_ctorElim___boxed(
    mut v_motive_4191_: *mut leanh::LeanObject,
    mut v_ctorIdx_4192_: *mut leanh::LeanObject,
    mut v_t_4193_: *mut leanh::LeanObject,
    mut v_h_4194_: *mut leanh::LeanObject,
    mut v_k_4195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_4196_: u8 = 0;
    let mut v_res_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4196_ = (leanh::lean_unbox(v_t_4193_) as u8);
    v_res_4197_ = l_Lean_Meta_Rewrites_RwDirection_ctorElim(
        v_motive_4191_,
        v_ctorIdx_4192_,
        v_t_boxed_4196_,
        v_h_4194_,
        v_k_4195_,
    );
    leanh::lean_dec(v_k_4195_);
    leanh::lean_dec(v_ctorIdx_4192_);
    return v_res_4197_;
}
pub unsafe fn l_Lean_Meta_Rewrites_RwDirection_forward_elim___redArg(
    mut v_forward_4198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_forward_4198_);
    return v_forward_4198_;
}
pub unsafe fn l_Lean_Meta_Rewrites_RwDirection_forward_elim___redArg___boxed(
    mut v_forward_4199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4200_ = l_Lean_Meta_Rewrites_RwDirection_forward_elim___redArg(v_forward_4199_);
    leanh::lean_dec(v_forward_4199_);
    return v_res_4200_;
}
pub unsafe fn l_Lean_Meta_Rewrites_RwDirection_forward_elim(
    mut v_motive_4201_: *mut leanh::LeanObject,
    mut v_t_4202_: u8,
    mut v_h_4203_: *mut leanh::LeanObject,
    mut v_forward_4204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_forward_4204_);
    return v_forward_4204_;
}
pub unsafe fn l_Lean_Meta_Rewrites_RwDirection_forward_elim___boxed(
    mut v_motive_4205_: *mut leanh::LeanObject,
    mut v_t_4206_: *mut leanh::LeanObject,
    mut v_h_4207_: *mut leanh::LeanObject,
    mut v_forward_4208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_4209_: u8 = 0;
    let mut v_res_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4209_ = (leanh::lean_unbox(v_t_4206_) as u8);
    v_res_4210_ = l_Lean_Meta_Rewrites_RwDirection_forward_elim(
        v_motive_4205_,
        v_t_boxed_4209_,
        v_h_4207_,
        v_forward_4208_,
    );
    leanh::lean_dec(v_forward_4208_);
    return v_res_4210_;
}
pub unsafe fn l_Lean_Meta_Rewrites_RwDirection_backward_elim___redArg(
    mut v_backward_4211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_backward_4211_);
    return v_backward_4211_;
}
pub unsafe fn l_Lean_Meta_Rewrites_RwDirection_backward_elim___redArg___boxed(
    mut v_backward_4212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4213_ = l_Lean_Meta_Rewrites_RwDirection_backward_elim___redArg(v_backward_4212_);
    leanh::lean_dec(v_backward_4212_);
    return v_res_4213_;
}
pub unsafe fn l_Lean_Meta_Rewrites_RwDirection_backward_elim(
    mut v_motive_4214_: *mut leanh::LeanObject,
    mut v_t_4215_: u8,
    mut v_h_4216_: *mut leanh::LeanObject,
    mut v_backward_4217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_backward_4217_);
    return v_backward_4217_;
}
pub unsafe fn l_Lean_Meta_Rewrites_RwDirection_backward_elim___boxed(
    mut v_motive_4218_: *mut leanh::LeanObject,
    mut v_t_4219_: *mut leanh::LeanObject,
    mut v_h_4220_: *mut leanh::LeanObject,
    mut v_backward_4221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_4222_: u8 = 0;
    let mut v_res_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4222_ = (leanh::lean_unbox(v_t_4219_) as u8);
    v_res_4223_ = l_Lean_Meta_Rewrites_RwDirection_backward_elim(
        v_motive_4218_,
        v_t_boxed_4222_,
        v_h_4220_,
        v_backward_4221_,
    );
    leanh::lean_dec(v_backward_4221_);
    return v_res_4223_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0(
    mut v_k_4224_: *mut leanh::LeanObject,
    mut v_b_4225_: *mut leanh::LeanObject,
    mut v_c_4226_: *mut leanh::LeanObject,
    mut v___y_4227_: *mut leanh::LeanObject,
    mut v___y_4228_: *mut leanh::LeanObject,
    mut v___y_4229_: *mut leanh::LeanObject,
    mut v___y_4230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_4230_);
    leanh::lean_inc_ref(v___y_4229_);
    leanh::lean_inc(v___y_4228_);
    leanh::lean_inc_ref(v___y_4227_);
    v___x_4232_ = leanh::lean_apply_7(
        v_k_4224_,
        v_b_4225_,
        v_c_4226_,
        v___y_4227_,
        v___y_4228_,
        v___y_4229_,
        v___y_4230_,
        leanh::lean_box(0),
    );
    return v___x_4232_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed(
    mut v_k_4233_: *mut leanh::LeanObject,
    mut v_b_4234_: *mut leanh::LeanObject,
    mut v_c_4235_: *mut leanh::LeanObject,
    mut v___y_4236_: *mut leanh::LeanObject,
    mut v___y_4237_: *mut leanh::LeanObject,
    mut v___y_4238_: *mut leanh::LeanObject,
    mut v___y_4239_: *mut leanh::LeanObject,
    mut v___y_4240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4241_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0(v_k_4233_, v_b_4234_, v_c_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_);
    leanh::lean_dec(v___y_4239_);
    leanh::lean_dec_ref(v___y_4238_);
    leanh::lean_dec(v___y_4237_);
    leanh::lean_dec_ref(v___y_4236_);
    return v_res_4241_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(
    mut v_type_4242_: *mut leanh::LeanObject,
    mut v_k_4243_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_4244_: u8,
    mut v_whnfType_4245_: u8,
    mut v___y_4246_: *mut leanh::LeanObject,
    mut v___y_4247_: *mut leanh::LeanObject,
    mut v___y_4248_: *mut leanh::LeanObject,
    mut v___y_4249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4256_: u8 = 0;
    let mut v___x_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4260_: u8 = 0;
    let mut v_a_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4264_: u8 = 0;
    let mut v___x_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4268_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4251_ = leanh::lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_4251_, 0, v_k_4243_);
                v___x_4252_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    leanh::lean_box(0),
                    v_type_4242_,
                    v___f_4251_,
                    v_cleanupAnnotations_4244_,
                    v_whnfType_4245_,
                    v___y_4246_,
                    v___y_4247_,
                    v___y_4248_,
                    v___y_4249_,
                );
                if leanh::lean_obj_tag(v___x_4252_) == 0 {
                    v_a_4253_ = leanh::lean_ctor_get(v___x_4252_, 0);
                    v_isSharedCheck_4260_ = (!leanh::lean_is_exclusive(v___x_4252_)) as u8;
                    if v_isSharedCheck_4260_ == 0 {
                        v___x_4255_ = v___x_4252_;
                        v_isShared_4256_ = v_isSharedCheck_4260_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4253_);
                        leanh::lean_dec(v___x_4252_);
                        v___x_4255_ = leanh::lean_box(0);
                        v_isShared_4256_ = v_isSharedCheck_4260_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4261_ = leanh::lean_ctor_get(v___x_4252_, 0);
                    v_isSharedCheck_4268_ = (!leanh::lean_is_exclusive(v___x_4252_)) as u8;
                    if v_isSharedCheck_4268_ == 0 {
                        v___x_4263_ = v___x_4252_;
                        v_isShared_4264_ = v_isSharedCheck_4268_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4261_);
                        leanh::lean_dec(v___x_4252_);
                        v___x_4263_ = leanh::lean_box(0);
                        v_isShared_4264_ = v_isSharedCheck_4268_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4256_ == 0 {
                    v___x_4258_ = v___x_4255_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4259_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_a_4253_);
                    v___x_4258_ = v_reuseFailAlloc_4259_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4258_;
            }
            3 => {
                if v_isShared_4264_ == 0 {
                    v___x_4266_ = v___x_4263_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4267_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4267_, 0, v_a_4261_);
                    v___x_4266_ = v_reuseFailAlloc_4267_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4266_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___boxed(
    mut v_type_4269_: *mut leanh::LeanObject,
    mut v_k_4270_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_4271_: *mut leanh::LeanObject,
    mut v_whnfType_4272_: *mut leanh::LeanObject,
    mut v___y_4273_: *mut leanh::LeanObject,
    mut v___y_4274_: *mut leanh::LeanObject,
    mut v___y_4275_: *mut leanh::LeanObject,
    mut v___y_4276_: *mut leanh::LeanObject,
    mut v___y_4277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4278_: u8 = 0;
    let mut v_whnfType_boxed_4279_: u8 = 0;
    let mut v_res_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4278_ = (leanh::lean_unbox(v_cleanupAnnotations_4271_) as u8);
    v_whnfType_boxed_4279_ = (leanh::lean_unbox(v_whnfType_4272_) as u8);
    v_res_4280_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(v_type_4269_, v_k_4270_, v_cleanupAnnotations_boxed_4278_, v_whnfType_boxed_4279_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_);
    leanh::lean_dec(v___y_4276_);
    leanh::lean_dec_ref(v___y_4275_);
    leanh::lean_dec(v___y_4274_);
    leanh::lean_dec_ref(v___y_4273_);
    return v_res_4280_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0(
    mut v_00_u03b1_4281_: *mut leanh::LeanObject,
    mut v_type_4282_: *mut leanh::LeanObject,
    mut v_k_4283_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_4284_: u8,
    mut v_whnfType_4285_: u8,
    mut v___y_4286_: *mut leanh::LeanObject,
    mut v___y_4287_: *mut leanh::LeanObject,
    mut v___y_4288_: *mut leanh::LeanObject,
    mut v___y_4289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4291_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(v_type_4282_, v_k_4283_, v_cleanupAnnotations_4284_, v_whnfType_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_);
    return v___x_4291_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___boxed(
    mut v_00_u03b1_4292_: *mut leanh::LeanObject,
    mut v_type_4293_: *mut leanh::LeanObject,
    mut v_k_4294_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_4295_: *mut leanh::LeanObject,
    mut v_whnfType_4296_: *mut leanh::LeanObject,
    mut v___y_4297_: *mut leanh::LeanObject,
    mut v___y_4298_: *mut leanh::LeanObject,
    mut v___y_4299_: *mut leanh::LeanObject,
    mut v___y_4300_: *mut leanh::LeanObject,
    mut v___y_4301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4302_: u8 = 0;
    let mut v_whnfType_boxed_4303_: u8 = 0;
    let mut v_res_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4302_ = (leanh::lean_unbox(v_cleanupAnnotations_4295_) as u8);
    v_whnfType_boxed_4303_ = (leanh::lean_unbox(v_whnfType_4296_) as u8);
    v_res_4304_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0(v_00_u03b1_4292_, v_type_4293_, v_k_4294_, v_cleanupAnnotations_boxed_4302_, v_whnfType_boxed_4303_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_);
    leanh::lean_dec(v___y_4300_);
    leanh::lean_dec_ref(v___y_4299_);
    leanh::lean_dec(v___y_4298_);
    leanh::lean_dec_ref(v___y_4297_);
    return v_res_4304_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg(
    mut v_k_4305_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_4306_: u8,
    mut v___y_4307_: *mut leanh::LeanObject,
    mut v___y_4308_: *mut leanh::LeanObject,
    mut v___y_4309_: *mut leanh::LeanObject,
    mut v___y_4310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4316_: u8 = 0;
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4320_: u8 = 0;
    let mut v_a_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4324_: u8 = 0;
    let mut v___x_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4328_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4312_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(
                    leanh::lean_box(0),
                    v_allowLevelAssignments_4306_,
                    v_k_4305_,
                    v___y_4307_,
                    v___y_4308_,
                    v___y_4309_,
                    v___y_4310_,
                );
                if leanh::lean_obj_tag(v___x_4312_) == 0 {
                    v_a_4313_ = leanh::lean_ctor_get(v___x_4312_, 0);
                    v_isSharedCheck_4320_ = (!leanh::lean_is_exclusive(v___x_4312_)) as u8;
                    if v_isSharedCheck_4320_ == 0 {
                        v___x_4315_ = v___x_4312_;
                        v_isShared_4316_ = v_isSharedCheck_4320_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4313_);
                        leanh::lean_dec(v___x_4312_);
                        v___x_4315_ = leanh::lean_box(0);
                        v_isShared_4316_ = v_isSharedCheck_4320_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4321_ = leanh::lean_ctor_get(v___x_4312_, 0);
                    v_isSharedCheck_4328_ = (!leanh::lean_is_exclusive(v___x_4312_)) as u8;
                    if v_isSharedCheck_4328_ == 0 {
                        v___x_4323_ = v___x_4312_;
                        v_isShared_4324_ = v_isSharedCheck_4328_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4321_);
                        leanh::lean_dec(v___x_4312_);
                        v___x_4323_ = leanh::lean_box(0);
                        v_isShared_4324_ = v_isSharedCheck_4328_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4316_ == 0 {
                    v___x_4318_ = v___x_4315_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4319_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_a_4313_);
                    v___x_4318_ = v_reuseFailAlloc_4319_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4318_;
            }
            3 => {
                if v_isShared_4324_ == 0 {
                    v___x_4326_ = v___x_4323_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4327_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4327_, 0, v_a_4321_);
                    v___x_4326_ = v_reuseFailAlloc_4327_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4326_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg___boxed(
    mut v_k_4329_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_4330_: *mut leanh::LeanObject,
    mut v___y_4331_: *mut leanh::LeanObject,
    mut v___y_4332_: *mut leanh::LeanObject,
    mut v___y_4333_: *mut leanh::LeanObject,
    mut v___y_4334_: *mut leanh::LeanObject,
    mut v___y_4335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_4336_: u8 = 0;
    let mut v_res_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_4336_ =
        (leanh::lean_unbox(v_allowLevelAssignments_4330_) as u8);
    v_res_4337_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg(v_k_4329_, v_allowLevelAssignments_boxed_4336_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_);
    leanh::lean_dec(v___y_4334_);
    leanh::lean_dec_ref(v___y_4333_);
    leanh::lean_dec(v___y_4332_);
    leanh::lean_dec_ref(v___y_4331_);
    return v_res_4337_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1(
    mut v_00_u03b1_4338_: *mut leanh::LeanObject,
    mut v_k_4339_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_4340_: u8,
    mut v___y_4341_: *mut leanh::LeanObject,
    mut v___y_4342_: *mut leanh::LeanObject,
    mut v___y_4343_: *mut leanh::LeanObject,
    mut v___y_4344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4346_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg(v_k_4339_, v_allowLevelAssignments_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_);
    return v___x_4346_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___boxed(
    mut v_00_u03b1_4347_: *mut leanh::LeanObject,
    mut v_k_4348_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_4349_: *mut leanh::LeanObject,
    mut v___y_4350_: *mut leanh::LeanObject,
    mut v___y_4351_: *mut leanh::LeanObject,
    mut v___y_4352_: *mut leanh::LeanObject,
    mut v___y_4353_: *mut leanh::LeanObject,
    mut v___y_4354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_4355_: u8 = 0;
    let mut v_res_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_4355_ =
        (leanh::lean_unbox(v_allowLevelAssignments_4349_) as u8);
    v_res_4356_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1(v_00_u03b1_4347_, v_k_4348_, v_allowLevelAssignments_boxed_4355_, v___y_4350_, v___y_4351_, v___y_4352_, v___y_4353_);
    leanh::lean_dec(v___y_4353_);
    leanh::lean_dec_ref(v___y_4352_);
    leanh::lean_dec(v___y_4351_);
    leanh::lean_dec_ref(v___y_4350_);
    return v_res_4356_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0(
    mut v_name_4361_: *mut leanh::LeanObject,
    mut v_x_4362_: *mut leanh::LeanObject,
    mut v_type_4363_: *mut leanh::LeanObject,
    mut v___y_4364_: *mut leanh::LeanObject,
    mut v___y_4365_: *mut leanh::LeanObject,
    mut v___y_4366_: *mut leanh::LeanObject,
    mut v___y_4367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4378_: u8 = 0;
    let mut v_str_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: u8 = 0;
    let mut v___x_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: u8 = 0;
    let mut v___x_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: u8 = 0;
    let mut v___x_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: u8 = 0;
    let mut v___x_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: u8 = 0;
    let mut v___x_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4404_: u8 = 0;
    let mut v___x_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4411_: u8 = 0;
    let mut v_a_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4415_: u8 = 0;
    let mut v___x_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4419_: u8 = 0;
    let mut v_a_4420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4423_: u8 = 0;
    let mut v___x_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4427_: u8 = 0;
    let mut v_reuseFailAlloc_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: u8 = 0;
    let mut v___x_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: u8 = 0;
    let mut v___x_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: u8 = 0;
    let mut v___x_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4449_: u8 = 0;
    let mut v___x_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4456_: u8 = 0;
    let mut v_a_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4460_: u8 = 0;
    let mut v___x_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4464_: u8 = 0;
    let mut v_a_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4468_: u8 = 0;
    let mut v___x_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4472_: u8 = 0;
    let mut v_reuseFailAlloc_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4474_: u8 = 0;
    let mut v_unused_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4372_ = l_Lean_Expr_getAppFnArgs(v_type_4363_);
                v_fst_4373_ = leanh::lean_ctor_get(v___x_4372_, 0);
                leanh::lean_inc(v_fst_4373_);
                if leanh::lean_obj_tag(v_fst_4373_) == 1 {
                    v_pre_4374_ = leanh::lean_ctor_get(v_fst_4373_, 0);
                    if leanh::lean_obj_tag(v_pre_4374_) == 0 {
                        v_snd_4375_ = leanh::lean_ctor_get(v___x_4372_, 1);
                        v_isSharedCheck_4474_ =
                            (!leanh::lean_is_exclusive(v___x_4372_)) as u8;
                        if v_isSharedCheck_4474_ == 0 {
                            v_unused_4475_ = leanh::lean_ctor_get(v___x_4372_, 0);
                            leanh::lean_dec(v_unused_4475_);
                            v___x_4377_ = v___x_4372_;
                            v_isShared_4378_ = v_isSharedCheck_4474_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_4375_);
                            leanh::lean_dec(v___x_4372_);
                            v___x_4377_ = leanh::lean_box(0);
                            v_isShared_4378_ = v_isSharedCheck_4474_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_fst_4373_, 2);
                        leanh::lean_dec_ref(v___x_4372_);
                        leanh::lean_dec(v_name_4361_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_4373_);
                    leanh::lean_dec_ref(v___x_4372_);
                    leanh::lean_dec(v_name_4361_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4370_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0;
                v___x_4371_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4371_, 0, v___x_4370_);
                return v___x_4371_;
            }
            2 => {
                v_str_4379_ = leanh::lean_ctor_get(v_fst_4373_, 1);
                leanh::lean_inc_ref(v_str_4379_);
                leanh::lean_dec_ref_known(v_fst_4373_, 2);
                v___x_4380_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1;
                v___x_4381_ = lean_string_dec_eq(v_str_4379_, v___x_4380_);
                if v___x_4381_ == 0 {
                    v___x_4382_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2;
                    v___x_4383_ = lean_string_dec_eq(v_str_4379_, v___x_4382_);
                    leanh::lean_dec_ref(v_str_4379_);
                    if v___x_4383_ == 0 {
                        leanh::lean_del_object(v___x_4377_);
                        leanh::lean_dec(v_snd_4375_);
                        leanh::lean_dec(v_name_4361_);
                        state = 1;
                        continue;
                    } else {
                        v___x_4384_ = lean_array_get_size(v_snd_4375_);
                        v___x_4385_ = leanh::lean_unsigned_to_nat(2);
                        v___x_4386_ = lean_nat_dec_eq(v___x_4384_, v___x_4385_);
                        if v___x_4386_ == 0 {
                            leanh::lean_del_object(v___x_4377_);
                            leanh::lean_dec(v_snd_4375_);
                            leanh::lean_dec(v_name_4361_);
                            state = 1;
                            continue;
                        } else {
                            v___x_4387_ = leanh::lean_unsigned_to_nat(0);
                            v___x_4388_ = lean_array_fget_borrowed(v_snd_4375_, v___x_4387_);
                            v___x_4389_ = 0;
                            v___x_4390_ = leanh::lean_box((v___x_4389_) as usize);
                            leanh::lean_inc(v_name_4361_);
                            if v_isShared_4378_ == 0 {
                                leanh::lean_ctor_set(v___x_4377_, 1, v___x_4390_);
                                leanh::lean_ctor_set(v___x_4377_, 0, v_name_4361_);
                                v___x_4392_ = v___x_4377_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_4428_ =
                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4428_,
                                    0,
                                    v_name_4361_,
                                );
                                leanh::lean_ctor_set(v_reuseFailAlloc_4428_, 1, v___x_4390_);
                                v___x_4392_ = v_reuseFailAlloc_4428_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_str_4379_);
                    v___x_4429_ = lean_array_get_size(v_snd_4375_);
                    v___x_4430_ = leanh::lean_unsigned_to_nat(3);
                    v___x_4431_ = lean_nat_dec_eq(v___x_4429_, v___x_4430_);
                    if v___x_4431_ == 0 {
                        leanh::lean_del_object(v___x_4377_);
                        leanh::lean_dec(v_snd_4375_);
                        leanh::lean_dec(v_name_4361_);
                        state = 1;
                        continue;
                    } else {
                        v___x_4432_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4433_ = lean_array_fget_borrowed(v_snd_4375_, v___x_4432_);
                        v___x_4434_ = 0;
                        v___x_4435_ = leanh::lean_box((v___x_4434_) as usize);
                        leanh::lean_inc(v_name_4361_);
                        if v_isShared_4378_ == 0 {
                            leanh::lean_ctor_set(v___x_4377_, 1, v___x_4435_);
                            leanh::lean_ctor_set(v___x_4377_, 0, v_name_4361_);
                            v___x_4437_ = v___x_4377_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_4473_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4473_, 0, v_name_4361_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4473_, 1, v___x_4435_);
                            v___x_4437_ = v_reuseFailAlloc_4473_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            3 => {
                leanh::lean_inc(v___x_4388_);
                v___x_4393_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(
                    v___x_4388_,
                    v___x_4392_,
                    v___y_4364_,
                    v___y_4365_,
                    v___y_4366_,
                    v___y_4367_,
                );
                if leanh::lean_obj_tag(v___x_4393_) == 0 {
                    v_a_4394_ = leanh::lean_ctor_get(v___x_4393_, 0);
                    leanh::lean_inc(v_a_4394_);
                    leanh::lean_dec_ref_known(v___x_4393_, 1);
                    v___x_4395_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4396_ = lean_array_fget(v_snd_4375_, v___x_4395_);
                    leanh::lean_dec(v_snd_4375_);
                    v___x_4397_ = 1;
                    v___x_4398_ = leanh::lean_box((v___x_4397_) as usize);
                    v___x_4399_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4399_, 0, v_name_4361_);
                    leanh::lean_ctor_set(v___x_4399_, 1, v___x_4398_);
                    v___x_4400_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(
                        v___x_4396_,
                        v___x_4399_,
                        v___y_4364_,
                        v___y_4365_,
                        v___y_4366_,
                        v___y_4367_,
                    );
                    if leanh::lean_obj_tag(v___x_4400_) == 0 {
                        v_a_4401_ = leanh::lean_ctor_get(v___x_4400_, 0);
                        v_isSharedCheck_4411_ =
                            (!leanh::lean_is_exclusive(v___x_4400_)) as u8;
                        if v_isSharedCheck_4411_ == 0 {
                            v___x_4403_ = v___x_4400_;
                            v_isShared_4404_ = v_isSharedCheck_4411_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4401_);
                            leanh::lean_dec(v___x_4400_);
                            v___x_4403_ = leanh::lean_box(0);
                            v_isShared_4404_ = v_isSharedCheck_4411_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_4394_);
                        v_a_4412_ = leanh::lean_ctor_get(v___x_4400_, 0);
                        v_isSharedCheck_4419_ =
                            (!leanh::lean_is_exclusive(v___x_4400_)) as u8;
                        if v_isSharedCheck_4419_ == 0 {
                            v___x_4414_ = v___x_4400_;
                            v_isShared_4415_ = v_isSharedCheck_4419_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4412_);
                            leanh::lean_dec(v___x_4400_);
                            v___x_4414_ = leanh::lean_box(0);
                            v_isShared_4415_ = v_isSharedCheck_4419_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_snd_4375_);
                    leanh::lean_dec(v_name_4361_);
                    v_a_4420_ = leanh::lean_ctor_get(v___x_4393_, 0);
                    v_isSharedCheck_4427_ = (!leanh::lean_is_exclusive(v___x_4393_)) as u8;
                    if v_isSharedCheck_4427_ == 0 {
                        v___x_4422_ = v___x_4393_;
                        v_isShared_4423_ = v_isSharedCheck_4427_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4420_);
                        leanh::lean_dec(v___x_4393_);
                        v___x_4422_ = leanh::lean_box(0);
                        v_isShared_4423_ = v_isSharedCheck_4427_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                v___x_4405_ = lean_mk_empty_array_with_capacity(v___x_4385_);
                v___x_4406_ = lean_array_push(v___x_4405_, v_a_4394_);
                v___x_4407_ = lean_array_push(v___x_4406_, v_a_4401_);
                if v_isShared_4404_ == 0 {
                    leanh::lean_ctor_set(v___x_4403_, 0, v___x_4407_);
                    v___x_4409_ = v___x_4403_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4410_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4410_, 0, v___x_4407_);
                    v___x_4409_ = v_reuseFailAlloc_4410_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4409_;
            }
            6 => {
                if v_isShared_4415_ == 0 {
                    v___x_4417_ = v___x_4414_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4418_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_a_4412_);
                    v___x_4417_ = v_reuseFailAlloc_4418_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4417_;
            }
            8 => {
                if v_isShared_4423_ == 0 {
                    v___x_4425_ = v___x_4422_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4426_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4426_, 0, v_a_4420_);
                    v___x_4425_ = v_reuseFailAlloc_4426_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4425_;
            }
            10 => {
                leanh::lean_inc(v___x_4433_);
                v___x_4438_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(
                    v___x_4433_,
                    v___x_4437_,
                    v___y_4364_,
                    v___y_4365_,
                    v___y_4366_,
                    v___y_4367_,
                );
                if leanh::lean_obj_tag(v___x_4438_) == 0 {
                    v_a_4439_ = leanh::lean_ctor_get(v___x_4438_, 0);
                    leanh::lean_inc(v_a_4439_);
                    leanh::lean_dec_ref_known(v___x_4438_, 1);
                    v___x_4440_ = leanh::lean_unsigned_to_nat(2);
                    v___x_4441_ = lean_array_fget(v_snd_4375_, v___x_4440_);
                    leanh::lean_dec(v_snd_4375_);
                    v___x_4442_ = 1;
                    v___x_4443_ = leanh::lean_box((v___x_4442_) as usize);
                    v___x_4444_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4444_, 0, v_name_4361_);
                    leanh::lean_ctor_set(v___x_4444_, 1, v___x_4443_);
                    v___x_4445_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(
                        v___x_4441_,
                        v___x_4444_,
                        v___y_4364_,
                        v___y_4365_,
                        v___y_4366_,
                        v___y_4367_,
                    );
                    if leanh::lean_obj_tag(v___x_4445_) == 0 {
                        v_a_4446_ = leanh::lean_ctor_get(v___x_4445_, 0);
                        v_isSharedCheck_4456_ =
                            (!leanh::lean_is_exclusive(v___x_4445_)) as u8;
                        if v_isSharedCheck_4456_ == 0 {
                            v___x_4448_ = v___x_4445_;
                            v_isShared_4449_ = v_isSharedCheck_4456_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4446_);
                            leanh::lean_dec(v___x_4445_);
                            v___x_4448_ = leanh::lean_box(0);
                            v_isShared_4449_ = v_isSharedCheck_4456_;
                            state = 11;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_4439_);
                        v_a_4457_ = leanh::lean_ctor_get(v___x_4445_, 0);
                        v_isSharedCheck_4464_ =
                            (!leanh::lean_is_exclusive(v___x_4445_)) as u8;
                        if v_isSharedCheck_4464_ == 0 {
                            v___x_4459_ = v___x_4445_;
                            v_isShared_4460_ = v_isSharedCheck_4464_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4457_);
                            leanh::lean_dec(v___x_4445_);
                            v___x_4459_ = leanh::lean_box(0);
                            v_isShared_4460_ = v_isSharedCheck_4464_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_snd_4375_);
                    leanh::lean_dec(v_name_4361_);
                    v_a_4465_ = leanh::lean_ctor_get(v___x_4438_, 0);
                    v_isSharedCheck_4472_ = (!leanh::lean_is_exclusive(v___x_4438_)) as u8;
                    if v_isSharedCheck_4472_ == 0 {
                        v___x_4467_ = v___x_4438_;
                        v_isShared_4468_ = v_isSharedCheck_4472_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4465_);
                        leanh::lean_dec(v___x_4438_);
                        v___x_4467_ = leanh::lean_box(0);
                        v_isShared_4468_ = v_isSharedCheck_4472_;
                        state = 15;
                        continue;
                    }
                }
            }
            11 => {
                v___x_4450_ = lean_mk_empty_array_with_capacity(v___x_4440_);
                v___x_4451_ = lean_array_push(v___x_4450_, v_a_4439_);
                v___x_4452_ = lean_array_push(v___x_4451_, v_a_4446_);
                if v_isShared_4449_ == 0 {
                    leanh::lean_ctor_set(v___x_4448_, 0, v___x_4452_);
                    v___x_4454_ = v___x_4448_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4455_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4455_, 0, v___x_4452_);
                    v___x_4454_ = v_reuseFailAlloc_4455_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4454_;
            }
            13 => {
                if v_isShared_4460_ == 0 {
                    v___x_4462_ = v___x_4459_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4463_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_a_4457_);
                    v___x_4462_ = v_reuseFailAlloc_4463_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4462_;
            }
            15 => {
                if v_isShared_4468_ == 0 {
                    v___x_4470_ = v___x_4467_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4471_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_a_4465_);
                    v___x_4470_ = v_reuseFailAlloc_4471_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4470_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___boxed(
    mut v_name_4476_: *mut leanh::LeanObject,
    mut v_x_4477_: *mut leanh::LeanObject,
    mut v_type_4478_: *mut leanh::LeanObject,
    mut v___y_4479_: *mut leanh::LeanObject,
    mut v___y_4480_: *mut leanh::LeanObject,
    mut v___y_4481_: *mut leanh::LeanObject,
    mut v___y_4482_: *mut leanh::LeanObject,
    mut v___y_4483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4484_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0(
        v_name_4476_,
        v_x_4477_,
        v_type_4478_,
        v___y_4479_,
        v___y_4480_,
        v___y_4481_,
        v___y_4482_,
    );
    leanh::lean_dec(v___y_4482_);
    leanh::lean_dec_ref(v___y_4481_);
    leanh::lean_dec(v___y_4480_);
    leanh::lean_dec_ref(v___y_4479_);
    leanh::lean_dec_ref(v_x_4477_);
    return v_res_4484_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1(
    mut v___x_4485_: u8,
    mut v___x_4486_: *mut leanh::LeanObject,
    mut v___f_4487_: *mut leanh::LeanObject,
    mut v___x_4488_: u8,
    mut v___y_4489_: *mut leanh::LeanObject,
    mut v___y_4490_: *mut leanh::LeanObject,
    mut v___y_4491_: *mut leanh::LeanObject,
    mut v___y_4492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_4495_: u8 = 0;
    let mut v_ctxApprox_4496_: u8 = 0;
    let mut v_quasiPatternApprox_4497_: u8 = 0;
    let mut v_constApprox_4498_: u8 = 0;
    let mut v_isDefEqStuckEx_4499_: u8 = 0;
    let mut v_unificationHints_4500_: u8 = 0;
    let mut v_proofIrrelevance_4501_: u8 = 0;
    let mut v_assignSyntheticOpaque_4502_: u8 = 0;
    let mut v_offsetCnstrs_4503_: u8 = 0;
    let mut v_etaStruct_4504_: u8 = 0;
    let mut v_univApprox_4505_: u8 = 0;
    let mut v_iota_4506_: u8 = 0;
    let mut v_beta_4507_: u8 = 0;
    let mut v_proj_4508_: u8 = 0;
    let mut v_zeta_4509_: u8 = 0;
    let mut v_zetaDelta_4510_: u8 = 0;
    let mut v_zetaUnused_4511_: u8 = 0;
    let mut v_zetaHave_4512_: u8 = 0;
    let mut v___x_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4515_: u8 = 0;
    let mut v_trackZetaDelta_4516_: u8 = 0;
    let mut v_zetaDeltaSet_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_4523_: u8 = 0;
    let mut v_inTypeClassResolution_4524_: u8 = 0;
    let mut v_cacheInferType_4525_: u8 = 0;
    let mut v_config_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: u64 = 0;
    let mut v___x_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4531_: u8 = 0;
    let mut v___x_4532_: u64 = 0;
    let mut v___x_4533_: u64 = 0;
    let mut v___x_4534_: u64 = 0;
    let mut v___x_4535_: u64 = 0;
    let mut v_key_4536_: u64 = 0;
    let mut v___x_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4542_: u8 = 0;
    let mut v_unused_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4551_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4494_ = l_Lean_Meta_Context_config(v___y_4489_);
                v_foApprox_4495_ = leanh::lean_ctor_get_uint8(v___x_4494_, 0 as u32);
                v_ctxApprox_4496_ = leanh::lean_ctor_get_uint8(v___x_4494_, 1 as u32);
                v_quasiPatternApprox_4497_ =
                    leanh::lean_ctor_get_uint8(v___x_4494_, 2 as u32);
                v_constApprox_4498_ = leanh::lean_ctor_get_uint8(v___x_4494_, 3 as u32);
                v_isDefEqStuckEx_4499_ = leanh::lean_ctor_get_uint8(v___x_4494_, 4 as u32);
                v_unificationHints_4500_ = leanh::lean_ctor_get_uint8(v___x_4494_, 5 as u32);
                v_proofIrrelevance_4501_ = leanh::lean_ctor_get_uint8(v___x_4494_, 6 as u32);
                v_assignSyntheticOpaque_4502_ =
                    leanh::lean_ctor_get_uint8(v___x_4494_, 7 as u32);
                v_offsetCnstrs_4503_ = leanh::lean_ctor_get_uint8(v___x_4494_, 8 as u32);
                v_etaStruct_4504_ = leanh::lean_ctor_get_uint8(v___x_4494_, 10 as u32);
                v_univApprox_4505_ = leanh::lean_ctor_get_uint8(v___x_4494_, 11 as u32);
                v_iota_4506_ = leanh::lean_ctor_get_uint8(v___x_4494_, 12 as u32);
                v_beta_4507_ = leanh::lean_ctor_get_uint8(v___x_4494_, 13 as u32);
                v_proj_4508_ = leanh::lean_ctor_get_uint8(v___x_4494_, 14 as u32);
                v_zeta_4509_ = leanh::lean_ctor_get_uint8(v___x_4494_, 15 as u32);
                v_zetaDelta_4510_ = leanh::lean_ctor_get_uint8(v___x_4494_, 16 as u32);
                v_zetaUnused_4511_ = leanh::lean_ctor_get_uint8(v___x_4494_, 17 as u32);
                v_zetaHave_4512_ = leanh::lean_ctor_get_uint8(v___x_4494_, 18 as u32);
                v_isSharedCheck_4551_ = (!leanh::lean_is_exclusive(v___x_4494_)) as u8;
                if v_isSharedCheck_4551_ == 0 {
                    v___x_4514_ = v___x_4494_;
                    v_isShared_4515_ = v_isSharedCheck_4551_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_4494_);
                    v___x_4514_ = leanh::lean_box(0);
                    v_isShared_4515_ = v_isSharedCheck_4551_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_4516_ = leanh::lean_ctor_get_uint8(
                    v___y_4489_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_4517_ = leanh::lean_ctor_get(v___y_4489_, 1);
                leanh::lean_inc(v_zetaDeltaSet_4517_);
                v_lctx_4518_ = leanh::lean_ctor_get(v___y_4489_, 2);
                leanh::lean_inc_ref(v_lctx_4518_);
                v_localInstances_4519_ = leanh::lean_ctor_get(v___y_4489_, 3);
                leanh::lean_inc_ref(v_localInstances_4519_);
                v_defEqCtx_x3f_4520_ = leanh::lean_ctor_get(v___y_4489_, 4);
                leanh::lean_inc(v_defEqCtx_x3f_4520_);
                v_synthPendingDepth_4521_ = leanh::lean_ctor_get(v___y_4489_, 5);
                leanh::lean_inc(v_synthPendingDepth_4521_);
                v_canUnfold_x3f_4522_ = leanh::lean_ctor_get(v___y_4489_, 6);
                leanh::lean_inc(v_canUnfold_x3f_4522_);
                v_univApprox_4523_ = leanh::lean_ctor_get_uint8(
                    v___y_4489_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_4524_ = leanh::lean_ctor_get_uint8(
                    v___y_4489_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_4525_ = leanh::lean_ctor_get_uint8(
                    v___y_4489_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_4515_ == 0 {
                    v_config_4527_ = v___x_4514_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4550_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4550_,
                        0 as u32,
                        v_foApprox_4495_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4550_,
                        1 as u32,
                        v_ctxApprox_4496_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4550_,
                        2 as u32,
                        v_quasiPatternApprox_4497_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4550_,
                        3 as u32,
                        v_constApprox_4498_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4550_,
                        4 as u32,
                        v_isDefEqStuckEx_4499_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4550_,
                        5 as u32,
                        v_unificationHints_4500_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4550_,
                        6 as u32,
                        v_proofIrrelevance_4501_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4550_,
                        7 as u32,
                        v_assignSyntheticOpaque_4502_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4550_,
                        8 as u32,
                        v_offsetCnstrs_4503_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4550_,
                        10 as u32,
                        v_etaStruct_4504_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4550_,
                        11 as u32,
                        v_univApprox_4505_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4550_,
                        12 as u32,
                        v_iota_4506_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4550_,
                        13 as u32,
                        v_beta_4507_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4550_,
                        14 as u32,
                        v_proj_4508_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4550_,
                        15 as u32,
                        v_zeta_4509_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4550_,
                        16 as u32,
                        v_zetaDelta_4510_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4550_,
                        17 as u32,
                        v_zetaUnused_4511_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4550_,
                        18 as u32,
                        v_zetaHave_4512_,
                    );
                    v_config_4527_ = v_reuseFailAlloc_4550_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(v_config_4527_, 9 as u32, v___x_4485_);
                v___x_4528_ = l_Lean_Meta_Context_configKey(v___y_4489_);
                v_isSharedCheck_4542_ = (!leanh::lean_is_exclusive(v___y_4489_)) as u8;
                if v_isSharedCheck_4542_ == 0 {
                    v_unused_4543_ = leanh::lean_ctor_get(v___y_4489_, 6);
                    leanh::lean_dec(v_unused_4543_);
                    v_unused_4544_ = leanh::lean_ctor_get(v___y_4489_, 5);
                    leanh::lean_dec(v_unused_4544_);
                    v_unused_4545_ = leanh::lean_ctor_get(v___y_4489_, 4);
                    leanh::lean_dec(v_unused_4545_);
                    v_unused_4546_ = leanh::lean_ctor_get(v___y_4489_, 3);
                    leanh::lean_dec(v_unused_4546_);
                    v_unused_4547_ = leanh::lean_ctor_get(v___y_4489_, 2);
                    leanh::lean_dec(v_unused_4547_);
                    v_unused_4548_ = leanh::lean_ctor_get(v___y_4489_, 1);
                    leanh::lean_dec(v_unused_4548_);
                    v_unused_4549_ = leanh::lean_ctor_get(v___y_4489_, 0);
                    leanh::lean_dec(v_unused_4549_);
                    v___x_4530_ = v___y_4489_;
                    v_isShared_4531_ = v_isSharedCheck_4542_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v___y_4489_);
                    v___x_4530_ = leanh::lean_box(0);
                    v_isShared_4531_ = v_isSharedCheck_4542_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4532_ = 3u64;
                v___x_4533_ = lean_uint64_shift_right(v___x_4528_, v___x_4532_);
                v___x_4534_ = lean_uint64_shift_left(v___x_4533_, v___x_4532_);
                v___x_4535_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_4485_);
                v_key_4536_ = lean_uint64_lor(v___x_4534_, v___x_4535_);
                v___x_4537_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_4537_, 0, v_config_4527_);
                leanh::lean_ctor_set_uint64(
                    v___x_4537_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_4536_,
                );
                if v_isShared_4531_ == 0 {
                    leanh::lean_ctor_set(v___x_4530_, 0, v___x_4537_);
                    v___x_4539_ = v___x_4530_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4541_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4541_, 0, v___x_4537_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4541_, 1, v_zetaDeltaSet_4517_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4541_, 2, v_lctx_4518_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4541_, 3, v_localInstances_4519_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4541_, 4, v_defEqCtx_x3f_4520_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4541_,
                        5,
                        v_synthPendingDepth_4521_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4541_, 6, v_canUnfold_x3f_4522_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4541_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                        v_trackZetaDelta_4516_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4541_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                        v_univApprox_4523_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4541_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                        v_inTypeClassResolution_4524_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4541_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                        v_cacheInferType_4525_,
                    );
                    v___x_4539_ = v_reuseFailAlloc_4541_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4540_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(v___x_4486_, v___f_4487_, v___x_4488_, v___x_4488_, v___x_4539_, v___y_4490_, v___y_4491_, v___y_4492_);
                leanh::lean_dec_ref(v___x_4539_);
                return v___x_4540_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1___boxed(
    mut v___x_4552_: *mut leanh::LeanObject,
    mut v___x_4553_: *mut leanh::LeanObject,
    mut v___f_4554_: *mut leanh::LeanObject,
    mut v___x_4555_: *mut leanh::LeanObject,
    mut v___y_4556_: *mut leanh::LeanObject,
    mut v___y_4557_: *mut leanh::LeanObject,
    mut v___y_4558_: *mut leanh::LeanObject,
    mut v___y_4559_: *mut leanh::LeanObject,
    mut v___y_4560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7247__boxed_4561_: u8 = 0;
    let mut v___x_7250__boxed_4562_: u8 = 0;
    let mut v_res_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7247__boxed_4561_ = (leanh::lean_unbox(v___x_4552_) as u8);
    v___x_7250__boxed_4562_ = (leanh::lean_unbox(v___x_4555_) as u8);
    v_res_4563_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1(
        v___x_7247__boxed_4561_,
        v___x_4553_,
        v___f_4554_,
        v___x_7250__boxed_4562_,
        v___y_4556_,
        v___y_4557_,
        v___y_4558_,
        v___y_4559_,
    );
    leanh::lean_dec(v___y_4559_);
    leanh::lean_dec_ref(v___y_4558_);
    leanh::lean_dec(v___y_4557_);
    return v_res_4563_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4565_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0;
    v___x_4566_ = lean_string_utf8_byte_size(v___x_4565_);
    return v___x_4566_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4570_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__4;
    v___x_4571_ = lean_string_utf8_byte_size(v___x_4570_);
    return v___x_4571_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport(
    mut v_name_4572_: *mut leanh::LeanObject,
    mut v_constInfo_4573_: *mut leanh::LeanObject,
    mut v_a_4574_: *mut leanh::LeanObject,
    mut v_a_4575_: *mut leanh::LeanObject,
    mut v_a_4576_: *mut leanh::LeanObject,
    mut v_a_4577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4579_: u8 = 0;
    let mut v___x_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: u8 = 0;
    let mut v___x_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: u8 = 0;
    let mut v___f_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: u8 = 0;
    let mut v___x_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: u8 = 0;
    let mut v___x_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4609_: u8 = 0;
    let mut v___x_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: u8 = 0;
    let mut v___x_4614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: u8 = 0;
    let mut v___x_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: u8 = 0;
    let mut v___x_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: u8 = 0;
    let mut v___x_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: u8 = 0;
    let mut v___x_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: u8 = 0;
    let mut v___x_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4579_ = l_Lean_ConstantInfo_isUnsafe(v_constInfo_4573_);
                if v___x_4579_ == 0 {
                    v___x_4580_ = lean_st_ref_get(v_a_4577_);
                    v_env_4584_ = leanh::lean_ctor_get(v___x_4580_, 0);
                    leanh::lean_inc_ref(v_env_4584_);
                    leanh::lean_dec(v___x_4580_);
                    leanh::lean_inc(v_name_4572_);
                    v___x_4585_ = l_Lean_Meta_allowCompletion(v_env_4584_, v_name_4572_);
                    if v___x_4585_ == 0 {
                        leanh::lean_dec(v_name_4572_);
                        state = 1;
                        continue;
                    } else {
                        if v___x_4579_ == 0 {
                            v___x_4586_ = lean_st_ref_get(v_a_4577_);
                            v_env_4590_ = leanh::lean_ctor_get(v___x_4586_, 0);
                            leanh::lean_inc_ref(v_env_4590_);
                            leanh::lean_dec(v___x_4586_);
                            leanh::lean_inc(v_name_4572_);
                            v___x_4591_ = l_Lean_Linter_isDeprecated(v_env_4590_, v_name_4572_);
                            if v___x_4591_ == 0 {
                                leanh::lean_inc(v_name_4572_);
                                v___f_4592_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                                leanh::lean_closure_set(v___f_4592_, 0, v_name_4572_);
                                if leanh::lean_obj_tag(v_name_4572_) == 1 {
                                    v_str_4607_ = leanh::lean_ctor_get(v_name_4572_, 1);
                                    v___x_4617_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2;
                                    v___x_4618_ = lean_string_dec_eq(v_str_4607_, v___x_4617_);
                                    if v___x_4618_ == 0 {
                                        v___x_4619_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3;
                                        v___x_4620_ = lean_string_dec_eq(v_str_4607_, v___x_4619_);
                                        if v___x_4620_ == 0 {
                                            v___x_4621_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__4;
                                            v___x_4622_ = lean_string_utf8_byte_size(v_str_4607_);
                                            v___x_4623_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5_once), _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5);
                                            v___x_4624_ = lean_nat_dec_le(v___x_4623_, v___x_4622_);
                                            if v___x_4624_ == 0 {
                                                v___y_4609_ = v___x_4591_;
                                                state = 4;
                                                continue;
                                            } else {
                                                v___x_4625_ = leanh::lean_unsigned_to_nat(0);
                                                v___x_4626_ =
                                                    lean_nat_sub(v___x_4622_, v___x_4623_);
                                                v___x_4627_ = lean_string_memcmp(
                                                    v_str_4607_,
                                                    v___x_4621_,
                                                    v___x_4626_,
                                                    v___x_4625_,
                                                    v___x_4623_,
                                                );
                                                leanh::lean_dec(v___x_4626_);
                                                v___y_4609_ = v___x_4627_;
                                                state = 4;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec_ref_known(v_name_4572_, 2);
                                            leanh::lean_dec_ref(v___f_4592_);
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec_ref_known(v_name_4572_, 2);
                                        leanh::lean_dec_ref(v___f_4592_);
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v___y_4594_ = v_a_4574_;
                                    v___y_4595_ = v_a_4575_;
                                    v___y_4596_ = v_a_4576_;
                                    v___y_4597_ = v_a_4577_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_name_4572_);
                                v___x_4628_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0;
                                v___x_4629_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_4629_, 0, v___x_4628_);
                                return v___x_4629_;
                            }
                        } else {
                            leanh::lean_dec(v_name_4572_);
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_name_4572_);
                    v___x_4630_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0;
                    v___x_4631_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4631_, 0, v___x_4630_);
                    return v___x_4631_;
                }
            }
            1 => {
                v___x_4582_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0;
                v___x_4583_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4583_, 0, v___x_4582_);
                return v___x_4583_;
            }
            2 => {
                v___x_4588_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0;
                v___x_4589_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4589_, 0, v___x_4588_);
                return v___x_4589_;
            }
            3 => {
                v___x_4598_ = l_Lean_Name_isMetaprogramming(v_name_4572_);
                if v___x_4598_ == 0 {
                    v___x_4599_ = l_Lean_ConstantInfo_type(v_constInfo_4573_);
                    v___x_4600_ = 2;
                    v___x_4601_ = leanh::lean_box((v___x_4600_) as usize);
                    v___x_4602_ = leanh::lean_box((v___x_4598_) as usize);
                    v___f_4603_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1___boxed as *mut core::ffi::c_void, 9, 4);
                    leanh::lean_closure_set(v___f_4603_, 0, v___x_4601_);
                    leanh::lean_closure_set(v___f_4603_, 1, v___x_4599_);
                    leanh::lean_closure_set(v___f_4603_, 2, v___f_4592_);
                    leanh::lean_closure_set(v___f_4603_, 3, v___x_4602_);
                    v___x_4604_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg(v___f_4603_, v___x_4598_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_);
                    return v___x_4604_;
                } else {
                    leanh::lean_dec_ref(v___f_4592_);
                    v___x_4605_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0;
                    v___x_4606_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4606_, 0, v___x_4605_);
                    return v___x_4606_;
                }
            }
            4 => {
                if v___y_4609_ == 0 {
                    v___x_4610_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0;
                    v___x_4611_ = lean_string_utf8_byte_size(v_str_4607_);
                    v___x_4612_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1_once), _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1);
                    v___x_4613_ = lean_nat_dec_le(v___x_4612_, v___x_4611_);
                    if v___x_4613_ == 0 {
                        v___y_4594_ = v_a_4574_;
                        v___y_4595_ = v_a_4575_;
                        v___y_4596_ = v_a_4576_;
                        v___y_4597_ = v_a_4577_;
                        state = 3;
                        continue;
                    } else {
                        v___x_4614_ = leanh::lean_unsigned_to_nat(0);
                        v___x_4615_ = lean_nat_sub(v___x_4611_, v___x_4612_);
                        v___x_4616_ = lean_string_memcmp(
                            v_str_4607_,
                            v___x_4610_,
                            v___x_4615_,
                            v___x_4614_,
                            v___x_4612_,
                        );
                        leanh::lean_dec(v___x_4615_);
                        if v___x_4616_ == 0 {
                            v___y_4594_ = v_a_4574_;
                            v___y_4595_ = v_a_4575_;
                            v___y_4596_ = v_a_4576_;
                            v___y_4597_ = v_a_4577_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec_ref_known(v_name_4572_, 2);
                            leanh::lean_dec_ref(v___f_4592_);
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref_known(v_name_4572_, 2);
                    leanh::lean_dec_ref(v___f_4592_);
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___boxed(
    mut v_name_4632_: *mut leanh::LeanObject,
    mut v_constInfo_4633_: *mut leanh::LeanObject,
    mut v_a_4634_: *mut leanh::LeanObject,
    mut v_a_4635_: *mut leanh::LeanObject,
    mut v_a_4636_: *mut leanh::LeanObject,
    mut v_a_4637_: *mut leanh::LeanObject,
    mut v_a_4638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4639_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport(
        v_name_4632_,
        v_constInfo_4633_,
        v_a_4634_,
        v_a_4635_,
        v_a_4636_,
        v_a_4637_,
    );
    leanh::lean_dec(v_a_4637_);
    leanh::lean_dec_ref(v_a_4636_);
    leanh::lean_dec(v_a_4635_);
    leanh::lean_dec_ref(v_a_4634_);
    leanh::lean_dec_ref(v_constInfo_4633_);
    return v_res_4639_;
}
pub unsafe fn l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0(
    mut v_a_4640_: *mut leanh::LeanObject,
    mut v_x_4641_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4642_: u8 = 0;
    let mut v_head_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4641_) == 0 {
                    v___x_4642_ = 0;
                    return v___x_4642_;
                } else {
                    v_head_4643_ = leanh::lean_ctor_get(v_x_4641_, 0);
                    v_tail_4644_ = leanh::lean_ctor_get(v_x_4641_, 1);
                    v___x_4645_ = l_Lean_instBEqFVarId_beq(v_a_4640_, v_head_4643_);
                    if v___x_4645_ == 0 {
                        v_x_4641_ = v_tail_4644_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4645_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0___boxed(
    mut v_a_4647_: *mut leanh::LeanObject,
    mut v_x_4648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4649_: u8 = 0;
    let mut v_r_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4649_ =
        l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0(v_a_4647_, v_x_4648_);
    leanh::lean_dec(v_x_4648_);
    leanh::lean_dec(v_a_4647_);
    v_r_4650_ = leanh::lean_box((v_res_4649_) as usize);
    return v_r_4650_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2(
    mut v_except_4651_: *mut leanh::LeanObject,
    mut v_as_4652_: *mut leanh::LeanObject,
    mut v_sz_4653_: usize,
    mut v_i_4654_: usize,
    mut v_b_4655_: *mut leanh::LeanObject,
    mut v___y_4656_: *mut leanh::LeanObject,
    mut v___y_4657_: *mut leanh::LeanObject,
    mut v___y_4658_: *mut leanh::LeanObject,
    mut v___y_4659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: usize = 0;
    let mut v___x_4664_: usize = 0;
    let mut v___x_4666_: u8 = 0;
    let mut v___x_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: u8 = 0;
    let mut v___x_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: u8 = 0;
    let mut v___x_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4680_: u8 = 0;
    let mut v_snd_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4684_: u8 = 0;
    let mut v___x_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4693_: u8 = 0;
    let mut v_str_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: u8 = 0;
    let mut v___x_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: u8 = 0;
    let mut v___x_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: u8 = 0;
    let mut v___x_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: u8 = 0;
    let mut v___x_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4736_: u8 = 0;
    let mut v_unused_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4741_: u8 = 0;
    let mut v___x_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4745_: u8 = 0;
    let mut v_isSharedCheck_4746_: u8 = 0;
    let mut v_unused_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4748_: u8 = 0;
    let mut v_unused_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4753_: u8 = 0;
    let mut v___x_4755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4757_: u8 = 0;
    let mut v_a_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4761_: u8 = 0;
    let mut v___x_4763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4765_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4666_ = lean_usize_dec_lt(v_i_4654_, v_sz_4653_);
                if v___x_4666_ == 0 {
                    v___x_4667_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4667_, 0, v_b_4655_);
                    return v___x_4667_;
                } else {
                    v_a_4668_ = lean_array_uget_borrowed(v_as_4652_, v_i_4654_);
                    v___x_4669_ = l_Lean_Expr_fvarId_x21(v_a_4668_);
                    v___x_4670_ = l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0(
                        v___x_4669_,
                        v_except_4651_,
                    );
                    leanh::lean_dec(v___x_4669_);
                    if v___x_4670_ == 0 {
                        leanh::lean_inc(v___y_4659_);
                        leanh::lean_inc_ref(v___y_4658_);
                        leanh::lean_inc(v___y_4657_);
                        leanh::lean_inc_ref(v___y_4656_);
                        leanh::lean_inc(v_a_4668_);
                        v___x_4671_ = lean_infer_type(
                            v_a_4668_,
                            v___y_4656_,
                            v___y_4657_,
                            v___y_4658_,
                            v___y_4659_,
                        );
                        if leanh::lean_obj_tag(v___x_4671_) == 0 {
                            v_a_4672_ = leanh::lean_ctor_get(v___x_4671_, 0);
                            leanh::lean_inc(v_a_4672_);
                            leanh::lean_dec_ref_known(v___x_4671_, 1);
                            v___x_4673_ = leanh::lean_box(0);
                            v___x_4674_ = 0;
                            v___x_4675_ = l_Lean_Meta_forallMetaTelescopeReducing(
                                v_a_4672_,
                                v___x_4673_,
                                v___x_4674_,
                                v___y_4656_,
                                v___y_4657_,
                                v___y_4658_,
                                v___y_4659_,
                            );
                            if leanh::lean_obj_tag(v___x_4675_) == 0 {
                                v_a_4676_ = leanh::lean_ctor_get(v___x_4675_, 0);
                                leanh::lean_inc(v_a_4676_);
                                leanh::lean_dec_ref_known(v___x_4675_, 1);
                                v_snd_4677_ = leanh::lean_ctor_get(v_a_4676_, 1);
                                v_isSharedCheck_4748_ =
                                    (!leanh::lean_is_exclusive(v_a_4676_)) as u8;
                                if v_isSharedCheck_4748_ == 0 {
                                    v_unused_4749_ = leanh::lean_ctor_get(v_a_4676_, 0);
                                    leanh::lean_dec(v_unused_4749_);
                                    v___x_4679_ = v_a_4676_;
                                    v_isShared_4680_ = v_isSharedCheck_4748_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_snd_4677_);
                                    leanh::lean_dec(v_a_4676_);
                                    v___x_4679_ = leanh::lean_box(0);
                                    v_isShared_4680_ = v_isSharedCheck_4748_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v_b_4655_);
                                v_a_4750_ = leanh::lean_ctor_get(v___x_4675_, 0);
                                v_isSharedCheck_4757_ =
                                    (!leanh::lean_is_exclusive(v___x_4675_)) as u8;
                                if v_isSharedCheck_4757_ == 0 {
                                    v___x_4752_ = v___x_4675_;
                                    v_isShared_4753_ = v_isSharedCheck_4757_;
                                    state = 13;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4750_);
                                    leanh::lean_dec(v___x_4675_);
                                    v___x_4752_ = leanh::lean_box(0);
                                    v_isShared_4753_ = v_isSharedCheck_4757_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_b_4655_);
                            v_a_4758_ = leanh::lean_ctor_get(v___x_4671_, 0);
                            v_isSharedCheck_4765_ =
                                (!leanh::lean_is_exclusive(v___x_4671_)) as u8;
                            if v_isSharedCheck_4765_ == 0 {
                                v___x_4760_ = v___x_4671_;
                                v_isShared_4761_ = v_isSharedCheck_4765_;
                                state = 15;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4758_);
                                leanh::lean_dec(v___x_4671_);
                                v___x_4760_ = leanh::lean_box(0);
                                v_isShared_4761_ = v_isSharedCheck_4765_;
                                state = 15;
                                continue;
                            }
                        }
                    } else {
                        v_a_4662_ = v_b_4655_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4663_ = 1usize;
                v___x_4664_ = lean_usize_add(v_i_4654_, v___x_4663_);
                v_i_4654_ = v___x_4664_;
                v_b_4655_ = v_a_4662_;
                state = 0;
                continue;
            }
            2 => {
                v_snd_4681_ = leanh::lean_ctor_get(v_snd_4677_, 1);
                v_isSharedCheck_4746_ = (!leanh::lean_is_exclusive(v_snd_4677_)) as u8;
                if v_isSharedCheck_4746_ == 0 {
                    v_unused_4747_ = leanh::lean_ctor_get(v_snd_4677_, 0);
                    leanh::lean_dec(v_unused_4747_);
                    v___x_4683_ = v_snd_4677_;
                    v_isShared_4684_ = v_isSharedCheck_4746_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4681_);
                    leanh::lean_dec(v_snd_4677_);
                    v___x_4683_ = leanh::lean_box(0);
                    v_isShared_4684_ = v_isSharedCheck_4746_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4685_ = l_Lean_Meta_whnfR(
                    v_snd_4681_,
                    v___y_4656_,
                    v___y_4657_,
                    v___y_4658_,
                    v___y_4659_,
                );
                if leanh::lean_obj_tag(v___x_4685_) == 0 {
                    v_a_4686_ = leanh::lean_ctor_get(v___x_4685_, 0);
                    leanh::lean_inc(v_a_4686_);
                    leanh::lean_dec_ref_known(v___x_4685_, 1);
                    v___x_4687_ = l_Lean_Expr_getAppFnArgs(v_a_4686_);
                    v_fst_4688_ = leanh::lean_ctor_get(v___x_4687_, 0);
                    leanh::lean_inc(v_fst_4688_);
                    if leanh::lean_obj_tag(v_fst_4688_) == 1 {
                        v_pre_4689_ = leanh::lean_ctor_get(v_fst_4688_, 0);
                        if leanh::lean_obj_tag(v_pre_4689_) == 0 {
                            v_snd_4690_ = leanh::lean_ctor_get(v___x_4687_, 1);
                            v_isSharedCheck_4736_ =
                                (!leanh::lean_is_exclusive(v___x_4687_)) as u8;
                            if v_isSharedCheck_4736_ == 0 {
                                v_unused_4737_ = leanh::lean_ctor_get(v___x_4687_, 0);
                                leanh::lean_dec(v_unused_4737_);
                                v___x_4692_ = v___x_4687_;
                                v_isShared_4693_ = v_isSharedCheck_4736_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_4690_);
                                leanh::lean_dec(v___x_4687_);
                                v___x_4692_ = leanh::lean_box(0);
                                v_isShared_4693_ = v_isSharedCheck_4736_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_fst_4688_, 2);
                            leanh::lean_dec_ref(v___x_4687_);
                            leanh::lean_del_object(v___x_4683_);
                            leanh::lean_del_object(v___x_4679_);
                            v_a_4662_ = v_b_4655_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_fst_4688_);
                        leanh::lean_dec_ref(v___x_4687_);
                        leanh::lean_del_object(v___x_4683_);
                        leanh::lean_del_object(v___x_4679_);
                        v_a_4662_ = v_b_4655_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4683_);
                    leanh::lean_del_object(v___x_4679_);
                    leanh::lean_dec_ref(v_b_4655_);
                    v_a_4738_ = leanh::lean_ctor_get(v___x_4685_, 0);
                    v_isSharedCheck_4745_ = (!leanh::lean_is_exclusive(v___x_4685_)) as u8;
                    if v_isSharedCheck_4745_ == 0 {
                        v___x_4740_ = v___x_4685_;
                        v_isShared_4741_ = v_isSharedCheck_4745_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4738_);
                        leanh::lean_dec(v___x_4685_);
                        v___x_4740_ = leanh::lean_box(0);
                        v_isShared_4741_ = v_isSharedCheck_4745_;
                        state = 11;
                        continue;
                    }
                }
            }
            4 => {
                v_str_4694_ = leanh::lean_ctor_get(v_fst_4688_, 1);
                leanh::lean_inc_ref(v_str_4694_);
                leanh::lean_dec_ref_known(v_fst_4688_, 2);
                v___x_4695_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1;
                v___x_4696_ = lean_string_dec_eq(v_str_4694_, v___x_4695_);
                if v___x_4696_ == 0 {
                    v___x_4697_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2;
                    v___x_4698_ = lean_string_dec_eq(v_str_4694_, v___x_4697_);
                    leanh::lean_dec_ref(v_str_4694_);
                    if v___x_4698_ == 0 {
                        leanh::lean_del_object(v___x_4692_);
                        leanh::lean_dec(v_snd_4690_);
                        leanh::lean_del_object(v___x_4683_);
                        leanh::lean_del_object(v___x_4679_);
                        v_a_4662_ = v_b_4655_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4699_ = lean_array_get_size(v_snd_4690_);
                        leanh::lean_dec(v_snd_4690_);
                        v___x_4700_ = leanh::lean_unsigned_to_nat(2);
                        v___x_4701_ = lean_nat_dec_eq(v___x_4699_, v___x_4700_);
                        if v___x_4701_ == 0 {
                            leanh::lean_del_object(v___x_4692_);
                            leanh::lean_del_object(v___x_4683_);
                            leanh::lean_del_object(v___x_4679_);
                            v_a_4662_ = v_b_4655_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4702_ = leanh::lean_box((v___x_4670_) as usize);
                            if v_isShared_4693_ == 0 {
                                leanh::lean_ctor_set(v___x_4692_, 1, v___x_4700_);
                                leanh::lean_ctor_set(v___x_4692_, 0, v___x_4702_);
                                v___x_4704_ = v___x_4692_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_4716_ =
                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_4716_, 0, v___x_4702_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_4716_, 1, v___x_4700_);
                                v___x_4704_ = v_reuseFailAlloc_4716_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_str_4694_);
                    v___x_4717_ = lean_array_get_size(v_snd_4690_);
                    leanh::lean_dec(v_snd_4690_);
                    v___x_4718_ = leanh::lean_unsigned_to_nat(3);
                    v___x_4719_ = lean_nat_dec_eq(v___x_4717_, v___x_4718_);
                    if v___x_4719_ == 0 {
                        leanh::lean_del_object(v___x_4692_);
                        leanh::lean_del_object(v___x_4683_);
                        leanh::lean_del_object(v___x_4679_);
                        v_a_4662_ = v_b_4655_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4720_ = leanh::lean_unsigned_to_nat(2);
                        v___x_4721_ = leanh::lean_box((v___x_4670_) as usize);
                        if v_isShared_4693_ == 0 {
                            leanh::lean_ctor_set(v___x_4692_, 1, v___x_4720_);
                            leanh::lean_ctor_set(v___x_4692_, 0, v___x_4721_);
                            v___x_4723_ = v___x_4692_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_4735_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4735_, 0, v___x_4721_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4735_, 1, v___x_4720_);
                            v___x_4723_ = v_reuseFailAlloc_4735_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            5 => {
                leanh::lean_inc(v_a_4668_);
                if v_isShared_4684_ == 0 {
                    leanh::lean_ctor_set(v___x_4683_, 1, v___x_4704_);
                    leanh::lean_ctor_set(v___x_4683_, 0, v_a_4668_);
                    v___x_4706_ = v___x_4683_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4715_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4715_, 0, v_a_4668_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4715_, 1, v___x_4704_);
                    v___x_4706_ = v_reuseFailAlloc_4715_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4707_ = lean_array_push(v_b_4655_, v___x_4706_);
                v___x_4708_ = leanh::lean_unsigned_to_nat(1);
                v___x_4709_ = leanh::lean_box((v___x_4666_) as usize);
                if v_isShared_4680_ == 0 {
                    leanh::lean_ctor_set(v___x_4679_, 1, v___x_4708_);
                    leanh::lean_ctor_set(v___x_4679_, 0, v___x_4709_);
                    v___x_4711_ = v___x_4679_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4714_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4714_, 0, v___x_4709_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4714_, 1, v___x_4708_);
                    v___x_4711_ = v_reuseFailAlloc_4714_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                leanh::lean_inc(v_a_4668_);
                v___x_4712_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4712_, 0, v_a_4668_);
                leanh::lean_ctor_set(v___x_4712_, 1, v___x_4711_);
                v___x_4713_ = lean_array_push(v___x_4707_, v___x_4712_);
                v_a_4662_ = v___x_4713_;
                state = 1;
                continue;
            }
            8 => {
                leanh::lean_inc(v_a_4668_);
                if v_isShared_4684_ == 0 {
                    leanh::lean_ctor_set(v___x_4683_, 1, v___x_4723_);
                    leanh::lean_ctor_set(v___x_4683_, 0, v_a_4668_);
                    v___x_4725_ = v___x_4683_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4734_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4734_, 0, v_a_4668_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4734_, 1, v___x_4723_);
                    v___x_4725_ = v_reuseFailAlloc_4734_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_4726_ = lean_array_push(v_b_4655_, v___x_4725_);
                v___x_4727_ = leanh::lean_unsigned_to_nat(1);
                v___x_4728_ = leanh::lean_box((v___x_4666_) as usize);
                if v_isShared_4680_ == 0 {
                    leanh::lean_ctor_set(v___x_4679_, 1, v___x_4727_);
                    leanh::lean_ctor_set(v___x_4679_, 0, v___x_4728_);
                    v___x_4730_ = v___x_4679_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4733_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4733_, 0, v___x_4728_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4733_, 1, v___x_4727_);
                    v___x_4730_ = v_reuseFailAlloc_4733_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                leanh::lean_inc(v_a_4668_);
                v___x_4731_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4731_, 0, v_a_4668_);
                leanh::lean_ctor_set(v___x_4731_, 1, v___x_4730_);
                v___x_4732_ = lean_array_push(v___x_4726_, v___x_4731_);
                v_a_4662_ = v___x_4732_;
                state = 1;
                continue;
            }
            11 => {
                if v_isShared_4741_ == 0 {
                    v___x_4743_ = v___x_4740_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4744_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4744_, 0, v_a_4738_);
                    v___x_4743_ = v_reuseFailAlloc_4744_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4743_;
            }
            13 => {
                if v_isShared_4753_ == 0 {
                    v___x_4755_ = v___x_4752_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4756_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4756_, 0, v_a_4750_);
                    v___x_4755_ = v_reuseFailAlloc_4756_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4755_;
            }
            15 => {
                if v_isShared_4761_ == 0 {
                    v___x_4763_ = v___x_4760_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4764_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4764_, 0, v_a_4758_);
                    v___x_4763_ = v_reuseFailAlloc_4764_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4763_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2___boxed(
    mut v_except_4766_: *mut leanh::LeanObject,
    mut v_as_4767_: *mut leanh::LeanObject,
    mut v_sz_4768_: *mut leanh::LeanObject,
    mut v_i_4769_: *mut leanh::LeanObject,
    mut v_b_4770_: *mut leanh::LeanObject,
    mut v___y_4771_: *mut leanh::LeanObject,
    mut v___y_4772_: *mut leanh::LeanObject,
    mut v___y_4773_: *mut leanh::LeanObject,
    mut v___y_4774_: *mut leanh::LeanObject,
    mut v___y_4775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4776_: usize = 0;
    let mut v_i_boxed_4777_: usize = 0;
    let mut v_res_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4776_ = leanh::lean_unbox_usize(v_sz_4768_);
    leanh::lean_dec(v_sz_4768_);
    v_i_boxed_4777_ = leanh::lean_unbox_usize(v_i_4769_);
    leanh::lean_dec(v_i_4769_);
    v_res_4778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2(v_except_4766_, v_as_4767_, v_sz_boxed_4776_, v_i_boxed_4777_, v_b_4770_, v___y_4771_, v___y_4772_, v___y_4773_, v___y_4774_);
    leanh::lean_dec(v___y_4774_);
    leanh::lean_dec_ref(v___y_4773_);
    leanh::lean_dec(v___y_4772_);
    leanh::lean_dec_ref(v___y_4771_);
    leanh::lean_dec_ref(v_as_4767_);
    leanh::lean_dec(v_except_4766_);
    return v_res_4778_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(
    mut v_as_4779_: *mut leanh::LeanObject,
    mut v_sz_4780_: usize,
    mut v_i_4781_: usize,
    mut v_b_4782_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4784_: u8 = 0;
    let mut v___x_4785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4789_: u8 = 0;
    let mut v___x_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: usize = 0;
    let mut v___x_4796_: usize = 0;
    let mut v_reuseFailAlloc_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: u8 = 0;
    let mut v___x_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4804_: u8 = 0;
    let mut v_unused_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4784_ = lean_usize_dec_lt(v_i_4781_, v_sz_4780_);
                if v___x_4784_ == 0 {
                    v___x_4785_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4785_, 0, v_b_4782_);
                    return v___x_4785_;
                } else {
                    v_snd_4786_ = leanh::lean_ctor_get(v_b_4782_, 1);
                    v_isSharedCheck_4804_ = (!leanh::lean_is_exclusive(v_b_4782_)) as u8;
                    if v_isSharedCheck_4804_ == 0 {
                        v_unused_4805_ = leanh::lean_ctor_get(v_b_4782_, 0);
                        leanh::lean_dec(v_unused_4805_);
                        v___x_4788_ = v_b_4782_;
                        v_isShared_4789_ = v_isSharedCheck_4804_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4786_);
                        leanh::lean_dec(v_b_4782_);
                        v___x_4788_ = leanh::lean_box(0);
                        v_isShared_4789_ = v_isSharedCheck_4804_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4790_ = leanh::lean_box(0);
                v_a_4799_ = lean_array_uget_borrowed(v_as_4779_, v_i_4781_);
                if leanh::lean_obj_tag(v_a_4799_) == 0 {
                    v_a_4792_ = v_snd_4786_;
                    state = 2;
                    continue;
                } else {
                    v_val_4800_ = leanh::lean_ctor_get(v_a_4799_, 0);
                    v___x_4801_ = l_Lean_LocalDecl_isImplementationDetail(v_val_4800_);
                    if v___x_4801_ == 0 {
                        leanh::lean_inc(v_val_4800_);
                        v___x_4802_ = l_Lean_LocalDecl_toExpr(v_val_4800_);
                        v___x_4803_ = lean_array_push(v_snd_4786_, v___x_4802_);
                        v_a_4792_ = v___x_4803_;
                        state = 2;
                        continue;
                    } else {
                        v_a_4792_ = v_snd_4786_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4789_ == 0 {
                    leanh::lean_ctor_set(v___x_4788_, 1, v_a_4792_);
                    leanh::lean_ctor_set(v___x_4788_, 0, v___x_4790_);
                    v___x_4794_ = v___x_4788_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4798_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 0, v___x_4790_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 1, v_a_4792_);
                    v___x_4794_ = v_reuseFailAlloc_4798_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4795_ = 1usize;
                v___x_4796_ = lean_usize_add(v_i_4781_, v___x_4795_);
                v_i_4781_ = v___x_4796_;
                v_b_4782_ = v___x_4794_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg___boxed(
    mut v_as_4806_: *mut leanh::LeanObject,
    mut v_sz_4807_: *mut leanh::LeanObject,
    mut v_i_4808_: *mut leanh::LeanObject,
    mut v_b_4809_: *mut leanh::LeanObject,
    mut v___y_4810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4811_: usize = 0;
    let mut v_i_boxed_4812_: usize = 0;
    let mut v_res_4813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4811_ = leanh::lean_unbox_usize(v_sz_4807_);
    leanh::lean_dec(v_sz_4807_);
    v_i_boxed_4812_ = leanh::lean_unbox_usize(v_i_4808_);
    leanh::lean_dec(v_i_4808_);
    v_res_4813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_as_4806_, v_sz_boxed_4811_, v_i_boxed_4812_, v_b_4809_);
    leanh::lean_dec_ref(v_as_4806_);
    return v_res_4813_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(
    mut v_as_4814_: *mut leanh::LeanObject,
    mut v_sz_4815_: usize,
    mut v_i_4816_: usize,
    mut v_b_4817_: *mut leanh::LeanObject,
    mut v___y_4818_: *mut leanh::LeanObject,
    mut v___y_4819_: *mut leanh::LeanObject,
    mut v___y_4820_: *mut leanh::LeanObject,
    mut v___y_4821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4823_: u8 = 0;
    let mut v___x_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4828_: u8 = 0;
    let mut v___x_4829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: usize = 0;
    let mut v___x_4835_: usize = 0;
    let mut v___x_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: u8 = 0;
    let mut v___x_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4843_: u8 = 0;
    let mut v_unused_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4823_ = lean_usize_dec_lt(v_i_4816_, v_sz_4815_);
                if v___x_4823_ == 0 {
                    v___x_4824_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4824_, 0, v_b_4817_);
                    return v___x_4824_;
                } else {
                    v_snd_4825_ = leanh::lean_ctor_get(v_b_4817_, 1);
                    v_isSharedCheck_4843_ = (!leanh::lean_is_exclusive(v_b_4817_)) as u8;
                    if v_isSharedCheck_4843_ == 0 {
                        v_unused_4844_ = leanh::lean_ctor_get(v_b_4817_, 0);
                        leanh::lean_dec(v_unused_4844_);
                        v___x_4827_ = v_b_4817_;
                        v_isShared_4828_ = v_isSharedCheck_4843_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4825_);
                        leanh::lean_dec(v_b_4817_);
                        v___x_4827_ = leanh::lean_box(0);
                        v_isShared_4828_ = v_isSharedCheck_4843_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4829_ = leanh::lean_box(0);
                v_a_4838_ = lean_array_uget_borrowed(v_as_4814_, v_i_4816_);
                if leanh::lean_obj_tag(v_a_4838_) == 0 {
                    v_a_4831_ = v_snd_4825_;
                    state = 2;
                    continue;
                } else {
                    v_val_4839_ = leanh::lean_ctor_get(v_a_4838_, 0);
                    v___x_4840_ = l_Lean_LocalDecl_isImplementationDetail(v_val_4839_);
                    if v___x_4840_ == 0 {
                        leanh::lean_inc(v_val_4839_);
                        v___x_4841_ = l_Lean_LocalDecl_toExpr(v_val_4839_);
                        v___x_4842_ = lean_array_push(v_snd_4825_, v___x_4841_);
                        v_a_4831_ = v___x_4842_;
                        state = 2;
                        continue;
                    } else {
                        v_a_4831_ = v_snd_4825_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4828_ == 0 {
                    leanh::lean_ctor_set(v___x_4827_, 1, v_a_4831_);
                    leanh::lean_ctor_set(v___x_4827_, 0, v___x_4829_);
                    v___x_4833_ = v___x_4827_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4837_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4837_, 0, v___x_4829_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4837_, 1, v_a_4831_);
                    v___x_4833_ = v_reuseFailAlloc_4837_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4834_ = 1usize;
                v___x_4835_ = lean_usize_add(v_i_4816_, v___x_4834_);
                v___x_4836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_as_4814_, v_sz_4815_, v___x_4835_, v___x_4833_);
                return v___x_4836_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5___boxed(
    mut v_as_4845_: *mut leanh::LeanObject,
    mut v_sz_4846_: *mut leanh::LeanObject,
    mut v_i_4847_: *mut leanh::LeanObject,
    mut v_b_4848_: *mut leanh::LeanObject,
    mut v___y_4849_: *mut leanh::LeanObject,
    mut v___y_4850_: *mut leanh::LeanObject,
    mut v___y_4851_: *mut leanh::LeanObject,
    mut v___y_4852_: *mut leanh::LeanObject,
    mut v___y_4853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4854_: usize = 0;
    let mut v_i_boxed_4855_: usize = 0;
    let mut v_res_4856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4854_ = leanh::lean_unbox_usize(v_sz_4846_);
    leanh::lean_dec(v_sz_4846_);
    v_i_boxed_4855_ = leanh::lean_unbox_usize(v_i_4847_);
    leanh::lean_dec(v_i_4847_);
    v_res_4856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(v_as_4845_, v_sz_boxed_4854_, v_i_boxed_4855_, v_b_4848_, v___y_4849_, v___y_4850_, v___y_4851_, v___y_4852_);
    leanh::lean_dec(v___y_4852_);
    leanh::lean_dec_ref(v___y_4851_);
    leanh::lean_dec(v___y_4850_);
    leanh::lean_dec_ref(v___y_4849_);
    leanh::lean_dec_ref(v_as_4845_);
    return v_res_4856_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(
    mut v_init_4857_: *mut leanh::LeanObject,
    mut v_n_4858_: *mut leanh::LeanObject,
    mut v_b_4859_: *mut leanh::LeanObject,
    mut v___y_4860_: *mut leanh::LeanObject,
    mut v___y_4861_: *mut leanh::LeanObject,
    mut v___y_4862_: *mut leanh::LeanObject,
    mut v___y_4863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_4865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4868_: usize = 0;
    let mut v___x_4869_: usize = 0;
    let mut v___x_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4874_: u8 = 0;
    let mut v_fst_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4885_: u8 = 0;
    let mut v_a_4886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4889_: u8 = 0;
    let mut v___x_4891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4893_: u8 = 0;
    let mut v_vs_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4897_: usize = 0;
    let mut v___x_4898_: usize = 0;
    let mut v___x_4899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4903_: u8 = 0;
    let mut v_fst_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4914_: u8 = 0;
    let mut v_a_4915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4918_: u8 = 0;
    let mut v___x_4920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4922_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_n_4858_) == 0 {
                    v_cs_4865_ = leanh::lean_ctor_get(v_n_4858_, 0);
                    v___x_4866_ = leanh::lean_box(0);
                    v___x_4867_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4867_, 0, v___x_4866_);
                    leanh::lean_ctor_set(v___x_4867_, 1, v_b_4859_);
                    v_sz_4868_ = lean_array_size(v_cs_4865_);
                    v___x_4869_ = 0usize;
                    v___x_4870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(v_init_4857_, v_cs_4865_, v_sz_4868_, v___x_4869_, v___x_4867_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_);
                    if leanh::lean_obj_tag(v___x_4870_) == 0 {
                        v_a_4871_ = leanh::lean_ctor_get(v___x_4870_, 0);
                        v_isSharedCheck_4885_ =
                            (!leanh::lean_is_exclusive(v___x_4870_)) as u8;
                        if v_isSharedCheck_4885_ == 0 {
                            v___x_4873_ = v___x_4870_;
                            v_isShared_4874_ = v_isSharedCheck_4885_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4871_);
                            leanh::lean_dec(v___x_4870_);
                            v___x_4873_ = leanh::lean_box(0);
                            v_isShared_4874_ = v_isSharedCheck_4885_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4886_ = leanh::lean_ctor_get(v___x_4870_, 0);
                        v_isSharedCheck_4893_ =
                            (!leanh::lean_is_exclusive(v___x_4870_)) as u8;
                        if v_isSharedCheck_4893_ == 0 {
                            v___x_4888_ = v___x_4870_;
                            v_isShared_4889_ = v_isSharedCheck_4893_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4886_);
                            leanh::lean_dec(v___x_4870_);
                            v___x_4888_ = leanh::lean_box(0);
                            v_isShared_4889_ = v_isSharedCheck_4893_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_4894_ = leanh::lean_ctor_get(v_n_4858_, 0);
                    v___x_4895_ = leanh::lean_box(0);
                    v___x_4896_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4896_, 0, v___x_4895_);
                    leanh::lean_ctor_set(v___x_4896_, 1, v_b_4859_);
                    v_sz_4897_ = lean_array_size(v_vs_4894_);
                    v___x_4898_ = 0usize;
                    v___x_4899_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(v_vs_4894_, v_sz_4897_, v___x_4898_, v___x_4896_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_);
                    if leanh::lean_obj_tag(v___x_4899_) == 0 {
                        v_a_4900_ = leanh::lean_ctor_get(v___x_4899_, 0);
                        v_isSharedCheck_4914_ =
                            (!leanh::lean_is_exclusive(v___x_4899_)) as u8;
                        if v_isSharedCheck_4914_ == 0 {
                            v___x_4902_ = v___x_4899_;
                            v_isShared_4903_ = v_isSharedCheck_4914_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4900_);
                            leanh::lean_dec(v___x_4899_);
                            v___x_4902_ = leanh::lean_box(0);
                            v_isShared_4903_ = v_isSharedCheck_4914_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_4915_ = leanh::lean_ctor_get(v___x_4899_, 0);
                        v_isSharedCheck_4922_ =
                            (!leanh::lean_is_exclusive(v___x_4899_)) as u8;
                        if v_isSharedCheck_4922_ == 0 {
                            v___x_4917_ = v___x_4899_;
                            v_isShared_4918_ = v_isSharedCheck_4922_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4915_);
                            leanh::lean_dec(v___x_4899_);
                            v___x_4917_ = leanh::lean_box(0);
                            v_isShared_4918_ = v_isSharedCheck_4922_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_4875_ = leanh::lean_ctor_get(v_a_4871_, 0);
                if leanh::lean_obj_tag(v_fst_4875_) == 0 {
                    v_snd_4876_ = leanh::lean_ctor_get(v_a_4871_, 1);
                    leanh::lean_inc(v_snd_4876_);
                    leanh::lean_dec(v_a_4871_);
                    v___x_4877_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4877_, 0, v_snd_4876_);
                    if v_isShared_4874_ == 0 {
                        leanh::lean_ctor_set(v___x_4873_, 0, v___x_4877_);
                        v___x_4879_ = v___x_4873_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4880_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4880_, 0, v___x_4877_);
                        v___x_4879_ = v_reuseFailAlloc_4880_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_4875_);
                    leanh::lean_dec(v_a_4871_);
                    v_val_4881_ = leanh::lean_ctor_get(v_fst_4875_, 0);
                    leanh::lean_inc(v_val_4881_);
                    leanh::lean_dec_ref_known(v_fst_4875_, 1);
                    if v_isShared_4874_ == 0 {
                        leanh::lean_ctor_set(v___x_4873_, 0, v_val_4881_);
                        v___x_4883_ = v___x_4873_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4884_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4884_, 0, v_val_4881_);
                        v___x_4883_ = v_reuseFailAlloc_4884_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4879_;
            }
            3 => {
                return v___x_4883_;
            }
            4 => {
                if v_isShared_4889_ == 0 {
                    v___x_4891_ = v___x_4888_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4892_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4892_, 0, v_a_4886_);
                    v___x_4891_ = v_reuseFailAlloc_4892_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4891_;
            }
            6 => {
                v_fst_4904_ = leanh::lean_ctor_get(v_a_4900_, 0);
                if leanh::lean_obj_tag(v_fst_4904_) == 0 {
                    v_snd_4905_ = leanh::lean_ctor_get(v_a_4900_, 1);
                    leanh::lean_inc(v_snd_4905_);
                    leanh::lean_dec(v_a_4900_);
                    v___x_4906_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4906_, 0, v_snd_4905_);
                    if v_isShared_4903_ == 0 {
                        leanh::lean_ctor_set(v___x_4902_, 0, v___x_4906_);
                        v___x_4908_ = v___x_4902_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4909_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4909_, 0, v___x_4906_);
                        v___x_4908_ = v_reuseFailAlloc_4909_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_4904_);
                    leanh::lean_dec(v_a_4900_);
                    v_val_4910_ = leanh::lean_ctor_get(v_fst_4904_, 0);
                    leanh::lean_inc(v_val_4910_);
                    leanh::lean_dec_ref_known(v_fst_4904_, 1);
                    if v_isShared_4903_ == 0 {
                        leanh::lean_ctor_set(v___x_4902_, 0, v_val_4910_);
                        v___x_4912_ = v___x_4902_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4913_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4913_, 0, v_val_4910_);
                        v___x_4912_ = v_reuseFailAlloc_4913_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_4908_;
            }
            8 => {
                return v___x_4912_;
            }
            9 => {
                if v_isShared_4918_ == 0 {
                    v___x_4920_ = v___x_4917_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4921_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4921_, 0, v_a_4915_);
                    v___x_4920_ = v_reuseFailAlloc_4921_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4920_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(
    mut v_init_4923_: *mut leanh::LeanObject,
    mut v_as_4924_: *mut leanh::LeanObject,
    mut v_sz_4925_: usize,
    mut v_i_4926_: usize,
    mut v_b_4927_: *mut leanh::LeanObject,
    mut v___y_4928_: *mut leanh::LeanObject,
    mut v___y_4929_: *mut leanh::LeanObject,
    mut v___y_4930_: *mut leanh::LeanObject,
    mut v___y_4931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4933_: u8 = 0;
    let mut v___x_4934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4938_: u8 = 0;
    let mut v_a_4939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4944_: u8 = 0;
    let mut v___x_4945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: usize = 0;
    let mut v___x_4957_: usize = 0;
    let mut v_reuseFailAlloc_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4960_: u8 = 0;
    let mut v_a_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4964_: u8 = 0;
    let mut v___x_4966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4968_: u8 = 0;
    let mut v_isSharedCheck_4969_: u8 = 0;
    let mut v_unused_4970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4933_ = lean_usize_dec_lt(v_i_4926_, v_sz_4925_);
                if v___x_4933_ == 0 {
                    v___x_4934_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4934_, 0, v_b_4927_);
                    return v___x_4934_;
                } else {
                    v_snd_4935_ = leanh::lean_ctor_get(v_b_4927_, 1);
                    v_isSharedCheck_4969_ = (!leanh::lean_is_exclusive(v_b_4927_)) as u8;
                    if v_isSharedCheck_4969_ == 0 {
                        v_unused_4970_ = leanh::lean_ctor_get(v_b_4927_, 0);
                        leanh::lean_dec(v_unused_4970_);
                        v___x_4937_ = v_b_4927_;
                        v_isShared_4938_ = v_isSharedCheck_4969_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4935_);
                        leanh::lean_dec(v_b_4927_);
                        v___x_4937_ = leanh::lean_box(0);
                        v_isShared_4938_ = v_isSharedCheck_4969_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4939_ = lean_array_uget_borrowed(v_as_4924_, v_i_4926_);
                leanh::lean_inc(v_snd_4935_);
                v___x_4940_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_4923_, v_a_4939_, v_snd_4935_, v___y_4928_, v___y_4929_, v___y_4930_, v___y_4931_);
                if leanh::lean_obj_tag(v___x_4940_) == 0 {
                    v_a_4941_ = leanh::lean_ctor_get(v___x_4940_, 0);
                    v_isSharedCheck_4960_ = (!leanh::lean_is_exclusive(v___x_4940_)) as u8;
                    if v_isSharedCheck_4960_ == 0 {
                        v___x_4943_ = v___x_4940_;
                        v_isShared_4944_ = v_isSharedCheck_4960_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4941_);
                        leanh::lean_dec(v___x_4940_);
                        v___x_4943_ = leanh::lean_box(0);
                        v_isShared_4944_ = v_isSharedCheck_4960_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4937_);
                    leanh::lean_dec(v_snd_4935_);
                    v_a_4961_ = leanh::lean_ctor_get(v___x_4940_, 0);
                    v_isSharedCheck_4968_ = (!leanh::lean_is_exclusive(v___x_4940_)) as u8;
                    if v_isSharedCheck_4968_ == 0 {
                        v___x_4963_ = v___x_4940_;
                        v_isShared_4964_ = v_isSharedCheck_4968_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4961_);
                        leanh::lean_dec(v___x_4940_);
                        v___x_4963_ = leanh::lean_box(0);
                        v_isShared_4964_ = v_isSharedCheck_4968_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_4941_) == 0 {
                    v___x_4945_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4945_, 0, v_a_4941_);
                    if v_isShared_4938_ == 0 {
                        leanh::lean_ctor_set(v___x_4937_, 0, v___x_4945_);
                        v___x_4947_ = v___x_4937_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4951_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4951_, 0, v___x_4945_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4951_, 1, v_snd_4935_);
                        v___x_4947_ = v_reuseFailAlloc_4951_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4943_);
                    leanh::lean_dec(v_snd_4935_);
                    v_a_4952_ = leanh::lean_ctor_get(v_a_4941_, 0);
                    leanh::lean_inc(v_a_4952_);
                    leanh::lean_dec_ref_known(v_a_4941_, 1);
                    v___x_4953_ = leanh::lean_box(0);
                    if v_isShared_4938_ == 0 {
                        leanh::lean_ctor_set(v___x_4937_, 1, v_a_4952_);
                        leanh::lean_ctor_set(v___x_4937_, 0, v___x_4953_);
                        v___x_4955_ = v___x_4937_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4959_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4959_, 0, v___x_4953_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4959_, 1, v_a_4952_);
                        v___x_4955_ = v_reuseFailAlloc_4959_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4944_ == 0 {
                    leanh::lean_ctor_set(v___x_4943_, 0, v___x_4947_);
                    v___x_4949_ = v___x_4943_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4950_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4950_, 0, v___x_4947_);
                    v___x_4949_ = v_reuseFailAlloc_4950_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4949_;
            }
            5 => {
                v___x_4956_ = 1usize;
                v___x_4957_ = lean_usize_add(v_i_4926_, v___x_4956_);
                v_i_4926_ = v___x_4957_;
                v_b_4927_ = v___x_4955_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_4964_ == 0 {
                    v___x_4966_ = v___x_4963_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4967_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4967_, 0, v_a_4961_);
                    v___x_4966_ = v_reuseFailAlloc_4967_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4966_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4___boxed(
    mut v_init_4971_: *mut leanh::LeanObject,
    mut v_as_4972_: *mut leanh::LeanObject,
    mut v_sz_4973_: *mut leanh::LeanObject,
    mut v_i_4974_: *mut leanh::LeanObject,
    mut v_b_4975_: *mut leanh::LeanObject,
    mut v___y_4976_: *mut leanh::LeanObject,
    mut v___y_4977_: *mut leanh::LeanObject,
    mut v___y_4978_: *mut leanh::LeanObject,
    mut v___y_4979_: *mut leanh::LeanObject,
    mut v___y_4980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4981_: usize = 0;
    let mut v_i_boxed_4982_: usize = 0;
    let mut v_res_4983_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4981_ = leanh::lean_unbox_usize(v_sz_4973_);
    leanh::lean_dec(v_sz_4973_);
    v_i_boxed_4982_ = leanh::lean_unbox_usize(v_i_4974_);
    leanh::lean_dec(v_i_4974_);
    v_res_4983_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(v_init_4971_, v_as_4972_, v_sz_boxed_4981_, v_i_boxed_4982_, v_b_4975_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_);
    leanh::lean_dec(v___y_4979_);
    leanh::lean_dec_ref(v___y_4978_);
    leanh::lean_dec(v___y_4977_);
    leanh::lean_dec_ref(v___y_4976_);
    leanh::lean_dec_ref(v_as_4972_);
    leanh::lean_dec_ref(v_init_4971_);
    return v_res_4983_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2___boxed(
    mut v_init_4984_: *mut leanh::LeanObject,
    mut v_n_4985_: *mut leanh::LeanObject,
    mut v_b_4986_: *mut leanh::LeanObject,
    mut v___y_4987_: *mut leanh::LeanObject,
    mut v___y_4988_: *mut leanh::LeanObject,
    mut v___y_4989_: *mut leanh::LeanObject,
    mut v___y_4990_: *mut leanh::LeanObject,
    mut v___y_4991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4992_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4992_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_4984_, v_n_4985_, v_b_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_);
    leanh::lean_dec(v___y_4990_);
    leanh::lean_dec_ref(v___y_4989_);
    leanh::lean_dec(v___y_4988_);
    leanh::lean_dec_ref(v___y_4987_);
    leanh::lean_dec_ref(v_n_4985_);
    leanh::lean_dec_ref(v_init_4984_);
    return v_res_4992_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(
    mut v_as_4993_: *mut leanh::LeanObject,
    mut v_sz_4994_: usize,
    mut v_i_4995_: usize,
    mut v_b_4996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4998_: u8 = 0;
    let mut v___x_4999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5003_: u8 = 0;
    let mut v___x_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: usize = 0;
    let mut v___x_5010_: usize = 0;
    let mut v_reuseFailAlloc_5012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: u8 = 0;
    let mut v___x_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5018_: u8 = 0;
    let mut v_unused_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4998_ = lean_usize_dec_lt(v_i_4995_, v_sz_4994_);
                if v___x_4998_ == 0 {
                    v___x_4999_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4999_, 0, v_b_4996_);
                    return v___x_4999_;
                } else {
                    v_snd_5000_ = leanh::lean_ctor_get(v_b_4996_, 1);
                    v_isSharedCheck_5018_ = (!leanh::lean_is_exclusive(v_b_4996_)) as u8;
                    if v_isSharedCheck_5018_ == 0 {
                        v_unused_5019_ = leanh::lean_ctor_get(v_b_4996_, 0);
                        leanh::lean_dec(v_unused_5019_);
                        v___x_5002_ = v_b_4996_;
                        v_isShared_5003_ = v_isSharedCheck_5018_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_5000_);
                        leanh::lean_dec(v_b_4996_);
                        v___x_5002_ = leanh::lean_box(0);
                        v_isShared_5003_ = v_isSharedCheck_5018_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5004_ = leanh::lean_box(0);
                v_a_5013_ = lean_array_uget_borrowed(v_as_4993_, v_i_4995_);
                if leanh::lean_obj_tag(v_a_5013_) == 0 {
                    v_a_5006_ = v_snd_5000_;
                    state = 2;
                    continue;
                } else {
                    v_val_5014_ = leanh::lean_ctor_get(v_a_5013_, 0);
                    v___x_5015_ = l_Lean_LocalDecl_isImplementationDetail(v_val_5014_);
                    if v___x_5015_ == 0 {
                        leanh::lean_inc(v_val_5014_);
                        v___x_5016_ = l_Lean_LocalDecl_toExpr(v_val_5014_);
                        v___x_5017_ = lean_array_push(v_snd_5000_, v___x_5016_);
                        v_a_5006_ = v___x_5017_;
                        state = 2;
                        continue;
                    } else {
                        v_a_5006_ = v_snd_5000_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5003_ == 0 {
                    leanh::lean_ctor_set(v___x_5002_, 1, v_a_5006_);
                    leanh::lean_ctor_set(v___x_5002_, 0, v___x_5004_);
                    v___x_5008_ = v___x_5002_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5012_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5012_, 0, v___x_5004_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5012_, 1, v_a_5006_);
                    v___x_5008_ = v_reuseFailAlloc_5012_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5009_ = 1usize;
                v___x_5010_ = lean_usize_add(v_i_4995_, v___x_5009_);
                v_i_4995_ = v___x_5010_;
                v_b_4996_ = v___x_5008_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg___boxed(
    mut v_as_5020_: *mut leanh::LeanObject,
    mut v_sz_5021_: *mut leanh::LeanObject,
    mut v_i_5022_: *mut leanh::LeanObject,
    mut v_b_5023_: *mut leanh::LeanObject,
    mut v___y_5024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5025_: usize = 0;
    let mut v_i_boxed_5026_: usize = 0;
    let mut v_res_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5025_ = leanh::lean_unbox_usize(v_sz_5021_);
    leanh::lean_dec(v_sz_5021_);
    v_i_boxed_5026_ = leanh::lean_unbox_usize(v_i_5022_);
    leanh::lean_dec(v_i_5022_);
    v_res_5027_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_5020_, v_sz_boxed_5025_, v_i_boxed_5026_, v_b_5023_);
    leanh::lean_dec_ref(v_as_5020_);
    return v_res_5027_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(
    mut v_as_5028_: *mut leanh::LeanObject,
    mut v_sz_5029_: usize,
    mut v_i_5030_: usize,
    mut v_b_5031_: *mut leanh::LeanObject,
    mut v___y_5032_: *mut leanh::LeanObject,
    mut v___y_5033_: *mut leanh::LeanObject,
    mut v___y_5034_: *mut leanh::LeanObject,
    mut v___y_5035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5037_: u8 = 0;
    let mut v___x_5038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5042_: u8 = 0;
    let mut v___x_5043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: usize = 0;
    let mut v___x_5049_: usize = 0;
    let mut v___x_5050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: u8 = 0;
    let mut v___x_5055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5057_: u8 = 0;
    let mut v_unused_5058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5037_ = lean_usize_dec_lt(v_i_5030_, v_sz_5029_);
                if v___x_5037_ == 0 {
                    v___x_5038_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5038_, 0, v_b_5031_);
                    return v___x_5038_;
                } else {
                    v_snd_5039_ = leanh::lean_ctor_get(v_b_5031_, 1);
                    v_isSharedCheck_5057_ = (!leanh::lean_is_exclusive(v_b_5031_)) as u8;
                    if v_isSharedCheck_5057_ == 0 {
                        v_unused_5058_ = leanh::lean_ctor_get(v_b_5031_, 0);
                        leanh::lean_dec(v_unused_5058_);
                        v___x_5041_ = v_b_5031_;
                        v_isShared_5042_ = v_isSharedCheck_5057_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_5039_);
                        leanh::lean_dec(v_b_5031_);
                        v___x_5041_ = leanh::lean_box(0);
                        v_isShared_5042_ = v_isSharedCheck_5057_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5043_ = leanh::lean_box(0);
                v_a_5052_ = lean_array_uget_borrowed(v_as_5028_, v_i_5030_);
                if leanh::lean_obj_tag(v_a_5052_) == 0 {
                    v_a_5045_ = v_snd_5039_;
                    state = 2;
                    continue;
                } else {
                    v_val_5053_ = leanh::lean_ctor_get(v_a_5052_, 0);
                    v___x_5054_ = l_Lean_LocalDecl_isImplementationDetail(v_val_5053_);
                    if v___x_5054_ == 0 {
                        leanh::lean_inc(v_val_5053_);
                        v___x_5055_ = l_Lean_LocalDecl_toExpr(v_val_5053_);
                        v___x_5056_ = lean_array_push(v_snd_5039_, v___x_5055_);
                        v_a_5045_ = v___x_5056_;
                        state = 2;
                        continue;
                    } else {
                        v_a_5045_ = v_snd_5039_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5042_ == 0 {
                    leanh::lean_ctor_set(v___x_5041_, 1, v_a_5045_);
                    leanh::lean_ctor_set(v___x_5041_, 0, v___x_5043_);
                    v___x_5047_ = v___x_5041_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5051_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5051_, 0, v___x_5043_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5051_, 1, v_a_5045_);
                    v___x_5047_ = v_reuseFailAlloc_5051_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5048_ = 1usize;
                v___x_5049_ = lean_usize_add(v_i_5030_, v___x_5048_);
                v___x_5050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_5028_, v_sz_5029_, v___x_5049_, v___x_5047_);
                return v___x_5050_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3___boxed(
    mut v_as_5059_: *mut leanh::LeanObject,
    mut v_sz_5060_: *mut leanh::LeanObject,
    mut v_i_5061_: *mut leanh::LeanObject,
    mut v_b_5062_: *mut leanh::LeanObject,
    mut v___y_5063_: *mut leanh::LeanObject,
    mut v___y_5064_: *mut leanh::LeanObject,
    mut v___y_5065_: *mut leanh::LeanObject,
    mut v___y_5066_: *mut leanh::LeanObject,
    mut v___y_5067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5068_: usize = 0;
    let mut v_i_boxed_5069_: usize = 0;
    let mut v_res_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5068_ = leanh::lean_unbox_usize(v_sz_5060_);
    leanh::lean_dec(v_sz_5060_);
    v_i_boxed_5069_ = leanh::lean_unbox_usize(v_i_5061_);
    leanh::lean_dec(v_i_5061_);
    v_res_5070_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(v_as_5059_, v_sz_boxed_5068_, v_i_boxed_5069_, v_b_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_);
    leanh::lean_dec(v___y_5066_);
    leanh::lean_dec_ref(v___y_5065_);
    leanh::lean_dec(v___y_5064_);
    leanh::lean_dec_ref(v___y_5063_);
    leanh::lean_dec_ref(v_as_5059_);
    return v_res_5070_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(
    mut v_t_5071_: *mut leanh::LeanObject,
    mut v_init_5072_: *mut leanh::LeanObject,
    mut v___y_5073_: *mut leanh::LeanObject,
    mut v___y_5074_: *mut leanh::LeanObject,
    mut v___y_5075_: *mut leanh::LeanObject,
    mut v___y_5076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_5078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5084_: u8 = 0;
    let mut v_a_5085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5092_: usize = 0;
    let mut v___x_5093_: usize = 0;
    let mut v___x_5094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5098_: u8 = 0;
    let mut v_fst_5099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5108_: u8 = 0;
    let mut v_a_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5112_: u8 = 0;
    let mut v___x_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5116_: u8 = 0;
    let mut v_isSharedCheck_5117_: u8 = 0;
    let mut v_a_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5121_: u8 = 0;
    let mut v___x_5123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5125_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_5078_ = leanh::lean_ctor_get(v_t_5071_, 0);
                v_tail_5079_ = leanh::lean_ctor_get(v_t_5071_, 1);
                leanh::lean_inc_ref(v_init_5072_);
                v___x_5080_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_5072_, v_root_5078_, v_init_5072_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_);
                leanh::lean_dec_ref(v_init_5072_);
                if leanh::lean_obj_tag(v___x_5080_) == 0 {
                    v_a_5081_ = leanh::lean_ctor_get(v___x_5080_, 0);
                    v_isSharedCheck_5117_ = (!leanh::lean_is_exclusive(v___x_5080_)) as u8;
                    if v_isSharedCheck_5117_ == 0 {
                        v___x_5083_ = v___x_5080_;
                        v_isShared_5084_ = v_isSharedCheck_5117_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5081_);
                        leanh::lean_dec(v___x_5080_);
                        v___x_5083_ = leanh::lean_box(0);
                        v_isShared_5084_ = v_isSharedCheck_5117_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5118_ = leanh::lean_ctor_get(v___x_5080_, 0);
                    v_isSharedCheck_5125_ = (!leanh::lean_is_exclusive(v___x_5080_)) as u8;
                    if v_isSharedCheck_5125_ == 0 {
                        v___x_5120_ = v___x_5080_;
                        v_isShared_5121_ = v_isSharedCheck_5125_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5118_);
                        leanh::lean_dec(v___x_5080_);
                        v___x_5120_ = leanh::lean_box(0);
                        v_isShared_5121_ = v_isSharedCheck_5125_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_5081_) == 0 {
                    v_a_5085_ = leanh::lean_ctor_get(v_a_5081_, 0);
                    leanh::lean_inc(v_a_5085_);
                    leanh::lean_dec_ref_known(v_a_5081_, 1);
                    if v_isShared_5084_ == 0 {
                        leanh::lean_ctor_set(v___x_5083_, 0, v_a_5085_);
                        v___x_5087_ = v___x_5083_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5088_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5088_, 0, v_a_5085_);
                        v___x_5087_ = v_reuseFailAlloc_5088_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5083_);
                    v_a_5089_ = leanh::lean_ctor_get(v_a_5081_, 0);
                    leanh::lean_inc(v_a_5089_);
                    leanh::lean_dec_ref_known(v_a_5081_, 1);
                    v___x_5090_ = leanh::lean_box(0);
                    v___x_5091_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5091_, 0, v___x_5090_);
                    leanh::lean_ctor_set(v___x_5091_, 1, v_a_5089_);
                    v_sz_5092_ = lean_array_size(v_tail_5079_);
                    v___x_5093_ = 0usize;
                    v___x_5094_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(v_tail_5079_, v_sz_5092_, v___x_5093_, v___x_5091_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_);
                    if leanh::lean_obj_tag(v___x_5094_) == 0 {
                        v_a_5095_ = leanh::lean_ctor_get(v___x_5094_, 0);
                        v_isSharedCheck_5108_ =
                            (!leanh::lean_is_exclusive(v___x_5094_)) as u8;
                        if v_isSharedCheck_5108_ == 0 {
                            v___x_5097_ = v___x_5094_;
                            v_isShared_5098_ = v_isSharedCheck_5108_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5095_);
                            leanh::lean_dec(v___x_5094_);
                            v___x_5097_ = leanh::lean_box(0);
                            v_isShared_5098_ = v_isSharedCheck_5108_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5109_ = leanh::lean_ctor_get(v___x_5094_, 0);
                        v_isSharedCheck_5116_ =
                            (!leanh::lean_is_exclusive(v___x_5094_)) as u8;
                        if v_isSharedCheck_5116_ == 0 {
                            v___x_5111_ = v___x_5094_;
                            v_isShared_5112_ = v_isSharedCheck_5116_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5109_);
                            leanh::lean_dec(v___x_5094_);
                            v___x_5111_ = leanh::lean_box(0);
                            v_isShared_5112_ = v_isSharedCheck_5116_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5087_;
            }
            3 => {
                v_fst_5099_ = leanh::lean_ctor_get(v_a_5095_, 0);
                if leanh::lean_obj_tag(v_fst_5099_) == 0 {
                    v_snd_5100_ = leanh::lean_ctor_get(v_a_5095_, 1);
                    leanh::lean_inc(v_snd_5100_);
                    leanh::lean_dec(v_a_5095_);
                    if v_isShared_5098_ == 0 {
                        leanh::lean_ctor_set(v___x_5097_, 0, v_snd_5100_);
                        v___x_5102_ = v___x_5097_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5103_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5103_, 0, v_snd_5100_);
                        v___x_5102_ = v_reuseFailAlloc_5103_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_5099_);
                    leanh::lean_dec(v_a_5095_);
                    v_val_5104_ = leanh::lean_ctor_get(v_fst_5099_, 0);
                    leanh::lean_inc(v_val_5104_);
                    leanh::lean_dec_ref_known(v_fst_5099_, 1);
                    if v_isShared_5098_ == 0 {
                        leanh::lean_ctor_set(v___x_5097_, 0, v_val_5104_);
                        v___x_5106_ = v___x_5097_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5107_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5107_, 0, v_val_5104_);
                        v___x_5106_ = v_reuseFailAlloc_5107_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_5102_;
            }
            5 => {
                return v___x_5106_;
            }
            6 => {
                if v_isShared_5112_ == 0 {
                    v___x_5114_ = v___x_5111_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5115_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5115_, 0, v_a_5109_);
                    v___x_5114_ = v_reuseFailAlloc_5115_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5114_;
            }
            8 => {
                if v_isShared_5121_ == 0 {
                    v___x_5123_ = v___x_5120_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5124_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5124_, 0, v_a_5118_);
                    v___x_5123_ = v_reuseFailAlloc_5124_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5123_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1___boxed(
    mut v_t_5126_: *mut leanh::LeanObject,
    mut v_init_5127_: *mut leanh::LeanObject,
    mut v___y_5128_: *mut leanh::LeanObject,
    mut v___y_5129_: *mut leanh::LeanObject,
    mut v___y_5130_: *mut leanh::LeanObject,
    mut v___y_5131_: *mut leanh::LeanObject,
    mut v___y_5132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5133_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(v_t_5126_, v_init_5127_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_);
    leanh::lean_dec(v___y_5131_);
    leanh::lean_dec_ref(v___y_5130_);
    leanh::lean_dec(v___y_5129_);
    leanh::lean_dec_ref(v___y_5128_);
    leanh::lean_dec_ref(v_t_5126_);
    return v_res_5133_;
}
pub unsafe fn l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(
    mut v___y_5136_: *mut leanh::LeanObject,
    mut v___y_5137_: *mut leanh::LeanObject,
    mut v___y_5138_: *mut leanh::LeanObject,
    mut v___y_5139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lctx_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_5142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hs_5143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lctx_5141_ = leanh::lean_ctor_get(v___y_5136_, 2);
    v_decls_5142_ = leanh::lean_ctor_get(v_lctx_5141_, 1);
    v_hs_5143_ =
        l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1___closed__0;
    v___x_5144_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(v_decls_5142_, v_hs_5143_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_);
    return v___x_5144_;
}
pub unsafe fn l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1___boxed(
    mut v___y_5145_: *mut leanh::LeanObject,
    mut v___y_5146_: *mut leanh::LeanObject,
    mut v___y_5147_: *mut leanh::LeanObject,
    mut v___y_5148_: *mut leanh::LeanObject,
    mut v___y_5149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5150_ = l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(
        v___y_5145_,
        v___y_5146_,
        v___y_5147_,
        v___y_5148_,
    );
    leanh::lean_dec(v___y_5148_);
    leanh::lean_dec_ref(v___y_5147_);
    leanh::lean_dec(v___y_5146_);
    leanh::lean_dec_ref(v___y_5145_);
    return v_res_5150_;
}
pub unsafe fn l_Lean_Meta_Rewrites_localHypotheses(
    mut v_except_5153_: *mut leanh::LeanObject,
    mut v_a_5154_: *mut leanh::LeanObject,
    mut v_a_5155_: *mut leanh::LeanObject,
    mut v_a_5156_: *mut leanh::LeanObject,
    mut v_a_5157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5162_: usize = 0;
    let mut v___x_5163_: usize = 0;
    let mut v___x_5164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5168_: u8 = 0;
    let mut v___x_5170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5172_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5159_ =
                    l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(
                        v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_,
                    );
                if leanh::lean_obj_tag(v___x_5159_) == 0 {
                    v_a_5160_ = leanh::lean_ctor_get(v___x_5159_, 0);
                    leanh::lean_inc(v_a_5160_);
                    leanh::lean_dec_ref_known(v___x_5159_, 1);
                    v___x_5161_ = l_Lean_Meta_Rewrites_localHypotheses___closed__0;
                    v_sz_5162_ = lean_array_size(v_a_5160_);
                    v___x_5163_ = 0usize;
                    v___x_5164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2(v_except_5153_, v_a_5160_, v_sz_5162_, v___x_5163_, v___x_5161_, v_a_5154_, v_a_5155_, v_a_5156_, v_a_5157_);
                    leanh::lean_dec(v_a_5160_);
                    return v___x_5164_;
                } else {
                    v_a_5165_ = leanh::lean_ctor_get(v___x_5159_, 0);
                    v_isSharedCheck_5172_ = (!leanh::lean_is_exclusive(v___x_5159_)) as u8;
                    if v_isSharedCheck_5172_ == 0 {
                        v___x_5167_ = v___x_5159_;
                        v_isShared_5168_ = v_isSharedCheck_5172_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5165_);
                        leanh::lean_dec(v___x_5159_);
                        v___x_5167_ = leanh::lean_box(0);
                        v_isShared_5168_ = v_isSharedCheck_5172_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5168_ == 0 {
                    v___x_5170_ = v___x_5167_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5171_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5171_, 0, v_a_5165_);
                    v___x_5170_ = v_reuseFailAlloc_5171_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5170_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Rewrites_localHypotheses___boxed(
    mut v_except_5173_: *mut leanh::LeanObject,
    mut v_a_5174_: *mut leanh::LeanObject,
    mut v_a_5175_: *mut leanh::LeanObject,
    mut v_a_5176_: *mut leanh::LeanObject,
    mut v_a_5177_: *mut leanh::LeanObject,
    mut v_a_5178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5179_ = l_Lean_Meta_Rewrites_localHypotheses(
        v_except_5173_,
        v_a_5174_,
        v_a_5175_,
        v_a_5176_,
        v_a_5177_,
    );
    leanh::lean_dec(v_a_5177_);
    leanh::lean_dec_ref(v_a_5176_);
    leanh::lean_dec(v_a_5175_);
    leanh::lean_dec_ref(v_a_5174_);
    leanh::lean_dec(v_except_5173_);
    return v_res_5179_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7(
    mut v_as_5180_: *mut leanh::LeanObject,
    mut v_sz_5181_: usize,
    mut v_i_5182_: usize,
    mut v_b_5183_: *mut leanh::LeanObject,
    mut v___y_5184_: *mut leanh::LeanObject,
    mut v___y_5185_: *mut leanh::LeanObject,
    mut v___y_5186_: *mut leanh::LeanObject,
    mut v___y_5187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_5180_, v_sz_5181_, v_i_5182_, v_b_5183_);
    return v___x_5189_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___boxed(
    mut v_as_5190_: *mut leanh::LeanObject,
    mut v_sz_5191_: *mut leanh::LeanObject,
    mut v_i_5192_: *mut leanh::LeanObject,
    mut v_b_5193_: *mut leanh::LeanObject,
    mut v___y_5194_: *mut leanh::LeanObject,
    mut v___y_5195_: *mut leanh::LeanObject,
    mut v___y_5196_: *mut leanh::LeanObject,
    mut v___y_5197_: *mut leanh::LeanObject,
    mut v___y_5198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5199_: usize = 0;
    let mut v_i_boxed_5200_: usize = 0;
    let mut v_res_5201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5199_ = leanh::lean_unbox_usize(v_sz_5191_);
    leanh::lean_dec(v_sz_5191_);
    v_i_boxed_5200_ = leanh::lean_unbox_usize(v_i_5192_);
    leanh::lean_dec(v_i_5192_);
    v_res_5201_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7(v_as_5190_, v_sz_boxed_5199_, v_i_boxed_5200_, v_b_5193_, v___y_5194_, v___y_5195_, v___y_5196_, v___y_5197_);
    leanh::lean_dec(v___y_5197_);
    leanh::lean_dec_ref(v___y_5196_);
    leanh::lean_dec(v___y_5195_);
    leanh::lean_dec_ref(v___y_5194_);
    leanh::lean_dec_ref(v_as_5190_);
    return v_res_5201_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6(
    mut v_as_5202_: *mut leanh::LeanObject,
    mut v_sz_5203_: usize,
    mut v_i_5204_: usize,
    mut v_b_5205_: *mut leanh::LeanObject,
    mut v___y_5206_: *mut leanh::LeanObject,
    mut v___y_5207_: *mut leanh::LeanObject,
    mut v___y_5208_: *mut leanh::LeanObject,
    mut v___y_5209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_as_5202_, v_sz_5203_, v_i_5204_, v_b_5205_);
    return v___x_5211_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___boxed(
    mut v_as_5212_: *mut leanh::LeanObject,
    mut v_sz_5213_: *mut leanh::LeanObject,
    mut v_i_5214_: *mut leanh::LeanObject,
    mut v_b_5215_: *mut leanh::LeanObject,
    mut v___y_5216_: *mut leanh::LeanObject,
    mut v___y_5217_: *mut leanh::LeanObject,
    mut v___y_5218_: *mut leanh::LeanObject,
    mut v___y_5219_: *mut leanh::LeanObject,
    mut v___y_5220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5221_: usize = 0;
    let mut v_i_boxed_5222_: usize = 0;
    let mut v_res_5223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5221_ = leanh::lean_unbox_usize(v_sz_5213_);
    leanh::lean_dec(v_sz_5213_);
    v_i_boxed_5222_ = leanh::lean_unbox_usize(v_i_5214_);
    leanh::lean_dec(v_i_5214_);
    v_res_5223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6(v_as_5212_, v_sz_boxed_5221_, v_i_boxed_5222_, v_b_5215_, v___y_5216_, v___y_5217_, v___y_5218_, v___y_5219_);
    leanh::lean_dec(v___y_5219_);
    leanh::lean_dec_ref(v___y_5218_);
    leanh::lean_dec(v___y_5217_);
    leanh::lean_dec_ref(v___y_5216_);
    leanh::lean_dec_ref(v_as_5212_);
    return v_res_5223_;
}
pub unsafe fn l_Lean_Meta_Rewrites_createModuleTreeRef(
    mut v_a_5249_: *mut leanh::LeanObject,
    mut v_a_5250_: *mut leanh::LeanObject,
    mut v_a_5251_: *mut leanh::LeanObject,
    mut v_a_5252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5254_ = l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0;
    v___x_5255_ = l_Lean_Meta_Rewrites_droppedKeys;
    v___x_5256_ = leanh::lean_box(0);
    v___x_5257_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(
        v___x_5254_,
        v___x_5255_,
        v___x_5256_,
        v_a_5249_,
        v_a_5250_,
        v_a_5251_,
        v_a_5252_,
    );
    return v___x_5257_;
}
pub unsafe fn l_Lean_Meta_Rewrites_createModuleTreeRef___boxed(
    mut v_a_5258_: *mut leanh::LeanObject,
    mut v_a_5259_: *mut leanh::LeanObject,
    mut v_a_5260_: *mut leanh::LeanObject,
    mut v_a_5261_: *mut leanh::LeanObject,
    mut v_a_5262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5263_ =
        l_Lean_Meta_Rewrites_createModuleTreeRef(v_a_5258_, v_a_5259_, v_a_5260_, v_a_5261_);
    leanh::lean_dec(v_a_5261_);
    leanh::lean_dec_ref(v_a_5260_);
    leanh::lean_dec(v_a_5259_);
    leanh::lean_dec_ref(v_a_5258_);
    return v_res_5263_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1202513136____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_5265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5265_ = leanh::lean_box(0);
    v___x_5266_ = lean_st_mk_ref(v___x_5265_);
    v___x_5267_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5267_, 0, v___x_5266_);
    return v___x_5267_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1202513136____hygCtx___hyg_2____boxed(
    mut v_a_5268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5269_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1202513136____hygCtx___hyg_2_();
    return v_res_5269_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState()
-> *mut leanh::LeanObject {
    let mut v___x_5270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5270_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ExtState_default;
    return v___x_5270_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___lam__0_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2_(
    mut v___x_5271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5273_ = lean_st_mk_ref(v___x_5271_);
    v___x_5274_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5274_, 0, v___x_5273_);
    return v___x_5274_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___lam__0_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2____boxed(
    mut v___x_5275_: *mut leanh::LeanObject,
    mut v___y_5276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5277_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___lam__0_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2_(v___x_5275_);
    return v_res_5277_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_5281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5281_ = leanh::lean_box(0);
    v___f_5282_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2_;
    v___x_5283_ = leanh::lean_box(2);
    v___x_5284_ = l_Lean_registerEnvExtension___redArg(v___f_5282_, v___x_5281_, v___x_5283_);
    return v___x_5284_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2____boxed(
    mut v_a_5285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5286_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2_();
    return v_res_5286_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask()
-> *mut leanh::LeanObject {
    let mut v___x_5287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5287_ = leanh::lean_unsigned_to_nat(6500);
    return v___x_5287_;
}
pub unsafe fn l_Lean_Meta_Rewrites_incPrio(
    mut v_x_5288_: *mut leanh::LeanObject,
    mut v_x_5289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_5290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: u8 = 0;
    let mut v_fst_5292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5295_: u8 = 0;
    let mut v___x_5296_: u8 = 0;
    let mut v___x_5297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5304_: u8 = 0;
    let mut v_unused_5305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5309_: u8 = 0;
    let mut v___x_5310_: u8 = 0;
    let mut v___x_5311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5316_: u8 = 0;
    let mut v_unused_5317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_5290_ = leanh::lean_ctor_get(v_x_5289_, 1);
                v___x_5291_ = (leanh::lean_unbox(v_snd_5290_) as u8);
                if v___x_5291_ == 0 {
                    v_fst_5292_ = leanh::lean_ctor_get(v_x_5289_, 0);
                    v_isSharedCheck_5304_ = (!leanh::lean_is_exclusive(v_x_5289_)) as u8;
                    if v_isSharedCheck_5304_ == 0 {
                        v_unused_5305_ = leanh::lean_ctor_get(v_x_5289_, 1);
                        leanh::lean_dec(v_unused_5305_);
                        v___x_5294_ = v_x_5289_;
                        v_isShared_5295_ = v_isSharedCheck_5304_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_5292_);
                        leanh::lean_dec(v_x_5289_);
                        v___x_5294_ = leanh::lean_box(0);
                        v_isShared_5295_ = v_isSharedCheck_5304_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_fst_5306_ = leanh::lean_ctor_get(v_x_5289_, 0);
                    v_isSharedCheck_5316_ = (!leanh::lean_is_exclusive(v_x_5289_)) as u8;
                    if v_isSharedCheck_5316_ == 0 {
                        v_unused_5317_ = leanh::lean_ctor_get(v_x_5289_, 1);
                        leanh::lean_dec(v_unused_5317_);
                        v___x_5308_ = v_x_5289_;
                        v_isShared_5309_ = v_isSharedCheck_5316_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_5306_);
                        leanh::lean_dec(v_x_5289_);
                        v___x_5308_ = leanh::lean_box(0);
                        v_isShared_5309_ = v_isSharedCheck_5316_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5296_ = 0;
                v___x_5297_ = leanh::lean_unsigned_to_nat(2);
                v___x_5298_ = lean_nat_mul(v___x_5297_, v_x_5288_);
                leanh::lean_dec(v_x_5288_);
                v___x_5299_ = leanh::lean_box((v___x_5296_) as usize);
                if v_isShared_5295_ == 0 {
                    leanh::lean_ctor_set(v___x_5294_, 1, v___x_5298_);
                    leanh::lean_ctor_set(v___x_5294_, 0, v___x_5299_);
                    v___x_5301_ = v___x_5294_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5303_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5303_, 0, v___x_5299_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5303_, 1, v___x_5298_);
                    v___x_5301_ = v_reuseFailAlloc_5303_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5302_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5302_, 0, v_fst_5292_);
                leanh::lean_ctor_set(v___x_5302_, 1, v___x_5301_);
                return v___x_5302_;
            }
            3 => {
                v___x_5310_ = 1;
                v___x_5311_ = leanh::lean_box((v___x_5310_) as usize);
                if v_isShared_5309_ == 0 {
                    leanh::lean_ctor_set(v___x_5308_, 1, v_x_5288_);
                    leanh::lean_ctor_set(v___x_5308_, 0, v___x_5311_);
                    v___x_5313_ = v___x_5308_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5315_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5315_, 0, v___x_5311_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5315_, 1, v_x_5288_);
                    v___x_5313_ = v_reuseFailAlloc_5315_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5314_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5314_, 0, v_fst_5306_);
                leanh::lean_ctor_set(v___x_5314_, 1, v___x_5313_);
                return v___x_5314_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Rewrites_rwFindDecls(
    mut v_moduleRef_5319_: *mut leanh::LeanObject,
    mut v_ty_5320_: *mut leanh::LeanObject,
    mut v_a_5321_: *mut leanh::LeanObject,
    mut v_a_5322_: *mut leanh::LeanObject,
    mut v_a_5323_: *mut leanh::LeanObject,
    mut v_a_5324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5326_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ext;
    v___x_5327_ = l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0;
    v___x_5328_ = l_Lean_Meta_Rewrites_droppedKeys;
    v___x_5329_ = leanh::lean_unsigned_to_nat(6500);
    v___x_5330_ = leanh::lean_box(0);
    v___x_5331_ = l_Lean_Meta_Rewrites_rwFindDecls___closed__0;
    v___x_5332_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(
        v_moduleRef_5319_,
        v___x_5326_,
        v___x_5327_,
        v___x_5328_,
        v___x_5329_,
        v___x_5330_,
        v___x_5331_,
        v_ty_5320_,
        v_a_5321_,
        v_a_5322_,
        v_a_5323_,
        v_a_5324_,
    );
    return v___x_5332_;
}
pub unsafe fn l_Lean_Meta_Rewrites_rwFindDecls___boxed(
    mut v_moduleRef_5333_: *mut leanh::LeanObject,
    mut v_ty_5334_: *mut leanh::LeanObject,
    mut v_a_5335_: *mut leanh::LeanObject,
    mut v_a_5336_: *mut leanh::LeanObject,
    mut v_a_5337_: *mut leanh::LeanObject,
    mut v_a_5338_: *mut leanh::LeanObject,
    mut v_a_5339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5340_ = l_Lean_Meta_Rewrites_rwFindDecls(
        v_moduleRef_5333_,
        v_ty_5334_,
        v_a_5335_,
        v_a_5336_,
        v_a_5337_,
        v_a_5338_,
    );
    leanh::lean_dec(v_a_5338_);
    leanh::lean_dec_ref(v_a_5337_);
    leanh::lean_dec(v_a_5336_);
    leanh::lean_dec_ref(v_a_5335_);
    return v_res_5340_;
}
pub unsafe fn l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(
    mut v_mctx_5341_: *mut leanh::LeanObject,
    mut v_x_5342_: *mut leanh::LeanObject,
    mut v___y_5343_: *mut leanh::LeanObject,
    mut v___y_5344_: *mut leanh::LeanObject,
    mut v___y_5345_: *mut leanh::LeanObject,
    mut v___y_5346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5352_: u8 = 0;
    let mut v___x_5354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5356_: u8 = 0;
    let mut v_a_5357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5360_: u8 = 0;
    let mut v___x_5362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5364_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5348_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(
                    leanh::lean_box(0),
                    v_mctx_5341_,
                    v_x_5342_,
                    v___y_5343_,
                    v___y_5344_,
                    v___y_5345_,
                    v___y_5346_,
                );
                if leanh::lean_obj_tag(v___x_5348_) == 0 {
                    v_a_5349_ = leanh::lean_ctor_get(v___x_5348_, 0);
                    v_isSharedCheck_5356_ = (!leanh::lean_is_exclusive(v___x_5348_)) as u8;
                    if v_isSharedCheck_5356_ == 0 {
                        v___x_5351_ = v___x_5348_;
                        v_isShared_5352_ = v_isSharedCheck_5356_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5349_);
                        leanh::lean_dec(v___x_5348_);
                        v___x_5351_ = leanh::lean_box(0);
                        v_isShared_5352_ = v_isSharedCheck_5356_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5357_ = leanh::lean_ctor_get(v___x_5348_, 0);
                    v_isSharedCheck_5364_ = (!leanh::lean_is_exclusive(v___x_5348_)) as u8;
                    if v_isSharedCheck_5364_ == 0 {
                        v___x_5359_ = v___x_5348_;
                        v_isShared_5360_ = v_isSharedCheck_5364_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5357_);
                        leanh::lean_dec(v___x_5348_);
                        v___x_5359_ = leanh::lean_box(0);
                        v_isShared_5360_ = v_isSharedCheck_5364_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5352_ == 0 {
                    v___x_5354_ = v___x_5351_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5355_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5355_, 0, v_a_5349_);
                    v___x_5354_ = v_reuseFailAlloc_5355_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5354_;
            }
            3 => {
                if v_isShared_5360_ == 0 {
                    v___x_5362_ = v___x_5359_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5363_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5363_, 0, v_a_5357_);
                    v___x_5362_ = v_reuseFailAlloc_5363_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5362_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg___boxed(
    mut v_mctx_5365_: *mut leanh::LeanObject,
    mut v_x_5366_: *mut leanh::LeanObject,
    mut v___y_5367_: *mut leanh::LeanObject,
    mut v___y_5368_: *mut leanh::LeanObject,
    mut v___y_5369_: *mut leanh::LeanObject,
    mut v___y_5370_: *mut leanh::LeanObject,
    mut v___y_5371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5372_ =
        l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(
            v_mctx_5365_,
            v_x_5366_,
            v___y_5367_,
            v___y_5368_,
            v___y_5369_,
            v___y_5370_,
        );
    leanh::lean_dec(v___y_5370_);
    leanh::lean_dec_ref(v___y_5369_);
    leanh::lean_dec(v___y_5368_);
    leanh::lean_dec_ref(v___y_5367_);
    return v_res_5372_;
}
pub unsafe fn l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0(
    mut v_00_u03b1_5373_: *mut leanh::LeanObject,
    mut v_mctx_5374_: *mut leanh::LeanObject,
    mut v_x_5375_: *mut leanh::LeanObject,
    mut v___y_5376_: *mut leanh::LeanObject,
    mut v___y_5377_: *mut leanh::LeanObject,
    mut v___y_5378_: *mut leanh::LeanObject,
    mut v___y_5379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5381_ =
        l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(
            v_mctx_5374_,
            v_x_5375_,
            v___y_5376_,
            v___y_5377_,
            v___y_5378_,
            v___y_5379_,
        );
    return v___x_5381_;
}
pub unsafe fn l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed(
    mut v_00_u03b1_5382_: *mut leanh::LeanObject,
    mut v_mctx_5383_: *mut leanh::LeanObject,
    mut v_x_5384_: *mut leanh::LeanObject,
    mut v___y_5385_: *mut leanh::LeanObject,
    mut v___y_5386_: *mut leanh::LeanObject,
    mut v___y_5387_: *mut leanh::LeanObject,
    mut v___y_5388_: *mut leanh::LeanObject,
    mut v___y_5389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5390_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0(
        v_00_u03b1_5382_,
        v_mctx_5383_,
        v_x_5384_,
        v___y_5385_,
        v___y_5386_,
        v___y_5387_,
        v___y_5388_,
    );
    leanh::lean_dec(v___y_5388_);
    leanh::lean_dec_ref(v___y_5387_);
    leanh::lean_dec(v___y_5386_);
    leanh::lean_dec_ref(v___y_5385_);
    return v_res_5390_;
}
pub unsafe fn l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(
    mut v_x_5391_: *mut leanh::LeanObject,
    mut v___y_5392_: *mut leanh::LeanObject,
    mut v___y_5393_: *mut leanh::LeanObject,
    mut v___y_5394_: *mut leanh::LeanObject,
    mut v___y_5395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5404_: u8 = 0;
    let mut v___x_5406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5408_: u8 = 0;
    let mut v_unused_5409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5413_: u8 = 0;
    let mut v___x_5415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5417_: u8 = 0;
    let mut v_a_5418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5422_: u8 = 0;
    let mut v___x_5424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5426_: u8 = 0;
    let mut v_unused_5427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5431_: u8 = 0;
    let mut v___x_5433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5435_: u8 = 0;
    let mut v_a_5436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5439_: u8 = 0;
    let mut v___x_5441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5443_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5397_ = l_Lean_Meta_saveState___redArg(v___y_5393_, v___y_5395_);
                if leanh::lean_obj_tag(v___x_5397_) == 0 {
                    v_a_5398_ = leanh::lean_ctor_get(v___x_5397_, 0);
                    leanh::lean_inc(v_a_5398_);
                    leanh::lean_dec_ref_known(v___x_5397_, 1);
                    leanh::lean_inc(v___y_5395_);
                    leanh::lean_inc_ref(v___y_5394_);
                    leanh::lean_inc(v___y_5393_);
                    leanh::lean_inc_ref(v___y_5392_);
                    v_r_5399_ = leanh::lean_apply_5(
                        v_x_5391_,
                        v___y_5392_,
                        v___y_5393_,
                        v___y_5394_,
                        v___y_5395_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v_r_5399_) == 0 {
                        v_a_5400_ = leanh::lean_ctor_get(v_r_5399_, 0);
                        leanh::lean_inc(v_a_5400_);
                        leanh::lean_dec_ref_known(v_r_5399_, 1);
                        v___x_5401_ = l_Lean_Meta_SavedState_restore___redArg(
                            v_a_5398_,
                            v___y_5393_,
                            v___y_5395_,
                        );
                        leanh::lean_dec(v_a_5398_);
                        if leanh::lean_obj_tag(v___x_5401_) == 0 {
                            v_isSharedCheck_5408_ =
                                (!leanh::lean_is_exclusive(v___x_5401_)) as u8;
                            if v_isSharedCheck_5408_ == 0 {
                                v_unused_5409_ = leanh::lean_ctor_get(v___x_5401_, 0);
                                leanh::lean_dec(v_unused_5409_);
                                v___x_5403_ = v___x_5401_;
                                v_isShared_5404_ = v_isSharedCheck_5408_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_5401_);
                                v___x_5403_ = leanh::lean_box(0);
                                v_isShared_5404_ = v_isSharedCheck_5408_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_5400_);
                            v_a_5410_ = leanh::lean_ctor_get(v___x_5401_, 0);
                            v_isSharedCheck_5417_ =
                                (!leanh::lean_is_exclusive(v___x_5401_)) as u8;
                            if v_isSharedCheck_5417_ == 0 {
                                v___x_5412_ = v___x_5401_;
                                v_isShared_5413_ = v_isSharedCheck_5417_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5410_);
                                leanh::lean_dec(v___x_5401_);
                                v___x_5412_ = leanh::lean_box(0);
                                v_isShared_5413_ = v_isSharedCheck_5417_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_5418_ = leanh::lean_ctor_get(v_r_5399_, 0);
                        leanh::lean_inc(v_a_5418_);
                        leanh::lean_dec_ref_known(v_r_5399_, 1);
                        v___x_5419_ = l_Lean_Meta_SavedState_restore___redArg(
                            v_a_5398_,
                            v___y_5393_,
                            v___y_5395_,
                        );
                        leanh::lean_dec(v_a_5398_);
                        if leanh::lean_obj_tag(v___x_5419_) == 0 {
                            v_isSharedCheck_5426_ =
                                (!leanh::lean_is_exclusive(v___x_5419_)) as u8;
                            if v_isSharedCheck_5426_ == 0 {
                                v_unused_5427_ = leanh::lean_ctor_get(v___x_5419_, 0);
                                leanh::lean_dec(v_unused_5427_);
                                v___x_5421_ = v___x_5419_;
                                v_isShared_5422_ = v_isSharedCheck_5426_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_5419_);
                                v___x_5421_ = leanh::lean_box(0);
                                v_isShared_5422_ = v_isSharedCheck_5426_;
                                state = 5;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_5418_);
                            v_a_5428_ = leanh::lean_ctor_get(v___x_5419_, 0);
                            v_isSharedCheck_5435_ =
                                (!leanh::lean_is_exclusive(v___x_5419_)) as u8;
                            if v_isSharedCheck_5435_ == 0 {
                                v___x_5430_ = v___x_5419_;
                                v_isShared_5431_ = v_isSharedCheck_5435_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5428_);
                                leanh::lean_dec(v___x_5419_);
                                v___x_5430_ = leanh::lean_box(0);
                                v_isShared_5431_ = v_isSharedCheck_5435_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_x_5391_);
                    v_a_5436_ = leanh::lean_ctor_get(v___x_5397_, 0);
                    v_isSharedCheck_5443_ = (!leanh::lean_is_exclusive(v___x_5397_)) as u8;
                    if v_isSharedCheck_5443_ == 0 {
                        v___x_5438_ = v___x_5397_;
                        v_isShared_5439_ = v_isSharedCheck_5443_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5436_);
                        leanh::lean_dec(v___x_5397_);
                        v___x_5438_ = leanh::lean_box(0);
                        v_isShared_5439_ = v_isSharedCheck_5443_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5404_ == 0 {
                    leanh::lean_ctor_set(v___x_5403_, 0, v_a_5400_);
                    v___x_5406_ = v___x_5403_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5407_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5407_, 0, v_a_5400_);
                    v___x_5406_ = v_reuseFailAlloc_5407_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5406_;
            }
            3 => {
                if v_isShared_5413_ == 0 {
                    v___x_5415_ = v___x_5412_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5416_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5416_, 0, v_a_5410_);
                    v___x_5415_ = v_reuseFailAlloc_5416_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5415_;
            }
            5 => {
                if v_isShared_5422_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5421_, 1);
                    leanh::lean_ctor_set(v___x_5421_, 0, v_a_5418_);
                    v___x_5424_ = v___x_5421_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5425_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5425_, 0, v_a_5418_);
                    v___x_5424_ = v_reuseFailAlloc_5425_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5424_;
            }
            7 => {
                if v_isShared_5431_ == 0 {
                    v___x_5433_ = v___x_5430_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5434_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5434_, 0, v_a_5428_);
                    v___x_5433_ = v_reuseFailAlloc_5434_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5433_;
            }
            9 => {
                if v_isShared_5439_ == 0 {
                    v___x_5441_ = v___x_5438_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5442_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5442_, 0, v_a_5436_);
                    v___x_5441_ = v_reuseFailAlloc_5442_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5441_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg___boxed(
    mut v_x_5444_: *mut leanh::LeanObject,
    mut v___y_5445_: *mut leanh::LeanObject,
    mut v___y_5446_: *mut leanh::LeanObject,
    mut v___y_5447_: *mut leanh::LeanObject,
    mut v___y_5448_: *mut leanh::LeanObject,
    mut v___y_5449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5450_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v_x_5444_, v___y_5445_, v___y_5446_, v___y_5447_, v___y_5448_);
    leanh::lean_dec(v___y_5448_);
    leanh::lean_dec_ref(v___y_5447_);
    leanh::lean_dec(v___y_5446_);
    leanh::lean_dec_ref(v___y_5445_);
    return v_res_5450_;
}
pub unsafe fn l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1(
    mut v_00_u03b1_5451_: *mut leanh::LeanObject,
    mut v_x_5452_: *mut leanh::LeanObject,
    mut v___y_5453_: *mut leanh::LeanObject,
    mut v___y_5454_: *mut leanh::LeanObject,
    mut v___y_5455_: *mut leanh::LeanObject,
    mut v___y_5456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5458_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v_x_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_);
    return v___x_5458_;
}
pub unsafe fn l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___boxed(
    mut v_00_u03b1_5459_: *mut leanh::LeanObject,
    mut v_x_5460_: *mut leanh::LeanObject,
    mut v___y_5461_: *mut leanh::LeanObject,
    mut v___y_5462_: *mut leanh::LeanObject,
    mut v___y_5463_: *mut leanh::LeanObject,
    mut v___y_5464_: *mut leanh::LeanObject,
    mut v___y_5465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5466_ =
        l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1(
            v_00_u03b1_5459_,
            v_x_5460_,
            v___y_5461_,
            v___y_5462_,
            v___y_5463_,
            v___y_5464_,
        );
    leanh::lean_dec(v___y_5464_);
    leanh::lean_dec_ref(v___y_5463_);
    leanh::lean_dec(v___y_5462_);
    leanh::lean_dec_ref(v___y_5461_);
    return v_res_5466_;
}
pub unsafe fn _init_l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0() -> u64 {
    let mut v___x_5467_: u8 = 0;
    let mut v___x_5468_: u64 = 0;
    v___x_5467_ = 2;
    v___x_5468_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_5467_);
    return v___x_5468_;
}
pub unsafe fn l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(
    mut v___x_5469_: *mut leanh::LeanObject,
    mut v___x_5470_: u8,
    mut v___x_5471_: *mut leanh::LeanObject,
    mut v___y_5472_: *mut leanh::LeanObject,
    mut v___y_5473_: *mut leanh::LeanObject,
    mut v___y_5474_: *mut leanh::LeanObject,
    mut v___y_5475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_5480_: u8 = 0;
    let mut v_ctxApprox_5481_: u8 = 0;
    let mut v_quasiPatternApprox_5482_: u8 = 0;
    let mut v_constApprox_5483_: u8 = 0;
    let mut v_isDefEqStuckEx_5484_: u8 = 0;
    let mut v_unificationHints_5485_: u8 = 0;
    let mut v_proofIrrelevance_5486_: u8 = 0;
    let mut v_assignSyntheticOpaque_5487_: u8 = 0;
    let mut v_offsetCnstrs_5488_: u8 = 0;
    let mut v_etaStruct_5489_: u8 = 0;
    let mut v_univApprox_5490_: u8 = 0;
    let mut v_iota_5491_: u8 = 0;
    let mut v_beta_5492_: u8 = 0;
    let mut v_proj_5493_: u8 = 0;
    let mut v_zeta_5494_: u8 = 0;
    let mut v_zetaDelta_5495_: u8 = 0;
    let mut v_zetaUnused_5496_: u8 = 0;
    let mut v_zetaHave_5497_: u8 = 0;
    let mut v___x_5499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5500_: u8 = 0;
    let mut v_trackZetaDelta_5501_: u8 = 0;
    let mut v_zetaDeltaSet_5502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_5504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_5505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_5506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_5507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_5508_: u8 = 0;
    let mut v_inTypeClassResolution_5509_: u8 = 0;
    let mut v_cacheInferType_5510_: u8 = 0;
    let mut v___x_5511_: u8 = 0;
    let mut v_config_5513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: u64 = 0;
    let mut v___x_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5517_: u8 = 0;
    let mut v___x_5518_: u64 = 0;
    let mut v___x_5519_: u64 = 0;
    let mut v___x_5520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: u8 = 0;
    let mut v___x_5522_: u64 = 0;
    let mut v___x_5523_: u64 = 0;
    let mut v_key_5524_: u64 = 0;
    let mut v___x_5525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5531_: u8 = 0;
    let mut v___x_5532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5536_: u8 = 0;
    let mut v_unused_5537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5541_: u8 = 0;
    let mut v___x_5543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5545_: u8 = 0;
    let mut v_reuseFailAlloc_5546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5547_: u8 = 0;
    let mut v_unused_5548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5556_: u8 = 0;
    let mut v_a_5557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5560_: u8 = 0;
    let mut v___x_5562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5564_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5477_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_5469_,
                    v___x_5470_,
                    v___x_5471_,
                    v___y_5472_,
                    v___y_5473_,
                    v___y_5474_,
                    v___y_5475_,
                );
                if leanh::lean_obj_tag(v___x_5477_) == 0 {
                    v_a_5478_ = leanh::lean_ctor_get(v___x_5477_, 0);
                    leanh::lean_inc(v_a_5478_);
                    leanh::lean_dec_ref_known(v___x_5477_, 1);
                    v___x_5479_ = l_Lean_Meta_Context_config(v___y_5472_);
                    v_foApprox_5480_ = leanh::lean_ctor_get_uint8(v___x_5479_, 0 as u32);
                    v_ctxApprox_5481_ = leanh::lean_ctor_get_uint8(v___x_5479_, 1 as u32);
                    v_quasiPatternApprox_5482_ =
                        leanh::lean_ctor_get_uint8(v___x_5479_, 2 as u32);
                    v_constApprox_5483_ = leanh::lean_ctor_get_uint8(v___x_5479_, 3 as u32);
                    v_isDefEqStuckEx_5484_ =
                        leanh::lean_ctor_get_uint8(v___x_5479_, 4 as u32);
                    v_unificationHints_5485_ =
                        leanh::lean_ctor_get_uint8(v___x_5479_, 5 as u32);
                    v_proofIrrelevance_5486_ =
                        leanh::lean_ctor_get_uint8(v___x_5479_, 6 as u32);
                    v_assignSyntheticOpaque_5487_ =
                        leanh::lean_ctor_get_uint8(v___x_5479_, 7 as u32);
                    v_offsetCnstrs_5488_ = leanh::lean_ctor_get_uint8(v___x_5479_, 8 as u32);
                    v_etaStruct_5489_ = leanh::lean_ctor_get_uint8(v___x_5479_, 10 as u32);
                    v_univApprox_5490_ = leanh::lean_ctor_get_uint8(v___x_5479_, 11 as u32);
                    v_iota_5491_ = leanh::lean_ctor_get_uint8(v___x_5479_, 12 as u32);
                    v_beta_5492_ = leanh::lean_ctor_get_uint8(v___x_5479_, 13 as u32);
                    v_proj_5493_ = leanh::lean_ctor_get_uint8(v___x_5479_, 14 as u32);
                    v_zeta_5494_ = leanh::lean_ctor_get_uint8(v___x_5479_, 15 as u32);
                    v_zetaDelta_5495_ = leanh::lean_ctor_get_uint8(v___x_5479_, 16 as u32);
                    v_zetaUnused_5496_ = leanh::lean_ctor_get_uint8(v___x_5479_, 17 as u32);
                    v_zetaHave_5497_ = leanh::lean_ctor_get_uint8(v___x_5479_, 18 as u32);
                    v_isSharedCheck_5556_ = (!leanh::lean_is_exclusive(v___x_5479_)) as u8;
                    if v_isSharedCheck_5556_ == 0 {
                        v___x_5499_ = v___x_5479_;
                        v_isShared_5500_ = v_isSharedCheck_5556_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_5479_);
                        v___x_5499_ = leanh::lean_box(0);
                        v_isShared_5500_ = v_isSharedCheck_5556_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___y_5472_);
                    v_a_5557_ = leanh::lean_ctor_get(v___x_5477_, 0);
                    v_isSharedCheck_5564_ = (!leanh::lean_is_exclusive(v___x_5477_)) as u8;
                    if v_isSharedCheck_5564_ == 0 {
                        v___x_5559_ = v___x_5477_;
                        v_isShared_5560_ = v_isSharedCheck_5564_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5557_);
                        leanh::lean_dec(v___x_5477_);
                        v___x_5559_ = leanh::lean_box(0);
                        v_isShared_5560_ = v_isSharedCheck_5564_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_trackZetaDelta_5501_ = leanh::lean_ctor_get_uint8(
                    v___y_5472_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_5502_ = leanh::lean_ctor_get(v___y_5472_, 1);
                leanh::lean_inc(v_zetaDeltaSet_5502_);
                v_lctx_5503_ = leanh::lean_ctor_get(v___y_5472_, 2);
                leanh::lean_inc_ref(v_lctx_5503_);
                v_localInstances_5504_ = leanh::lean_ctor_get(v___y_5472_, 3);
                leanh::lean_inc_ref(v_localInstances_5504_);
                v_defEqCtx_x3f_5505_ = leanh::lean_ctor_get(v___y_5472_, 4);
                leanh::lean_inc(v_defEqCtx_x3f_5505_);
                v_synthPendingDepth_5506_ = leanh::lean_ctor_get(v___y_5472_, 5);
                leanh::lean_inc(v_synthPendingDepth_5506_);
                v_canUnfold_x3f_5507_ = leanh::lean_ctor_get(v___y_5472_, 6);
                leanh::lean_inc(v_canUnfold_x3f_5507_);
                v_univApprox_5508_ = leanh::lean_ctor_get_uint8(
                    v___y_5472_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_5509_ = leanh::lean_ctor_get_uint8(
                    v___y_5472_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_5510_ = leanh::lean_ctor_get_uint8(
                    v___y_5472_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_5511_ = 2;
                if v_isShared_5500_ == 0 {
                    v_config_5513_ = v___x_5499_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5555_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5555_,
                        0 as u32,
                        v_foApprox_5480_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5555_,
                        1 as u32,
                        v_ctxApprox_5481_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5555_,
                        2 as u32,
                        v_quasiPatternApprox_5482_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5555_,
                        3 as u32,
                        v_constApprox_5483_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5555_,
                        4 as u32,
                        v_isDefEqStuckEx_5484_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5555_,
                        5 as u32,
                        v_unificationHints_5485_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5555_,
                        6 as u32,
                        v_proofIrrelevance_5486_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5555_,
                        7 as u32,
                        v_assignSyntheticOpaque_5487_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5555_,
                        8 as u32,
                        v_offsetCnstrs_5488_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5555_,
                        10 as u32,
                        v_etaStruct_5489_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5555_,
                        11 as u32,
                        v_univApprox_5490_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5555_,
                        12 as u32,
                        v_iota_5491_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5555_,
                        13 as u32,
                        v_beta_5492_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5555_,
                        14 as u32,
                        v_proj_5493_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5555_,
                        15 as u32,
                        v_zeta_5494_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5555_,
                        16 as u32,
                        v_zetaDelta_5495_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5555_,
                        17 as u32,
                        v_zetaUnused_5496_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5555_,
                        18 as u32,
                        v_zetaHave_5497_,
                    );
                    v_config_5513_ = v_reuseFailAlloc_5555_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(v_config_5513_, 9 as u32, v___x_5511_);
                v___x_5514_ = l_Lean_Meta_Context_configKey(v___y_5472_);
                v_isSharedCheck_5547_ = (!leanh::lean_is_exclusive(v___y_5472_)) as u8;
                if v_isSharedCheck_5547_ == 0 {
                    v_unused_5548_ = leanh::lean_ctor_get(v___y_5472_, 6);
                    leanh::lean_dec(v_unused_5548_);
                    v_unused_5549_ = leanh::lean_ctor_get(v___y_5472_, 5);
                    leanh::lean_dec(v_unused_5549_);
                    v_unused_5550_ = leanh::lean_ctor_get(v___y_5472_, 4);
                    leanh::lean_dec(v_unused_5550_);
                    v_unused_5551_ = leanh::lean_ctor_get(v___y_5472_, 3);
                    leanh::lean_dec(v_unused_5551_);
                    v_unused_5552_ = leanh::lean_ctor_get(v___y_5472_, 2);
                    leanh::lean_dec(v_unused_5552_);
                    v_unused_5553_ = leanh::lean_ctor_get(v___y_5472_, 1);
                    leanh::lean_dec(v_unused_5553_);
                    v_unused_5554_ = leanh::lean_ctor_get(v___y_5472_, 0);
                    leanh::lean_dec(v_unused_5554_);
                    v___x_5516_ = v___y_5472_;
                    v_isShared_5517_ = v_isSharedCheck_5547_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v___y_5472_);
                    v___x_5516_ = leanh::lean_box(0);
                    v_isShared_5517_ = v_isSharedCheck_5547_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5518_ = 3u64;
                v___x_5519_ = lean_uint64_shift_right(v___x_5514_, v___x_5518_);
                v___x_5520_ = l_Lean_Expr_mvarId_x21(v_a_5478_);
                leanh::lean_dec(v_a_5478_);
                v___x_5521_ = 1;
                v___x_5522_ = lean_uint64_shift_left(v___x_5519_, v___x_5518_);
                v___x_5523_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0_once
                    ),
                    _init_l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0,
                );
                v_key_5524_ = lean_uint64_lor(v___x_5522_, v___x_5523_);
                v___x_5525_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_5525_, 0, v_config_5513_);
                leanh::lean_ctor_set_uint64(
                    v___x_5525_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_5524_,
                );
                if v_isShared_5517_ == 0 {
                    leanh::lean_ctor_set(v___x_5516_, 0, v___x_5525_);
                    v___x_5527_ = v___x_5516_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5546_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5546_, 0, v___x_5525_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5546_, 1, v_zetaDeltaSet_5502_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5546_, 2, v_lctx_5503_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5546_, 3, v_localInstances_5504_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5546_, 4, v_defEqCtx_x3f_5505_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5546_,
                        5,
                        v_synthPendingDepth_5506_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5546_, 6, v_canUnfold_x3f_5507_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5546_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                        v_trackZetaDelta_5501_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5546_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                        v_univApprox_5508_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5546_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                        v_inTypeClassResolution_5509_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5546_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                        v_cacheInferType_5510_,
                    );
                    v___x_5527_ = v_reuseFailAlloc_5546_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5528_ = l_Lean_MVarId_refl(
                    v___x_5520_,
                    v___x_5521_,
                    v___x_5527_,
                    v___y_5473_,
                    v___y_5474_,
                    v___y_5475_,
                );
                leanh::lean_dec_ref(v___x_5527_);
                if leanh::lean_obj_tag(v___x_5528_) == 0 {
                    v_isSharedCheck_5536_ = (!leanh::lean_is_exclusive(v___x_5528_)) as u8;
                    if v_isSharedCheck_5536_ == 0 {
                        v_unused_5537_ = leanh::lean_ctor_get(v___x_5528_, 0);
                        leanh::lean_dec(v_unused_5537_);
                        v___x_5530_ = v___x_5528_;
                        v_isShared_5531_ = v_isSharedCheck_5536_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_5528_);
                        v___x_5530_ = leanh::lean_box(0);
                        v_isShared_5531_ = v_isSharedCheck_5536_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_5538_ = leanh::lean_ctor_get(v___x_5528_, 0);
                    v_isSharedCheck_5545_ = (!leanh::lean_is_exclusive(v___x_5528_)) as u8;
                    if v_isSharedCheck_5545_ == 0 {
                        v___x_5540_ = v___x_5528_;
                        v_isShared_5541_ = v_isSharedCheck_5545_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5538_);
                        leanh::lean_dec(v___x_5528_);
                        v___x_5540_ = leanh::lean_box(0);
                        v_isShared_5541_ = v_isSharedCheck_5545_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v___x_5532_ = leanh::lean_box((v___x_5521_) as usize);
                if v_isShared_5531_ == 0 {
                    leanh::lean_ctor_set(v___x_5530_, 0, v___x_5532_);
                    v___x_5534_ = v___x_5530_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5535_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 0, v___x_5532_);
                    v___x_5534_ = v_reuseFailAlloc_5535_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5534_;
            }
            7 => {
                if v_isShared_5541_ == 0 {
                    v___x_5543_ = v___x_5540_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5544_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5544_, 0, v_a_5538_);
                    v___x_5543_ = v_reuseFailAlloc_5544_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5543_;
            }
            9 => {
                if v_isShared_5560_ == 0 {
                    v___x_5562_ = v___x_5559_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5563_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5563_, 0, v_a_5557_);
                    v___x_5562_ = v_reuseFailAlloc_5563_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5562_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___boxed(
    mut v___x_5565_: *mut leanh::LeanObject,
    mut v___x_5566_: *mut leanh::LeanObject,
    mut v___x_5567_: *mut leanh::LeanObject,
    mut v___y_5568_: *mut leanh::LeanObject,
    mut v___y_5569_: *mut leanh::LeanObject,
    mut v___y_5570_: *mut leanh::LeanObject,
    mut v___y_5571_: *mut leanh::LeanObject,
    mut v___y_5572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2362__boxed_5573_: u8 = 0;
    let mut v_res_5574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2362__boxed_5573_ = (leanh::lean_unbox(v___x_5566_) as u8);
    v_res_5574_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(
        v___x_5565_,
        v___x_2362__boxed_5573_,
        v___x_5567_,
        v___y_5568_,
        v___y_5569_,
        v___y_5570_,
        v___y_5571_,
    );
    leanh::lean_dec(v___y_5571_);
    leanh::lean_dec_ref(v___y_5570_);
    leanh::lean_dec(v___y_5569_);
    return v_res_5574_;
}
pub unsafe fn l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(
    mut v_mctx_5575_: *mut leanh::LeanObject,
    mut v_e_5576_: *mut leanh::LeanObject,
    mut v_a_5577_: *mut leanh::LeanObject,
    mut v_a_5578_: *mut leanh::LeanObject,
    mut v_a_5579_: *mut leanh::LeanObject,
    mut v_a_5580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: u8 = 0;
    let mut v___x_5584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5591_: u8 = 0;
    let mut v___x_5593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5594_: u8 = 0;
    let mut v___x_5595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5599_: u8 = 0;
    let mut v_unused_5600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5601_: u8 = 0;
    let mut v___x_5602_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5582_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5582_, 0, v_e_5576_);
                v___x_5583_ = 0;
                v___x_5584_ = leanh::lean_box(0);
                v___x_5585_ = leanh::lean_box((v___x_5583_) as usize);
                v___f_5586_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___boxed
                        as *mut core::ffi::c_void,
                    8,
                    3,
                );
                leanh::lean_closure_set(v___f_5586_, 0, v___x_5582_);
                leanh::lean_closure_set(v___f_5586_, 1, v___x_5585_);
                leanh::lean_closure_set(v___f_5586_, 2, v___x_5584_);
                v___x_5587_ = leanh::lean_alloc_closure(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed as *mut core::ffi::c_void, 8, 3);
                leanh::lean_closure_set(v___x_5587_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_5587_, 1, v_mctx_5575_);
                leanh::lean_closure_set(v___x_5587_, 2, v___f_5586_);
                v___x_5588_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_5587_, v_a_5577_, v_a_5578_, v_a_5579_, v_a_5580_);
                if leanh::lean_obj_tag(v___x_5588_) == 0 {
                    return v___x_5588_;
                } else {
                    v_a_5589_ = leanh::lean_ctor_get(v___x_5588_, 0);
                    leanh::lean_inc(v_a_5589_);
                    v___x_5601_ = l_Lean_Exception_isInterrupt(v_a_5589_);
                    if v___x_5601_ == 0 {
                        v___x_5602_ = l_Lean_Exception_isRuntime(v_a_5589_);
                        v___y_5591_ = v___x_5602_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_5589_);
                        v___y_5591_ = v___x_5601_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_5591_ == 0 {
                    v_isSharedCheck_5599_ = (!leanh::lean_is_exclusive(v___x_5588_)) as u8;
                    if v_isSharedCheck_5599_ == 0 {
                        v_unused_5600_ = leanh::lean_ctor_get(v___x_5588_, 0);
                        leanh::lean_dec(v_unused_5600_);
                        v___x_5593_ = v___x_5588_;
                        v_isShared_5594_ = v_isSharedCheck_5599_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_5588_);
                        v___x_5593_ = leanh::lean_box(0);
                        v_isShared_5594_ = v_isSharedCheck_5599_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_5588_;
                }
            }
            2 => {
                v___x_5595_ = leanh::lean_box((v___y_5591_) as usize);
                if v_isShared_5594_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5593_, 0);
                    leanh::lean_ctor_set(v___x_5593_, 0, v___x_5595_);
                    v___x_5597_ = v___x_5593_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5598_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5598_, 0, v___x_5595_);
                    v___x_5597_ = v_reuseFailAlloc_5598_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5597_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___boxed(
    mut v_mctx_5603_: *mut leanh::LeanObject,
    mut v_e_5604_: *mut leanh::LeanObject,
    mut v_a_5605_: *mut leanh::LeanObject,
    mut v_a_5606_: *mut leanh::LeanObject,
    mut v_a_5607_: *mut leanh::LeanObject,
    mut v_a_5608_: *mut leanh::LeanObject,
    mut v_a_5609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5610_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(
        v_mctx_5603_,
        v_e_5604_,
        v_a_5605_,
        v_a_5606_,
        v_a_5607_,
        v_a_5608_,
    );
    leanh::lean_dec(v_a_5608_);
    leanh::lean_dec_ref(v_a_5607_);
    leanh::lean_dec(v_a_5606_);
    leanh::lean_dec_ref(v_a_5605_);
    return v_res_5610_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(
    mut v_r_5611_: *mut leanh::LeanObject,
    mut v_a_5612_: *mut leanh::LeanObject,
    mut v_a_5613_: *mut leanh::LeanObject,
    mut v_a_5614_: *mut leanh::LeanObject,
    mut v_a_5615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_result_5617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eNew_5618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5623_: u8 = 0;
    let mut v___x_5624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5630_: u8 = 0;
    let mut v_a_5631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5634_: u8 = 0;
    let mut v___x_5636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5638_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_result_5617_ = leanh::lean_ctor_get(v_r_5611_, 2);
                leanh::lean_inc_ref(v_result_5617_);
                leanh::lean_dec_ref(v_r_5611_);
                v_eNew_5618_ = leanh::lean_ctor_get(v_result_5617_, 0);
                leanh::lean_inc_ref(v_eNew_5618_);
                leanh::lean_dec_ref(v_result_5617_);
                v___x_5619_ =
                    l_Lean_Meta_ppExpr(v_eNew_5618_, v_a_5612_, v_a_5613_, v_a_5614_, v_a_5615_);
                if leanh::lean_obj_tag(v___x_5619_) == 0 {
                    v_a_5620_ = leanh::lean_ctor_get(v___x_5619_, 0);
                    v_isSharedCheck_5630_ = (!leanh::lean_is_exclusive(v___x_5619_)) as u8;
                    if v_isSharedCheck_5630_ == 0 {
                        v___x_5622_ = v___x_5619_;
                        v_isShared_5623_ = v_isSharedCheck_5630_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5620_);
                        leanh::lean_dec(v___x_5619_);
                        v___x_5622_ = leanh::lean_box(0);
                        v_isShared_5623_ = v_isSharedCheck_5630_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5631_ = leanh::lean_ctor_get(v___x_5619_, 0);
                    v_isSharedCheck_5638_ = (!leanh::lean_is_exclusive(v___x_5619_)) as u8;
                    if v_isSharedCheck_5638_ == 0 {
                        v___x_5633_ = v___x_5619_;
                        v_isShared_5634_ = v_isSharedCheck_5638_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5631_);
                        leanh::lean_dec(v___x_5619_);
                        v___x_5633_ = leanh::lean_box(0);
                        v_isShared_5634_ = v_isSharedCheck_5638_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5624_ = l_Std_Format_defWidth;
                v___x_5625_ = leanh::lean_unsigned_to_nat(0);
                v___x_5626_ = l_Std_Format_pretty(v_a_5620_, v___x_5624_, v___x_5625_, v___x_5625_);
                if v_isShared_5623_ == 0 {
                    leanh::lean_ctor_set(v___x_5622_, 0, v___x_5626_);
                    v___x_5628_ = v___x_5622_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5629_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5629_, 0, v___x_5626_);
                    v___x_5628_ = v_reuseFailAlloc_5629_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5628_;
            }
            3 => {
                if v_isShared_5634_ == 0 {
                    v___x_5636_ = v___x_5633_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5637_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5637_, 0, v_a_5631_);
                    v___x_5636_ = v_reuseFailAlloc_5637_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5636_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed(
    mut v_r_5639_: *mut leanh::LeanObject,
    mut v_a_5640_: *mut leanh::LeanObject,
    mut v_a_5641_: *mut leanh::LeanObject,
    mut v_a_5642_: *mut leanh::LeanObject,
    mut v_a_5643_: *mut leanh::LeanObject,
    mut v_a_5644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5645_ =
        l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(
            v_r_5639_, v_a_5640_, v_a_5641_, v_a_5642_, v_a_5643_,
        );
    leanh::lean_dec(v_a_5643_);
    leanh::lean_dec_ref(v_a_5642_);
    leanh::lean_dec(v_a_5641_);
    leanh::lean_dec_ref(v_a_5640_);
    return v_res_5645_;
}
pub unsafe fn l_Lean_Meta_Rewrites_SideConditions_ctorIdx(
    mut v_x_5646_: u8,
) -> *mut leanh::LeanObject {
    match v_x_5646_ {
        0 => {
            let mut v___x_5647_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_5647_ = leanh::lean_unsigned_to_nat(0);
            return v___x_5647_;
        }
        1 => {
            let mut v___x_5648_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_5648_ = leanh::lean_unsigned_to_nat(1);
            return v___x_5648_;
        }
        _ => {
            let mut v___x_5649_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_5649_ = leanh::lean_unsigned_to_nat(2);
            return v___x_5649_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Rewrites_SideConditions_ctorIdx___boxed(
    mut v_x_5650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_5651_: u8 = 0;
    let mut v_res_5652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_5651_ = (leanh::lean_unbox(v_x_5650_) as u8);
    v_res_5652_ = l_Lean_Meta_Rewrites_SideConditions_ctorIdx(v_x_boxed_5651_);
    return v_res_5652_;
}
pub unsafe fn l_Lean_Meta_Rewrites_SideConditions_toCtorIdx(
    mut v_x_5653_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_5654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5654_ = l_Lean_Meta_Rewrites_SideConditions_ctorIdx(v_x_5653_);
    return v___x_5654_;
}
pub unsafe fn l_Lean_Meta_Rewrites_SideConditions_toCtorIdx___boxed(
    mut v_x_5655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_5656_: u8 = 0;
    let mut v_res_5657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_5656_ = (leanh::lean_unbox(v_x_5655_) as u8);
    v_res_5657_ = l_Lean_Meta_Rewrites_SideConditions_toCtorIdx(v_x_4__boxed_5656_);
    return v_res_5657_;
}
pub unsafe fn l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg(
    mut v_k_5658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_5658_);
    return v_k_5658_;
}
pub unsafe fn l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg___boxed(
    mut v_k_5659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5660_ = l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg(v_k_5659_);
    leanh::lean_dec(v_k_5659_);
    return v_res_5660_;
}
pub unsafe fn l_Lean_Meta_Rewrites_SideConditions_ctorElim(
    mut v_motive_5661_: *mut leanh::LeanObject,
    mut v_ctorIdx_5662_: *mut leanh::LeanObject,
    mut v_t_5663_: u8,
    mut v_h_5664_: *mut leanh::LeanObject,
    mut v_k_5665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_5665_);
    return v_k_5665_;
}
pub unsafe fn l_Lean_Meta_Rewrites_SideConditions_ctorElim___boxed(
    mut v_motive_5666_: *mut leanh::LeanObject,
    mut v_ctorIdx_5667_: *mut leanh::LeanObject,
    mut v_t_5668_: *mut leanh::LeanObject,
    mut v_h_5669_: *mut leanh::LeanObject,
    mut v_k_5670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_5671_: u8 = 0;
    let mut v_res_5672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_5671_ = (leanh::lean_unbox(v_t_5668_) as u8);
    v_res_5672_ = l_Lean_Meta_Rewrites_SideConditions_ctorElim(
        v_motive_5666_,
        v_ctorIdx_5667_,
        v_t_boxed_5671_,
        v_h_5669_,
        v_k_5670_,
    );
    leanh::lean_dec(v_k_5670_);
    leanh::lean_dec(v_ctorIdx_5667_);
    return v_res_5672_;
}
pub unsafe fn l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg(
    mut v_none_5673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_none_5673_);
    return v_none_5673_;
}
pub unsafe fn l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg___boxed(
    mut v_none_5674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5675_ = l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg(v_none_5674_);
    leanh::lean_dec(v_none_5674_);
    return v_res_5675_;
}
pub unsafe fn l_Lean_Meta_Rewrites_SideConditions_none_elim(
    mut v_motive_5676_: *mut leanh::LeanObject,
    mut v_t_5677_: u8,
    mut v_h_5678_: *mut leanh::LeanObject,
    mut v_none_5679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_none_5679_);
    return v_none_5679_;
}
pub unsafe fn l_Lean_Meta_Rewrites_SideConditions_none_elim___boxed(
    mut v_motive_5680_: *mut leanh::LeanObject,
    mut v_t_5681_: *mut leanh::LeanObject,
    mut v_h_5682_: *mut leanh::LeanObject,
    mut v_none_5683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_5684_: u8 = 0;
    let mut v_res_5685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_5684_ = (leanh::lean_unbox(v_t_5681_) as u8);
    v_res_5685_ = l_Lean_Meta_Rewrites_SideConditions_none_elim(
        v_motive_5680_,
        v_t_boxed_5684_,
        v_h_5682_,
        v_none_5683_,
    );
    leanh::lean_dec(v_none_5683_);
    return v_res_5685_;
}
pub unsafe fn l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg(
    mut v_assumption_5686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_assumption_5686_);
    return v_assumption_5686_;
}
pub unsafe fn l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg___boxed(
    mut v_assumption_5687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5688_ = l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg(v_assumption_5687_);
    leanh::lean_dec(v_assumption_5687_);
    return v_res_5688_;
}
pub unsafe fn l_Lean_Meta_Rewrites_SideConditions_assumption_elim(
    mut v_motive_5689_: *mut leanh::LeanObject,
    mut v_t_5690_: u8,
    mut v_h_5691_: *mut leanh::LeanObject,
    mut v_assumption_5692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_assumption_5692_);
    return v_assumption_5692_;
}
pub unsafe fn l_Lean_Meta_Rewrites_SideConditions_assumption_elim___boxed(
    mut v_motive_5693_: *mut leanh::LeanObject,
    mut v_t_5694_: *mut leanh::LeanObject,
    mut v_h_5695_: *mut leanh::LeanObject,
    mut v_assumption_5696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_5697_: u8 = 0;
    let mut v_res_5698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_5697_ = (leanh::lean_unbox(v_t_5694_) as u8);
    v_res_5698_ = l_Lean_Meta_Rewrites_SideConditions_assumption_elim(
        v_motive_5693_,
        v_t_boxed_5697_,
        v_h_5695_,
        v_assumption_5696_,
    );
    leanh::lean_dec(v_assumption_5696_);
    return v_res_5698_;
}
pub unsafe fn l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg(
    mut v_solveByElim_5699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_solveByElim_5699_);
    return v_solveByElim_5699_;
}
pub unsafe fn l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg___boxed(
    mut v_solveByElim_5700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5701_ =
        l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg(v_solveByElim_5700_);
    leanh::lean_dec(v_solveByElim_5700_);
    return v_res_5701_;
}
pub unsafe fn l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim(
    mut v_motive_5702_: *mut leanh::LeanObject,
    mut v_t_5703_: u8,
    mut v_h_5704_: *mut leanh::LeanObject,
    mut v_solveByElim_5705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_solveByElim_5705_);
    return v_solveByElim_5705_;
}
pub unsafe fn l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___boxed(
    mut v_motive_5706_: *mut leanh::LeanObject,
    mut v_t_5707_: *mut leanh::LeanObject,
    mut v_h_5708_: *mut leanh::LeanObject,
    mut v_solveByElim_5709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_5710_: u8 = 0;
    let mut v_res_5711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_5710_ = (leanh::lean_unbox(v_t_5707_) as u8);
    v_res_5711_ = l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim(
        v_motive_5706_,
        v_t_boxed_5710_,
        v_h_5708_,
        v_solveByElim_5709_,
    );
    leanh::lean_dec(v_solveByElim_5709_);
    return v_res_5711_;
}
pub unsafe fn l_Lean_Meta_Rewrites_solveByElim___lam__0(
    mut v_x_5712_: *mut leanh::LeanObject,
    mut v_x_5713_: *mut leanh::LeanObject,
    mut v___y_5714_: *mut leanh::LeanObject,
    mut v___y_5715_: *mut leanh::LeanObject,
    mut v___y_5716_: *mut leanh::LeanObject,
    mut v___y_5717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5719_ = leanh::lean_box(0);
    v___x_5720_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5720_, 0, v___x_5719_);
    return v___x_5720_;
}
pub unsafe fn l_Lean_Meta_Rewrites_solveByElim___lam__0___boxed(
    mut v_x_5721_: *mut leanh::LeanObject,
    mut v_x_5722_: *mut leanh::LeanObject,
    mut v___y_5723_: *mut leanh::LeanObject,
    mut v___y_5724_: *mut leanh::LeanObject,
    mut v___y_5725_: *mut leanh::LeanObject,
    mut v___y_5726_: *mut leanh::LeanObject,
    mut v___y_5727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5728_ = l_Lean_Meta_Rewrites_solveByElim___lam__0(
        v_x_5721_,
        v_x_5722_,
        v___y_5723_,
        v___y_5724_,
        v___y_5725_,
        v___y_5726_,
    );
    leanh::lean_dec(v___y_5726_);
    leanh::lean_dec_ref(v___y_5725_);
    leanh::lean_dec(v___y_5724_);
    leanh::lean_dec_ref(v___y_5723_);
    leanh::lean_dec(v_x_5722_);
    leanh::lean_dec(v_x_5721_);
    return v_res_5728_;
}
pub unsafe fn l_Lean_Meta_Rewrites_solveByElim___lam__1(
    mut v_x_5729_: *mut leanh::LeanObject,
    mut v___y_5730_: *mut leanh::LeanObject,
    mut v___y_5731_: *mut leanh::LeanObject,
    mut v___y_5732_: *mut leanh::LeanObject,
    mut v___y_5733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5735_: u8 = 0;
    let mut v___x_5736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5735_ = 0;
    v___x_5736_ = leanh::lean_box((v___x_5735_) as usize);
    v___x_5737_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5737_, 0, v___x_5736_);
    return v___x_5737_;
}
pub unsafe fn l_Lean_Meta_Rewrites_solveByElim___lam__1___boxed(
    mut v_x_5738_: *mut leanh::LeanObject,
    mut v___y_5739_: *mut leanh::LeanObject,
    mut v___y_5740_: *mut leanh::LeanObject,
    mut v___y_5741_: *mut leanh::LeanObject,
    mut v___y_5742_: *mut leanh::LeanObject,
    mut v___y_5743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5744_ = l_Lean_Meta_Rewrites_solveByElim___lam__1(
        v_x_5738_,
        v___y_5739_,
        v___y_5740_,
        v___y_5741_,
        v___y_5742_,
    );
    leanh::lean_dec(v___y_5742_);
    leanh::lean_dec_ref(v___y_5741_);
    leanh::lean_dec(v___y_5740_);
    leanh::lean_dec_ref(v___y_5739_);
    leanh::lean_dec(v_x_5738_);
    return v_res_5744_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(
    mut v_msgData_5745_: *mut leanh::LeanObject,
    mut v___y_5746_: *mut leanh::LeanObject,
    mut v___y_5747_: *mut leanh::LeanObject,
    mut v___y_5748_: *mut leanh::LeanObject,
    mut v___y_5749_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5751_ = lean_st_ref_get(v___y_5749_);
    v_env_5752_ = leanh::lean_ctor_get(v___x_5751_, 0);
    leanh::lean_inc_ref(v_env_5752_);
    leanh::lean_dec(v___x_5751_);
    v___x_5753_ = lean_st_ref_get(v___y_5747_);
    v_mctx_5754_ = leanh::lean_ctor_get(v___x_5753_, 0);
    leanh::lean_inc_ref(v_mctx_5754_);
    leanh::lean_dec(v___x_5753_);
    v_lctx_5755_ = leanh::lean_ctor_get(v___y_5746_, 2);
    v_options_5756_ = leanh::lean_ctor_get(v___y_5748_, 2);
    leanh::lean_inc_ref(v_options_5756_);
    leanh::lean_inc_ref(v_lctx_5755_);
    v___x_5757_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_5757_, 0, v_env_5752_);
    leanh::lean_ctor_set(v___x_5757_, 1, v_mctx_5754_);
    leanh::lean_ctor_set(v___x_5757_, 2, v_lctx_5755_);
    leanh::lean_ctor_set(v___x_5757_, 3, v_options_5756_);
    v___x_5758_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5758_, 0, v___x_5757_);
    leanh::lean_ctor_set(v___x_5758_, 1, v_msgData_5745_);
    v___x_5759_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5759_, 0, v___x_5758_);
    return v___x_5759_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0___boxed(
    mut v_msgData_5760_: *mut leanh::LeanObject,
    mut v___y_5761_: *mut leanh::LeanObject,
    mut v___y_5762_: *mut leanh::LeanObject,
    mut v___y_5763_: *mut leanh::LeanObject,
    mut v___y_5764_: *mut leanh::LeanObject,
    mut v___y_5765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5766_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msgData_5760_, v___y_5761_, v___y_5762_, v___y_5763_, v___y_5764_);
    leanh::lean_dec(v___y_5764_);
    leanh::lean_dec_ref(v___y_5763_);
    leanh::lean_dec(v___y_5762_);
    leanh::lean_dec_ref(v___y_5761_);
    return v_res_5766_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(
    mut v_msg_5767_: *mut leanh::LeanObject,
    mut v___y_5768_: *mut leanh::LeanObject,
    mut v___y_5769_: *mut leanh::LeanObject,
    mut v___y_5770_: *mut leanh::LeanObject,
    mut v___y_5771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_5773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5778_: u8 = 0;
    let mut v___x_5779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5783_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5773_ = leanh::lean_ctor_get(v___y_5770_, 5);
                v___x_5774_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msg_5767_, v___y_5768_, v___y_5769_, v___y_5770_, v___y_5771_);
                v_a_5775_ = leanh::lean_ctor_get(v___x_5774_, 0);
                v_isSharedCheck_5783_ = (!leanh::lean_is_exclusive(v___x_5774_)) as u8;
                if v_isSharedCheck_5783_ == 0 {
                    v___x_5777_ = v___x_5774_;
                    v_isShared_5778_ = v_isSharedCheck_5783_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_5775_);
                    leanh::lean_dec(v___x_5774_);
                    v___x_5777_ = leanh::lean_box(0);
                    v_isShared_5778_ = v_isSharedCheck_5783_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_5773_);
                v___x_5779_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5779_, 0, v_ref_5773_);
                leanh::lean_ctor_set(v___x_5779_, 1, v_a_5775_);
                if v_isShared_5778_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5777_, 1);
                    leanh::lean_ctor_set(v___x_5777_, 0, v___x_5779_);
                    v___x_5781_ = v___x_5777_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5782_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5782_, 0, v___x_5779_);
                    v___x_5781_ = v_reuseFailAlloc_5782_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5781_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg___boxed(
    mut v_msg_5784_: *mut leanh::LeanObject,
    mut v___y_5785_: *mut leanh::LeanObject,
    mut v___y_5786_: *mut leanh::LeanObject,
    mut v___y_5787_: *mut leanh::LeanObject,
    mut v___y_5788_: *mut leanh::LeanObject,
    mut v___y_5789_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5790_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(
        v_msg_5784_,
        v___y_5785_,
        v___y_5786_,
        v___y_5787_,
        v___y_5788_,
    );
    leanh::lean_dec(v___y_5788_);
    leanh::lean_dec_ref(v___y_5787_);
    leanh::lean_dec(v___y_5786_);
    leanh::lean_dec_ref(v___y_5785_);
    return v_res_5790_;
}
pub unsafe fn _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5792_ = l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__0;
    v___x_5793_ = l_Lean_stringToMessageData(v___x_5792_);
    return v___x_5793_;
}
pub unsafe fn l_Lean_Meta_Rewrites_solveByElim___lam__2(
    mut v_x_5794_: *mut leanh::LeanObject,
    mut v___y_5795_: *mut leanh::LeanObject,
    mut v___y_5796_: *mut leanh::LeanObject,
    mut v___y_5797_: *mut leanh::LeanObject,
    mut v___y_5798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5800_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1_once),
        _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1,
    );
    v___x_5801_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(
        v___x_5800_,
        v___y_5795_,
        v___y_5796_,
        v___y_5797_,
        v___y_5798_,
    );
    return v___x_5801_;
}
pub unsafe fn l_Lean_Meta_Rewrites_solveByElim___lam__2___boxed(
    mut v_x_5802_: *mut leanh::LeanObject,
    mut v___y_5803_: *mut leanh::LeanObject,
    mut v___y_5804_: *mut leanh::LeanObject,
    mut v___y_5805_: *mut leanh::LeanObject,
    mut v___y_5806_: *mut leanh::LeanObject,
    mut v___y_5807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5808_ = l_Lean_Meta_Rewrites_solveByElim___lam__2(
        v_x_5802_,
        v___y_5803_,
        v___y_5804_,
        v___y_5805_,
        v___y_5806_,
    );
    leanh::lean_dec(v___y_5806_);
    leanh::lean_dec_ref(v___y_5805_);
    leanh::lean_dec(v___y_5804_);
    leanh::lean_dec_ref(v___y_5803_);
    leanh::lean_dec(v_x_5802_);
    return v_res_5808_;
}
pub unsafe fn l_Lean_Meta_Rewrites_solveByElim(
    mut v_goals_5818_: *mut leanh::LeanObject,
    mut v_depth_5819_: *mut leanh::LeanObject,
    mut v_a_5820_: *mut leanh::LeanObject,
    mut v_a_5821_: *mut leanh::LeanObject,
    mut v_a_5822_: *mut leanh::LeanObject,
    mut v_a_5823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: u8 = 0;
    let mut v___x_5829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: u8 = 0;
    let mut v___x_5831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: u8 = 0;
    let mut v___x_5833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cfg_5834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5845_: u8 = 0;
    let mut v___x_5846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5852_: u8 = 0;
    let mut v_a_5853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5856_: u8 = 0;
    let mut v___x_5858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5860_: u8 = 0;
    let mut v_a_5861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5864_: u8 = 0;
    let mut v___x_5866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5868_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5825_ = l_Lean_Meta_Rewrites_solveByElim___closed__0;
                v___f_5826_ = l_Lean_Meta_Rewrites_solveByElim___closed__1;
                v___f_5827_ = l_Lean_Meta_Rewrites_solveByElim___closed__2;
                v___x_5828_ = 0;
                v___x_5829_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                leanh::lean_ctor_set(v___x_5829_, 0, v_depth_5819_);
                leanh::lean_ctor_set(v___x_5829_, 1, v___f_5825_);
                leanh::lean_ctor_set(v___x_5829_, 2, v___f_5826_);
                leanh::lean_ctor_set(v___x_5829_, 3, v___f_5827_);
                leanh::lean_ctor_set_uint8(
                    v___x_5829_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v___x_5828_,
                );
                v___x_5830_ = 1;
                v___x_5831_ = l_Lean_Meta_Rewrites_solveByElim___closed__3;
                v___x_5832_ = 1;
                v___x_5833_ = leanh::lean_alloc_ctor(0, 2, (3) as u32);
                leanh::lean_ctor_set(v___x_5833_, 0, v___x_5829_);
                leanh::lean_ctor_set(v___x_5833_, 1, v___x_5831_);
                leanh::lean_ctor_set_uint8(
                    v___x_5833_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_5832_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5833_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___x_5830_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5833_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 2) as u32,
                    v___x_5828_,
                );
                v_cfg_5834_ = leanh::lean_alloc_ctor(0, 1, (4) as u32);
                leanh::lean_ctor_set(v_cfg_5834_, 0, v___x_5833_);
                leanh::lean_ctor_set_uint8(
                    v_cfg_5834_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_5830_,
                );
                leanh::lean_ctor_set_uint8(
                    v_cfg_5834_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                    v___x_5830_,
                );
                leanh::lean_ctor_set_uint8(
                    v_cfg_5834_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 2) as u32,
                    v___x_5830_,
                );
                leanh::lean_ctor_set_uint8(
                    v_cfg_5834_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 3) as u32,
                    v___x_5828_,
                );
                v___x_5835_ = leanh::lean_box(0);
                v___x_5836_ = l_Lean_Meta_Rewrites_solveByElim___closed__4;
                v___x_5837_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(
                    v___x_5828_,
                    v___x_5828_,
                    v___x_5835_,
                    v___x_5835_,
                    v___x_5836_,
                    v_a_5820_,
                    v_a_5821_,
                    v_a_5822_,
                    v_a_5823_,
                );
                if leanh::lean_obj_tag(v___x_5837_) == 0 {
                    v_a_5838_ = leanh::lean_ctor_get(v___x_5837_, 0);
                    leanh::lean_inc(v_a_5838_);
                    leanh::lean_dec_ref_known(v___x_5837_, 1);
                    v_fst_5839_ = leanh::lean_ctor_get(v_a_5838_, 0);
                    leanh::lean_inc(v_fst_5839_);
                    v_snd_5840_ = leanh::lean_ctor_get(v_a_5838_, 1);
                    leanh::lean_inc(v_snd_5840_);
                    leanh::lean_dec(v_a_5838_);
                    v___x_5841_ = l_Lean_Meta_SolveByElim_solveByElim(
                        v_cfg_5834_,
                        v_fst_5839_,
                        v_snd_5840_,
                        v_goals_5818_,
                        v_a_5820_,
                        v_a_5821_,
                        v_a_5822_,
                        v_a_5823_,
                    );
                    if leanh::lean_obj_tag(v___x_5841_) == 0 {
                        v_a_5842_ = leanh::lean_ctor_get(v___x_5841_, 0);
                        v_isSharedCheck_5852_ =
                            (!leanh::lean_is_exclusive(v___x_5841_)) as u8;
                        if v_isSharedCheck_5852_ == 0 {
                            v___x_5844_ = v___x_5841_;
                            v_isShared_5845_ = v_isSharedCheck_5852_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5842_);
                            leanh::lean_dec(v___x_5841_);
                            v___x_5844_ = leanh::lean_box(0);
                            v_isShared_5845_ = v_isSharedCheck_5852_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5853_ = leanh::lean_ctor_get(v___x_5841_, 0);
                        v_isSharedCheck_5860_ =
                            (!leanh::lean_is_exclusive(v___x_5841_)) as u8;
                        if v_isSharedCheck_5860_ == 0 {
                            v___x_5855_ = v___x_5841_;
                            v_isShared_5856_ = v_isSharedCheck_5860_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5853_);
                            leanh::lean_dec(v___x_5841_);
                            v___x_5855_ = leanh::lean_box(0);
                            v_isShared_5856_ = v_isSharedCheck_5860_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref_known(v_cfg_5834_, 1);
                    leanh::lean_dec(v_goals_5818_);
                    v_a_5861_ = leanh::lean_ctor_get(v___x_5837_, 0);
                    v_isSharedCheck_5868_ = (!leanh::lean_is_exclusive(v___x_5837_)) as u8;
                    if v_isSharedCheck_5868_ == 0 {
                        v___x_5863_ = v___x_5837_;
                        v_isShared_5864_ = v_isSharedCheck_5868_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5861_);
                        leanh::lean_dec(v___x_5837_);
                        v___x_5863_ = leanh::lean_box(0);
                        v_isShared_5864_ = v_isSharedCheck_5868_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_5842_) == 0 {
                    v___x_5846_ = leanh::lean_box(0);
                    if v_isShared_5845_ == 0 {
                        leanh::lean_ctor_set(v___x_5844_, 0, v___x_5846_);
                        v___x_5848_ = v___x_5844_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5849_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5849_, 0, v___x_5846_);
                        v___x_5848_ = v_reuseFailAlloc_5849_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5844_);
                    leanh::lean_dec(v_a_5842_);
                    v___x_5850_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1_once
                        ),
                        _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1,
                    );
                    v___x_5851_ =
                        l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(
                            v___x_5850_,
                            v_a_5820_,
                            v_a_5821_,
                            v_a_5822_,
                            v_a_5823_,
                        );
                    return v___x_5851_;
                }
            }
            2 => {
                return v___x_5848_;
            }
            3 => {
                if v_isShared_5856_ == 0 {
                    v___x_5858_ = v___x_5855_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5859_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5859_, 0, v_a_5853_);
                    v___x_5858_ = v_reuseFailAlloc_5859_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5858_;
            }
            5 => {
                if v_isShared_5864_ == 0 {
                    v___x_5866_ = v___x_5863_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5867_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5867_, 0, v_a_5861_);
                    v___x_5866_ = v_reuseFailAlloc_5867_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5866_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Rewrites_solveByElim___boxed(
    mut v_goals_5869_: *mut leanh::LeanObject,
    mut v_depth_5870_: *mut leanh::LeanObject,
    mut v_a_5871_: *mut leanh::LeanObject,
    mut v_a_5872_: *mut leanh::LeanObject,
    mut v_a_5873_: *mut leanh::LeanObject,
    mut v_a_5874_: *mut leanh::LeanObject,
    mut v_a_5875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5876_ = l_Lean_Meta_Rewrites_solveByElim(
        v_goals_5869_,
        v_depth_5870_,
        v_a_5871_,
        v_a_5872_,
        v_a_5873_,
        v_a_5874_,
    );
    leanh::lean_dec(v_a_5874_);
    leanh::lean_dec_ref(v_a_5873_);
    leanh::lean_dec(v_a_5872_);
    leanh::lean_dec_ref(v_a_5871_);
    return v_res_5876_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0(
    mut v_00_u03b1_5877_: *mut leanh::LeanObject,
    mut v_msg_5878_: *mut leanh::LeanObject,
    mut v___y_5879_: *mut leanh::LeanObject,
    mut v___y_5880_: *mut leanh::LeanObject,
    mut v___y_5881_: *mut leanh::LeanObject,
    mut v___y_5882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5884_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(
        v_msg_5878_,
        v___y_5879_,
        v___y_5880_,
        v___y_5881_,
        v___y_5882_,
    );
    return v___x_5884_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___boxed(
    mut v_00_u03b1_5885_: *mut leanh::LeanObject,
    mut v_msg_5886_: *mut leanh::LeanObject,
    mut v___y_5887_: *mut leanh::LeanObject,
    mut v___y_5888_: *mut leanh::LeanObject,
    mut v___y_5889_: *mut leanh::LeanObject,
    mut v___y_5890_: *mut leanh::LeanObject,
    mut v___y_5891_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5892_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0(
        v_00_u03b1_5885_,
        v_msg_5886_,
        v___y_5887_,
        v___y_5888_,
        v___y_5889_,
        v___y_5890_,
    );
    leanh::lean_dec(v___y_5890_);
    leanh::lean_dec_ref(v___y_5889_);
    leanh::lean_dec(v___y_5888_);
    leanh::lean_dec_ref(v___y_5887_);
    return v_res_5892_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(
    mut v_e_5893_: *mut leanh::LeanObject,
    mut v___y_5894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5896_: u8 = 0;
    let mut v___x_5897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5910_: u8 = 0;
    let mut v___x_5912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5916_: u8 = 0;
    let mut v_unused_5917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5896_ = l_Lean_Expr_hasMVar(v_e_5893_);
                if v___x_5896_ == 0 {
                    v___x_5897_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5897_, 0, v_e_5893_);
                    return v___x_5897_;
                } else {
                    v___x_5898_ = lean_st_ref_get(v___y_5894_);
                    v_mctx_5899_ = leanh::lean_ctor_get(v___x_5898_, 0);
                    leanh::lean_inc_ref(v_mctx_5899_);
                    leanh::lean_dec(v___x_5898_);
                    v___x_5900_ = l_Lean_instantiateMVarsCore(v_mctx_5899_, v_e_5893_);
                    v_fst_5901_ = leanh::lean_ctor_get(v___x_5900_, 0);
                    leanh::lean_inc(v_fst_5901_);
                    v_snd_5902_ = leanh::lean_ctor_get(v___x_5900_, 1);
                    leanh::lean_inc(v_snd_5902_);
                    leanh::lean_dec_ref(v___x_5900_);
                    v___x_5903_ = lean_st_ref_take(v___y_5894_);
                    v_cache_5904_ = leanh::lean_ctor_get(v___x_5903_, 1);
                    v_zetaDeltaFVarIds_5905_ = leanh::lean_ctor_get(v___x_5903_, 2);
                    v_postponed_5906_ = leanh::lean_ctor_get(v___x_5903_, 3);
                    v_diag_5907_ = leanh::lean_ctor_get(v___x_5903_, 4);
                    v_isSharedCheck_5916_ = (!leanh::lean_is_exclusive(v___x_5903_)) as u8;
                    if v_isSharedCheck_5916_ == 0 {
                        v_unused_5917_ = leanh::lean_ctor_get(v___x_5903_, 0);
                        leanh::lean_dec(v_unused_5917_);
                        v___x_5909_ = v___x_5903_;
                        v_isShared_5910_ = v_isSharedCheck_5916_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_5907_);
                        leanh::lean_inc(v_postponed_5906_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_5905_);
                        leanh::lean_inc(v_cache_5904_);
                        leanh::lean_dec(v___x_5903_);
                        v___x_5909_ = leanh::lean_box(0);
                        v_isShared_5910_ = v_isSharedCheck_5916_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5910_ == 0 {
                    leanh::lean_ctor_set(v___x_5909_, 0, v_snd_5902_);
                    v___x_5912_ = v___x_5909_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5915_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5915_, 0, v_snd_5902_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5915_, 1, v_cache_5904_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5915_,
                        2,
                        v_zetaDeltaFVarIds_5905_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5915_, 3, v_postponed_5906_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5915_, 4, v_diag_5907_);
                    v___x_5912_ = v_reuseFailAlloc_5915_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5913_ = lean_st_ref_set(v___y_5894_, v___x_5912_);
                v___x_5914_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5914_, 0, v_fst_5901_);
                return v___x_5914_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg___boxed(
    mut v_e_5918_: *mut leanh::LeanObject,
    mut v___y_5919_: *mut leanh::LeanObject,
    mut v___y_5920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5921_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(
        v_e_5918_,
        v___y_5919_,
    );
    leanh::lean_dec(v___y_5919_);
    return v_res_5921_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0(
    mut v_e_5922_: *mut leanh::LeanObject,
    mut v___y_5923_: *mut leanh::LeanObject,
    mut v___y_5924_: *mut leanh::LeanObject,
    mut v___y_5925_: *mut leanh::LeanObject,
    mut v___y_5926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5928_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(
        v_e_5922_,
        v___y_5924_,
    );
    return v___x_5928_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___boxed(
    mut v_e_5929_: *mut leanh::LeanObject,
    mut v___y_5930_: *mut leanh::LeanObject,
    mut v___y_5931_: *mut leanh::LeanObject,
    mut v___y_5932_: *mut leanh::LeanObject,
    mut v___y_5933_: *mut leanh::LeanObject,
    mut v___y_5934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5935_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0(
        v_e_5929_,
        v___y_5930_,
        v___y_5931_,
        v___y_5932_,
        v___y_5933_,
    );
    leanh::lean_dec(v___y_5933_);
    leanh::lean_dec_ref(v___y_5932_);
    leanh::lean_dec(v___y_5931_);
    leanh::lean_dec_ref(v___y_5930_);
    return v_res_5935_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0() -> f64
{
    let mut v___x_5936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: f64 = 0.0;
    v___x_5936_ = leanh::lean_unsigned_to_nat(0);
    v___x_5937_ = lean_float_of_nat(v___x_5936_);
    return v___x_5937_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(
    mut v_cls_5941_: *mut leanh::LeanObject,
    mut v_msg_5942_: *mut leanh::LeanObject,
    mut v___y_5943_: *mut leanh::LeanObject,
    mut v___y_5944_: *mut leanh::LeanObject,
    mut v___y_5945_: *mut leanh::LeanObject,
    mut v___y_5946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_5948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5953_: u8 = 0;
    let mut v___x_5954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5966_: u8 = 0;
    let mut v_tid_5967_: u64 = 0;
    let mut v_traces_5968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5971_: u8 = 0;
    let mut v___x_5972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: f64 = 0.0;
    let mut v___x_5974_: u8 = 0;
    let mut v___x_5975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5992_: u8 = 0;
    let mut v_isSharedCheck_5993_: u8 = 0;
    let mut v_isSharedCheck_5994_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5948_ = leanh::lean_ctor_get(v___y_5945_, 5);
                v___x_5949_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msg_5942_, v___y_5943_, v___y_5944_, v___y_5945_, v___y_5946_);
                v_a_5950_ = leanh::lean_ctor_get(v___x_5949_, 0);
                v_isSharedCheck_5994_ = (!leanh::lean_is_exclusive(v___x_5949_)) as u8;
                if v_isSharedCheck_5994_ == 0 {
                    v___x_5952_ = v___x_5949_;
                    v_isShared_5953_ = v_isSharedCheck_5994_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_5950_);
                    leanh::lean_dec(v___x_5949_);
                    v___x_5952_ = leanh::lean_box(0);
                    v_isShared_5953_ = v_isSharedCheck_5994_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5954_ = lean_st_ref_take(v___y_5946_);
                v_traceState_5955_ = leanh::lean_ctor_get(v___x_5954_, 4);
                v_env_5956_ = leanh::lean_ctor_get(v___x_5954_, 0);
                v_nextMacroScope_5957_ = leanh::lean_ctor_get(v___x_5954_, 1);
                v_ngen_5958_ = leanh::lean_ctor_get(v___x_5954_, 2);
                v_auxDeclNGen_5959_ = leanh::lean_ctor_get(v___x_5954_, 3);
                v_cache_5960_ = leanh::lean_ctor_get(v___x_5954_, 5);
                v_messages_5961_ = leanh::lean_ctor_get(v___x_5954_, 6);
                v_infoState_5962_ = leanh::lean_ctor_get(v___x_5954_, 7);
                v_snapshotTasks_5963_ = leanh::lean_ctor_get(v___x_5954_, 8);
                v_isSharedCheck_5993_ = (!leanh::lean_is_exclusive(v___x_5954_)) as u8;
                if v_isSharedCheck_5993_ == 0 {
                    v___x_5965_ = v___x_5954_;
                    v_isShared_5966_ = v_isSharedCheck_5993_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_5963_);
                    leanh::lean_inc(v_infoState_5962_);
                    leanh::lean_inc(v_messages_5961_);
                    leanh::lean_inc(v_cache_5960_);
                    leanh::lean_inc(v_traceState_5955_);
                    leanh::lean_inc(v_auxDeclNGen_5959_);
                    leanh::lean_inc(v_ngen_5958_);
                    leanh::lean_inc(v_nextMacroScope_5957_);
                    leanh::lean_inc(v_env_5956_);
                    leanh::lean_dec(v___x_5954_);
                    v___x_5965_ = leanh::lean_box(0);
                    v_isShared_5966_ = v_isSharedCheck_5993_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_5967_ = leanh::lean_ctor_get_uint64(
                    v_traceState_5955_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_5968_ = leanh::lean_ctor_get(v_traceState_5955_, 0);
                v_isSharedCheck_5992_ =
                    (!leanh::lean_is_exclusive(v_traceState_5955_)) as u8;
                if v_isSharedCheck_5992_ == 0 {
                    v___x_5970_ = v_traceState_5955_;
                    v_isShared_5971_ = v_isSharedCheck_5992_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_5968_);
                    leanh::lean_dec(v_traceState_5955_);
                    v___x_5970_ = leanh::lean_box(0);
                    v_isShared_5971_ = v_isSharedCheck_5992_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5972_ = leanh::lean_box(0);
                v___x_5973_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0);
                v___x_5974_ = 0;
                v___x_5975_ =
                    l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__1;
                v___x_5976_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_5976_, 0, v_cls_5941_);
                leanh::lean_ctor_set(v___x_5976_, 1, v___x_5972_);
                leanh::lean_ctor_set(v___x_5976_, 2, v___x_5975_);
                leanh::lean_ctor_set_float(
                    v___x_5976_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_5973_,
                );
                leanh::lean_ctor_set_float(
                    v___x_5976_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_5973_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5976_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_5974_,
                );
                v___x_5977_ =
                    l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__2;
                v___x_5978_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_5978_, 0, v___x_5976_);
                leanh::lean_ctor_set(v___x_5978_, 1, v_a_5950_);
                leanh::lean_ctor_set(v___x_5978_, 2, v___x_5977_);
                leanh::lean_inc(v_ref_5948_);
                v___x_5979_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5979_, 0, v_ref_5948_);
                leanh::lean_ctor_set(v___x_5979_, 1, v___x_5978_);
                v___x_5980_ = l_Lean_PersistentArray_push___redArg(v_traces_5968_, v___x_5979_);
                if v_isShared_5971_ == 0 {
                    leanh::lean_ctor_set(v___x_5970_, 0, v___x_5980_);
                    v___x_5982_ = v___x_5970_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5991_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5991_, 0, v___x_5980_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_5991_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_5967_,
                    );
                    v___x_5982_ = v_reuseFailAlloc_5991_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5966_ == 0 {
                    leanh::lean_ctor_set(v___x_5965_, 4, v___x_5982_);
                    v___x_5984_ = v___x_5965_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5990_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5990_, 0, v_env_5956_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5990_, 1, v_nextMacroScope_5957_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5990_, 2, v_ngen_5958_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5990_, 3, v_auxDeclNGen_5959_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5990_, 4, v___x_5982_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5990_, 5, v_cache_5960_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5990_, 6, v_messages_5961_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5990_, 7, v_infoState_5962_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5990_, 8, v_snapshotTasks_5963_);
                    v___x_5984_ = v_reuseFailAlloc_5990_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5985_ = lean_st_ref_set(v___y_5946_, v___x_5984_);
                v___x_5986_ = leanh::lean_box(0);
                if v_isShared_5953_ == 0 {
                    leanh::lean_ctor_set(v___x_5952_, 0, v___x_5986_);
                    v___x_5988_ = v___x_5952_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5989_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5989_, 0, v___x_5986_);
                    v___x_5988_ = v_reuseFailAlloc_5989_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5988_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___boxed(
    mut v_cls_5995_: *mut leanh::LeanObject,
    mut v_msg_5996_: *mut leanh::LeanObject,
    mut v___y_5997_: *mut leanh::LeanObject,
    mut v___y_5998_: *mut leanh::LeanObject,
    mut v___y_5999_: *mut leanh::LeanObject,
    mut v___y_6000_: *mut leanh::LeanObject,
    mut v___y_6001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6002_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(
        v_cls_5995_,
        v_msg_5996_,
        v___y_5997_,
        v___y_5998_,
        v___y_5999_,
        v___y_6000_,
    );
    leanh::lean_dec(v___y_6000_);
    leanh::lean_dec_ref(v___y_5999_);
    leanh::lean_dec(v___y_5998_);
    leanh::lean_dec_ref(v___y_5997_);
    return v_res_6002_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(
    mut v_x_6003_: *mut leanh::LeanObject,
    mut v_x_6004_: *mut leanh::LeanObject,
    mut v___y_6005_: *mut leanh::LeanObject,
    mut v___y_6006_: *mut leanh::LeanObject,
    mut v___y_6007_: *mut leanh::LeanObject,
    mut v___y_6008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6016_: u8 = 0;
    let mut v___x_6017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6026_: u8 = 0;
    let mut v___x_6028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6030_: u8 = 0;
    let mut v_isSharedCheck_6031_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6003_) == 0 {
                    v___x_6010_ = l_List_reverse___redArg(v_x_6004_);
                    v___x_6011_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6011_, 0, v___x_6010_);
                    return v___x_6011_;
                } else {
                    v_head_6012_ = leanh::lean_ctor_get(v_x_6003_, 0);
                    v_tail_6013_ = leanh::lean_ctor_get(v_x_6003_, 1);
                    v_isSharedCheck_6031_ = (!leanh::lean_is_exclusive(v_x_6003_)) as u8;
                    if v_isSharedCheck_6031_ == 0 {
                        v___x_6015_ = v_x_6003_;
                        v_isShared_6016_ = v_isSharedCheck_6031_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_6013_);
                        leanh::lean_inc(v_head_6012_);
                        leanh::lean_dec(v_x_6003_);
                        v___x_6015_ = leanh::lean_box(0);
                        v_isShared_6016_ = v_isSharedCheck_6031_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6017_ = l_Lean_MVarId_assumption(
                    v_head_6012_,
                    v___y_6005_,
                    v___y_6006_,
                    v___y_6007_,
                    v___y_6008_,
                );
                if leanh::lean_obj_tag(v___x_6017_) == 0 {
                    v_a_6018_ = leanh::lean_ctor_get(v___x_6017_, 0);
                    leanh::lean_inc(v_a_6018_);
                    leanh::lean_dec_ref_known(v___x_6017_, 1);
                    if v_isShared_6016_ == 0 {
                        leanh::lean_ctor_set(v___x_6015_, 1, v_x_6004_);
                        leanh::lean_ctor_set(v___x_6015_, 0, v_a_6018_);
                        v___x_6020_ = v___x_6015_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6022_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6022_, 0, v_a_6018_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6022_, 1, v_x_6004_);
                        v___x_6020_ = v_reuseFailAlloc_6022_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6015_);
                    leanh::lean_dec(v_tail_6013_);
                    leanh::lean_dec(v_x_6004_);
                    v_a_6023_ = leanh::lean_ctor_get(v___x_6017_, 0);
                    v_isSharedCheck_6030_ = (!leanh::lean_is_exclusive(v___x_6017_)) as u8;
                    if v_isSharedCheck_6030_ == 0 {
                        v___x_6025_ = v___x_6017_;
                        v_isShared_6026_ = v_isSharedCheck_6030_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6023_);
                        leanh::lean_dec(v___x_6017_);
                        v___x_6025_ = leanh::lean_box(0);
                        v_isShared_6026_ = v_isSharedCheck_6030_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_6003_ = v_tail_6013_;
                v_x_6004_ = v___x_6020_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_6026_ == 0 {
                    v___x_6028_ = v___x_6025_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6029_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6029_, 0, v_a_6023_);
                    v___x_6028_ = v_reuseFailAlloc_6029_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6028_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1___boxed(
    mut v_x_6032_: *mut leanh::LeanObject,
    mut v_x_6033_: *mut leanh::LeanObject,
    mut v___y_6034_: *mut leanh::LeanObject,
    mut v___y_6035_: *mut leanh::LeanObject,
    mut v___y_6036_: *mut leanh::LeanObject,
    mut v___y_6037_: *mut leanh::LeanObject,
    mut v___y_6038_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6039_ = l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(
        v_x_6032_,
        v_x_6033_,
        v___y_6034_,
        v___y_6035_,
        v___y_6036_,
        v___y_6037_,
    );
    leanh::lean_dec(v___y_6037_);
    leanh::lean_dec_ref(v___y_6036_);
    leanh::lean_dec(v___y_6035_);
    leanh::lean_dec_ref(v___y_6034_);
    return v_res_6039_;
}
pub unsafe fn _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_6052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6052_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
    v___x_6053_ = l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4;
    v___x_6054_ = l_Lean_Name_append(v___x_6053_, v___x_6052_);
    return v___x_6054_;
}
pub unsafe fn _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_6056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6056_ = l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__6;
    v___x_6057_ = l_Lean_stringToMessageData(v___x_6056_);
    return v___x_6057_;
}
pub unsafe fn l_Lean_Meta_Rewrites_rwLemma___lam__0(
    mut v_weight_6059_: *mut leanh::LeanObject,
    mut v_goal_6060_: *mut leanh::LeanObject,
    mut v_target_6061_: *mut leanh::LeanObject,
    mut v_symm_6062_: u8,
    mut v_side_6063_: u8,
    mut v_lem_6064_: *mut leanh::LeanObject,
    mut v___y_6065_: *mut leanh::LeanObject,
    mut v___y_6066_: *mut leanh::LeanObject,
    mut v___y_6067_: *mut leanh::LeanObject,
    mut v___y_6068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6075_: u8 = 0;
    let mut v___x_6076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6079_: u8 = 0;
    let mut v___x_6080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6084_: u8 = 0;
    let mut v_unused_6085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6089_: u8 = 0;
    let mut v___x_6091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6093_: u8 = 0;
    let mut v___x_6094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6103_: u8 = 0;
    let mut v___x_6104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6110_: u8 = 0;
    let mut v___x_6111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6112_: u8 = 0;
    let mut v___x_6113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6117_: u8 = 0;
    let mut v_a_6118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6121_: u8 = 0;
    let mut v___x_6123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6125_: u8 = 0;
    let mut v___y_6127_: u8 = 0;
    let mut v___y_6128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6130_: u8 = 0;
    let mut v___y_6131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6141_: u8 = 0;
    let mut v___x_6142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6158_: u8 = 0;
    let mut v___x_6159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6163_: u8 = 0;
    let mut v___x_6165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6167_: u8 = 0;
    let mut v___x_6168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6174_: u8 = 0;
    let mut v___x_6175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6179_: u8 = 0;
    let mut v___x_6181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6183_: u8 = 0;
    let mut v___x_6184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: u8 = 0;
    let mut v___x_6190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6195_: u8 = 0;
    let mut v_eNew_6196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_6197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6198_: u8 = 0;
    let mut v___x_6199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6204_: u8 = 0;
    let mut v___x_6205_: u8 = 0;
    let mut v_a_6206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6209_: u8 = 0;
    let mut v___x_6211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6213_: u8 = 0;
    let mut v___x_6214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6219_: u8 = 0;
    let mut v___x_6220_: u8 = 0;
    let mut v_a_6221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6224_: u8 = 0;
    let mut v___x_6226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6228_: u8 = 0;
    let mut v___x_6229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6235_: u8 = 0;
    let mut v___x_6236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6237_: u8 = 0;
    let mut v___x_6239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6244_: u8 = 0;
    let mut v_a_6245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6248_: u8 = 0;
    let mut v___x_6250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6252_: u8 = 0;
    let mut v_isSharedCheck_6253_: u8 = 0;
    let mut v_a_6254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6255_: u8 = 0;
    let mut v___x_6256_: u8 = 0;
    let mut v_a_6257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6260_: u8 = 0;
    let mut v___x_6262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6264_: u8 = 0;
    let mut v___y_6266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6278_: u8 = 0;
    let mut v___x_6280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6282_: u8 = 0;
    let mut v_val_6284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6286_: u8 = 0;
    let mut v_inheritedTraceOptions_6287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6290_: u8 = 0;
    let mut v___x_6291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6303_: u8 = 0;
    let mut v___y_6305_: u8 = 0;
    let mut v___x_6306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6309_: u8 = 0;
    let mut v___x_6310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6314_: u8 = 0;
    let mut v_unused_6315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6319_: u8 = 0;
    let mut v___x_6321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6323_: u8 = 0;
    let mut v___x_6325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6327_: u8 = 0;
    let mut v___x_6328_: u8 = 0;
    let mut v_isSharedCheck_6329_: u8 = 0;
    let mut v_a_6330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6333_: u8 = 0;
    let mut v___x_6335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6337_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_lem_6064_) == 0 {
                    v_val_6294_ = leanh::lean_ctor_get(v_lem_6064_, 0);
                    leanh::lean_inc(v_val_6294_);
                    leanh::lean_dec_ref_known(v_lem_6064_, 1);
                    v_val_6284_ = v_val_6294_;
                    state = 35;
                    continue;
                } else {
                    v_val_6295_ = leanh::lean_ctor_get(v_lem_6064_, 0);
                    leanh::lean_inc(v_val_6295_);
                    leanh::lean_dec_ref_known(v_lem_6064_, 1);
                    v___x_6296_ = l_Lean_Meta_saveState___redArg(v___y_6066_, v___y_6068_);
                    if leanh::lean_obj_tag(v___x_6296_) == 0 {
                        v_a_6297_ = leanh::lean_ctor_get(v___x_6296_, 0);
                        leanh::lean_inc(v_a_6297_);
                        leanh::lean_dec_ref_known(v___x_6296_, 1);
                        v___x_6298_ = l_Lean_Meta_mkConstWithFreshMVarLevels(
                            v_val_6295_,
                            v___y_6065_,
                            v___y_6066_,
                            v___y_6067_,
                            v___y_6068_,
                        );
                        if leanh::lean_obj_tag(v___x_6298_) == 0 {
                            leanh::lean_dec(v_a_6297_);
                            v_a_6299_ = leanh::lean_ctor_get(v___x_6298_, 0);
                            leanh::lean_inc(v_a_6299_);
                            leanh::lean_dec_ref_known(v___x_6298_, 1);
                            v_val_6284_ = v_a_6299_;
                            state = 35;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_target_6061_);
                            leanh::lean_dec(v_goal_6060_);
                            leanh::lean_dec(v_weight_6059_);
                            v_a_6300_ = leanh::lean_ctor_get(v___x_6298_, 0);
                            v_isSharedCheck_6329_ =
                                (!leanh::lean_is_exclusive(v___x_6298_)) as u8;
                            if v_isSharedCheck_6329_ == 0 {
                                v___x_6302_ = v___x_6298_;
                                v_isShared_6303_ = v_isSharedCheck_6329_;
                                state = 36;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6300_);
                                leanh::lean_dec(v___x_6298_);
                                v___x_6302_ = leanh::lean_box(0);
                                v_isShared_6303_ = v_isSharedCheck_6329_;
                                state = 36;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_val_6295_);
                        leanh::lean_dec_ref(v_target_6061_);
                        leanh::lean_dec(v_goal_6060_);
                        leanh::lean_dec(v_weight_6059_);
                        v_a_6330_ = leanh::lean_ctor_get(v___x_6296_, 0);
                        v_isSharedCheck_6337_ =
                            (!leanh::lean_is_exclusive(v___x_6296_)) as u8;
                        if v_isSharedCheck_6337_ == 0 {
                            v___x_6332_ = v___x_6296_;
                            v_isShared_6333_ = v_isSharedCheck_6337_;
                            state = 43;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6330_);
                            leanh::lean_dec(v___x_6296_);
                            v___x_6332_ = leanh::lean_box(0);
                            v_isShared_6333_ = v_isSharedCheck_6337_;
                            state = 43;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v___y_6075_ == 0 {
                    leanh::lean_dec_ref(v___y_6072_);
                    v___x_6076_ = l_Lean_Meta_SavedState_restore___redArg(
                        v___y_6071_,
                        v___y_6074_,
                        v___y_6073_,
                    );
                    leanh::lean_dec_ref(v___y_6071_);
                    if leanh::lean_obj_tag(v___x_6076_) == 0 {
                        v_isSharedCheck_6084_ =
                            (!leanh::lean_is_exclusive(v___x_6076_)) as u8;
                        if v_isSharedCheck_6084_ == 0 {
                            v_unused_6085_ = leanh::lean_ctor_get(v___x_6076_, 0);
                            leanh::lean_dec(v_unused_6085_);
                            v___x_6078_ = v___x_6076_;
                            v_isShared_6079_ = v_isSharedCheck_6084_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_6076_);
                            v___x_6078_ = leanh::lean_box(0);
                            v_isShared_6079_ = v_isSharedCheck_6084_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_6086_ = leanh::lean_ctor_get(v___x_6076_, 0);
                        v_isSharedCheck_6093_ =
                            (!leanh::lean_is_exclusive(v___x_6076_)) as u8;
                        if v_isSharedCheck_6093_ == 0 {
                            v___x_6088_ = v___x_6076_;
                            v_isShared_6089_ = v_isSharedCheck_6093_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6086_);
                            leanh::lean_dec(v___x_6076_);
                            v___x_6088_ = leanh::lean_box(0);
                            v_isShared_6089_ = v_isSharedCheck_6093_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_6071_);
                    v___x_6094_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6094_, 0, v___y_6072_);
                    return v___x_6094_;
                }
            }
            2 => {
                v___x_6080_ = leanh::lean_box(0);
                if v_isShared_6079_ == 0 {
                    leanh::lean_ctor_set(v___x_6078_, 0, v___x_6080_);
                    v___x_6082_ = v___x_6078_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6083_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6083_, 0, v___x_6080_);
                    v___x_6082_ = v_reuseFailAlloc_6083_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6082_;
            }
            4 => {
                if v_isShared_6089_ == 0 {
                    v___x_6091_ = v___x_6088_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6092_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6092_, 0, v_a_6086_);
                    v___x_6091_ = v_reuseFailAlloc_6092_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6091_;
            }
            6 => {
                v___x_6104_ = lean_st_ref_get(v___y_6097_);
                v_mctx_6105_ = leanh::lean_ctor_get(v___x_6104_, 0);
                leanh::lean_inc_ref_n(v_mctx_6105_, 2);
                leanh::lean_dec(v___x_6104_);
                v___x_6106_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(
                    v_mctx_6105_,
                    v___y_6098_,
                    v___y_6100_,
                    v___y_6097_,
                    v___y_6096_,
                    v___y_6101_,
                );
                if leanh::lean_obj_tag(v___x_6106_) == 0 {
                    v_a_6107_ = leanh::lean_ctor_get(v___x_6106_, 0);
                    v_isSharedCheck_6117_ = (!leanh::lean_is_exclusive(v___x_6106_)) as u8;
                    if v_isSharedCheck_6117_ == 0 {
                        v___x_6109_ = v___x_6106_;
                        v_isShared_6110_ = v_isSharedCheck_6117_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6107_);
                        leanh::lean_dec(v___x_6106_);
                        v___x_6109_ = leanh::lean_box(0);
                        v_isShared_6110_ = v_isSharedCheck_6117_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_mctx_6105_);
                    leanh::lean_dec_ref(v_fst_6102_);
                    leanh::lean_dec_ref(v___y_6099_);
                    leanh::lean_dec(v_weight_6059_);
                    v_a_6118_ = leanh::lean_ctor_get(v___x_6106_, 0);
                    v_isSharedCheck_6125_ = (!leanh::lean_is_exclusive(v___x_6106_)) as u8;
                    if v_isSharedCheck_6125_ == 0 {
                        v___x_6120_ = v___x_6106_;
                        v_isShared_6121_ = v_isSharedCheck_6125_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6118_);
                        leanh::lean_dec(v___x_6106_);
                        v___x_6120_ = leanh::lean_box(0);
                        v_isShared_6121_ = v_isSharedCheck_6125_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                v___x_6111_ = leanh::lean_alloc_ctor(0, 4, (2) as u32);
                leanh::lean_ctor_set(v___x_6111_, 0, v_fst_6102_);
                leanh::lean_ctor_set(v___x_6111_, 1, v_weight_6059_);
                leanh::lean_ctor_set(v___x_6111_, 2, v___y_6099_);
                leanh::lean_ctor_set(v___x_6111_, 3, v_mctx_6105_);
                leanh::lean_ctor_set_uint8(
                    v___x_6111_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v_snd_6103_,
                );
                v___x_6112_ = (leanh::lean_unbox(v_a_6107_) as u8);
                leanh::lean_dec(v_a_6107_);
                leanh::lean_ctor_set_uint8(
                    v___x_6111_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1) as u32,
                    v___x_6112_,
                );
                v___x_6113_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6113_, 0, v___x_6111_);
                if v_isShared_6110_ == 0 {
                    leanh::lean_ctor_set(v___x_6109_, 0, v___x_6113_);
                    v___x_6115_ = v___x_6109_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6116_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6116_, 0, v___x_6113_);
                    v___x_6115_ = v_reuseFailAlloc_6116_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6115_;
            }
            9 => {
                if v_isShared_6121_ == 0 {
                    v___x_6123_ = v___x_6120_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6124_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6124_, 0, v_a_6118_);
                    v___x_6123_ = v_reuseFailAlloc_6124_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6123_;
            }
            11 => {
                v___x_6135_ = l_Lean_Meta_Rewrites_rewriteResultLemma(v___y_6129_);
                if leanh::lean_obj_tag(v___x_6135_) == 1 {
                    v_val_6136_ = leanh::lean_ctor_get(v___x_6135_, 0);
                    leanh::lean_inc(v_val_6136_);
                    leanh::lean_dec_ref_known(v___x_6135_, 1);
                    v___x_6137_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_val_6136_, v___y_6132_);
                    v_a_6138_ = leanh::lean_ctor_get(v___x_6137_, 0);
                    leanh::lean_inc(v_a_6138_);
                    leanh::lean_dec_ref(v___x_6137_);
                    v___x_6139_ = l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1;
                    v___x_6140_ = leanh::lean_unsigned_to_nat(4);
                    v___x_6141_ = l_Lean_Expr_isAppOfArity(v_a_6138_, v___x_6139_, v___x_6140_);
                    if v___x_6141_ == 0 {
                        v___y_6096_ = v___y_6133_;
                        v___y_6097_ = v___y_6132_;
                        v___y_6098_ = v___y_6128_;
                        v___y_6099_ = v___y_6129_;
                        v___y_6100_ = v___y_6131_;
                        v___y_6101_ = v___y_6134_;
                        v_fst_6102_ = v_a_6138_;
                        v_snd_6103_ = v___y_6130_;
                        state = 6;
                        continue;
                    } else {
                        v___x_6142_ = leanh::lean_unsigned_to_nat(3);
                        v___x_6143_ = l_Lean_Expr_getAppNumArgs(v_a_6138_);
                        v___x_6144_ = lean_nat_sub(v___x_6143_, v___x_6142_);
                        leanh::lean_dec(v___x_6143_);
                        v___x_6145_ = leanh::lean_unsigned_to_nat(1);
                        v___x_6146_ = lean_nat_sub(v___x_6144_, v___x_6145_);
                        leanh::lean_dec(v___x_6144_);
                        v___x_6147_ = l_Lean_Expr_getRevArg_x21(v_a_6138_, v___x_6146_);
                        leanh::lean_dec(v_a_6138_);
                        v___y_6096_ = v___y_6133_;
                        v___y_6097_ = v___y_6132_;
                        v___y_6098_ = v___y_6128_;
                        v___y_6099_ = v___y_6129_;
                        v___y_6100_ = v___y_6131_;
                        v___y_6101_ = v___y_6134_;
                        v_fst_6102_ = v___x_6147_;
                        v_snd_6103_ = v___y_6127_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_6135_);
                    leanh::lean_dec_ref(v___y_6129_);
                    leanh::lean_dec_ref(v___y_6128_);
                    leanh::lean_dec(v_weight_6059_);
                    v___x_6148_ = leanh::lean_box(0);
                    v___x_6149_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6149_, 0, v___x_6148_);
                    return v___x_6149_;
                }
            }
            12 => {
                v___x_6151_ = leanh::lean_box(0);
                v___x_6152_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6152_, 0, v___x_6151_);
                return v___x_6152_;
            }
            13 => {
                if v___y_6158_ == 0 {
                    leanh::lean_dec_ref(v___y_6157_);
                    v___x_6159_ = l_Lean_Meta_SavedState_restore___redArg(
                        v___y_6154_,
                        v___y_6156_,
                        v___y_6155_,
                    );
                    leanh::lean_dec_ref(v___y_6154_);
                    if leanh::lean_obj_tag(v___x_6159_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6159_, 1);
                        state = 12;
                        continue;
                    } else {
                        v_a_6160_ = leanh::lean_ctor_get(v___x_6159_, 0);
                        v_isSharedCheck_6167_ =
                            (!leanh::lean_is_exclusive(v___x_6159_)) as u8;
                        if v_isSharedCheck_6167_ == 0 {
                            v___x_6162_ = v___x_6159_;
                            v_isShared_6163_ = v_isSharedCheck_6167_;
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6160_);
                            leanh::lean_dec(v___x_6159_);
                            v___x_6162_ = leanh::lean_box(0);
                            v_isShared_6163_ = v_isSharedCheck_6167_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_6154_);
                    v___x_6168_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6168_, 0, v___y_6157_);
                    return v___x_6168_;
                }
            }
            14 => {
                if v_isShared_6163_ == 0 {
                    v___x_6165_ = v___x_6162_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6166_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6166_, 0, v_a_6160_);
                    v___x_6165_ = v_reuseFailAlloc_6166_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6165_;
            }
            16 => {
                if v___y_6174_ == 0 {
                    leanh::lean_dec_ref(v___y_6171_);
                    v___x_6175_ = l_Lean_Meta_SavedState_restore___redArg(
                        v___y_6170_,
                        v___y_6173_,
                        v___y_6172_,
                    );
                    leanh::lean_dec_ref(v___y_6170_);
                    if leanh::lean_obj_tag(v___x_6175_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6175_, 1);
                        state = 12;
                        continue;
                    } else {
                        v_a_6176_ = leanh::lean_ctor_get(v___x_6175_, 0);
                        v_isSharedCheck_6183_ =
                            (!leanh::lean_is_exclusive(v___x_6175_)) as u8;
                        if v_isSharedCheck_6183_ == 0 {
                            v___x_6178_ = v___x_6175_;
                            v_isShared_6179_ = v_isSharedCheck_6183_;
                            state = 17;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6176_);
                            leanh::lean_dec(v___x_6175_);
                            v___x_6178_ = leanh::lean_box(0);
                            v_isShared_6179_ = v_isSharedCheck_6183_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_6170_);
                    v___x_6184_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6184_, 0, v___y_6171_);
                    return v___x_6184_;
                }
            }
            17 => {
                if v_isShared_6179_ == 0 {
                    v___x_6181_ = v___x_6178_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6182_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6182_, 0, v_a_6176_);
                    v___x_6181_ = v_reuseFailAlloc_6182_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_6181_;
            }
            19 => {
                v___x_6187_ = l_Lean_Meta_saveState___redArg(v___y_6066_, v___y_6068_);
                if leanh::lean_obj_tag(v___x_6187_) == 0 {
                    v_a_6188_ = leanh::lean_ctor_get(v___x_6187_, 0);
                    leanh::lean_inc(v_a_6188_);
                    leanh::lean_dec_ref_known(v___x_6187_, 1);
                    v___x_6189_ = 1;
                    v___x_6190_ = l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__2;
                    leanh::lean_inc_ref(v___y_6186_);
                    v___x_6191_ = l_Lean_MVarId_rewrite(
                        v_goal_6060_,
                        v_target_6061_,
                        v___y_6186_,
                        v_symm_6062_,
                        v___x_6190_,
                        v___y_6065_,
                        v___y_6066_,
                        v___y_6067_,
                        v___y_6068_,
                    );
                    if leanh::lean_obj_tag(v___x_6191_) == 0 {
                        leanh::lean_dec(v_a_6188_);
                        v_a_6192_ = leanh::lean_ctor_get(v___x_6191_, 0);
                        v_isSharedCheck_6253_ =
                            (!leanh::lean_is_exclusive(v___x_6191_)) as u8;
                        if v_isSharedCheck_6253_ == 0 {
                            v___x_6194_ = v___x_6191_;
                            v_isShared_6195_ = v_isSharedCheck_6253_;
                            state = 20;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6192_);
                            leanh::lean_dec(v___x_6191_);
                            v___x_6194_ = leanh::lean_box(0);
                            v_isShared_6195_ = v_isSharedCheck_6253_;
                            state = 20;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___y_6186_);
                        leanh::lean_dec(v_weight_6059_);
                        v_a_6254_ = leanh::lean_ctor_get(v___x_6191_, 0);
                        leanh::lean_inc(v_a_6254_);
                        leanh::lean_dec_ref_known(v___x_6191_, 1);
                        v___x_6255_ = l_Lean_Exception_isInterrupt(v_a_6254_);
                        if v___x_6255_ == 0 {
                            leanh::lean_inc(v_a_6254_);
                            v___x_6256_ = l_Lean_Exception_isRuntime(v_a_6254_);
                            v___y_6071_ = v_a_6188_;
                            v___y_6072_ = v_a_6254_;
                            v___y_6073_ = v___y_6068_;
                            v___y_6074_ = v___y_6066_;
                            v___y_6075_ = v___x_6256_;
                            state = 1;
                            continue;
                        } else {
                            v___y_6071_ = v_a_6188_;
                            v___y_6072_ = v_a_6254_;
                            v___y_6073_ = v___y_6068_;
                            v___y_6074_ = v___y_6066_;
                            v___y_6075_ = v___x_6255_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_6186_);
                    leanh::lean_dec_ref(v_target_6061_);
                    leanh::lean_dec(v_goal_6060_);
                    leanh::lean_dec(v_weight_6059_);
                    v_a_6257_ = leanh::lean_ctor_get(v___x_6187_, 0);
                    v_isSharedCheck_6264_ = (!leanh::lean_is_exclusive(v___x_6187_)) as u8;
                    if v_isSharedCheck_6264_ == 0 {
                        v___x_6259_ = v___x_6187_;
                        v_isShared_6260_ = v_isSharedCheck_6264_;
                        state = 30;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6257_);
                        leanh::lean_dec(v___x_6187_);
                        v___x_6259_ = leanh::lean_box(0);
                        v_isShared_6260_ = v_isSharedCheck_6264_;
                        state = 30;
                        continue;
                    }
                }
            }
            20 => {
                v_eNew_6196_ = leanh::lean_ctor_get(v_a_6192_, 0);
                v_mvarIds_6197_ = leanh::lean_ctor_get(v_a_6192_, 2);
                v___x_6198_ = l_List_isEmpty___redArg(v_mvarIds_6197_);
                if v___x_6198_ == 0 {
                    leanh::lean_inc_ref(v_eNew_6196_);
                    leanh::lean_del_object(v___x_6194_);
                    leanh::lean_dec_ref(v___y_6186_);
                    match v_side_6063_ {
                        0 => {
                            if v___x_6198_ == 0 {
                                leanh::lean_dec_ref(v_eNew_6196_);
                                leanh::lean_dec(v_a_6192_);
                                leanh::lean_dec(v_weight_6059_);
                                state = 12;
                                continue;
                            } else {
                                v___y_6127_ = v___x_6189_;
                                v___y_6128_ = v_eNew_6196_;
                                v___y_6129_ = v_a_6192_;
                                v___y_6130_ = v___x_6198_;
                                v___y_6131_ = v___y_6065_;
                                v___y_6132_ = v___y_6066_;
                                v___y_6133_ = v___y_6067_;
                                v___y_6134_ = v___y_6068_;
                                state = 11;
                                continue;
                            }
                        }
                        1 => {
                            v___x_6199_ = l_Lean_Meta_saveState___redArg(v___y_6066_, v___y_6068_);
                            if leanh::lean_obj_tag(v___x_6199_) == 0 {
                                v_a_6200_ = leanh::lean_ctor_get(v___x_6199_, 0);
                                leanh::lean_inc(v_a_6200_);
                                leanh::lean_dec_ref_known(v___x_6199_, 1);
                                v___x_6201_ = leanh::lean_box(0);
                                leanh::lean_inc(v_mvarIds_6197_);
                                v___x_6202_ =
                                    l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(
                                        v_mvarIds_6197_,
                                        v___x_6201_,
                                        v___y_6065_,
                                        v___y_6066_,
                                        v___y_6067_,
                                        v___y_6068_,
                                    );
                                if leanh::lean_obj_tag(v___x_6202_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_6202_, 1);
                                    leanh::lean_dec(v_a_6200_);
                                    v___y_6127_ = v___x_6189_;
                                    v___y_6128_ = v_eNew_6196_;
                                    v___y_6129_ = v_a_6192_;
                                    v___y_6130_ = v___x_6198_;
                                    v___y_6131_ = v___y_6065_;
                                    v___y_6132_ = v___y_6066_;
                                    v___y_6133_ = v___y_6067_;
                                    v___y_6134_ = v___y_6068_;
                                    state = 11;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v_eNew_6196_);
                                    leanh::lean_dec(v_a_6192_);
                                    leanh::lean_dec(v_weight_6059_);
                                    v_a_6203_ = leanh::lean_ctor_get(v___x_6202_, 0);
                                    leanh::lean_inc(v_a_6203_);
                                    leanh::lean_dec_ref_known(v___x_6202_, 1);
                                    v___x_6204_ = l_Lean_Exception_isInterrupt(v_a_6203_);
                                    if v___x_6204_ == 0 {
                                        leanh::lean_inc(v_a_6203_);
                                        v___x_6205_ = l_Lean_Exception_isRuntime(v_a_6203_);
                                        v___y_6170_ = v_a_6200_;
                                        v___y_6171_ = v_a_6203_;
                                        v___y_6172_ = v___y_6068_;
                                        v___y_6173_ = v___y_6066_;
                                        v___y_6174_ = v___x_6205_;
                                        state = 16;
                                        continue;
                                    } else {
                                        v___y_6170_ = v_a_6200_;
                                        v___y_6171_ = v_a_6203_;
                                        v___y_6172_ = v___y_6068_;
                                        v___y_6173_ = v___y_6066_;
                                        v___y_6174_ = v___x_6204_;
                                        state = 16;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_eNew_6196_);
                                leanh::lean_dec(v_a_6192_);
                                leanh::lean_dec(v_weight_6059_);
                                v_a_6206_ = leanh::lean_ctor_get(v___x_6199_, 0);
                                v_isSharedCheck_6213_ =
                                    (!leanh::lean_is_exclusive(v___x_6199_)) as u8;
                                if v_isSharedCheck_6213_ == 0 {
                                    v___x_6208_ = v___x_6199_;
                                    v_isShared_6209_ = v_isSharedCheck_6213_;
                                    state = 21;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6206_);
                                    leanh::lean_dec(v___x_6199_);
                                    v___x_6208_ = leanh::lean_box(0);
                                    v_isShared_6209_ = v_isSharedCheck_6213_;
                                    state = 21;
                                    continue;
                                }
                            }
                        }
                        _ => {
                            v___x_6214_ = l_Lean_Meta_saveState___redArg(v___y_6066_, v___y_6068_);
                            if leanh::lean_obj_tag(v___x_6214_) == 0 {
                                v_a_6215_ = leanh::lean_ctor_get(v___x_6214_, 0);
                                leanh::lean_inc(v_a_6215_);
                                leanh::lean_dec_ref_known(v___x_6214_, 1);
                                v___x_6216_ = leanh::lean_unsigned_to_nat(6);
                                leanh::lean_inc(v_mvarIds_6197_);
                                v___x_6217_ = l_Lean_Meta_Rewrites_solveByElim(
                                    v_mvarIds_6197_,
                                    v___x_6216_,
                                    v___y_6065_,
                                    v___y_6066_,
                                    v___y_6067_,
                                    v___y_6068_,
                                );
                                if leanh::lean_obj_tag(v___x_6217_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_6217_, 1);
                                    leanh::lean_dec(v_a_6215_);
                                    v___y_6127_ = v___x_6189_;
                                    v___y_6128_ = v_eNew_6196_;
                                    v___y_6129_ = v_a_6192_;
                                    v___y_6130_ = v___x_6198_;
                                    v___y_6131_ = v___y_6065_;
                                    v___y_6132_ = v___y_6066_;
                                    v___y_6133_ = v___y_6067_;
                                    v___y_6134_ = v___y_6068_;
                                    state = 11;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v_eNew_6196_);
                                    leanh::lean_dec(v_a_6192_);
                                    leanh::lean_dec(v_weight_6059_);
                                    v_a_6218_ = leanh::lean_ctor_get(v___x_6217_, 0);
                                    leanh::lean_inc(v_a_6218_);
                                    leanh::lean_dec_ref_known(v___x_6217_, 1);
                                    v___x_6219_ = l_Lean_Exception_isInterrupt(v_a_6218_);
                                    if v___x_6219_ == 0 {
                                        leanh::lean_inc(v_a_6218_);
                                        v___x_6220_ = l_Lean_Exception_isRuntime(v_a_6218_);
                                        v___y_6154_ = v_a_6215_;
                                        v___y_6155_ = v___y_6068_;
                                        v___y_6156_ = v___y_6066_;
                                        v___y_6157_ = v_a_6218_;
                                        v___y_6158_ = v___x_6220_;
                                        state = 13;
                                        continue;
                                    } else {
                                        v___y_6154_ = v_a_6215_;
                                        v___y_6155_ = v___y_6068_;
                                        v___y_6156_ = v___y_6066_;
                                        v___y_6157_ = v_a_6218_;
                                        v___y_6158_ = v___x_6219_;
                                        state = 13;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_eNew_6196_);
                                leanh::lean_dec(v_a_6192_);
                                leanh::lean_dec(v_weight_6059_);
                                v_a_6221_ = leanh::lean_ctor_get(v___x_6214_, 0);
                                v_isSharedCheck_6228_ =
                                    (!leanh::lean_is_exclusive(v___x_6214_)) as u8;
                                if v_isSharedCheck_6228_ == 0 {
                                    v___x_6223_ = v___x_6214_;
                                    v_isShared_6224_ = v_isSharedCheck_6228_;
                                    state = 23;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6221_);
                                    leanh::lean_dec(v___x_6214_);
                                    v___x_6223_ = leanh::lean_box(0);
                                    v_isShared_6224_ = v_isSharedCheck_6228_;
                                    state = 23;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    v___x_6229_ = lean_st_ref_get(v___y_6066_);
                    v_mctx_6230_ = leanh::lean_ctor_get(v___x_6229_, 0);
                    leanh::lean_inc_ref_n(v_mctx_6230_, 2);
                    leanh::lean_dec(v___x_6229_);
                    leanh::lean_inc_ref(v_eNew_6196_);
                    v___x_6231_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(
                        v_mctx_6230_,
                        v_eNew_6196_,
                        v___y_6065_,
                        v___y_6066_,
                        v___y_6067_,
                        v___y_6068_,
                    );
                    if leanh::lean_obj_tag(v___x_6231_) == 0 {
                        v_a_6232_ = leanh::lean_ctor_get(v___x_6231_, 0);
                        v_isSharedCheck_6244_ =
                            (!leanh::lean_is_exclusive(v___x_6231_)) as u8;
                        if v_isSharedCheck_6244_ == 0 {
                            v___x_6234_ = v___x_6231_;
                            v_isShared_6235_ = v_isSharedCheck_6244_;
                            state = 25;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6232_);
                            leanh::lean_dec(v___x_6231_);
                            v___x_6234_ = leanh::lean_box(0);
                            v_isShared_6235_ = v_isSharedCheck_6244_;
                            state = 25;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_mctx_6230_);
                        leanh::lean_del_object(v___x_6194_);
                        leanh::lean_dec(v_a_6192_);
                        leanh::lean_dec_ref(v___y_6186_);
                        leanh::lean_dec(v_weight_6059_);
                        v_a_6245_ = leanh::lean_ctor_get(v___x_6231_, 0);
                        v_isSharedCheck_6252_ =
                            (!leanh::lean_is_exclusive(v___x_6231_)) as u8;
                        if v_isSharedCheck_6252_ == 0 {
                            v___x_6247_ = v___x_6231_;
                            v_isShared_6248_ = v_isSharedCheck_6252_;
                            state = 28;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6245_);
                            leanh::lean_dec(v___x_6231_);
                            v___x_6247_ = leanh::lean_box(0);
                            v_isShared_6248_ = v_isSharedCheck_6252_;
                            state = 28;
                            continue;
                        }
                    }
                }
            }
            21 => {
                if v_isShared_6209_ == 0 {
                    v___x_6211_ = v___x_6208_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_6212_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6212_, 0, v_a_6206_);
                    v___x_6211_ = v_reuseFailAlloc_6212_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_6211_;
            }
            23 => {
                if v_isShared_6224_ == 0 {
                    v___x_6226_ = v___x_6223_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_6227_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6227_, 0, v_a_6221_);
                    v___x_6226_ = v_reuseFailAlloc_6227_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_6226_;
            }
            25 => {
                v___x_6236_ = leanh::lean_alloc_ctor(0, 4, (2) as u32);
                leanh::lean_ctor_set(v___x_6236_, 0, v___y_6186_);
                leanh::lean_ctor_set(v___x_6236_, 1, v_weight_6059_);
                leanh::lean_ctor_set(v___x_6236_, 2, v_a_6192_);
                leanh::lean_ctor_set(v___x_6236_, 3, v_mctx_6230_);
                leanh::lean_ctor_set_uint8(
                    v___x_6236_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v_symm_6062_,
                );
                v___x_6237_ = (leanh::lean_unbox(v_a_6232_) as u8);
                leanh::lean_dec(v_a_6232_);
                leanh::lean_ctor_set_uint8(
                    v___x_6236_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1) as u32,
                    v___x_6237_,
                );
                if v_isShared_6195_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6194_, 1);
                    leanh::lean_ctor_set(v___x_6194_, 0, v___x_6236_);
                    v___x_6239_ = v___x_6194_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_6243_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6243_, 0, v___x_6236_);
                    v___x_6239_ = v_reuseFailAlloc_6243_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                if v_isShared_6235_ == 0 {
                    leanh::lean_ctor_set(v___x_6234_, 0, v___x_6239_);
                    v___x_6241_ = v___x_6234_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_6242_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6242_, 0, v___x_6239_);
                    v___x_6241_ = v_reuseFailAlloc_6242_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_6241_;
            }
            28 => {
                if v_isShared_6248_ == 0 {
                    v___x_6250_ = v___x_6247_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_6251_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6251_, 0, v_a_6245_);
                    v___x_6250_ = v_reuseFailAlloc_6251_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_6250_;
            }
            30 => {
                if v_isShared_6260_ == 0 {
                    v___x_6262_ = v___x_6259_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_6263_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6263_, 0, v_a_6257_);
                    v___x_6262_ = v_reuseFailAlloc_6263_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_6262_;
            }
            32 => {
                leanh::lean_inc_ref(v___y_6269_);
                v___x_6270_ = l_Lean_stringToMessageData(v___y_6269_);
                leanh::lean_inc_ref(v___y_6266_);
                v___x_6271_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6271_, 0, v___y_6266_);
                leanh::lean_ctor_set(v___x_6271_, 1, v___x_6270_);
                leanh::lean_inc_ref(v___y_6268_);
                v___x_6272_ = l_Lean_MessageData_ofExpr(v___y_6268_);
                v___x_6273_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6273_, 0, v___x_6271_);
                leanh::lean_ctor_set(v___x_6273_, 1, v___x_6272_);
                leanh::lean_inc(v___y_6267_);
                v___x_6274_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(
                    v___y_6267_,
                    v___x_6273_,
                    v___y_6065_,
                    v___y_6066_,
                    v___y_6067_,
                    v___y_6068_,
                );
                if leanh::lean_obj_tag(v___x_6274_) == 0 {
                    leanh::lean_dec_ref_known(v___x_6274_, 1);
                    v___y_6186_ = v___y_6268_;
                    state = 19;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_6268_);
                    leanh::lean_dec_ref(v_target_6061_);
                    leanh::lean_dec(v_goal_6060_);
                    leanh::lean_dec(v_weight_6059_);
                    v_a_6275_ = leanh::lean_ctor_get(v___x_6274_, 0);
                    v_isSharedCheck_6282_ = (!leanh::lean_is_exclusive(v___x_6274_)) as u8;
                    if v_isSharedCheck_6282_ == 0 {
                        v___x_6277_ = v___x_6274_;
                        v_isShared_6278_ = v_isSharedCheck_6282_;
                        state = 33;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6275_);
                        leanh::lean_dec(v___x_6274_);
                        v___x_6277_ = leanh::lean_box(0);
                        v_isShared_6278_ = v_isSharedCheck_6282_;
                        state = 33;
                        continue;
                    }
                }
            }
            33 => {
                if v_isShared_6278_ == 0 {
                    v___x_6280_ = v___x_6277_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_6281_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6281_, 0, v_a_6275_);
                    v___x_6280_ = v_reuseFailAlloc_6281_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_6280_;
            }
            35 => {
                v_options_6285_ = leanh::lean_ctor_get(v___y_6067_, 2);
                v_hasTrace_6286_ = leanh::lean_ctor_get_uint8(
                    v_options_6285_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_6286_ == 0 {
                    v___y_6186_ = v_val_6284_;
                    state = 19;
                    continue;
                } else {
                    v_inheritedTraceOptions_6287_ = leanh::lean_ctor_get(v___y_6067_, 13);
                    v___x_6288_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
                    v___x_6289_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5_once
                        ),
                        _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5,
                    );
                    v___x_6290_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_6287_,
                        v_options_6285_,
                        v___x_6289_,
                    );
                    if v___x_6290_ == 0 {
                        v___y_6186_ = v_val_6284_;
                        state = 19;
                        continue;
                    } else {
                        v___x_6291_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7_once
                            ),
                            _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7,
                        );
                        if v_symm_6062_ == 0 {
                            v___x_6292_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__1;
                            v___y_6266_ = v___x_6291_;
                            v___y_6267_ = v___x_6288_;
                            v___y_6268_ = v_val_6284_;
                            v___y_6269_ = v___x_6292_;
                            state = 32;
                            continue;
                        } else {
                            v___x_6293_ = l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__8;
                            v___y_6266_ = v___x_6291_;
                            v___y_6267_ = v___x_6288_;
                            v___y_6268_ = v_val_6284_;
                            v___y_6269_ = v___x_6293_;
                            state = 32;
                            continue;
                        }
                    }
                }
            }
            36 => {
                v___x_6327_ = l_Lean_Exception_isInterrupt(v_a_6300_);
                if v___x_6327_ == 0 {
                    leanh::lean_inc(v_a_6300_);
                    v___x_6328_ = l_Lean_Exception_isRuntime(v_a_6300_);
                    v___y_6305_ = v___x_6328_;
                    state = 37;
                    continue;
                } else {
                    v___y_6305_ = v___x_6327_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v___y_6305_ == 0 {
                    leanh::lean_del_object(v___x_6302_);
                    leanh::lean_dec(v_a_6300_);
                    v___x_6306_ = l_Lean_Meta_SavedState_restore___redArg(
                        v_a_6297_,
                        v___y_6066_,
                        v___y_6068_,
                    );
                    leanh::lean_dec(v_a_6297_);
                    if leanh::lean_obj_tag(v___x_6306_) == 0 {
                        v_isSharedCheck_6314_ =
                            (!leanh::lean_is_exclusive(v___x_6306_)) as u8;
                        if v_isSharedCheck_6314_ == 0 {
                            v_unused_6315_ = leanh::lean_ctor_get(v___x_6306_, 0);
                            leanh::lean_dec(v_unused_6315_);
                            v___x_6308_ = v___x_6306_;
                            v_isShared_6309_ = v_isSharedCheck_6314_;
                            state = 38;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_6306_);
                            v___x_6308_ = leanh::lean_box(0);
                            v_isShared_6309_ = v_isSharedCheck_6314_;
                            state = 38;
                            continue;
                        }
                    } else {
                        v_a_6316_ = leanh::lean_ctor_get(v___x_6306_, 0);
                        v_isSharedCheck_6323_ =
                            (!leanh::lean_is_exclusive(v___x_6306_)) as u8;
                        if v_isSharedCheck_6323_ == 0 {
                            v___x_6318_ = v___x_6306_;
                            v_isShared_6319_ = v_isSharedCheck_6323_;
                            state = 40;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6316_);
                            leanh::lean_dec(v___x_6306_);
                            v___x_6318_ = leanh::lean_box(0);
                            v_isShared_6319_ = v_isSharedCheck_6323_;
                            state = 40;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_6297_);
                    if v_isShared_6303_ == 0 {
                        v___x_6325_ = v___x_6302_;
                        state = 42;
                        continue;
                    } else {
                        v_reuseFailAlloc_6326_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6326_, 0, v_a_6300_);
                        v___x_6325_ = v_reuseFailAlloc_6326_;
                        state = 42;
                        continue;
                    }
                }
            }
            38 => {
                v___x_6310_ = leanh::lean_box(0);
                if v_isShared_6309_ == 0 {
                    leanh::lean_ctor_set(v___x_6308_, 0, v___x_6310_);
                    v___x_6312_ = v___x_6308_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_6313_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6313_, 0, v___x_6310_);
                    v___x_6312_ = v_reuseFailAlloc_6313_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_6312_;
            }
            40 => {
                if v_isShared_6319_ == 0 {
                    v___x_6321_ = v___x_6318_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_6322_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6322_, 0, v_a_6316_);
                    v___x_6321_ = v_reuseFailAlloc_6322_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_6321_;
            }
            42 => {
                return v___x_6325_;
            }
            43 => {
                if v_isShared_6333_ == 0 {
                    v___x_6335_ = v___x_6332_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_6336_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6336_, 0, v_a_6330_);
                    v___x_6335_ = v_reuseFailAlloc_6336_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_6335_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed(
    mut v_weight_6338_: *mut leanh::LeanObject,
    mut v_goal_6339_: *mut leanh::LeanObject,
    mut v_target_6340_: *mut leanh::LeanObject,
    mut v_symm_6341_: *mut leanh::LeanObject,
    mut v_side_6342_: *mut leanh::LeanObject,
    mut v_lem_6343_: *mut leanh::LeanObject,
    mut v___y_6344_: *mut leanh::LeanObject,
    mut v___y_6345_: *mut leanh::LeanObject,
    mut v___y_6346_: *mut leanh::LeanObject,
    mut v___y_6347_: *mut leanh::LeanObject,
    mut v___y_6348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_symm_boxed_6349_: u8 = 0;
    let mut v_side_boxed_6350_: u8 = 0;
    let mut v_res_6351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_symm_boxed_6349_ = (leanh::lean_unbox(v_symm_6341_) as u8);
    v_side_boxed_6350_ = (leanh::lean_unbox(v_side_6342_) as u8);
    v_res_6351_ = l_Lean_Meta_Rewrites_rwLemma___lam__0(
        v_weight_6338_,
        v_goal_6339_,
        v_target_6340_,
        v_symm_boxed_6349_,
        v_side_boxed_6350_,
        v_lem_6343_,
        v___y_6344_,
        v___y_6345_,
        v___y_6346_,
        v___y_6347_,
    );
    leanh::lean_dec(v___y_6347_);
    leanh::lean_dec_ref(v___y_6346_);
    leanh::lean_dec(v___y_6345_);
    leanh::lean_dec_ref(v___y_6344_);
    return v_res_6351_;
}
pub unsafe fn l_Lean_Meta_Rewrites_rwLemma(
    mut v_ctx_6352_: *mut leanh::LeanObject,
    mut v_goal_6353_: *mut leanh::LeanObject,
    mut v_target_6354_: *mut leanh::LeanObject,
    mut v_side_6355_: u8,
    mut v_lem_6356_: *mut leanh::LeanObject,
    mut v_symm_6357_: u8,
    mut v_weight_6358_: *mut leanh::LeanObject,
    mut v_a_6359_: *mut leanh::LeanObject,
    mut v_a_6360_: *mut leanh::LeanObject,
    mut v_a_6361_: *mut leanh::LeanObject,
    mut v_a_6362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6364_ = leanh::lean_box((v_symm_6357_) as usize);
    v___x_6365_ = leanh::lean_box((v_side_6355_) as usize);
    v___f_6366_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    leanh::lean_closure_set(v___f_6366_, 0, v_weight_6358_);
    leanh::lean_closure_set(v___f_6366_, 1, v_goal_6353_);
    leanh::lean_closure_set(v___f_6366_, 2, v_target_6354_);
    leanh::lean_closure_set(v___f_6366_, 3, v___x_6364_);
    leanh::lean_closure_set(v___f_6366_, 4, v___x_6365_);
    leanh::lean_closure_set(v___f_6366_, 5, v_lem_6356_);
    v___x_6367_ =
        l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(
            v_ctx_6352_,
            v___f_6366_,
            v_a_6359_,
            v_a_6360_,
            v_a_6361_,
            v_a_6362_,
        );
    return v___x_6367_;
}
pub unsafe fn l_Lean_Meta_Rewrites_rwLemma___boxed(
    mut v_ctx_6368_: *mut leanh::LeanObject,
    mut v_goal_6369_: *mut leanh::LeanObject,
    mut v_target_6370_: *mut leanh::LeanObject,
    mut v_side_6371_: *mut leanh::LeanObject,
    mut v_lem_6372_: *mut leanh::LeanObject,
    mut v_symm_6373_: *mut leanh::LeanObject,
    mut v_weight_6374_: *mut leanh::LeanObject,
    mut v_a_6375_: *mut leanh::LeanObject,
    mut v_a_6376_: *mut leanh::LeanObject,
    mut v_a_6377_: *mut leanh::LeanObject,
    mut v_a_6378_: *mut leanh::LeanObject,
    mut v_a_6379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_side_boxed_6380_: u8 = 0;
    let mut v_symm_boxed_6381_: u8 = 0;
    let mut v_res_6382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_side_boxed_6380_ = (leanh::lean_unbox(v_side_6371_) as u8);
    v_symm_boxed_6381_ = (leanh::lean_unbox(v_symm_6373_) as u8);
    v_res_6382_ = l_Lean_Meta_Rewrites_rwLemma(
        v_ctx_6368_,
        v_goal_6369_,
        v_target_6370_,
        v_side_boxed_6380_,
        v_lem_6372_,
        v_symm_boxed_6381_,
        v_weight_6374_,
        v_a_6375_,
        v_a_6376_,
        v_a_6377_,
        v_a_6378_,
    );
    leanh::lean_dec(v_a_6378_);
    leanh::lean_dec_ref(v_a_6377_);
    leanh::lean_dec(v_a_6376_);
    leanh::lean_dec_ref(v_a_6375_);
    return v_res_6382_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(
    mut v_type_6383_: *mut leanh::LeanObject,
    mut v_k_6384_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_6385_: u8,
    mut v___y_6386_: *mut leanh::LeanObject,
    mut v___y_6387_: *mut leanh::LeanObject,
    mut v___y_6388_: *mut leanh::LeanObject,
    mut v___y_6389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6392_: u8 = 0;
    let mut v___x_6393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6398_: u8 = 0;
    let mut v___x_6400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6402_: u8 = 0;
    let mut v_a_6403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6406_: u8 = 0;
    let mut v___x_6408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6410_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_6391_ = leanh::lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_6391_, 0, v_k_6384_);
                v___x_6392_ = 0;
                v___x_6393_ = leanh::lean_box(0);
                v___x_6394_ =
                    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                        leanh::lean_box(0),
                        v___x_6392_,
                        v___x_6393_,
                        v_type_6383_,
                        v___f_6391_,
                        v_cleanupAnnotations_6385_,
                        v___x_6392_,
                        v___y_6386_,
                        v___y_6387_,
                        v___y_6388_,
                        v___y_6389_,
                    );
                if leanh::lean_obj_tag(v___x_6394_) == 0 {
                    v_a_6395_ = leanh::lean_ctor_get(v___x_6394_, 0);
                    v_isSharedCheck_6402_ = (!leanh::lean_is_exclusive(v___x_6394_)) as u8;
                    if v_isSharedCheck_6402_ == 0 {
                        v___x_6397_ = v___x_6394_;
                        v_isShared_6398_ = v_isSharedCheck_6402_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6395_);
                        leanh::lean_dec(v___x_6394_);
                        v___x_6397_ = leanh::lean_box(0);
                        v_isShared_6398_ = v_isSharedCheck_6402_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6403_ = leanh::lean_ctor_get(v___x_6394_, 0);
                    v_isSharedCheck_6410_ = (!leanh::lean_is_exclusive(v___x_6394_)) as u8;
                    if v_isSharedCheck_6410_ == 0 {
                        v___x_6405_ = v___x_6394_;
                        v_isShared_6406_ = v_isSharedCheck_6410_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6403_);
                        leanh::lean_dec(v___x_6394_);
                        v___x_6405_ = leanh::lean_box(0);
                        v_isShared_6406_ = v_isSharedCheck_6410_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6398_ == 0 {
                    v___x_6400_ = v___x_6397_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6401_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6401_, 0, v_a_6395_);
                    v___x_6400_ = v_reuseFailAlloc_6401_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6400_;
            }
            3 => {
                if v_isShared_6406_ == 0 {
                    v___x_6408_ = v___x_6405_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6409_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6409_, 0, v_a_6403_);
                    v___x_6408_ = v_reuseFailAlloc_6409_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6408_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg___boxed(
    mut v_type_6411_: *mut leanh::LeanObject,
    mut v_k_6412_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_6413_: *mut leanh::LeanObject,
    mut v___y_6414_: *mut leanh::LeanObject,
    mut v___y_6415_: *mut leanh::LeanObject,
    mut v___y_6416_: *mut leanh::LeanObject,
    mut v___y_6417_: *mut leanh::LeanObject,
    mut v___y_6418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_6419_: u8 = 0;
    let mut v_res_6420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_6419_ = (leanh::lean_unbox(v_cleanupAnnotations_6413_) as u8);
    v_res_6420_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_type_6411_, v_k_6412_, v_cleanupAnnotations_boxed_6419_, v___y_6414_, v___y_6415_, v___y_6416_, v___y_6417_);
    leanh::lean_dec(v___y_6417_);
    leanh::lean_dec_ref(v___y_6416_);
    leanh::lean_dec(v___y_6415_);
    leanh::lean_dec_ref(v___y_6414_);
    return v_res_6420_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(
    mut v_00_u03b1_6421_: *mut leanh::LeanObject,
    mut v_type_6422_: *mut leanh::LeanObject,
    mut v_k_6423_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_6424_: u8,
    mut v___y_6425_: *mut leanh::LeanObject,
    mut v___y_6426_: *mut leanh::LeanObject,
    mut v___y_6427_: *mut leanh::LeanObject,
    mut v___y_6428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6430_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_type_6422_, v_k_6423_, v_cleanupAnnotations_6424_, v___y_6425_, v___y_6426_, v___y_6427_, v___y_6428_);
    return v___x_6430_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___boxed(
    mut v_00_u03b1_6431_: *mut leanh::LeanObject,
    mut v_type_6432_: *mut leanh::LeanObject,
    mut v_k_6433_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_6434_: *mut leanh::LeanObject,
    mut v___y_6435_: *mut leanh::LeanObject,
    mut v___y_6436_: *mut leanh::LeanObject,
    mut v___y_6437_: *mut leanh::LeanObject,
    mut v___y_6438_: *mut leanh::LeanObject,
    mut v___y_6439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_6440_: u8 = 0;
    let mut v_res_6441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_6440_ = (leanh::lean_unbox(v_cleanupAnnotations_6434_) as u8);
    v_res_6441_ =
        l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(
            v_00_u03b1_6431_,
            v_type_6432_,
            v_k_6433_,
            v_cleanupAnnotations_boxed_6440_,
            v___y_6435_,
            v___y_6436_,
            v___y_6437_,
            v___y_6438_,
        );
    leanh::lean_dec(v___y_6438_);
    leanh::lean_dec_ref(v___y_6437_);
    leanh::lean_dec(v___y_6436_);
    leanh::lean_dec_ref(v___y_6435_);
    return v_res_6441_;
}
pub unsafe fn l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(
    mut v_e_6442_: *mut leanh::LeanObject,
    mut v_k_6443_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_6444_: u8,
    mut v_preserveNondepLet_6445_: u8,
    mut v___y_6446_: *mut leanh::LeanObject,
    mut v___y_6447_: *mut leanh::LeanObject,
    mut v___y_6448_: *mut leanh::LeanObject,
    mut v___y_6449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6452_: u8 = 0;
    let mut v___x_6453_: u8 = 0;
    let mut v___x_6454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6459_: u8 = 0;
    let mut v___x_6461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6463_: u8 = 0;
    let mut v_a_6464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6467_: u8 = 0;
    let mut v___x_6469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6471_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_6451_ = leanh::lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_6451_, 0, v_k_6443_);
                v___x_6452_ = 1;
                v___x_6453_ = 0;
                v___x_6454_ = leanh::lean_box(0);
                v___x_6455_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(
                    leanh::lean_box(0),
                    v_e_6442_,
                    v___x_6452_,
                    v___x_6452_,
                    v_preserveNondepLet_6445_,
                    v___x_6453_,
                    v___x_6454_,
                    v___f_6451_,
                    v_cleanupAnnotations_6444_,
                    v___y_6446_,
                    v___y_6447_,
                    v___y_6448_,
                    v___y_6449_,
                );
                if leanh::lean_obj_tag(v___x_6455_) == 0 {
                    v_a_6456_ = leanh::lean_ctor_get(v___x_6455_, 0);
                    v_isSharedCheck_6463_ = (!leanh::lean_is_exclusive(v___x_6455_)) as u8;
                    if v_isSharedCheck_6463_ == 0 {
                        v___x_6458_ = v___x_6455_;
                        v_isShared_6459_ = v_isSharedCheck_6463_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6456_);
                        leanh::lean_dec(v___x_6455_);
                        v___x_6458_ = leanh::lean_box(0);
                        v_isShared_6459_ = v_isSharedCheck_6463_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6464_ = leanh::lean_ctor_get(v___x_6455_, 0);
                    v_isSharedCheck_6471_ = (!leanh::lean_is_exclusive(v___x_6455_)) as u8;
                    if v_isSharedCheck_6471_ == 0 {
                        v___x_6466_ = v___x_6455_;
                        v_isShared_6467_ = v_isSharedCheck_6471_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6464_);
                        leanh::lean_dec(v___x_6455_);
                        v___x_6466_ = leanh::lean_box(0);
                        v_isShared_6467_ = v_isSharedCheck_6471_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6459_ == 0 {
                    v___x_6461_ = v___x_6458_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6462_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6462_, 0, v_a_6456_);
                    v___x_6461_ = v_reuseFailAlloc_6462_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6461_;
            }
            3 => {
                if v_isShared_6467_ == 0 {
                    v___x_6469_ = v___x_6466_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6470_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6470_, 0, v_a_6464_);
                    v___x_6469_ = v_reuseFailAlloc_6470_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6469_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg___boxed(
    mut v_e_6472_: *mut leanh::LeanObject,
    mut v_k_6473_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_6474_: *mut leanh::LeanObject,
    mut v_preserveNondepLet_6475_: *mut leanh::LeanObject,
    mut v___y_6476_: *mut leanh::LeanObject,
    mut v___y_6477_: *mut leanh::LeanObject,
    mut v___y_6478_: *mut leanh::LeanObject,
    mut v___y_6479_: *mut leanh::LeanObject,
    mut v___y_6480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_6481_: u8 = 0;
    let mut v_preserveNondepLet_boxed_6482_: u8 = 0;
    let mut v_res_6483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_6481_ = (leanh::lean_unbox(v_cleanupAnnotations_6474_) as u8);
    v_preserveNondepLet_boxed_6482_ = (leanh::lean_unbox(v_preserveNondepLet_6475_) as u8);
    v_res_6483_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_6472_, v_k_6473_, v_cleanupAnnotations_boxed_6481_, v_preserveNondepLet_boxed_6482_, v___y_6476_, v___y_6477_, v___y_6478_, v___y_6479_);
    leanh::lean_dec(v___y_6479_);
    leanh::lean_dec_ref(v___y_6478_);
    leanh::lean_dec(v___y_6477_);
    leanh::lean_dec_ref(v___y_6476_);
    return v_res_6483_;
}
pub unsafe fn l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2(
    mut v_00_u03b1_6484_: *mut leanh::LeanObject,
    mut v_e_6485_: *mut leanh::LeanObject,
    mut v_k_6486_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_6487_: u8,
    mut v_preserveNondepLet_6488_: u8,
    mut v___y_6489_: *mut leanh::LeanObject,
    mut v___y_6490_: *mut leanh::LeanObject,
    mut v___y_6491_: *mut leanh::LeanObject,
    mut v___y_6492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6494_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_6485_, v_k_6486_, v_cleanupAnnotations_6487_, v_preserveNondepLet_6488_, v___y_6489_, v___y_6490_, v___y_6491_, v___y_6492_);
    return v___x_6494_;
}
pub unsafe fn l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___boxed(
    mut v_00_u03b1_6495_: *mut leanh::LeanObject,
    mut v_e_6496_: *mut leanh::LeanObject,
    mut v_k_6497_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_6498_: *mut leanh::LeanObject,
    mut v_preserveNondepLet_6499_: *mut leanh::LeanObject,
    mut v___y_6500_: *mut leanh::LeanObject,
    mut v___y_6501_: *mut leanh::LeanObject,
    mut v___y_6502_: *mut leanh::LeanObject,
    mut v___y_6503_: *mut leanh::LeanObject,
    mut v___y_6504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_6505_: u8 = 0;
    let mut v_preserveNondepLet_boxed_6506_: u8 = 0;
    let mut v_res_6507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_6505_ = (leanh::lean_unbox(v_cleanupAnnotations_6498_) as u8);
    v_preserveNondepLet_boxed_6506_ = (leanh::lean_unbox(v_preserveNondepLet_6499_) as u8);
    v_res_6507_ =
        l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2(
            v_00_u03b1_6495_,
            v_e_6496_,
            v_k_6497_,
            v_cleanupAnnotations_boxed_6505_,
            v_preserveNondepLet_boxed_6506_,
            v___y_6500_,
            v___y_6501_,
            v___y_6502_,
            v___y_6503_,
        );
    leanh::lean_dec(v___y_6503_);
    leanh::lean_dec_ref(v___y_6502_);
    leanh::lean_dec(v___y_6501_);
    leanh::lean_dec_ref(v___y_6500_);
    return v_res_6507_;
}
pub unsafe fn l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(
    mut v_f_6508_: *mut leanh::LeanObject,
    mut v_e_x27_6509_: *mut leanh::LeanObject,
    mut v_a_6510_: *mut leanh::LeanObject,
    mut v___y_6511_: *mut leanh::LeanObject,
    mut v___y_6512_: *mut leanh::LeanObject,
    mut v___y_6513_: *mut leanh::LeanObject,
    mut v___y_6514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6520_: u8 = 0;
    let mut v___x_6521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6525_: u8 = 0;
    let mut v_a_6526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6529_: u8 = 0;
    let mut v___x_6531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6533_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_6514_);
                leanh::lean_inc_ref(v___y_6513_);
                leanh::lean_inc(v___y_6512_);
                leanh::lean_inc_ref(v___y_6511_);
                leanh::lean_inc_ref(v_e_x27_6509_);
                v___x_6516_ = leanh::lean_apply_7(
                    v_f_6508_,
                    v_a_6510_,
                    v_e_x27_6509_,
                    v___y_6511_,
                    v___y_6512_,
                    v___y_6513_,
                    v___y_6514_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_6516_) == 0 {
                    v_a_6517_ = leanh::lean_ctor_get(v___x_6516_, 0);
                    v_isSharedCheck_6525_ = (!leanh::lean_is_exclusive(v___x_6516_)) as u8;
                    if v_isSharedCheck_6525_ == 0 {
                        v___x_6519_ = v___x_6516_;
                        v_isShared_6520_ = v_isSharedCheck_6525_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6517_);
                        leanh::lean_dec(v___x_6516_);
                        v___x_6519_ = leanh::lean_box(0);
                        v_isShared_6520_ = v_isSharedCheck_6525_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_x27_6509_);
                    v_a_6526_ = leanh::lean_ctor_get(v___x_6516_, 0);
                    v_isSharedCheck_6533_ = (!leanh::lean_is_exclusive(v___x_6516_)) as u8;
                    if v_isSharedCheck_6533_ == 0 {
                        v___x_6528_ = v___x_6516_;
                        v_isShared_6529_ = v_isSharedCheck_6533_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6526_);
                        leanh::lean_dec(v___x_6516_);
                        v___x_6528_ = leanh::lean_box(0);
                        v_isShared_6529_ = v_isSharedCheck_6533_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6521_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6521_, 0, v_e_x27_6509_);
                leanh::lean_ctor_set(v___x_6521_, 1, v_a_6517_);
                if v_isShared_6520_ == 0 {
                    leanh::lean_ctor_set(v___x_6519_, 0, v___x_6521_);
                    v___x_6523_ = v___x_6519_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6524_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6524_, 0, v___x_6521_);
                    v___x_6523_ = v_reuseFailAlloc_6524_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6523_;
            }
            3 => {
                if v_isShared_6529_ == 0 {
                    v___x_6531_ = v___x_6528_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6532_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6532_, 0, v_a_6526_);
                    v___x_6531_ = v_reuseFailAlloc_6532_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6531_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0___boxed(
    mut v_f_6534_: *mut leanh::LeanObject,
    mut v_e_x27_6535_: *mut leanh::LeanObject,
    mut v_a_6536_: *mut leanh::LeanObject,
    mut v___y_6537_: *mut leanh::LeanObject,
    mut v___y_6538_: *mut leanh::LeanObject,
    mut v___y_6539_: *mut leanh::LeanObject,
    mut v___y_6540_: *mut leanh::LeanObject,
    mut v___y_6541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6542_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_6534_, v_e_x27_6535_, v_a_6536_, v___y_6537_, v___y_6538_, v___y_6539_, v___y_6540_);
    leanh::lean_dec(v___y_6540_);
    leanh::lean_dec_ref(v___y_6539_);
    leanh::lean_dec(v___y_6538_);
    leanh::lean_dec_ref(v___y_6537_);
    return v_res_6542_;
}
pub unsafe fn l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(
    mut v_f_6543_: *mut leanh::LeanObject,
    mut v_x_6544_: *mut leanh::LeanObject,
    mut v___y_6545_: *mut leanh::LeanObject,
    mut v___y_6546_: *mut leanh::LeanObject,
    mut v___y_6547_: *mut leanh::LeanObject,
    mut v___y_6548_: *mut leanh::LeanObject,
    mut v___y_6549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_binderName_6551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_6552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_6553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_6554_: u8 = 0;
    let mut v___x_6555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6563_: u8 = 0;
    let mut v_fst_6564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6568_: u8 = 0;
    let mut v___y_6570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6578_: u8 = 0;
    let mut v___x_6579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: u8 = 0;
    let mut v___x_6581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: usize = 0;
    let mut v___x_6583_: usize = 0;
    let mut v___x_6584_: u8 = 0;
    let mut v___x_6585_: usize = 0;
    let mut v___x_6586_: usize = 0;
    let mut v___x_6587_: u8 = 0;
    let mut v_isSharedCheck_6588_: u8 = 0;
    let mut v_isSharedCheck_6589_: u8 = 0;
    let mut v_binderName_6590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_6591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_6592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_6593_: u8 = 0;
    let mut v___x_6594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6602_: u8 = 0;
    let mut v_fst_6603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6607_: u8 = 0;
    let mut v___y_6609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6617_: u8 = 0;
    let mut v___x_6618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6619_: u8 = 0;
    let mut v___x_6620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6621_: usize = 0;
    let mut v___x_6622_: usize = 0;
    let mut v___x_6623_: u8 = 0;
    let mut v___x_6624_: usize = 0;
    let mut v___x_6625_: usize = 0;
    let mut v___x_6626_: u8 = 0;
    let mut v_isSharedCheck_6627_: u8 = 0;
    let mut v_isSharedCheck_6628_: u8 = 0;
    let mut v_data_6629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_6630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6635_: u8 = 0;
    let mut v_fst_6636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6640_: u8 = 0;
    let mut v___y_6642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6649_: usize = 0;
    let mut v___x_6650_: usize = 0;
    let mut v___x_6651_: u8 = 0;
    let mut v___x_6652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6653_: u8 = 0;
    let mut v_isSharedCheck_6654_: u8 = 0;
    let mut v_declName_6655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_6658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_6659_: u8 = 0;
    let mut v___x_6660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6672_: u8 = 0;
    let mut v_fst_6673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6677_: u8 = 0;
    let mut v___y_6679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6687_: u8 = 0;
    let mut v___x_6688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6689_: usize = 0;
    let mut v___x_6690_: usize = 0;
    let mut v___x_6691_: u8 = 0;
    let mut v___x_6692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6693_: usize = 0;
    let mut v___x_6694_: usize = 0;
    let mut v___x_6695_: u8 = 0;
    let mut v___x_6696_: usize = 0;
    let mut v___x_6697_: usize = 0;
    let mut v___x_6698_: u8 = 0;
    let mut v_isSharedCheck_6699_: u8 = 0;
    let mut v_isSharedCheck_6700_: u8 = 0;
    let mut v_fn_6701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_6702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6711_: u8 = 0;
    let mut v_fst_6712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6716_: u8 = 0;
    let mut v___y_6718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6726_: u8 = 0;
    let mut v___x_6727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6728_: usize = 0;
    let mut v___x_6729_: usize = 0;
    let mut v___x_6730_: u8 = 0;
    let mut v___x_6731_: usize = 0;
    let mut v___x_6732_: usize = 0;
    let mut v___x_6733_: u8 = 0;
    let mut v_isSharedCheck_6734_: u8 = 0;
    let mut v_isSharedCheck_6735_: u8 = 0;
    let mut v_typeName_6736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_6737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_6738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6743_: u8 = 0;
    let mut v_fst_6744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6748_: u8 = 0;
    let mut v___y_6750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6757_: usize = 0;
    let mut v___x_6758_: usize = 0;
    let mut v___x_6759_: u8 = 0;
    let mut v___x_6760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6761_: u8 = 0;
    let mut v_isSharedCheck_6762_: u8 = 0;
    let mut v___x_6763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_6544_) {
                7 => {
                    v_binderName_6551_ = leanh::lean_ctor_get(v_x_6544_, 0);
                    v_binderType_6552_ = leanh::lean_ctor_get(v_x_6544_, 1);
                    v_body_6553_ = leanh::lean_ctor_get(v_x_6544_, 2);
                    v_binderInfo_6554_ = leanh::lean_ctor_get_uint8(
                        v_x_6544_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    leanh::lean_inc_ref(v_binderType_6552_);
                    leanh::lean_inc_ref(v_f_6543_);
                    v___x_6555_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_6543_, v_binderType_6552_, v___y_6545_, v___y_6546_, v___y_6547_, v___y_6548_, v___y_6549_);
                    if leanh::lean_obj_tag(v___x_6555_) == 0 {
                        v_a_6556_ = leanh::lean_ctor_get(v___x_6555_, 0);
                        leanh::lean_inc(v_a_6556_);
                        leanh::lean_dec_ref_known(v___x_6555_, 1);
                        v_fst_6557_ = leanh::lean_ctor_get(v_a_6556_, 0);
                        leanh::lean_inc(v_fst_6557_);
                        v_snd_6558_ = leanh::lean_ctor_get(v_a_6556_, 1);
                        leanh::lean_inc(v_snd_6558_);
                        leanh::lean_dec(v_a_6556_);
                        leanh::lean_inc_ref(v_body_6553_);
                        v___x_6559_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_6543_, v_body_6553_, v_snd_6558_, v___y_6546_, v___y_6547_, v___y_6548_, v___y_6549_);
                        if leanh::lean_obj_tag(v___x_6559_) == 0 {
                            v_a_6560_ = leanh::lean_ctor_get(v___x_6559_, 0);
                            v_isSharedCheck_6589_ =
                                (!leanh::lean_is_exclusive(v___x_6559_)) as u8;
                            if v_isSharedCheck_6589_ == 0 {
                                v___x_6562_ = v___x_6559_;
                                v_isShared_6563_ = v_isSharedCheck_6589_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6560_);
                                leanh::lean_dec(v___x_6559_);
                                v___x_6562_ = leanh::lean_box(0);
                                v_isShared_6563_ = v_isSharedCheck_6589_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_fst_6557_);
                            leanh::lean_dec_ref_known(v_x_6544_, 3);
                            return v___x_6559_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_x_6544_, 3);
                        leanh::lean_dec_ref(v_f_6543_);
                        return v___x_6555_;
                    }
                }
                6 => {
                    v_binderName_6590_ = leanh::lean_ctor_get(v_x_6544_, 0);
                    v_binderType_6591_ = leanh::lean_ctor_get(v_x_6544_, 1);
                    v_body_6592_ = leanh::lean_ctor_get(v_x_6544_, 2);
                    v_binderInfo_6593_ = leanh::lean_ctor_get_uint8(
                        v_x_6544_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    leanh::lean_inc_ref(v_binderType_6591_);
                    leanh::lean_inc_ref(v_f_6543_);
                    v___x_6594_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_6543_, v_binderType_6591_, v___y_6545_, v___y_6546_, v___y_6547_, v___y_6548_, v___y_6549_);
                    if leanh::lean_obj_tag(v___x_6594_) == 0 {
                        v_a_6595_ = leanh::lean_ctor_get(v___x_6594_, 0);
                        leanh::lean_inc(v_a_6595_);
                        leanh::lean_dec_ref_known(v___x_6594_, 1);
                        v_fst_6596_ = leanh::lean_ctor_get(v_a_6595_, 0);
                        leanh::lean_inc(v_fst_6596_);
                        v_snd_6597_ = leanh::lean_ctor_get(v_a_6595_, 1);
                        leanh::lean_inc(v_snd_6597_);
                        leanh::lean_dec(v_a_6595_);
                        leanh::lean_inc_ref(v_body_6592_);
                        v___x_6598_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_6543_, v_body_6592_, v_snd_6597_, v___y_6546_, v___y_6547_, v___y_6548_, v___y_6549_);
                        if leanh::lean_obj_tag(v___x_6598_) == 0 {
                            v_a_6599_ = leanh::lean_ctor_get(v___x_6598_, 0);
                            v_isSharedCheck_6628_ =
                                (!leanh::lean_is_exclusive(v___x_6598_)) as u8;
                            if v_isSharedCheck_6628_ == 0 {
                                v___x_6601_ = v___x_6598_;
                                v_isShared_6602_ = v_isSharedCheck_6628_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6599_);
                                leanh::lean_dec(v___x_6598_);
                                v___x_6601_ = leanh::lean_box(0);
                                v_isShared_6602_ = v_isSharedCheck_6628_;
                                state = 7;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_fst_6596_);
                            leanh::lean_dec_ref_known(v_x_6544_, 3);
                            return v___x_6598_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_x_6544_, 3);
                        leanh::lean_dec_ref(v_f_6543_);
                        return v___x_6594_;
                    }
                }
                10 => {
                    v_data_6629_ = leanh::lean_ctor_get(v_x_6544_, 0);
                    v_expr_6630_ = leanh::lean_ctor_get(v_x_6544_, 1);
                    leanh::lean_inc_ref(v_expr_6630_);
                    v___x_6631_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_6543_, v_expr_6630_, v___y_6545_, v___y_6546_, v___y_6547_, v___y_6548_, v___y_6549_);
                    if leanh::lean_obj_tag(v___x_6631_) == 0 {
                        v_a_6632_ = leanh::lean_ctor_get(v___x_6631_, 0);
                        v_isSharedCheck_6654_ =
                            (!leanh::lean_is_exclusive(v___x_6631_)) as u8;
                        if v_isSharedCheck_6654_ == 0 {
                            v___x_6634_ = v___x_6631_;
                            v_isShared_6635_ = v_isSharedCheck_6654_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6632_);
                            leanh::lean_dec(v___x_6631_);
                            v___x_6634_ = leanh::lean_box(0);
                            v_isShared_6635_ = v_isSharedCheck_6654_;
                            state = 13;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_x_6544_, 2);
                        return v___x_6631_;
                    }
                }
                8 => {
                    v_declName_6655_ = leanh::lean_ctor_get(v_x_6544_, 0);
                    v_type_6656_ = leanh::lean_ctor_get(v_x_6544_, 1);
                    v_value_6657_ = leanh::lean_ctor_get(v_x_6544_, 2);
                    v_body_6658_ = leanh::lean_ctor_get(v_x_6544_, 3);
                    v_nondep_6659_ = leanh::lean_ctor_get_uint8(
                        v_x_6544_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    leanh::lean_inc_ref(v_type_6656_);
                    leanh::lean_inc_ref(v_f_6543_);
                    v___x_6660_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_6543_, v_type_6656_, v___y_6545_, v___y_6546_, v___y_6547_, v___y_6548_, v___y_6549_);
                    if leanh::lean_obj_tag(v___x_6660_) == 0 {
                        v_a_6661_ = leanh::lean_ctor_get(v___x_6660_, 0);
                        leanh::lean_inc(v_a_6661_);
                        leanh::lean_dec_ref_known(v___x_6660_, 1);
                        v_fst_6662_ = leanh::lean_ctor_get(v_a_6661_, 0);
                        leanh::lean_inc(v_fst_6662_);
                        v_snd_6663_ = leanh::lean_ctor_get(v_a_6661_, 1);
                        leanh::lean_inc(v_snd_6663_);
                        leanh::lean_dec(v_a_6661_);
                        leanh::lean_inc_ref(v_value_6657_);
                        leanh::lean_inc_ref(v_f_6543_);
                        v___x_6664_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_6543_, v_value_6657_, v_snd_6663_, v___y_6546_, v___y_6547_, v___y_6548_, v___y_6549_);
                        if leanh::lean_obj_tag(v___x_6664_) == 0 {
                            v_a_6665_ = leanh::lean_ctor_get(v___x_6664_, 0);
                            leanh::lean_inc(v_a_6665_);
                            leanh::lean_dec_ref_known(v___x_6664_, 1);
                            v_fst_6666_ = leanh::lean_ctor_get(v_a_6665_, 0);
                            leanh::lean_inc(v_fst_6666_);
                            v_snd_6667_ = leanh::lean_ctor_get(v_a_6665_, 1);
                            leanh::lean_inc(v_snd_6667_);
                            leanh::lean_dec(v_a_6665_);
                            leanh::lean_inc_ref(v_body_6658_);
                            v___x_6668_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_6543_, v_body_6658_, v_snd_6667_, v___y_6546_, v___y_6547_, v___y_6548_, v___y_6549_);
                            if leanh::lean_obj_tag(v___x_6668_) == 0 {
                                v_a_6669_ = leanh::lean_ctor_get(v___x_6668_, 0);
                                v_isSharedCheck_6700_ =
                                    (!leanh::lean_is_exclusive(v___x_6668_)) as u8;
                                if v_isSharedCheck_6700_ == 0 {
                                    v___x_6671_ = v___x_6668_;
                                    v_isShared_6672_ = v_isSharedCheck_6700_;
                                    state = 18;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6669_);
                                    leanh::lean_dec(v___x_6668_);
                                    v___x_6671_ = leanh::lean_box(0);
                                    v_isShared_6672_ = v_isSharedCheck_6700_;
                                    state = 18;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_fst_6666_);
                                leanh::lean_dec(v_fst_6662_);
                                leanh::lean_dec_ref_known(v_x_6544_, 4);
                                return v___x_6668_;
                            }
                        } else {
                            leanh::lean_dec(v_fst_6662_);
                            leanh::lean_dec_ref_known(v_x_6544_, 4);
                            leanh::lean_dec_ref(v_f_6543_);
                            return v___x_6664_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_x_6544_, 4);
                        leanh::lean_dec_ref(v_f_6543_);
                        return v___x_6660_;
                    }
                }
                5 => {
                    v_fn_6701_ = leanh::lean_ctor_get(v_x_6544_, 0);
                    v_arg_6702_ = leanh::lean_ctor_get(v_x_6544_, 1);
                    leanh::lean_inc_ref(v_fn_6701_);
                    leanh::lean_inc_ref(v_f_6543_);
                    v___x_6703_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_6543_, v_fn_6701_, v___y_6545_, v___y_6546_, v___y_6547_, v___y_6548_, v___y_6549_);
                    if leanh::lean_obj_tag(v___x_6703_) == 0 {
                        v_a_6704_ = leanh::lean_ctor_get(v___x_6703_, 0);
                        leanh::lean_inc(v_a_6704_);
                        leanh::lean_dec_ref_known(v___x_6703_, 1);
                        v_fst_6705_ = leanh::lean_ctor_get(v_a_6704_, 0);
                        leanh::lean_inc(v_fst_6705_);
                        v_snd_6706_ = leanh::lean_ctor_get(v_a_6704_, 1);
                        leanh::lean_inc(v_snd_6706_);
                        leanh::lean_dec(v_a_6704_);
                        leanh::lean_inc_ref(v_arg_6702_);
                        v___x_6707_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_6543_, v_arg_6702_, v_snd_6706_, v___y_6546_, v___y_6547_, v___y_6548_, v___y_6549_);
                        if leanh::lean_obj_tag(v___x_6707_) == 0 {
                            v_a_6708_ = leanh::lean_ctor_get(v___x_6707_, 0);
                            v_isSharedCheck_6735_ =
                                (!leanh::lean_is_exclusive(v___x_6707_)) as u8;
                            if v_isSharedCheck_6735_ == 0 {
                                v___x_6710_ = v___x_6707_;
                                v_isShared_6711_ = v_isSharedCheck_6735_;
                                state = 24;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6708_);
                                leanh::lean_dec(v___x_6707_);
                                v___x_6710_ = leanh::lean_box(0);
                                v_isShared_6711_ = v_isSharedCheck_6735_;
                                state = 24;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_fst_6705_);
                            leanh::lean_dec_ref_known(v_x_6544_, 2);
                            return v___x_6707_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_x_6544_, 2);
                        leanh::lean_dec_ref(v_f_6543_);
                        return v___x_6703_;
                    }
                }
                11 => {
                    v_typeName_6736_ = leanh::lean_ctor_get(v_x_6544_, 0);
                    v_idx_6737_ = leanh::lean_ctor_get(v_x_6544_, 1);
                    v_struct_6738_ = leanh::lean_ctor_get(v_x_6544_, 2);
                    leanh::lean_inc_ref(v_struct_6738_);
                    v___x_6739_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_6543_, v_struct_6738_, v___y_6545_, v___y_6546_, v___y_6547_, v___y_6548_, v___y_6549_);
                    if leanh::lean_obj_tag(v___x_6739_) == 0 {
                        v_a_6740_ = leanh::lean_ctor_get(v___x_6739_, 0);
                        v_isSharedCheck_6762_ =
                            (!leanh::lean_is_exclusive(v___x_6739_)) as u8;
                        if v_isSharedCheck_6762_ == 0 {
                            v___x_6742_ = v___x_6739_;
                            v_isShared_6743_ = v_isSharedCheck_6762_;
                            state = 30;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6740_);
                            leanh::lean_dec(v___x_6739_);
                            v___x_6742_ = leanh::lean_box(0);
                            v_isShared_6743_ = v_isSharedCheck_6762_;
                            state = 30;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_x_6544_, 3);
                        return v___x_6739_;
                    }
                }
                _ => {
                    leanh::lean_dec_ref(v_f_6543_);
                    v___x_6763_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6763_, 0, v_x_6544_);
                    leanh::lean_ctor_set(v___x_6763_, 1, v___y_6545_);
                    v___x_6764_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6764_, 0, v___x_6763_);
                    return v___x_6764_;
                }
            },
            1 => {
                v_fst_6564_ = leanh::lean_ctor_get(v_a_6560_, 0);
                v_snd_6565_ = leanh::lean_ctor_get(v_a_6560_, 1);
                v_isSharedCheck_6588_ = (!leanh::lean_is_exclusive(v_a_6560_)) as u8;
                if v_isSharedCheck_6588_ == 0 {
                    v___x_6567_ = v_a_6560_;
                    v_isShared_6568_ = v_isSharedCheck_6588_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_6565_);
                    leanh::lean_inc(v_fst_6564_);
                    leanh::lean_dec(v_a_6560_);
                    v___x_6567_ = leanh::lean_box(0);
                    v_isShared_6568_ = v_isSharedCheck_6588_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6582_ = lean_ptr_addr(v_binderType_6552_);
                v___x_6583_ = lean_ptr_addr(v_fst_6557_);
                v___x_6584_ = lean_usize_dec_eq(v___x_6582_, v___x_6583_);
                if v___x_6584_ == 0 {
                    v___y_6578_ = v___x_6584_;
                    state = 6;
                    continue;
                } else {
                    v___x_6585_ = lean_ptr_addr(v_body_6553_);
                    v___x_6586_ = lean_ptr_addr(v_fst_6564_);
                    v___x_6587_ = lean_usize_dec_eq(v___x_6585_, v___x_6586_);
                    v___y_6578_ = v___x_6587_;
                    state = 6;
                    continue;
                }
            }
            3 => {
                if v_isShared_6568_ == 0 {
                    leanh::lean_ctor_set(v___x_6567_, 0, v___y_6570_);
                    v___x_6572_ = v___x_6567_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6576_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6576_, 0, v___y_6570_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6576_, 1, v_snd_6565_);
                    v___x_6572_ = v_reuseFailAlloc_6576_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6563_ == 0 {
                    leanh::lean_ctor_set(v___x_6562_, 0, v___x_6572_);
                    v___x_6574_ = v___x_6562_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6575_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6575_, 0, v___x_6572_);
                    v___x_6574_ = v_reuseFailAlloc_6575_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6574_;
            }
            6 => {
                if v___y_6578_ == 0 {
                    leanh::lean_inc(v_binderName_6551_);
                    leanh::lean_dec_ref_known(v_x_6544_, 3);
                    v___x_6579_ = l_Lean_Expr_forallE___override(
                        v_binderName_6551_,
                        v_fst_6557_,
                        v_fst_6564_,
                        v_binderInfo_6554_,
                    );
                    v___y_6570_ = v___x_6579_;
                    state = 3;
                    continue;
                } else {
                    v___x_6580_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_6554_, v_binderInfo_6554_);
                    if v___x_6580_ == 0 {
                        leanh::lean_inc(v_binderName_6551_);
                        leanh::lean_dec_ref_known(v_x_6544_, 3);
                        v___x_6581_ = l_Lean_Expr_forallE___override(
                            v_binderName_6551_,
                            v_fst_6557_,
                            v_fst_6564_,
                            v_binderInfo_6554_,
                        );
                        v___y_6570_ = v___x_6581_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v_fst_6564_);
                        leanh::lean_dec(v_fst_6557_);
                        v___y_6570_ = v_x_6544_;
                        state = 3;
                        continue;
                    }
                }
            }
            7 => {
                v_fst_6603_ = leanh::lean_ctor_get(v_a_6599_, 0);
                v_snd_6604_ = leanh::lean_ctor_get(v_a_6599_, 1);
                v_isSharedCheck_6627_ = (!leanh::lean_is_exclusive(v_a_6599_)) as u8;
                if v_isSharedCheck_6627_ == 0 {
                    v___x_6606_ = v_a_6599_;
                    v_isShared_6607_ = v_isSharedCheck_6627_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_6604_);
                    leanh::lean_inc(v_fst_6603_);
                    leanh::lean_dec(v_a_6599_);
                    v___x_6606_ = leanh::lean_box(0);
                    v_isShared_6607_ = v_isSharedCheck_6627_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_6621_ = lean_ptr_addr(v_binderType_6591_);
                v___x_6622_ = lean_ptr_addr(v_fst_6596_);
                v___x_6623_ = lean_usize_dec_eq(v___x_6621_, v___x_6622_);
                if v___x_6623_ == 0 {
                    v___y_6617_ = v___x_6623_;
                    state = 12;
                    continue;
                } else {
                    v___x_6624_ = lean_ptr_addr(v_body_6592_);
                    v___x_6625_ = lean_ptr_addr(v_fst_6603_);
                    v___x_6626_ = lean_usize_dec_eq(v___x_6624_, v___x_6625_);
                    v___y_6617_ = v___x_6626_;
                    state = 12;
                    continue;
                }
            }
            9 => {
                if v_isShared_6607_ == 0 {
                    leanh::lean_ctor_set(v___x_6606_, 0, v___y_6609_);
                    v___x_6611_ = v___x_6606_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6615_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6615_, 0, v___y_6609_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6615_, 1, v_snd_6604_);
                    v___x_6611_ = v_reuseFailAlloc_6615_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_6602_ == 0 {
                    leanh::lean_ctor_set(v___x_6601_, 0, v___x_6611_);
                    v___x_6613_ = v___x_6601_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6614_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6614_, 0, v___x_6611_);
                    v___x_6613_ = v_reuseFailAlloc_6614_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6613_;
            }
            12 => {
                if v___y_6617_ == 0 {
                    leanh::lean_inc(v_binderName_6590_);
                    leanh::lean_dec_ref_known(v_x_6544_, 3);
                    v___x_6618_ = l_Lean_Expr_lam___override(
                        v_binderName_6590_,
                        v_fst_6596_,
                        v_fst_6603_,
                        v_binderInfo_6593_,
                    );
                    v___y_6609_ = v___x_6618_;
                    state = 9;
                    continue;
                } else {
                    v___x_6619_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_6593_, v_binderInfo_6593_);
                    if v___x_6619_ == 0 {
                        leanh::lean_inc(v_binderName_6590_);
                        leanh::lean_dec_ref_known(v_x_6544_, 3);
                        v___x_6620_ = l_Lean_Expr_lam___override(
                            v_binderName_6590_,
                            v_fst_6596_,
                            v_fst_6603_,
                            v_binderInfo_6593_,
                        );
                        v___y_6609_ = v___x_6620_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_dec(v_fst_6603_);
                        leanh::lean_dec(v_fst_6596_);
                        v___y_6609_ = v_x_6544_;
                        state = 9;
                        continue;
                    }
                }
            }
            13 => {
                v_fst_6636_ = leanh::lean_ctor_get(v_a_6632_, 0);
                v_snd_6637_ = leanh::lean_ctor_get(v_a_6632_, 1);
                v_isSharedCheck_6653_ = (!leanh::lean_is_exclusive(v_a_6632_)) as u8;
                if v_isSharedCheck_6653_ == 0 {
                    v___x_6639_ = v_a_6632_;
                    v_isShared_6640_ = v_isSharedCheck_6653_;
                    state = 14;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_6637_);
                    leanh::lean_inc(v_fst_6636_);
                    leanh::lean_dec(v_a_6632_);
                    v___x_6639_ = leanh::lean_box(0);
                    v_isShared_6640_ = v_isSharedCheck_6653_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_6649_ = lean_ptr_addr(v_expr_6630_);
                v___x_6650_ = lean_ptr_addr(v_fst_6636_);
                v___x_6651_ = lean_usize_dec_eq(v___x_6649_, v___x_6650_);
                if v___x_6651_ == 0 {
                    leanh::lean_inc(v_data_6629_);
                    leanh::lean_dec_ref_known(v_x_6544_, 2);
                    v___x_6652_ = l_Lean_Expr_mdata___override(v_data_6629_, v_fst_6636_);
                    v___y_6642_ = v___x_6652_;
                    state = 15;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_6636_);
                    v___y_6642_ = v_x_6544_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_6640_ == 0 {
                    leanh::lean_ctor_set(v___x_6639_, 0, v___y_6642_);
                    v___x_6644_ = v___x_6639_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6648_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6648_, 0, v___y_6642_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6648_, 1, v_snd_6637_);
                    v___x_6644_ = v_reuseFailAlloc_6648_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_6635_ == 0 {
                    leanh::lean_ctor_set(v___x_6634_, 0, v___x_6644_);
                    v___x_6646_ = v___x_6634_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6647_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6647_, 0, v___x_6644_);
                    v___x_6646_ = v_reuseFailAlloc_6647_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6646_;
            }
            18 => {
                v_fst_6673_ = leanh::lean_ctor_get(v_a_6669_, 0);
                v_snd_6674_ = leanh::lean_ctor_get(v_a_6669_, 1);
                v_isSharedCheck_6699_ = (!leanh::lean_is_exclusive(v_a_6669_)) as u8;
                if v_isSharedCheck_6699_ == 0 {
                    v___x_6676_ = v_a_6669_;
                    v_isShared_6677_ = v_isSharedCheck_6699_;
                    state = 19;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_6674_);
                    leanh::lean_inc(v_fst_6673_);
                    leanh::lean_dec(v_a_6669_);
                    v___x_6676_ = leanh::lean_box(0);
                    v_isShared_6677_ = v_isSharedCheck_6699_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_6693_ = lean_ptr_addr(v_type_6656_);
                v___x_6694_ = lean_ptr_addr(v_fst_6662_);
                v___x_6695_ = lean_usize_dec_eq(v___x_6693_, v___x_6694_);
                if v___x_6695_ == 0 {
                    v___y_6687_ = v___x_6695_;
                    state = 23;
                    continue;
                } else {
                    v___x_6696_ = lean_ptr_addr(v_value_6657_);
                    v___x_6697_ = lean_ptr_addr(v_fst_6666_);
                    v___x_6698_ = lean_usize_dec_eq(v___x_6696_, v___x_6697_);
                    v___y_6687_ = v___x_6698_;
                    state = 23;
                    continue;
                }
            }
            20 => {
                if v_isShared_6677_ == 0 {
                    leanh::lean_ctor_set(v___x_6676_, 0, v___y_6679_);
                    v___x_6681_ = v___x_6676_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_6685_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6685_, 0, v___y_6679_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6685_, 1, v_snd_6674_);
                    v___x_6681_ = v_reuseFailAlloc_6685_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                if v_isShared_6672_ == 0 {
                    leanh::lean_ctor_set(v___x_6671_, 0, v___x_6681_);
                    v___x_6683_ = v___x_6671_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_6684_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6684_, 0, v___x_6681_);
                    v___x_6683_ = v_reuseFailAlloc_6684_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_6683_;
            }
            23 => {
                if v___y_6687_ == 0 {
                    leanh::lean_inc(v_declName_6655_);
                    leanh::lean_dec_ref_known(v_x_6544_, 4);
                    v___x_6688_ = l_Lean_Expr_letE___override(
                        v_declName_6655_,
                        v_fst_6662_,
                        v_fst_6666_,
                        v_fst_6673_,
                        v_nondep_6659_,
                    );
                    v___y_6679_ = v___x_6688_;
                    state = 20;
                    continue;
                } else {
                    v___x_6689_ = lean_ptr_addr(v_body_6658_);
                    v___x_6690_ = lean_ptr_addr(v_fst_6673_);
                    v___x_6691_ = lean_usize_dec_eq(v___x_6689_, v___x_6690_);
                    if v___x_6691_ == 0 {
                        leanh::lean_inc(v_declName_6655_);
                        leanh::lean_dec_ref_known(v_x_6544_, 4);
                        v___x_6692_ = l_Lean_Expr_letE___override(
                            v_declName_6655_,
                            v_fst_6662_,
                            v_fst_6666_,
                            v_fst_6673_,
                            v_nondep_6659_,
                        );
                        v___y_6679_ = v___x_6692_;
                        state = 20;
                        continue;
                    } else {
                        leanh::lean_dec(v_fst_6673_);
                        leanh::lean_dec(v_fst_6666_);
                        leanh::lean_dec(v_fst_6662_);
                        v___y_6679_ = v_x_6544_;
                        state = 20;
                        continue;
                    }
                }
            }
            24 => {
                v_fst_6712_ = leanh::lean_ctor_get(v_a_6708_, 0);
                v_snd_6713_ = leanh::lean_ctor_get(v_a_6708_, 1);
                v_isSharedCheck_6734_ = (!leanh::lean_is_exclusive(v_a_6708_)) as u8;
                if v_isSharedCheck_6734_ == 0 {
                    v___x_6715_ = v_a_6708_;
                    v_isShared_6716_ = v_isSharedCheck_6734_;
                    state = 25;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_6713_);
                    leanh::lean_inc(v_fst_6712_);
                    leanh::lean_dec(v_a_6708_);
                    v___x_6715_ = leanh::lean_box(0);
                    v_isShared_6716_ = v_isSharedCheck_6734_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                v___x_6728_ = lean_ptr_addr(v_fn_6701_);
                v___x_6729_ = lean_ptr_addr(v_fst_6705_);
                v___x_6730_ = lean_usize_dec_eq(v___x_6728_, v___x_6729_);
                if v___x_6730_ == 0 {
                    v___y_6726_ = v___x_6730_;
                    state = 29;
                    continue;
                } else {
                    v___x_6731_ = lean_ptr_addr(v_arg_6702_);
                    v___x_6732_ = lean_ptr_addr(v_fst_6712_);
                    v___x_6733_ = lean_usize_dec_eq(v___x_6731_, v___x_6732_);
                    v___y_6726_ = v___x_6733_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                if v_isShared_6716_ == 0 {
                    leanh::lean_ctor_set(v___x_6715_, 0, v___y_6718_);
                    v___x_6720_ = v___x_6715_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_6724_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6724_, 0, v___y_6718_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6724_, 1, v_snd_6713_);
                    v___x_6720_ = v_reuseFailAlloc_6724_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_6711_ == 0 {
                    leanh::lean_ctor_set(v___x_6710_, 0, v___x_6720_);
                    v___x_6722_ = v___x_6710_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_6723_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6723_, 0, v___x_6720_);
                    v___x_6722_ = v_reuseFailAlloc_6723_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_6722_;
            }
            29 => {
                if v___y_6726_ == 0 {
                    leanh::lean_dec_ref_known(v_x_6544_, 2);
                    v___x_6727_ = l_Lean_Expr_app___override(v_fst_6705_, v_fst_6712_);
                    v___y_6718_ = v___x_6727_;
                    state = 26;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_6712_);
                    leanh::lean_dec(v_fst_6705_);
                    v___y_6718_ = v_x_6544_;
                    state = 26;
                    continue;
                }
            }
            30 => {
                v_fst_6744_ = leanh::lean_ctor_get(v_a_6740_, 0);
                v_snd_6745_ = leanh::lean_ctor_get(v_a_6740_, 1);
                v_isSharedCheck_6761_ = (!leanh::lean_is_exclusive(v_a_6740_)) as u8;
                if v_isSharedCheck_6761_ == 0 {
                    v___x_6747_ = v_a_6740_;
                    v_isShared_6748_ = v_isSharedCheck_6761_;
                    state = 31;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_6745_);
                    leanh::lean_inc(v_fst_6744_);
                    leanh::lean_dec(v_a_6740_);
                    v___x_6747_ = leanh::lean_box(0);
                    v_isShared_6748_ = v_isSharedCheck_6761_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                v___x_6757_ = lean_ptr_addr(v_struct_6738_);
                v___x_6758_ = lean_ptr_addr(v_fst_6744_);
                v___x_6759_ = lean_usize_dec_eq(v___x_6757_, v___x_6758_);
                if v___x_6759_ == 0 {
                    leanh::lean_inc(v_idx_6737_);
                    leanh::lean_inc(v_typeName_6736_);
                    leanh::lean_dec_ref_known(v_x_6544_, 3);
                    v___x_6760_ =
                        l_Lean_Expr_proj___override(v_typeName_6736_, v_idx_6737_, v_fst_6744_);
                    v___y_6750_ = v___x_6760_;
                    state = 32;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_6744_);
                    v___y_6750_ = v_x_6544_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_6748_ == 0 {
                    leanh::lean_ctor_set(v___x_6747_, 0, v___y_6750_);
                    v___x_6752_ = v___x_6747_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_6756_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6756_, 0, v___y_6750_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6756_, 1, v_snd_6745_);
                    v___x_6752_ = v_reuseFailAlloc_6756_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                if v_isShared_6743_ == 0 {
                    leanh::lean_ctor_set(v___x_6742_, 0, v___x_6752_);
                    v___x_6754_ = v___x_6742_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_6755_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6755_, 0, v___x_6752_);
                    v___x_6754_ = v_reuseFailAlloc_6755_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_6754_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___boxed(
    mut v_f_6765_: *mut leanh::LeanObject,
    mut v_x_6766_: *mut leanh::LeanObject,
    mut v___y_6767_: *mut leanh::LeanObject,
    mut v___y_6768_: *mut leanh::LeanObject,
    mut v___y_6769_: *mut leanh::LeanObject,
    mut v___y_6770_: *mut leanh::LeanObject,
    mut v___y_6771_: *mut leanh::LeanObject,
    mut v___y_6772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6773_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6773_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_6765_, v_x_6766_, v___y_6767_, v___y_6768_, v___y_6769_, v___y_6770_, v___y_6771_);
    leanh::lean_dec(v___y_6771_);
    leanh::lean_dec_ref(v___y_6770_);
    leanh::lean_dec(v___y_6769_);
    leanh::lean_dec_ref(v___y_6768_);
    return v_res_6773_;
}
pub unsafe fn l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(
    mut v_f_6774_: *mut leanh::LeanObject,
    mut v_init_6775_: *mut leanh::LeanObject,
    mut v_e_6776_: *mut leanh::LeanObject,
    mut v___y_6777_: *mut leanh::LeanObject,
    mut v___y_6778_: *mut leanh::LeanObject,
    mut v___y_6779_: *mut leanh::LeanObject,
    mut v___y_6780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6786_: u8 = 0;
    let mut v_snd_6787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6791_: u8 = 0;
    let mut v_a_6792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6795_: u8 = 0;
    let mut v___x_6797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6799_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6782_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_6774_, v_e_6776_, v_init_6775_, v___y_6777_, v___y_6778_, v___y_6779_, v___y_6780_);
                if leanh::lean_obj_tag(v___x_6782_) == 0 {
                    v_a_6783_ = leanh::lean_ctor_get(v___x_6782_, 0);
                    v_isSharedCheck_6791_ = (!leanh::lean_is_exclusive(v___x_6782_)) as u8;
                    if v_isSharedCheck_6791_ == 0 {
                        v___x_6785_ = v___x_6782_;
                        v_isShared_6786_ = v_isSharedCheck_6791_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6783_);
                        leanh::lean_dec(v___x_6782_);
                        v___x_6785_ = leanh::lean_box(0);
                        v_isShared_6786_ = v_isSharedCheck_6791_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6792_ = leanh::lean_ctor_get(v___x_6782_, 0);
                    v_isSharedCheck_6799_ = (!leanh::lean_is_exclusive(v___x_6782_)) as u8;
                    if v_isSharedCheck_6799_ == 0 {
                        v___x_6794_ = v___x_6782_;
                        v_isShared_6795_ = v_isSharedCheck_6799_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6792_);
                        leanh::lean_dec(v___x_6782_);
                        v___x_6794_ = leanh::lean_box(0);
                        v_isShared_6795_ = v_isSharedCheck_6799_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_6787_ = leanh::lean_ctor_get(v_a_6783_, 1);
                leanh::lean_inc(v_snd_6787_);
                leanh::lean_dec(v_a_6783_);
                if v_isShared_6786_ == 0 {
                    leanh::lean_ctor_set(v___x_6785_, 0, v_snd_6787_);
                    v___x_6789_ = v___x_6785_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6790_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6790_, 0, v_snd_6787_);
                    v___x_6789_ = v_reuseFailAlloc_6790_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6789_;
            }
            3 => {
                if v_isShared_6795_ == 0 {
                    v___x_6797_ = v___x_6794_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6798_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6798_, 0, v_a_6792_);
                    v___x_6797_ = v_reuseFailAlloc_6798_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6797_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg___boxed(
    mut v_f_6800_: *mut leanh::LeanObject,
    mut v_init_6801_: *mut leanh::LeanObject,
    mut v_e_6802_: *mut leanh::LeanObject,
    mut v___y_6803_: *mut leanh::LeanObject,
    mut v___y_6804_: *mut leanh::LeanObject,
    mut v___y_6805_: *mut leanh::LeanObject,
    mut v___y_6806_: *mut leanh::LeanObject,
    mut v___y_6807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6808_ =
        l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(
            v_f_6800_,
            v_init_6801_,
            v_e_6802_,
            v___y_6803_,
            v___y_6804_,
            v___y_6805_,
            v___y_6806_,
        );
    leanh::lean_dec(v___y_6806_);
    leanh::lean_dec_ref(v___y_6805_);
    leanh::lean_dec(v___y_6804_);
    leanh::lean_dec_ref(v___y_6803_);
    return v_res_6808_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(
    mut v_op_6811_: *mut leanh::LeanObject,
    mut v_as_6812_: *mut leanh::LeanObject,
    mut v_i_6813_: usize,
    mut v_stop_6814_: usize,
    mut v_b_6815_: *mut leanh::LeanObject,
    mut v___y_6816_: *mut leanh::LeanObject,
    mut v___y_6817_: *mut leanh::LeanObject,
    mut v___y_6818_: *mut leanh::LeanObject,
    mut v___y_6819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_6822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6823_: usize = 0;
    let mut v___x_6824_: usize = 0;
    let mut v___x_6826_: u8 = 0;
    let mut v___x_6827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6837_: u8 = 0;
    let mut v___x_6839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6841_: u8 = 0;
    let mut v___x_6842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6826_ = lean_usize_dec_eq(v_i_6813_, v_stop_6814_);
                if v___x_6826_ == 0 {
                    v___x_6827_ = lean_array_uget_borrowed(v_as_6812_, v_i_6813_);
                    leanh::lean_inc(v___y_6819_);
                    leanh::lean_inc_ref(v___y_6818_);
                    leanh::lean_inc(v___y_6817_);
                    leanh::lean_inc_ref(v___y_6816_);
                    leanh::lean_inc(v___x_6827_);
                    v___x_6828_ = lean_infer_type(
                        v___x_6827_,
                        v___y_6816_,
                        v___y_6817_,
                        v___y_6818_,
                        v___y_6819_,
                    );
                    if leanh::lean_obj_tag(v___x_6828_) == 0 {
                        v_a_6829_ = leanh::lean_ctor_get(v___x_6828_, 0);
                        leanh::lean_inc(v_a_6829_);
                        leanh::lean_dec_ref_known(v___x_6828_, 1);
                        leanh::lean_inc_ref(v_op_6811_);
                        v___x_6830_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(
                            v_op_6811_,
                            v_a_6829_,
                            v___y_6816_,
                            v___y_6817_,
                            v___y_6818_,
                            v___y_6819_,
                        );
                        if leanh::lean_obj_tag(v___x_6830_) == 0 {
                            v_a_6831_ = leanh::lean_ctor_get(v___x_6830_, 0);
                            leanh::lean_inc(v_a_6831_);
                            leanh::lean_dec_ref_known(v___x_6830_, 1);
                            v___x_6832_ = l_Array_append___redArg(v_b_6815_, v_a_6831_);
                            leanh::lean_dec(v_a_6831_);
                            v_a_6822_ = v___x_6832_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_b_6815_);
                            if leanh::lean_obj_tag(v___x_6830_) == 0 {
                                v_a_6833_ = leanh::lean_ctor_get(v___x_6830_, 0);
                                leanh::lean_inc(v_a_6833_);
                                leanh::lean_dec_ref_known(v___x_6830_, 1);
                                v_a_6822_ = v_a_6833_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_op_6811_);
                                return v___x_6830_;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_6815_);
                        leanh::lean_dec_ref(v_op_6811_);
                        v_a_6834_ = leanh::lean_ctor_get(v___x_6828_, 0);
                        v_isSharedCheck_6841_ =
                            (!leanh::lean_is_exclusive(v___x_6828_)) as u8;
                        if v_isSharedCheck_6841_ == 0 {
                            v___x_6836_ = v___x_6828_;
                            v_isShared_6837_ = v_isSharedCheck_6841_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6834_);
                            leanh::lean_dec(v___x_6828_);
                            v___x_6836_ = leanh::lean_box(0);
                            v_isShared_6837_ = v_isSharedCheck_6841_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_op_6811_);
                    v___x_6842_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6842_, 0, v_b_6815_);
                    return v___x_6842_;
                }
            }
            1 => {
                v___x_6823_ = 1usize;
                v___x_6824_ = lean_usize_add(v_i_6813_, v___x_6823_);
                v_i_6813_ = v___x_6824_;
                v_b_6815_ = v_a_6822_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_6837_ == 0 {
                    v___x_6839_ = v___x_6836_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6840_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6840_, 0, v_a_6834_);
                    v___x_6839_ = v_reuseFailAlloc_6840_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6839_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(
    mut v_op_6843_: *mut leanh::LeanObject,
    mut v_args_6844_: *mut leanh::LeanObject,
    mut v_body_6845_: *mut leanh::LeanObject,
    mut v___y_6846_: *mut leanh::LeanObject,
    mut v___y_6847_: *mut leanh::LeanObject,
    mut v___y_6848_: *mut leanh::LeanObject,
    mut v___y_6849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6855_: u8 = 0;
    let mut v___x_6856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6859_: u8 = 0;
    let mut v___x_6861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6863_: u8 = 0;
    let mut v___x_6865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6867_: usize = 0;
    let mut v___x_6868_: usize = 0;
    let mut v___x_6869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6870_: usize = 0;
    let mut v___x_6871_: usize = 0;
    let mut v___x_6872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6873_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_op_6843_);
                v___x_6851_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(
                    v_op_6843_,
                    v_body_6845_,
                    v___y_6846_,
                    v___y_6847_,
                    v___y_6848_,
                    v___y_6849_,
                );
                if leanh::lean_obj_tag(v___x_6851_) == 0 {
                    v_a_6852_ = leanh::lean_ctor_get(v___x_6851_, 0);
                    v_isSharedCheck_6873_ = (!leanh::lean_is_exclusive(v___x_6851_)) as u8;
                    if v_isSharedCheck_6873_ == 0 {
                        v___x_6854_ = v___x_6851_;
                        v_isShared_6855_ = v_isSharedCheck_6873_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6852_);
                        leanh::lean_dec(v___x_6851_);
                        v___x_6854_ = leanh::lean_box(0);
                        v_isShared_6855_ = v_isSharedCheck_6873_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_op_6843_);
                    return v___x_6851_;
                }
            }
            1 => {
                v___x_6856_ = l_Array_reverse___redArg(v_a_6852_);
                v___x_6857_ = leanh::lean_unsigned_to_nat(0);
                v___x_6858_ = lean_array_get_size(v_args_6844_);
                v___x_6859_ = lean_nat_dec_lt(v___x_6857_, v___x_6858_);
                if v___x_6859_ == 0 {
                    leanh::lean_dec_ref(v_op_6843_);
                    if v_isShared_6855_ == 0 {
                        leanh::lean_ctor_set(v___x_6854_, 0, v___x_6856_);
                        v___x_6861_ = v___x_6854_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6862_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6862_, 0, v___x_6856_);
                        v___x_6861_ = v_reuseFailAlloc_6862_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_6863_ = lean_nat_dec_le(v___x_6858_, v___x_6858_);
                    if v___x_6863_ == 0 {
                        if v___x_6859_ == 0 {
                            leanh::lean_dec_ref(v_op_6843_);
                            if v_isShared_6855_ == 0 {
                                leanh::lean_ctor_set(v___x_6854_, 0, v___x_6856_);
                                v___x_6865_ = v___x_6854_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_6866_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_6866_, 0, v___x_6856_);
                                v___x_6865_ = v_reuseFailAlloc_6866_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_6854_);
                            v___x_6867_ = 0usize;
                            v___x_6868_ = lean_usize_of_nat(v___x_6858_);
                            v___x_6869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_6843_, v_args_6844_, v___x_6867_, v___x_6868_, v___x_6856_, v___y_6846_, v___y_6847_, v___y_6848_, v___y_6849_);
                            return v___x_6869_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_6854_);
                        v___x_6870_ = 0usize;
                        v___x_6871_ = lean_usize_of_nat(v___x_6858_);
                        v___x_6872_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_6843_, v_args_6844_, v___x_6870_, v___x_6871_, v___x_6856_, v___y_6846_, v___y_6847_, v___y_6848_, v___y_6849_);
                        return v___x_6872_;
                    }
                }
            }
            2 => {
                return v___x_6861_;
            }
            3 => {
                return v___x_6865_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed(
    mut v_op_6874_: *mut leanh::LeanObject,
    mut v_args_6875_: *mut leanh::LeanObject,
    mut v_body_6876_: *mut leanh::LeanObject,
    mut v___y_6877_: *mut leanh::LeanObject,
    mut v___y_6878_: *mut leanh::LeanObject,
    mut v___y_6879_: *mut leanh::LeanObject,
    mut v___y_6880_: *mut leanh::LeanObject,
    mut v___y_6881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6882_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(
        v_op_6874_,
        v_args_6875_,
        v_body_6876_,
        v___y_6877_,
        v___y_6878_,
        v___y_6879_,
        v___y_6880_,
    );
    leanh::lean_dec(v___y_6880_);
    leanh::lean_dec_ref(v___y_6879_);
    leanh::lean_dec(v___y_6878_);
    leanh::lean_dec_ref(v___y_6877_);
    leanh::lean_dec_ref(v_args_6875_);
    return v_res_6882_;
}
pub unsafe fn l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3___boxed(
    mut v_op_6883_: *mut leanh::LeanObject,
    mut v_a_6884_: *mut leanh::LeanObject,
    mut v_f_6885_: *mut leanh::LeanObject,
    mut v___y_6886_: *mut leanh::LeanObject,
    mut v___y_6887_: *mut leanh::LeanObject,
    mut v___y_6888_: *mut leanh::LeanObject,
    mut v___y_6889_: *mut leanh::LeanObject,
    mut v___y_6890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6891_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3(
        v_op_6883_,
        v_a_6884_,
        v_f_6885_,
        v___y_6886_,
        v___y_6887_,
        v___y_6888_,
        v___y_6889_,
    );
    leanh::lean_dec(v___y_6889_);
    leanh::lean_dec_ref(v___y_6888_);
    leanh::lean_dec(v___y_6887_);
    leanh::lean_dec_ref(v___y_6886_);
    return v_res_6891_;
}
pub unsafe fn l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(
    mut v_op_6892_: *mut leanh::LeanObject,
    mut v_e_6893_: *mut leanh::LeanObject,
    mut v_a_6894_: *mut leanh::LeanObject,
    mut v_a_6895_: *mut leanh::LeanObject,
    mut v_a_6896_: *mut leanh::LeanObject,
    mut v_a_6897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_e_6893_) {
        0 => {
            let mut v___x_6899_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6900_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v_e_6893_, 1);
            leanh::lean_dec_ref(v_op_6892_);
            v___x_6899_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___closed__0;
            v___x_6900_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_6900_, 0, v___x_6899_);
            return v___x_6900_;
        }
        7 => {
            let mut v___f_6901_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6902_: u8 = 0;
            let mut v___x_6903_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___f_6901_ = leanh::lean_alloc_closure(
                l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed
                    as *mut core::ffi::c_void,
                8,
                1,
            );
            leanh::lean_closure_set(v___f_6901_, 0, v_op_6892_);
            v___x_6902_ = 0;
            v___x_6903_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_e_6893_, v___f_6901_, v___x_6902_, v_a_6894_, v_a_6895_, v_a_6896_, v_a_6897_);
            return v___x_6903_;
        }
        6 => {
            let mut v___f_6904_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6905_: u8 = 0;
            let mut v___x_6906_: u8 = 0;
            let mut v___x_6907_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___f_6904_ = leanh::lean_alloc_closure(
                l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed
                    as *mut core::ffi::c_void,
                8,
                1,
            );
            leanh::lean_closure_set(v___f_6904_, 0, v_op_6892_);
            v___x_6905_ = 0;
            v___x_6906_ = 1;
            v___x_6907_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_6893_, v___f_6904_, v___x_6905_, v___x_6906_, v_a_6894_, v_a_6895_, v_a_6896_, v_a_6897_);
            return v___x_6907_;
        }
        8 => {
            let mut v___f_6908_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6909_: u8 = 0;
            let mut v___x_6910_: u8 = 0;
            let mut v___x_6911_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___f_6908_ = leanh::lean_alloc_closure(
                l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed
                    as *mut core::ffi::c_void,
                8,
                1,
            );
            leanh::lean_closure_set(v___f_6908_, 0, v_op_6892_);
            v___x_6909_ = 0;
            v___x_6910_ = 1;
            v___x_6911_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_6893_, v___f_6908_, v___x_6909_, v___x_6910_, v_a_6894_, v_a_6895_, v_a_6896_, v_a_6897_);
            return v___x_6911_;
        }
        _ => {
            let mut v___x_6912_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc_ref(v_op_6892_);
            leanh::lean_inc(v_a_6897_);
            leanh::lean_inc_ref(v_a_6896_);
            leanh::lean_inc(v_a_6895_);
            leanh::lean_inc_ref(v_a_6894_);
            leanh::lean_inc_ref(v_e_6893_);
            v___x_6912_ = leanh::lean_apply_6(
                v_op_6892_,
                v_e_6893_,
                v_a_6894_,
                v_a_6895_,
                v_a_6896_,
                v_a_6897_,
                leanh::lean_box(0),
            );
            if leanh::lean_obj_tag(v___x_6912_) == 0 {
                let mut v_a_6913_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___f_6914_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6915_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6916_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_a_6913_ = leanh::lean_ctor_get(v___x_6912_, 0);
                leanh::lean_inc(v_a_6913_);
                leanh::lean_dec_ref_known(v___x_6912_, 1);
                v___f_6914_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3___boxed
                        as *mut core::ffi::c_void,
                    8,
                    1,
                );
                leanh::lean_closure_set(v___f_6914_, 0, v_op_6892_);
                v___x_6915_ = l_Array_reverse___redArg(v_a_6913_);
                v___x_6916_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v___f_6914_, v___x_6915_, v_e_6893_, v_a_6894_, v_a_6895_, v_a_6896_, v_a_6897_);
                return v___x_6916_;
            } else {
                leanh::lean_dec_ref(v_e_6893_);
                leanh::lean_dec_ref(v_op_6892_);
                return v___x_6912_;
            }
        }
    }
}
pub unsafe fn l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3(
    mut v_op_6917_: *mut leanh::LeanObject,
    mut v_a_6918_: *mut leanh::LeanObject,
    mut v_f_6919_: *mut leanh::LeanObject,
    mut v___y_6920_: *mut leanh::LeanObject,
    mut v___y_6921_: *mut leanh::LeanObject,
    mut v___y_6922_: *mut leanh::LeanObject,
    mut v___y_6923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6929_: u8 = 0;
    let mut v___x_6930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6934_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6925_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(
                    v_op_6917_,
                    v_f_6919_,
                    v___y_6920_,
                    v___y_6921_,
                    v___y_6922_,
                    v___y_6923_,
                );
                if leanh::lean_obj_tag(v___x_6925_) == 0 {
                    v_a_6926_ = leanh::lean_ctor_get(v___x_6925_, 0);
                    v_isSharedCheck_6934_ = (!leanh::lean_is_exclusive(v___x_6925_)) as u8;
                    if v_isSharedCheck_6934_ == 0 {
                        v___x_6928_ = v___x_6925_;
                        v_isShared_6929_ = v_isSharedCheck_6934_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6926_);
                        leanh::lean_dec(v___x_6925_);
                        v___x_6928_ = leanh::lean_box(0);
                        v_isShared_6929_ = v_isSharedCheck_6934_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_a_6918_);
                    return v___x_6925_;
                }
            }
            1 => {
                v___x_6930_ = l_Array_append___redArg(v_a_6918_, v_a_6926_);
                leanh::lean_dec(v_a_6926_);
                if v_isShared_6929_ == 0 {
                    leanh::lean_ctor_set(v___x_6928_, 0, v___x_6930_);
                    v___x_6932_ = v___x_6928_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6933_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6933_, 0, v___x_6930_);
                    v___x_6932_ = v_reuseFailAlloc_6933_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6932_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg___boxed(
    mut v_op_6935_: *mut leanh::LeanObject,
    mut v_as_6936_: *mut leanh::LeanObject,
    mut v_i_6937_: *mut leanh::LeanObject,
    mut v_stop_6938_: *mut leanh::LeanObject,
    mut v_b_6939_: *mut leanh::LeanObject,
    mut v___y_6940_: *mut leanh::LeanObject,
    mut v___y_6941_: *mut leanh::LeanObject,
    mut v___y_6942_: *mut leanh::LeanObject,
    mut v___y_6943_: *mut leanh::LeanObject,
    mut v___y_6944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_6945_: usize = 0;
    let mut v_stop_boxed_6946_: usize = 0;
    let mut v_res_6947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6945_ = leanh::lean_unbox_usize(v_i_6937_);
    leanh::lean_dec(v_i_6937_);
    v_stop_boxed_6946_ = leanh::lean_unbox_usize(v_stop_6938_);
    leanh::lean_dec(v_stop_6938_);
    v_res_6947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_6935_, v_as_6936_, v_i_boxed_6945_, v_stop_boxed_6946_, v_b_6939_, v___y_6940_, v___y_6941_, v___y_6942_, v___y_6943_);
    leanh::lean_dec(v___y_6943_);
    leanh::lean_dec_ref(v___y_6942_);
    leanh::lean_dec(v___y_6941_);
    leanh::lean_dec_ref(v___y_6940_);
    leanh::lean_dec_ref(v_as_6936_);
    return v_res_6947_;
}
pub unsafe fn l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___boxed(
    mut v_op_6948_: *mut leanh::LeanObject,
    mut v_e_6949_: *mut leanh::LeanObject,
    mut v_a_6950_: *mut leanh::LeanObject,
    mut v_a_6951_: *mut leanh::LeanObject,
    mut v_a_6952_: *mut leanh::LeanObject,
    mut v_a_6953_: *mut leanh::LeanObject,
    mut v_a_6954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6955_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(
        v_op_6948_, v_e_6949_, v_a_6950_, v_a_6951_, v_a_6952_, v_a_6953_,
    );
    leanh::lean_dec(v_a_6953_);
    leanh::lean_dec_ref(v_a_6952_);
    leanh::lean_dec(v_a_6951_);
    leanh::lean_dec_ref(v_a_6950_);
    return v_res_6955_;
}
pub unsafe fn l_Lean_Meta_Rewrites_getSubexpressionMatches(
    mut v_00_u03b1_6956_: *mut leanh::LeanObject,
    mut v_op_6957_: *mut leanh::LeanObject,
    mut v_e_6958_: *mut leanh::LeanObject,
    mut v_a_6959_: *mut leanh::LeanObject,
    mut v_a_6960_: *mut leanh::LeanObject,
    mut v_a_6961_: *mut leanh::LeanObject,
    mut v_a_6962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6964_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(
        v_op_6957_, v_e_6958_, v_a_6959_, v_a_6960_, v_a_6961_, v_a_6962_,
    );
    return v___x_6964_;
}
pub unsafe fn l_Lean_Meta_Rewrites_getSubexpressionMatches___boxed(
    mut v_00_u03b1_6965_: *mut leanh::LeanObject,
    mut v_op_6966_: *mut leanh::LeanObject,
    mut v_e_6967_: *mut leanh::LeanObject,
    mut v_a_6968_: *mut leanh::LeanObject,
    mut v_a_6969_: *mut leanh::LeanObject,
    mut v_a_6970_: *mut leanh::LeanObject,
    mut v_a_6971_: *mut leanh::LeanObject,
    mut v_a_6972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6973_ = l_Lean_Meta_Rewrites_getSubexpressionMatches(
        v_00_u03b1_6965_,
        v_op_6966_,
        v_e_6967_,
        v_a_6968_,
        v_a_6969_,
        v_a_6970_,
        v_a_6971_,
    );
    leanh::lean_dec(v_a_6971_);
    leanh::lean_dec_ref(v_a_6970_);
    leanh::lean_dec(v_a_6969_);
    leanh::lean_dec_ref(v_a_6968_);
    return v_res_6973_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(
    mut v_00_u03b1_6974_: *mut leanh::LeanObject,
    mut v_op_6975_: *mut leanh::LeanObject,
    mut v_as_6976_: *mut leanh::LeanObject,
    mut v_i_6977_: usize,
    mut v_stop_6978_: usize,
    mut v_b_6979_: *mut leanh::LeanObject,
    mut v___y_6980_: *mut leanh::LeanObject,
    mut v___y_6981_: *mut leanh::LeanObject,
    mut v___y_6982_: *mut leanh::LeanObject,
    mut v___y_6983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_6975_, v_as_6976_, v_i_6977_, v_stop_6978_, v_b_6979_, v___y_6980_, v___y_6981_, v___y_6982_, v___y_6983_);
    return v___x_6985_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___boxed(
    mut v_00_u03b1_6986_: *mut leanh::LeanObject,
    mut v_op_6987_: *mut leanh::LeanObject,
    mut v_as_6988_: *mut leanh::LeanObject,
    mut v_i_6989_: *mut leanh::LeanObject,
    mut v_stop_6990_: *mut leanh::LeanObject,
    mut v_b_6991_: *mut leanh::LeanObject,
    mut v___y_6992_: *mut leanh::LeanObject,
    mut v___y_6993_: *mut leanh::LeanObject,
    mut v___y_6994_: *mut leanh::LeanObject,
    mut v___y_6995_: *mut leanh::LeanObject,
    mut v___y_6996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_6997_: usize = 0;
    let mut v_stop_boxed_6998_: usize = 0;
    let mut v_res_6999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6997_ = leanh::lean_unbox_usize(v_i_6989_);
    leanh::lean_dec(v_i_6989_);
    v_stop_boxed_6998_ = leanh::lean_unbox_usize(v_stop_6990_);
    leanh::lean_dec(v_stop_6990_);
    v_res_6999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(v_00_u03b1_6986_, v_op_6987_, v_as_6988_, v_i_boxed_6997_, v_stop_boxed_6998_, v_b_6991_, v___y_6992_, v___y_6993_, v___y_6994_, v___y_6995_);
    leanh::lean_dec(v___y_6995_);
    leanh::lean_dec_ref(v___y_6994_);
    leanh::lean_dec(v___y_6993_);
    leanh::lean_dec_ref(v___y_6992_);
    leanh::lean_dec_ref(v_as_6988_);
    return v_res_6999_;
}
pub unsafe fn l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3(
    mut v_00_u03b1_7000_: *mut leanh::LeanObject,
    mut v_f_7001_: *mut leanh::LeanObject,
    mut v_x_7002_: *mut leanh::LeanObject,
    mut v___y_7003_: *mut leanh::LeanObject,
    mut v___y_7004_: *mut leanh::LeanObject,
    mut v___y_7005_: *mut leanh::LeanObject,
    mut v___y_7006_: *mut leanh::LeanObject,
    mut v___y_7007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7009_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_7001_, v_x_7002_, v___y_7003_, v___y_7004_, v___y_7005_, v___y_7006_, v___y_7007_);
    return v___x_7009_;
}
pub unsafe fn l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___boxed(
    mut v_00_u03b1_7010_: *mut leanh::LeanObject,
    mut v_f_7011_: *mut leanh::LeanObject,
    mut v_x_7012_: *mut leanh::LeanObject,
    mut v___y_7013_: *mut leanh::LeanObject,
    mut v___y_7014_: *mut leanh::LeanObject,
    mut v___y_7015_: *mut leanh::LeanObject,
    mut v___y_7016_: *mut leanh::LeanObject,
    mut v___y_7017_: *mut leanh::LeanObject,
    mut v___y_7018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7019_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3(v_00_u03b1_7010_, v_f_7011_, v_x_7012_, v___y_7013_, v___y_7014_, v___y_7015_, v___y_7016_, v___y_7017_);
    leanh::lean_dec(v___y_7017_);
    leanh::lean_dec_ref(v___y_7016_);
    leanh::lean_dec(v___y_7015_);
    leanh::lean_dec_ref(v___y_7014_);
    return v_res_7019_;
}
pub unsafe fn l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3(
    mut v_00_u03b1_7020_: *mut leanh::LeanObject,
    mut v_f_7021_: *mut leanh::LeanObject,
    mut v_init_7022_: *mut leanh::LeanObject,
    mut v_e_7023_: *mut leanh::LeanObject,
    mut v___y_7024_: *mut leanh::LeanObject,
    mut v___y_7025_: *mut leanh::LeanObject,
    mut v___y_7026_: *mut leanh::LeanObject,
    mut v___y_7027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7029_ =
        l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(
            v_f_7021_,
            v_init_7022_,
            v_e_7023_,
            v___y_7024_,
            v___y_7025_,
            v___y_7026_,
            v___y_7027_,
        );
    return v___x_7029_;
}
pub unsafe fn l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___boxed(
    mut v_00_u03b1_7030_: *mut leanh::LeanObject,
    mut v_f_7031_: *mut leanh::LeanObject,
    mut v_init_7032_: *mut leanh::LeanObject,
    mut v_e_7033_: *mut leanh::LeanObject,
    mut v___y_7034_: *mut leanh::LeanObject,
    mut v___y_7035_: *mut leanh::LeanObject,
    mut v___y_7036_: *mut leanh::LeanObject,
    mut v___y_7037_: *mut leanh::LeanObject,
    mut v___y_7038_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7039_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3(
        v_00_u03b1_7030_,
        v_f_7031_,
        v_init_7032_,
        v_e_7033_,
        v___y_7034_,
        v___y_7035_,
        v___y_7036_,
        v___y_7037_,
    );
    leanh::lean_dec(v___y_7037_);
    leanh::lean_dec_ref(v___y_7036_);
    leanh::lean_dec(v___y_7035_);
    leanh::lean_dec_ref(v___y_7034_);
    return v_res_7039_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(
    mut v_sz_7040_: usize,
    mut v_i_7041_: usize,
    mut v_bs_7042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7043_: u8 = 0;
    let mut v_v_7044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7049_: u8 = 0;
    let mut v___x_7050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_7051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7055_: usize = 0;
    let mut v___x_7056_: usize = 0;
    let mut v___x_7057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7060_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7043_ = lean_usize_dec_lt(v_i_7041_, v_sz_7040_);
                if v___x_7043_ == 0 {
                    return v_bs_7042_;
                } else {
                    v_v_7044_ = lean_array_uget(v_bs_7042_, v_i_7041_);
                    v_fst_7045_ = leanh::lean_ctor_get(v_v_7044_, 0);
                    v_snd_7046_ = leanh::lean_ctor_get(v_v_7044_, 1);
                    v_isSharedCheck_7060_ = (!leanh::lean_is_exclusive(v_v_7044_)) as u8;
                    if v_isSharedCheck_7060_ == 0 {
                        v___x_7048_ = v_v_7044_;
                        v_isShared_7049_ = v_isSharedCheck_7060_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_7046_);
                        leanh::lean_inc(v_fst_7045_);
                        leanh::lean_dec(v_v_7044_);
                        v___x_7048_ = leanh::lean_box(0);
                        v_isShared_7049_ = v_isSharedCheck_7060_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7050_ = leanh::lean_unsigned_to_nat(0);
                v_bs_x27_7051_ = lean_array_uset(v_bs_7042_, v_i_7041_, v___x_7050_);
                v___x_7052_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7052_, 0, v_fst_7045_);
                if v_isShared_7049_ == 0 {
                    leanh::lean_ctor_set(v___x_7048_, 0, v___x_7052_);
                    v___x_7054_ = v___x_7048_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7059_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7059_, 0, v___x_7052_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7059_, 1, v_snd_7046_);
                    v___x_7054_ = v_reuseFailAlloc_7059_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7055_ = 1usize;
                v___x_7056_ = lean_usize_add(v_i_7041_, v___x_7055_);
                v___x_7057_ = lean_array_uset(v_bs_x27_7051_, v_i_7041_, v___x_7054_);
                v_i_7041_ = v___x_7056_;
                v_bs_7042_ = v___x_7057_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3___boxed(
    mut v_sz_7061_: *mut leanh::LeanObject,
    mut v_i_7062_: *mut leanh::LeanObject,
    mut v_bs_7063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_7064_: usize = 0;
    let mut v_i_boxed_7065_: usize = 0;
    let mut v_res_7066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7064_ = leanh::lean_unbox_usize(v_sz_7061_);
    leanh::lean_dec(v_sz_7061_);
    v_i_boxed_7065_ = leanh::lean_unbox_usize(v_i_7062_);
    leanh::lean_dec(v_i_7062_);
    v_res_7066_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(v_sz_boxed_7064_, v_i_boxed_7065_, v_bs_7063_);
    return v_res_7066_;
}
pub unsafe fn l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(
    mut v_xs_7067_: *mut leanh::LeanObject,
    mut v_j_7068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_7069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_7070_: u8 = 0;
    let mut v___x_7071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_7074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_7075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7079_: u8 = 0;
    let mut v___x_7080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_7069_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_7070_ = lean_nat_dec_eq(v_j_7068_, v_zero_7069_);
                if v_isZero_7070_ == 1 {
                    leanh::lean_dec(v_j_7068_);
                    return v_xs_7067_;
                } else {
                    v___x_7071_ = lean_array_fget_borrowed(v_xs_7067_, v_j_7068_);
                    v_snd_7072_ = leanh::lean_ctor_get(v___x_7071_, 1);
                    v_snd_7073_ = leanh::lean_ctor_get(v_snd_7072_, 1);
                    v_one_7074_ = leanh::lean_unsigned_to_nat(1);
                    v_n_7075_ = lean_nat_sub(v_j_7068_, v_one_7074_);
                    v___x_7076_ = lean_array_fget_borrowed(v_xs_7067_, v_n_7075_);
                    v_snd_7077_ = leanh::lean_ctor_get(v___x_7076_, 1);
                    v_snd_7078_ = leanh::lean_ctor_get(v_snd_7077_, 1);
                    v___x_7079_ = lean_nat_dec_lt(v_snd_7078_, v_snd_7073_);
                    if v___x_7079_ == 0 {
                        leanh::lean_dec(v_n_7075_);
                        leanh::lean_dec(v_j_7068_);
                        return v_xs_7067_;
                    } else {
                        v___x_7080_ = lean_array_fswap(v_xs_7067_, v_j_7068_, v_n_7075_);
                        leanh::lean_dec(v_j_7068_);
                        v_xs_7067_ = v___x_7080_;
                        v_j_7068_ = v_n_7075_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0(
    mut v_xs_7082_: *mut leanh::LeanObject,
    mut v_i_7083_: *mut leanh::LeanObject,
    mut v_fuel_7084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_7085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_7086_: u8 = 0;
    let mut v___x_7087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7088_: u8 = 0;
    let mut v_one_7089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_7090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_7085_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_7086_ = lean_nat_dec_eq(v_fuel_7084_, v_zero_7085_);
                if v_isZero_7086_ == 1 {
                    leanh::lean_dec(v_fuel_7084_);
                    leanh::lean_dec(v_i_7083_);
                    return v_xs_7082_;
                } else {
                    v___x_7087_ = lean_array_get_size(v_xs_7082_);
                    v___x_7088_ = lean_nat_dec_lt(v_i_7083_, v___x_7087_);
                    if v___x_7088_ == 0 {
                        leanh::lean_dec(v_fuel_7084_);
                        leanh::lean_dec(v_i_7083_);
                        return v_xs_7082_;
                    } else {
                        v_one_7089_ = leanh::lean_unsigned_to_nat(1);
                        v_n_7090_ = lean_nat_sub(v_fuel_7084_, v_one_7089_);
                        leanh::lean_dec(v_fuel_7084_);
                        leanh::lean_inc(v_i_7083_);
                        v___x_7091_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(v_xs_7082_, v_i_7083_);
                        v___x_7092_ = lean_nat_add(v_i_7083_, v_one_7089_);
                        leanh::lean_dec(v_i_7083_);
                        v_xs_7082_ = v___x_7091_;
                        v_i_7083_ = v___x_7092_;
                        v_fuel_7084_ = v_n_7090_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(
    mut v_sz_7094_: usize,
    mut v_i_7095_: usize,
    mut v_bs_7096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7097_: u8 = 0;
    let mut v_v_7098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7103_: u8 = 0;
    let mut v___x_7104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_7105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7109_: usize = 0;
    let mut v___x_7110_: usize = 0;
    let mut v___x_7111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7114_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7097_ = lean_usize_dec_lt(v_i_7095_, v_sz_7094_);
                if v___x_7097_ == 0 {
                    return v_bs_7096_;
                } else {
                    v_v_7098_ = lean_array_uget(v_bs_7096_, v_i_7095_);
                    v_fst_7099_ = leanh::lean_ctor_get(v_v_7098_, 0);
                    v_snd_7100_ = leanh::lean_ctor_get(v_v_7098_, 1);
                    v_isSharedCheck_7114_ = (!leanh::lean_is_exclusive(v_v_7098_)) as u8;
                    if v_isSharedCheck_7114_ == 0 {
                        v___x_7102_ = v_v_7098_;
                        v_isShared_7103_ = v_isSharedCheck_7114_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_7100_);
                        leanh::lean_inc(v_fst_7099_);
                        leanh::lean_dec(v_v_7098_);
                        v___x_7102_ = leanh::lean_box(0);
                        v_isShared_7103_ = v_isSharedCheck_7114_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7104_ = leanh::lean_unsigned_to_nat(0);
                v_bs_x27_7105_ = lean_array_uset(v_bs_7096_, v_i_7095_, v___x_7104_);
                v___x_7106_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7106_, 0, v_fst_7099_);
                if v_isShared_7103_ == 0 {
                    leanh::lean_ctor_set(v___x_7102_, 0, v___x_7106_);
                    v___x_7108_ = v___x_7102_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7113_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7113_, 0, v___x_7106_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7113_, 1, v_snd_7100_);
                    v___x_7108_ = v_reuseFailAlloc_7113_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7109_ = 1usize;
                v___x_7110_ = lean_usize_add(v_i_7095_, v___x_7109_);
                v___x_7111_ = lean_array_uset(v_bs_x27_7105_, v_i_7095_, v___x_7108_);
                v_i_7095_ = v___x_7110_;
                v_bs_7096_ = v___x_7111_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2___boxed(
    mut v_sz_7115_: *mut leanh::LeanObject,
    mut v_i_7116_: *mut leanh::LeanObject,
    mut v_bs_7117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_7118_: usize = 0;
    let mut v_i_boxed_7119_: usize = 0;
    let mut v_res_7120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7118_ = leanh::lean_unbox_usize(v_sz_7115_);
    leanh::lean_dec(v_sz_7115_);
    v_i_boxed_7119_ = leanh::lean_unbox_usize(v_i_7116_);
    leanh::lean_dec(v_i_7116_);
    v_res_7120_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(v_sz_boxed_7118_, v_i_boxed_7119_, v_bs_7117_);
    return v_res_7120_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(
    mut v_forbidden_7121_: *mut leanh::LeanObject,
    mut v_as_7122_: *mut leanh::LeanObject,
    mut v_sz_7123_: usize,
    mut v_i_7124_: usize,
    mut v_b_7125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_7128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7129_: usize = 0;
    let mut v___x_7130_: usize = 0;
    let mut v___x_7132_: u8 = 0;
    let mut v___x_7133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7141_: u8 = 0;
    let mut v_fst_7142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7145_: u8 = 0;
    let mut v_fst_7146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7150_: u8 = 0;
    let mut v___x_7153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7163_: u8 = 0;
    let mut v___x_7164_: u8 = 0;
    let mut v___x_7165_: u8 = 0;
    let mut v___x_7166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7170_: u8 = 0;
    let mut v___x_7171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7177_: u8 = 0;
    let mut v___x_7179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7182_: u8 = 0;
    let mut v_unused_7183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7185_: u8 = 0;
    let mut v_isSharedCheck_7186_: u8 = 0;
    let mut v_unused_7187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7188_: u8 = 0;
    let mut v_unused_7189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7132_ = lean_usize_dec_lt(v_i_7124_, v_sz_7123_);
                if v___x_7132_ == 0 {
                    v___x_7133_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7133_, 0, v_b_7125_);
                    return v___x_7133_;
                } else {
                    v_a_7134_ = lean_array_uget(v_as_7122_, v_i_7124_);
                    v_snd_7135_ = leanh::lean_ctor_get(v_a_7134_, 1);
                    leanh::lean_inc(v_snd_7135_);
                    v_snd_7136_ = leanh::lean_ctor_get(v_b_7125_, 1);
                    leanh::lean_inc(v_snd_7136_);
                    v_fst_7137_ = leanh::lean_ctor_get(v_a_7134_, 0);
                    v_fst_7138_ = leanh::lean_ctor_get(v_snd_7135_, 0);
                    v_isSharedCheck_7188_ = (!leanh::lean_is_exclusive(v_snd_7135_)) as u8;
                    if v_isSharedCheck_7188_ == 0 {
                        v_unused_7189_ = leanh::lean_ctor_get(v_snd_7135_, 1);
                        leanh::lean_dec(v_unused_7189_);
                        v___x_7140_ = v_snd_7135_;
                        v_isShared_7141_ = v_isSharedCheck_7188_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_7138_);
                        leanh::lean_dec(v_snd_7135_);
                        v___x_7140_ = leanh::lean_box(0);
                        v_isShared_7141_ = v_isSharedCheck_7188_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7129_ = 1usize;
                v___x_7130_ = lean_usize_add(v_i_7124_, v___x_7129_);
                v_i_7124_ = v___x_7130_;
                v_b_7125_ = v_a_7128_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_7142_ = leanh::lean_ctor_get(v_b_7125_, 0);
                v_isSharedCheck_7186_ = (!leanh::lean_is_exclusive(v_b_7125_)) as u8;
                if v_isSharedCheck_7186_ == 0 {
                    v_unused_7187_ = leanh::lean_ctor_get(v_b_7125_, 1);
                    leanh::lean_dec(v_unused_7187_);
                    v___x_7144_ = v_b_7125_;
                    v_isShared_7145_ = v_isSharedCheck_7186_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_7142_);
                    leanh::lean_dec(v_b_7125_);
                    v___x_7144_ = leanh::lean_box(0);
                    v_isShared_7145_ = v_isSharedCheck_7186_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_7146_ = leanh::lean_ctor_get(v_snd_7136_, 0);
                v_snd_7147_ = leanh::lean_ctor_get(v_snd_7136_, 1);
                v_isSharedCheck_7185_ = (!leanh::lean_is_exclusive(v_snd_7136_)) as u8;
                if v_isSharedCheck_7185_ == 0 {
                    v___x_7149_ = v_snd_7136_;
                    v_isShared_7150_ = v_isSharedCheck_7185_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_7147_);
                    leanh::lean_inc(v_fst_7146_);
                    leanh::lean_dec(v_snd_7136_);
                    v___x_7149_ = leanh::lean_box(0);
                    v_isShared_7150_ = v_isSharedCheck_7185_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7163_ = l_Lean_NameSet_contains(v_forbidden_7121_, v_fst_7137_);
                if v___x_7163_ == 0 {
                    leanh::lean_inc(v_fst_7137_);
                    v___x_7164_ = (leanh::lean_unbox(v_fst_7138_) as u8);
                    leanh::lean_dec(v_fst_7138_);
                    if v___x_7164_ == 0 {
                        leanh::lean_del_object(v___x_7149_);
                        leanh::lean_del_object(v___x_7144_);
                        v___x_7165_ = l_Lean_NameSet_contains(v_fst_7142_, v_fst_7137_);
                        if v___x_7165_ == 0 {
                            if v___x_7132_ == 0 {
                                leanh::lean_dec(v_fst_7137_);
                                leanh::lean_dec(v_a_7134_);
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_del_object(v___x_7140_);
                                v___x_7166_ = lean_array_push(v_snd_7147_, v_a_7134_);
                                v___x_7167_ = l_Lean_NameSet_insert(v_fst_7142_, v_fst_7137_);
                                v___x_7168_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_7168_, 0, v_fst_7146_);
                                leanh::lean_ctor_set(v___x_7168_, 1, v___x_7166_);
                                v___x_7169_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_7169_, 0, v___x_7167_);
                                leanh::lean_ctor_set(v___x_7169_, 1, v___x_7168_);
                                v_a_7128_ = v___x_7169_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_fst_7137_);
                            leanh::lean_dec(v_a_7134_);
                            state = 8;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_7140_);
                        v___x_7170_ = l_Lean_NameSet_contains(v_fst_7146_, v_fst_7137_);
                        if v___x_7170_ == 0 {
                            if v___x_7132_ == 0 {
                                leanh::lean_dec(v_fst_7137_);
                                leanh::lean_dec(v_a_7134_);
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_del_object(v___x_7149_);
                                leanh::lean_del_object(v___x_7144_);
                                v___x_7171_ = lean_array_push(v_snd_7147_, v_a_7134_);
                                v___x_7172_ = l_Lean_NameSet_insert(v_fst_7146_, v_fst_7137_);
                                v___x_7173_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_7173_, 0, v___x_7172_);
                                leanh::lean_ctor_set(v___x_7173_, 1, v___x_7171_);
                                v___x_7174_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_7174_, 0, v_fst_7142_);
                                leanh::lean_ctor_set(v___x_7174_, 1, v___x_7173_);
                                v_a_7128_ = v___x_7174_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_fst_7137_);
                            leanh::lean_dec(v_a_7134_);
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_7149_);
                    leanh::lean_del_object(v___x_7144_);
                    leanh::lean_del_object(v___x_7140_);
                    leanh::lean_dec(v_fst_7138_);
                    v_isSharedCheck_7182_ = (!leanh::lean_is_exclusive(v_a_7134_)) as u8;
                    if v_isSharedCheck_7182_ == 0 {
                        v_unused_7183_ = leanh::lean_ctor_get(v_a_7134_, 1);
                        leanh::lean_dec(v_unused_7183_);
                        v_unused_7184_ = leanh::lean_ctor_get(v_a_7134_, 0);
                        leanh::lean_dec(v_unused_7184_);
                        v___x_7176_ = v_a_7134_;
                        v_isShared_7177_ = v_isSharedCheck_7182_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_7134_);
                        v___x_7176_ = leanh::lean_box(0);
                        v_isShared_7177_ = v_isSharedCheck_7182_;
                        state = 10;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_7150_ == 0 {
                    v___x_7153_ = v___x_7149_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7157_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7157_, 0, v_fst_7146_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7157_, 1, v_snd_7147_);
                    v___x_7153_ = v_reuseFailAlloc_7157_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_7145_ == 0 {
                    leanh::lean_ctor_set(v___x_7144_, 1, v___x_7153_);
                    v___x_7155_ = v___x_7144_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7156_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7156_, 0, v_fst_7142_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7156_, 1, v___x_7153_);
                    v___x_7155_ = v_reuseFailAlloc_7156_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_a_7128_ = v___x_7155_;
                state = 1;
                continue;
            }
            8 => {
                if v_isShared_7141_ == 0 {
                    leanh::lean_ctor_set(v___x_7140_, 1, v_snd_7147_);
                    leanh::lean_ctor_set(v___x_7140_, 0, v_fst_7146_);
                    v___x_7160_ = v___x_7140_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7162_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7162_, 0, v_fst_7146_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7162_, 1, v_snd_7147_);
                    v___x_7160_ = v_reuseFailAlloc_7162_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_7161_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7161_, 0, v_fst_7142_);
                leanh::lean_ctor_set(v___x_7161_, 1, v___x_7160_);
                v_a_7128_ = v___x_7161_;
                state = 1;
                continue;
            }
            10 => {
                if v_isShared_7177_ == 0 {
                    leanh::lean_ctor_set(v___x_7176_, 1, v_snd_7147_);
                    leanh::lean_ctor_set(v___x_7176_, 0, v_fst_7146_);
                    v___x_7179_ = v___x_7176_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_7181_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7181_, 0, v_fst_7146_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7181_, 1, v_snd_7147_);
                    v___x_7179_ = v_reuseFailAlloc_7181_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_7180_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7180_, 0, v_fst_7142_);
                leanh::lean_ctor_set(v___x_7180_, 1, v___x_7179_);
                v_a_7128_ = v___x_7180_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg___boxed(
    mut v_forbidden_7190_: *mut leanh::LeanObject,
    mut v_as_7191_: *mut leanh::LeanObject,
    mut v_sz_7192_: *mut leanh::LeanObject,
    mut v_i_7193_: *mut leanh::LeanObject,
    mut v_b_7194_: *mut leanh::LeanObject,
    mut v___y_7195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_7196_: usize = 0;
    let mut v_i_boxed_7197_: usize = 0;
    let mut v_res_7198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7196_ = leanh::lean_unbox_usize(v_sz_7192_);
    leanh::lean_dec(v_sz_7192_);
    v_i_boxed_7197_ = leanh::lean_unbox_usize(v_i_7193_);
    leanh::lean_dec(v_i_7193_);
    v_res_7198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_7190_, v_as_7191_, v_sz_boxed_7196_, v_i_boxed_7197_, v_b_7194_);
    leanh::lean_dec_ref(v_as_7191_);
    leanh::lean_dec(v_forbidden_7190_);
    return v_res_7198_;
}
pub unsafe fn _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_7202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7202_ =
        l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__1;
    v___x_7203_ = l_Lean_MessageData_ofFormat(v___x_7202_);
    return v___x_7203_;
}
pub unsafe fn _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_7204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7204_ = leanh::lean_box(1);
    v___x_7205_ = l_Lean_MessageData_ofFormat(v___x_7204_);
    return v___x_7205_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4(
    mut v_a_7208_: *mut leanh::LeanObject,
    mut v_a_7209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_7211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7216_: u8 = 0;
    let mut v_fst_7217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7220_: u8 = 0;
    let mut v_fst_7221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7225_: u8 = 0;
    let mut v___x_7226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7250_: u8 = 0;
    let mut v___x_7251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7255_: u8 = 0;
    let mut v_isSharedCheck_7256_: u8 = 0;
    let mut v_unused_7257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7258_: u8 = 0;
    let mut v_unused_7259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_7208_) == 0 {
                    v___x_7210_ = l_List_reverse___redArg(v_a_7209_);
                    return v___x_7210_;
                } else {
                    v_head_7211_ = leanh::lean_ctor_get(v_a_7208_, 0);
                    leanh::lean_inc(v_head_7211_);
                    v_snd_7212_ = leanh::lean_ctor_get(v_head_7211_, 1);
                    leanh::lean_inc(v_snd_7212_);
                    v_tail_7213_ = leanh::lean_ctor_get(v_a_7208_, 1);
                    v_isSharedCheck_7258_ = (!leanh::lean_is_exclusive(v_a_7208_)) as u8;
                    if v_isSharedCheck_7258_ == 0 {
                        v_unused_7259_ = leanh::lean_ctor_get(v_a_7208_, 0);
                        leanh::lean_dec(v_unused_7259_);
                        v___x_7215_ = v_a_7208_;
                        v_isShared_7216_ = v_isSharedCheck_7258_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_7213_);
                        leanh::lean_dec(v_a_7208_);
                        v___x_7215_ = leanh::lean_box(0);
                        v_isShared_7216_ = v_isSharedCheck_7258_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_7217_ = leanh::lean_ctor_get(v_head_7211_, 0);
                v_isSharedCheck_7256_ = (!leanh::lean_is_exclusive(v_head_7211_)) as u8;
                if v_isSharedCheck_7256_ == 0 {
                    v_unused_7257_ = leanh::lean_ctor_get(v_head_7211_, 1);
                    leanh::lean_dec(v_unused_7257_);
                    v___x_7219_ = v_head_7211_;
                    v_isShared_7220_ = v_isSharedCheck_7256_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_7217_);
                    leanh::lean_dec(v_head_7211_);
                    v___x_7219_ = leanh::lean_box(0);
                    v_isShared_7220_ = v_isSharedCheck_7256_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_7221_ = leanh::lean_ctor_get(v_snd_7212_, 0);
                v_snd_7222_ = leanh::lean_ctor_get(v_snd_7212_, 1);
                v_isSharedCheck_7255_ = (!leanh::lean_is_exclusive(v_snd_7212_)) as u8;
                if v_isSharedCheck_7255_ == 0 {
                    v___x_7224_ = v_snd_7212_;
                    v_isShared_7225_ = v_isSharedCheck_7255_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_7222_);
                    leanh::lean_inc(v_fst_7221_);
                    leanh::lean_dec(v_snd_7212_);
                    v___x_7224_ = leanh::lean_box(0);
                    v_isShared_7225_ = v_isSharedCheck_7255_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7226_ = l_Lean_MessageData_ofName(v_fst_7217_);
                v___x_7227_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2_once), _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2);
                if v_isShared_7225_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_7224_, 7);
                    leanh::lean_ctor_set(v___x_7224_, 1, v___x_7227_);
                    leanh::lean_ctor_set(v___x_7224_, 0, v___x_7226_);
                    v___x_7229_ = v___x_7224_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7254_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7254_, 0, v___x_7226_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7254_, 1, v___x_7227_);
                    v___x_7229_ = v_reuseFailAlloc_7254_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7230_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3_once), _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3);
                if v_isShared_7220_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_7219_, 7);
                    leanh::lean_ctor_set(v___x_7219_, 1, v___x_7230_);
                    leanh::lean_ctor_set(v___x_7219_, 0, v___x_7229_);
                    v___x_7232_ = v___x_7219_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7253_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7253_, 0, v___x_7229_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7253_, 1, v___x_7230_);
                    v___x_7232_ = v_reuseFailAlloc_7253_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_7250_ = (leanh::lean_unbox(v_fst_7221_) as u8);
                leanh::lean_dec(v_fst_7221_);
                if v___x_7250_ == 0 {
                    v___x_7251_ = l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__4;
                    v___y_7234_ = v___x_7251_;
                    state = 6;
                    continue;
                } else {
                    v___x_7252_ = l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__5;
                    v___y_7234_ = v___x_7252_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                leanh::lean_inc_ref(v___y_7234_);
                v___x_7235_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7235_, 0, v___y_7234_);
                v___x_7236_ = l_Lean_MessageData_ofFormat(v___x_7235_);
                v___x_7237_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7237_, 0, v___x_7236_);
                leanh::lean_ctor_set(v___x_7237_, 1, v___x_7227_);
                v___x_7238_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7238_, 0, v___x_7237_);
                leanh::lean_ctor_set(v___x_7238_, 1, v___x_7230_);
                v___x_7239_ = l_Nat_reprFast(v_snd_7222_);
                v___x_7240_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7240_, 0, v___x_7239_);
                v___x_7241_ = l_Lean_MessageData_ofFormat(v___x_7240_);
                v___x_7242_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7242_, 0, v___x_7238_);
                leanh::lean_ctor_set(v___x_7242_, 1, v___x_7241_);
                v___x_7243_ = l_Lean_MessageData_paren(v___x_7242_);
                v___x_7244_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7244_, 0, v___x_7232_);
                leanh::lean_ctor_set(v___x_7244_, 1, v___x_7243_);
                v___x_7245_ = l_Lean_MessageData_paren(v___x_7244_);
                if v_isShared_7216_ == 0 {
                    leanh::lean_ctor_set(v___x_7215_, 1, v_a_7209_);
                    leanh::lean_ctor_set(v___x_7215_, 0, v___x_7245_);
                    v___x_7247_ = v___x_7215_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7249_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7249_, 0, v___x_7245_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7249_, 1, v_a_7209_);
                    v___x_7247_ = v_reuseFailAlloc_7249_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_a_7208_ = v_tail_7213_;
                v_a_7209_ = v___x_7247_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_7262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7262_ = l_Lean_Meta_Rewrites_rewriteCandidates___closed__0;
    v___x_7263_ = l_Lean_NameSet_empty;
    v___x_7264_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7264_, 0, v___x_7263_);
    leanh::lean_ctor_set(v___x_7264_, 1, v___x_7262_);
    return v___x_7264_;
}
pub unsafe fn _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_7265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7265_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Rewrites_rewriteCandidates___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Rewrites_rewriteCandidates___closed__1_once),
        _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__1,
    );
    v___x_7266_ = l_Lean_NameSet_empty;
    v___x_7267_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7267_, 0, v___x_7266_);
    leanh::lean_ctor_set(v___x_7267_, 1, v___x_7265_);
    return v___x_7267_;
}
pub unsafe fn _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_7268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7268_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_;
    v___x_7269_ = l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4;
    v___x_7270_ = l_Lean_Name_append(v___x_7269_, v___x_7268_);
    return v___x_7270_;
}
pub unsafe fn _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_7272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7272_ = l_Lean_Meta_Rewrites_rewriteCandidates___closed__4;
    v___x_7273_ = l_Lean_stringToMessageData(v___x_7272_);
    return v___x_7273_;
}
pub unsafe fn l_Lean_Meta_Rewrites_rewriteCandidates(
    mut v_hyps_7274_: *mut leanh::LeanObject,
    mut v_moduleRef_7275_: *mut leanh::LeanObject,
    mut v_target_7276_: *mut leanh::LeanObject,
    mut v_forbidden_7277_: *mut leanh::LeanObject,
    mut v_a_7278_: *mut leanh::LeanObject,
    mut v_a_7279_: *mut leanh::LeanObject,
    mut v_a_7280_: *mut leanh::LeanObject,
    mut v_a_7281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7290_: usize = 0;
    let mut v___x_7291_: usize = 0;
    let mut v___x_7292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7296_: u8 = 0;
    let mut v_snd_7297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7301_: u8 = 0;
    let mut v_sz_7303_: usize = 0;
    let mut v___x_7304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7305_: usize = 0;
    let mut v___x_7306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_7311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_7312_: u8 = 0;
    let mut v_inheritedTraceOptions_7313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7316_: u8 = 0;
    let mut v___x_7317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7328_: u8 = 0;
    let mut v___x_7330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7332_: u8 = 0;
    let mut v_reuseFailAlloc_7333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7334_: u8 = 0;
    let mut v_unused_7335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7336_: u8 = 0;
    let mut v_a_7337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7340_: u8 = 0;
    let mut v___x_7342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7344_: u8 = 0;
    let mut v_a_7345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7348_: u8 = 0;
    let mut v___x_7350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7352_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7283_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Rewrites_rwFindDecls___boxed as *mut core::ffi::c_void,
                    7,
                    1,
                );
                leanh::lean_closure_set(v___x_7283_, 0, v_moduleRef_7275_);
                v___x_7284_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(
                    v___x_7283_,
                    v_target_7276_,
                    v_a_7278_,
                    v_a_7279_,
                    v_a_7280_,
                    v_a_7281_,
                );
                if leanh::lean_obj_tag(v___x_7284_) == 0 {
                    v_a_7285_ = leanh::lean_ctor_get(v___x_7284_, 0);
                    leanh::lean_inc(v_a_7285_);
                    leanh::lean_dec_ref_known(v___x_7284_, 1);
                    v___x_7286_ = leanh::lean_unsigned_to_nat(0);
                    v___x_7287_ = lean_array_get_size(v_a_7285_);
                    v___x_7288_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0(v_a_7285_, v___x_7286_, v___x_7287_);
                    v___x_7289_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Rewrites_rewriteCandidates___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Rewrites_rewriteCandidates___closed__2_once
                        ),
                        _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__2,
                    );
                    v_sz_7290_ = lean_array_size(v___x_7288_);
                    v___x_7291_ = 0usize;
                    v___x_7292_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_7277_, v___x_7288_, v_sz_7290_, v___x_7291_, v___x_7289_);
                    leanh::lean_dec_ref(v___x_7288_);
                    if leanh::lean_obj_tag(v___x_7292_) == 0 {
                        v_a_7293_ = leanh::lean_ctor_get(v___x_7292_, 0);
                        v_isSharedCheck_7336_ =
                            (!leanh::lean_is_exclusive(v___x_7292_)) as u8;
                        if v_isSharedCheck_7336_ == 0 {
                            v___x_7295_ = v___x_7292_;
                            v_isShared_7296_ = v_isSharedCheck_7336_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7293_);
                            leanh::lean_dec(v___x_7292_);
                            v___x_7295_ = leanh::lean_box(0);
                            v_isShared_7296_ = v_isSharedCheck_7336_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_hyps_7274_);
                        v_a_7337_ = leanh::lean_ctor_get(v___x_7292_, 0);
                        v_isSharedCheck_7344_ =
                            (!leanh::lean_is_exclusive(v___x_7292_)) as u8;
                        if v_isSharedCheck_7344_ == 0 {
                            v___x_7339_ = v___x_7292_;
                            v_isShared_7340_ = v_isSharedCheck_7344_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7337_);
                            leanh::lean_dec(v___x_7292_);
                            v___x_7339_ = leanh::lean_box(0);
                            v_isShared_7340_ = v_isSharedCheck_7344_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_hyps_7274_);
                    v_a_7345_ = leanh::lean_ctor_get(v___x_7284_, 0);
                    v_isSharedCheck_7352_ = (!leanh::lean_is_exclusive(v___x_7284_)) as u8;
                    if v_isSharedCheck_7352_ == 0 {
                        v___x_7347_ = v___x_7284_;
                        v_isShared_7348_ = v_isSharedCheck_7352_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7345_);
                        leanh::lean_dec(v___x_7284_);
                        v___x_7347_ = leanh::lean_box(0);
                        v_isShared_7348_ = v_isSharedCheck_7352_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_7297_ = leanh::lean_ctor_get(v_a_7293_, 1);
                leanh::lean_inc(v_snd_7297_);
                leanh::lean_dec(v_a_7293_);
                v_snd_7298_ = leanh::lean_ctor_get(v_snd_7297_, 1);
                v_isSharedCheck_7334_ = (!leanh::lean_is_exclusive(v_snd_7297_)) as u8;
                if v_isSharedCheck_7334_ == 0 {
                    v_unused_7335_ = leanh::lean_ctor_get(v_snd_7297_, 0);
                    leanh::lean_dec(v_unused_7335_);
                    v___x_7300_ = v_snd_7297_;
                    v_isShared_7301_ = v_isSharedCheck_7334_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_7298_);
                    leanh::lean_dec(v_snd_7297_);
                    v___x_7300_ = leanh::lean_box(0);
                    v_isShared_7301_ = v_isSharedCheck_7334_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_options_7311_ = leanh::lean_ctor_get(v_a_7280_, 2);
                v_hasTrace_7312_ = leanh::lean_ctor_get_uint8(
                    v_options_7311_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_7312_ == 0 {
                    leanh::lean_del_object(v___x_7300_);
                    state = 3;
                    continue;
                } else {
                    v_inheritedTraceOptions_7313_ = leanh::lean_ctor_get(v_a_7280_, 13);
                    v___x_7314_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_;
                    v___x_7315_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Rewrites_rewriteCandidates___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Rewrites_rewriteCandidates___closed__3_once
                        ),
                        _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__3,
                    );
                    v___x_7316_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_7313_,
                        v_options_7311_,
                        v___x_7315_,
                    );
                    if v___x_7316_ == 0 {
                        leanh::lean_del_object(v___x_7300_);
                        state = 3;
                        continue;
                    } else {
                        v___x_7317_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Rewrites_rewriteCandidates___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Rewrites_rewriteCandidates___closed__5_once
                            ),
                            _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__5,
                        );
                        leanh::lean_inc(v_snd_7298_);
                        v___x_7318_ = lean_array_to_list(v_snd_7298_);
                        v___x_7319_ = leanh::lean_box(0);
                        v___x_7320_ =
                            l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4(
                                v___x_7318_,
                                v___x_7319_,
                            );
                        v___x_7321_ = l_Lean_MessageData_ofList(v___x_7320_);
                        if v_isShared_7301_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_7300_, 7);
                            leanh::lean_ctor_set(v___x_7300_, 1, v___x_7321_);
                            leanh::lean_ctor_set(v___x_7300_, 0, v___x_7317_);
                            v___x_7323_ = v___x_7300_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_7333_ =
                                leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7333_, 0, v___x_7317_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7333_, 1, v___x_7321_);
                            v___x_7323_ = v_reuseFailAlloc_7333_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v_sz_7303_ = lean_array_size(v_hyps_7274_);
                v___x_7304_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(v_sz_7303_, v___x_7291_, v_hyps_7274_);
                v_sz_7305_ = lean_array_size(v_snd_7298_);
                v___x_7306_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(v_sz_7305_, v___x_7291_, v_snd_7298_);
                v___x_7307_ = l_Array_append___redArg(v___x_7304_, v___x_7306_);
                leanh::lean_dec_ref(v___x_7306_);
                if v_isShared_7296_ == 0 {
                    leanh::lean_ctor_set(v___x_7295_, 0, v___x_7307_);
                    v___x_7309_ = v___x_7295_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7310_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7310_, 0, v___x_7307_);
                    v___x_7309_ = v_reuseFailAlloc_7310_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7309_;
            }
            5 => {
                v___x_7324_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(
                    v___x_7314_,
                    v___x_7323_,
                    v_a_7278_,
                    v_a_7279_,
                    v_a_7280_,
                    v_a_7281_,
                );
                if leanh::lean_obj_tag(v___x_7324_) == 0 {
                    leanh::lean_dec_ref_known(v___x_7324_, 1);
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_7298_);
                    leanh::lean_del_object(v___x_7295_);
                    leanh::lean_dec_ref(v_hyps_7274_);
                    v_a_7325_ = leanh::lean_ctor_get(v___x_7324_, 0);
                    v_isSharedCheck_7332_ = (!leanh::lean_is_exclusive(v___x_7324_)) as u8;
                    if v_isSharedCheck_7332_ == 0 {
                        v___x_7327_ = v___x_7324_;
                        v_isShared_7328_ = v_isSharedCheck_7332_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7325_);
                        leanh::lean_dec(v___x_7324_);
                        v___x_7327_ = leanh::lean_box(0);
                        v_isShared_7328_ = v_isSharedCheck_7332_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_7328_ == 0 {
                    v___x_7330_ = v___x_7327_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7331_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7331_, 0, v_a_7325_);
                    v___x_7330_ = v_reuseFailAlloc_7331_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7330_;
            }
            8 => {
                if v_isShared_7340_ == 0 {
                    v___x_7342_ = v___x_7339_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7343_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7343_, 0, v_a_7337_);
                    v___x_7342_ = v_reuseFailAlloc_7343_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7342_;
            }
            10 => {
                if v_isShared_7348_ == 0 {
                    v___x_7350_ = v___x_7347_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_7351_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7351_, 0, v_a_7345_);
                    v___x_7350_ = v_reuseFailAlloc_7351_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_7350_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Rewrites_rewriteCandidates___boxed(
    mut v_hyps_7353_: *mut leanh::LeanObject,
    mut v_moduleRef_7354_: *mut leanh::LeanObject,
    mut v_target_7355_: *mut leanh::LeanObject,
    mut v_forbidden_7356_: *mut leanh::LeanObject,
    mut v_a_7357_: *mut leanh::LeanObject,
    mut v_a_7358_: *mut leanh::LeanObject,
    mut v_a_7359_: *mut leanh::LeanObject,
    mut v_a_7360_: *mut leanh::LeanObject,
    mut v_a_7361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7362_ = l_Lean_Meta_Rewrites_rewriteCandidates(
        v_hyps_7353_,
        v_moduleRef_7354_,
        v_target_7355_,
        v_forbidden_7356_,
        v_a_7357_,
        v_a_7358_,
        v_a_7359_,
        v_a_7360_,
    );
    leanh::lean_dec(v_a_7360_);
    leanh::lean_dec_ref(v_a_7359_);
    leanh::lean_dec(v_a_7358_);
    leanh::lean_dec_ref(v_a_7357_);
    leanh::lean_dec(v_forbidden_7356_);
    return v_res_7362_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1(
    mut v_forbidden_7363_: *mut leanh::LeanObject,
    mut v_as_7364_: *mut leanh::LeanObject,
    mut v_sz_7365_: usize,
    mut v_i_7366_: usize,
    mut v_b_7367_: *mut leanh::LeanObject,
    mut v___y_7368_: *mut leanh::LeanObject,
    mut v___y_7369_: *mut leanh::LeanObject,
    mut v___y_7370_: *mut leanh::LeanObject,
    mut v___y_7371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_7363_, v_as_7364_, v_sz_7365_, v_i_7366_, v_b_7367_);
    return v___x_7373_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___boxed(
    mut v_forbidden_7374_: *mut leanh::LeanObject,
    mut v_as_7375_: *mut leanh::LeanObject,
    mut v_sz_7376_: *mut leanh::LeanObject,
    mut v_i_7377_: *mut leanh::LeanObject,
    mut v_b_7378_: *mut leanh::LeanObject,
    mut v___y_7379_: *mut leanh::LeanObject,
    mut v___y_7380_: *mut leanh::LeanObject,
    mut v___y_7381_: *mut leanh::LeanObject,
    mut v___y_7382_: *mut leanh::LeanObject,
    mut v___y_7383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_7384_: usize = 0;
    let mut v_i_boxed_7385_: usize = 0;
    let mut v_res_7386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7384_ = leanh::lean_unbox_usize(v_sz_7376_);
    leanh::lean_dec(v_sz_7376_);
    v_i_boxed_7385_ = leanh::lean_unbox_usize(v_i_7377_);
    leanh::lean_dec(v_i_7377_);
    v_res_7386_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1(v_forbidden_7374_, v_as_7375_, v_sz_boxed_7384_, v_i_boxed_7385_, v_b_7378_, v___y_7379_, v___y_7380_, v___y_7381_, v___y_7382_);
    leanh::lean_dec(v___y_7382_);
    leanh::lean_dec_ref(v___y_7381_);
    leanh::lean_dec(v___y_7380_);
    leanh::lean_dec_ref(v___y_7379_);
    leanh::lean_dec_ref(v_as_7375_);
    leanh::lean_dec(v_forbidden_7374_);
    return v_res_7386_;
}
pub unsafe fn l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0(
    mut v_xs_7387_: *mut leanh::LeanObject,
    mut v_j_7388_: *mut leanh::LeanObject,
    mut v_h_7389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7390_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(v_xs_7387_, v_j_7388_);
    return v___x_7390_;
}
pub unsafe fn l_Lean_Meta_Rewrites_RewriteResult_newGoal(
    mut v_r_7391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_rfl_x3f_7392_: u8 = 0;
    v_rfl_x3f_7392_ = leanh::lean_ctor_get_uint8(
        v_r_7391_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1) as u32,
    );
    if v_rfl_x3f_7392_ == 0 {
        let mut v_result_7393_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_eNew_7394_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7395_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_result_7393_ = leanh::lean_ctor_get(v_r_7391_, 2);
        v_eNew_7394_ = leanh::lean_ctor_get(v_result_7393_, 0);
        leanh::lean_inc_ref(v_eNew_7394_);
        v___x_7395_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_7395_, 0, v_eNew_7394_);
        return v___x_7395_;
    } else {
        let mut v___x_7396_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_7396_ = leanh::lean_box(0);
        return v___x_7396_;
    }
}
pub unsafe fn l_Lean_Meta_Rewrites_RewriteResult_newGoal___boxed(
    mut v_r_7397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7398_ = l_Lean_Meta_Rewrites_RewriteResult_newGoal(v_r_7397_);
    leanh::lean_dec_ref(v_r_7397_);
    return v_res_7398_;
}
pub unsafe fn l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0(
    mut v_x_7399_: *mut leanh::LeanObject,
    mut v___y_7400_: *mut leanh::LeanObject,
    mut v___y_7401_: *mut leanh::LeanObject,
    mut v___y_7402_: *mut leanh::LeanObject,
    mut v___y_7403_: *mut leanh::LeanObject,
    mut v___y_7404_: *mut leanh::LeanObject,
    mut v___y_7405_: *mut leanh::LeanObject,
    mut v___y_7406_: *mut leanh::LeanObject,
    mut v___y_7407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7409_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_7403_);
    leanh::lean_inc_ref(v___y_7402_);
    leanh::lean_inc(v___y_7401_);
    leanh::lean_inc_ref(v___y_7400_);
    v___x_7409_ = leanh::lean_apply_9(
        v_x_7399_,
        v___y_7400_,
        v___y_7401_,
        v___y_7402_,
        v___y_7403_,
        v___y_7404_,
        v___y_7405_,
        v___y_7406_,
        v___y_7407_,
        leanh::lean_box(0),
    );
    return v___x_7409_;
}
pub unsafe fn l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0___boxed(
    mut v_x_7410_: *mut leanh::LeanObject,
    mut v___y_7411_: *mut leanh::LeanObject,
    mut v___y_7412_: *mut leanh::LeanObject,
    mut v___y_7413_: *mut leanh::LeanObject,
    mut v___y_7414_: *mut leanh::LeanObject,
    mut v___y_7415_: *mut leanh::LeanObject,
    mut v___y_7416_: *mut leanh::LeanObject,
    mut v___y_7417_: *mut leanh::LeanObject,
    mut v___y_7418_: *mut leanh::LeanObject,
    mut v___y_7419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7420_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0(v_x_7410_, v___y_7411_, v___y_7412_, v___y_7413_, v___y_7414_, v___y_7415_, v___y_7416_, v___y_7417_, v___y_7418_);
    leanh::lean_dec(v___y_7414_);
    leanh::lean_dec_ref(v___y_7413_);
    leanh::lean_dec(v___y_7412_);
    leanh::lean_dec_ref(v___y_7411_);
    return v_res_7420_;
}
pub unsafe fn l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(
    mut v_mctx_7421_: *mut leanh::LeanObject,
    mut v_x_7422_: *mut leanh::LeanObject,
    mut v___y_7423_: *mut leanh::LeanObject,
    mut v___y_7424_: *mut leanh::LeanObject,
    mut v___y_7425_: *mut leanh::LeanObject,
    mut v___y_7426_: *mut leanh::LeanObject,
    mut v___y_7427_: *mut leanh::LeanObject,
    mut v___y_7428_: *mut leanh::LeanObject,
    mut v___y_7429_: *mut leanh::LeanObject,
    mut v___y_7430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7437_: u8 = 0;
    let mut v___x_7439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7441_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_7426_);
                leanh::lean_inc_ref(v___y_7425_);
                leanh::lean_inc(v___y_7424_);
                leanh::lean_inc_ref(v___y_7423_);
                v___f_7432_ = leanh::lean_alloc_closure(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                leanh::lean_closure_set(v___f_7432_, 0, v_x_7422_);
                leanh::lean_closure_set(v___f_7432_, 1, v___y_7423_);
                leanh::lean_closure_set(v___f_7432_, 2, v___y_7424_);
                leanh::lean_closure_set(v___f_7432_, 3, v___y_7425_);
                leanh::lean_closure_set(v___f_7432_, 4, v___y_7426_);
                v___x_7433_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(
                    leanh::lean_box(0),
                    v_mctx_7421_,
                    v___f_7432_,
                    v___y_7427_,
                    v___y_7428_,
                    v___y_7429_,
                    v___y_7430_,
                );
                if leanh::lean_obj_tag(v___x_7433_) == 0 {
                    return v___x_7433_;
                } else {
                    v_a_7434_ = leanh::lean_ctor_get(v___x_7433_, 0);
                    v_isSharedCheck_7441_ = (!leanh::lean_is_exclusive(v___x_7433_)) as u8;
                    if v_isSharedCheck_7441_ == 0 {
                        v___x_7436_ = v___x_7433_;
                        v_isShared_7437_ = v_isSharedCheck_7441_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7434_);
                        leanh::lean_dec(v___x_7433_);
                        v___x_7436_ = leanh::lean_box(0);
                        v_isShared_7437_ = v_isSharedCheck_7441_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7437_ == 0 {
                    v___x_7439_ = v___x_7436_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7440_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7440_, 0, v_a_7434_);
                    v___x_7439_ = v_reuseFailAlloc_7440_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7439_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___boxed(
    mut v_mctx_7442_: *mut leanh::LeanObject,
    mut v_x_7443_: *mut leanh::LeanObject,
    mut v___y_7444_: *mut leanh::LeanObject,
    mut v___y_7445_: *mut leanh::LeanObject,
    mut v___y_7446_: *mut leanh::LeanObject,
    mut v___y_7447_: *mut leanh::LeanObject,
    mut v___y_7448_: *mut leanh::LeanObject,
    mut v___y_7449_: *mut leanh::LeanObject,
    mut v___y_7450_: *mut leanh::LeanObject,
    mut v___y_7451_: *mut leanh::LeanObject,
    mut v___y_7452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7453_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_7442_, v_x_7443_, v___y_7444_, v___y_7445_, v___y_7446_, v___y_7447_, v___y_7448_, v___y_7449_, v___y_7450_, v___y_7451_);
    leanh::lean_dec(v___y_7451_);
    leanh::lean_dec_ref(v___y_7450_);
    leanh::lean_dec(v___y_7449_);
    leanh::lean_dec_ref(v___y_7448_);
    leanh::lean_dec(v___y_7447_);
    leanh::lean_dec_ref(v___y_7446_);
    leanh::lean_dec(v___y_7445_);
    leanh::lean_dec_ref(v___y_7444_);
    return v_res_7453_;
}
pub unsafe fn l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(
    mut v_00_u03b1_7454_: *mut leanh::LeanObject,
    mut v_mctx_7455_: *mut leanh::LeanObject,
    mut v_x_7456_: *mut leanh::LeanObject,
    mut v___y_7457_: *mut leanh::LeanObject,
    mut v___y_7458_: *mut leanh::LeanObject,
    mut v___y_7459_: *mut leanh::LeanObject,
    mut v___y_7460_: *mut leanh::LeanObject,
    mut v___y_7461_: *mut leanh::LeanObject,
    mut v___y_7462_: *mut leanh::LeanObject,
    mut v___y_7463_: *mut leanh::LeanObject,
    mut v___y_7464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7466_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_7455_, v_x_7456_, v___y_7457_, v___y_7458_, v___y_7459_, v___y_7460_, v___y_7461_, v___y_7462_, v___y_7463_, v___y_7464_);
    return v___x_7466_;
}
pub unsafe fn l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___boxed(
    mut v_00_u03b1_7467_: *mut leanh::LeanObject,
    mut v_mctx_7468_: *mut leanh::LeanObject,
    mut v_x_7469_: *mut leanh::LeanObject,
    mut v___y_7470_: *mut leanh::LeanObject,
    mut v___y_7471_: *mut leanh::LeanObject,
    mut v___y_7472_: *mut leanh::LeanObject,
    mut v___y_7473_: *mut leanh::LeanObject,
    mut v___y_7474_: *mut leanh::LeanObject,
    mut v___y_7475_: *mut leanh::LeanObject,
    mut v___y_7476_: *mut leanh::LeanObject,
    mut v___y_7477_: *mut leanh::LeanObject,
    mut v___y_7478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7479_ =
        l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(
            v_00_u03b1_7467_,
            v_mctx_7468_,
            v_x_7469_,
            v___y_7470_,
            v___y_7471_,
            v___y_7472_,
            v___y_7473_,
            v___y_7474_,
            v___y_7475_,
            v___y_7476_,
            v___y_7477_,
        );
    leanh::lean_dec(v___y_7477_);
    leanh::lean_dec_ref(v___y_7476_);
    leanh::lean_dec(v___y_7475_);
    leanh::lean_dec_ref(v___y_7474_);
    leanh::lean_dec(v___y_7473_);
    leanh::lean_dec_ref(v___y_7472_);
    leanh::lean_dec(v___y_7471_);
    leanh::lean_dec_ref(v___y_7470_);
    return v_res_7479_;
}
pub unsafe fn l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(
    mut v_expr_7480_: *mut leanh::LeanObject,
    mut v_symm_7481_: u8,
    mut v_r_7482_: *mut leanh::LeanObject,
    mut v_ref_7483_: *mut leanh::LeanObject,
    mut v_checkState_x3f_7484_: *mut leanh::LeanObject,
    mut v___y_7485_: *mut leanh::LeanObject,
    mut v___y_7486_: *mut leanh::LeanObject,
    mut v___y_7487_: *mut leanh::LeanObject,
    mut v___y_7488_: *mut leanh::LeanObject,
    mut v___y_7489_: *mut leanh::LeanObject,
    mut v___y_7490_: *mut leanh::LeanObject,
    mut v___y_7491_: *mut leanh::LeanObject,
    mut v___y_7492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7513_: u8 = 0;
    let mut v___x_7515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7517_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7494_ = l_Lean_Elab_Tactic_saveState___redArg(
                    v___y_7486_,
                    v___y_7488_,
                    v___y_7490_,
                    v___y_7492_,
                );
                if leanh::lean_obj_tag(v___x_7494_) == 0 {
                    v_a_7495_ = leanh::lean_ctor_get(v___x_7494_, 0);
                    leanh::lean_inc(v_a_7495_);
                    leanh::lean_dec_ref_known(v___x_7494_, 1);
                    v_ref_7496_ = leanh::lean_ctor_get(v___y_7491_, 5);
                    v___x_7497_ = leanh::lean_box((v_symm_7481_) as usize);
                    v___x_7498_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_7498_, 0, v_expr_7480_);
                    leanh::lean_ctor_set(v___x_7498_, 1, v___x_7497_);
                    v___x_7499_ = leanh::lean_box(0);
                    v___x_7500_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_7500_, 0, v___x_7498_);
                    leanh::lean_ctor_set(v___x_7500_, 1, v___x_7499_);
                    v___x_7501_ = l_Lean_Meta_Rewrites_RewriteResult_newGoal(v_r_7482_);
                    v___x_7502_ = l_Option_toLOption___redArg(v___x_7501_);
                    v___x_7503_ = leanh::lean_box(0);
                    leanh::lean_inc(v_ref_7496_);
                    v___x_7504_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7504_, 0, v_ref_7496_);
                    if leanh::lean_obj_tag(v_checkState_x3f_7484_) == 0 {
                        v___y_7506_ = v_a_7495_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_7495_);
                        v_val_7509_ = leanh::lean_ctor_get(v_checkState_x3f_7484_, 0);
                        leanh::lean_inc(v_val_7509_);
                        leanh::lean_dec_ref_known(v_checkState_x3f_7484_, 1);
                        v___y_7506_ = v_val_7509_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_checkState_x3f_7484_);
                    leanh::lean_dec(v_ref_7483_);
                    leanh::lean_dec_ref(v_expr_7480_);
                    v_a_7510_ = leanh::lean_ctor_get(v___x_7494_, 0);
                    v_isSharedCheck_7517_ = (!leanh::lean_is_exclusive(v___x_7494_)) as u8;
                    if v_isSharedCheck_7517_ == 0 {
                        v___x_7512_ = v___x_7494_;
                        v_isShared_7513_ = v_isSharedCheck_7517_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7510_);
                        leanh::lean_dec(v___x_7494_);
                        v___x_7512_ = leanh::lean_box(0);
                        v_isShared_7513_ = v_isSharedCheck_7517_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7507_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7507_, 0, v___y_7506_);
                v___x_7508_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(
                    v_ref_7483_,
                    v___x_7500_,
                    v___x_7502_,
                    v___x_7503_,
                    v___x_7504_,
                    v___x_7507_,
                    v___y_7485_,
                    v___y_7486_,
                    v___y_7487_,
                    v___y_7488_,
                    v___y_7489_,
                    v___y_7490_,
                    v___y_7491_,
                    v___y_7492_,
                );
                return v___x_7508_;
            }
            2 => {
                if v_isShared_7513_ == 0 {
                    v___x_7515_ = v___x_7512_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7516_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7516_, 0, v_a_7510_);
                    v___x_7515_ = v_reuseFailAlloc_7516_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7515_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0___boxed(
    mut v_expr_7518_: *mut leanh::LeanObject,
    mut v_symm_7519_: *mut leanh::LeanObject,
    mut v_r_7520_: *mut leanh::LeanObject,
    mut v_ref_7521_: *mut leanh::LeanObject,
    mut v_checkState_x3f_7522_: *mut leanh::LeanObject,
    mut v___y_7523_: *mut leanh::LeanObject,
    mut v___y_7524_: *mut leanh::LeanObject,
    mut v___y_7525_: *mut leanh::LeanObject,
    mut v___y_7526_: *mut leanh::LeanObject,
    mut v___y_7527_: *mut leanh::LeanObject,
    mut v___y_7528_: *mut leanh::LeanObject,
    mut v___y_7529_: *mut leanh::LeanObject,
    mut v___y_7530_: *mut leanh::LeanObject,
    mut v___y_7531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_symm_boxed_7532_: u8 = 0;
    let mut v_res_7533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_symm_boxed_7532_ = (leanh::lean_unbox(v_symm_7519_) as u8);
    v_res_7533_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(
        v_expr_7518_,
        v_symm_boxed_7532_,
        v_r_7520_,
        v_ref_7521_,
        v_checkState_x3f_7522_,
        v___y_7523_,
        v___y_7524_,
        v___y_7525_,
        v___y_7526_,
        v___y_7527_,
        v___y_7528_,
        v___y_7529_,
        v___y_7530_,
    );
    leanh::lean_dec(v___y_7530_);
    leanh::lean_dec_ref(v___y_7529_);
    leanh::lean_dec(v___y_7528_);
    leanh::lean_dec_ref(v___y_7527_);
    leanh::lean_dec(v___y_7526_);
    leanh::lean_dec_ref(v___y_7525_);
    leanh::lean_dec(v___y_7524_);
    leanh::lean_dec_ref(v___y_7523_);
    leanh::lean_dec_ref(v_r_7520_);
    return v_res_7533_;
}
pub unsafe fn l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(
    mut v_ref_7534_: *mut leanh::LeanObject,
    mut v_r_7535_: *mut leanh::LeanObject,
    mut v_checkState_x3f_7536_: *mut leanh::LeanObject,
    mut v_a_7537_: *mut leanh::LeanObject,
    mut v_a_7538_: *mut leanh::LeanObject,
    mut v_a_7539_: *mut leanh::LeanObject,
    mut v_a_7540_: *mut leanh::LeanObject,
    mut v_a_7541_: *mut leanh::LeanObject,
    mut v_a_7542_: *mut leanh::LeanObject,
    mut v_a_7543_: *mut leanh::LeanObject,
    mut v_a_7544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_expr_7546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_symm_7547_: u8 = 0;
    let mut v_mctx_7548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_expr_7546_ = leanh::lean_ctor_get(v_r_7535_, 0);
    leanh::lean_inc_ref(v_expr_7546_);
    v_symm_7547_ = leanh::lean_ctor_get_uint8(
        v_r_7535_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
    );
    v_mctx_7548_ = leanh::lean_ctor_get(v_r_7535_, 3);
    leanh::lean_inc_ref(v_mctx_7548_);
    v___x_7549_ = leanh::lean_box((v_symm_7547_) as usize);
    v___f_7550_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0___boxed as *mut core::ffi::c_void,
        14,
        5,
    );
    leanh::lean_closure_set(v___f_7550_, 0, v_expr_7546_);
    leanh::lean_closure_set(v___f_7550_, 1, v___x_7549_);
    leanh::lean_closure_set(v___f_7550_, 2, v_r_7535_);
    leanh::lean_closure_set(v___f_7550_, 3, v_ref_7534_);
    leanh::lean_closure_set(v___f_7550_, 4, v_checkState_x3f_7536_);
    v___x_7551_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_7548_, v___f_7550_, v_a_7537_, v_a_7538_, v_a_7539_, v_a_7540_, v_a_7541_, v_a_7542_, v_a_7543_, v_a_7544_);
    return v___x_7551_;
}
pub unsafe fn l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___boxed(
    mut v_ref_7552_: *mut leanh::LeanObject,
    mut v_r_7553_: *mut leanh::LeanObject,
    mut v_checkState_x3f_7554_: *mut leanh::LeanObject,
    mut v_a_7555_: *mut leanh::LeanObject,
    mut v_a_7556_: *mut leanh::LeanObject,
    mut v_a_7557_: *mut leanh::LeanObject,
    mut v_a_7558_: *mut leanh::LeanObject,
    mut v_a_7559_: *mut leanh::LeanObject,
    mut v_a_7560_: *mut leanh::LeanObject,
    mut v_a_7561_: *mut leanh::LeanObject,
    mut v_a_7562_: *mut leanh::LeanObject,
    mut v_a_7563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7564_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(
        v_ref_7552_,
        v_r_7553_,
        v_checkState_x3f_7554_,
        v_a_7555_,
        v_a_7556_,
        v_a_7557_,
        v_a_7558_,
        v_a_7559_,
        v_a_7560_,
        v_a_7561_,
        v_a_7562_,
    );
    leanh::lean_dec(v_a_7562_);
    leanh::lean_dec_ref(v_a_7561_);
    leanh::lean_dec(v_a_7560_);
    leanh::lean_dec_ref(v_a_7559_);
    leanh::lean_dec(v_a_7558_);
    leanh::lean_dec_ref(v_a_7557_);
    leanh::lean_dec(v_a_7556_);
    leanh::lean_dec_ref(v_a_7555_);
    return v_res_7564_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(
    mut v_a_7565_: *mut leanh::LeanObject,
    mut v_b_7566_: *mut leanh::LeanObject,
    mut v_x_7567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_7568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7573_: u8 = 0;
    let mut v___x_7574_: u8 = 0;
    let mut v___x_7575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7582_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_7567_) == 0 {
                    leanh::lean_dec(v_b_7566_);
                    leanh::lean_dec_ref(v_a_7565_);
                    return v_x_7567_;
                } else {
                    v_key_7568_ = leanh::lean_ctor_get(v_x_7567_, 0);
                    v_value_7569_ = leanh::lean_ctor_get(v_x_7567_, 1);
                    v_tail_7570_ = leanh::lean_ctor_get(v_x_7567_, 2);
                    v_isSharedCheck_7582_ = (!leanh::lean_is_exclusive(v_x_7567_)) as u8;
                    if v_isSharedCheck_7582_ == 0 {
                        v___x_7572_ = v_x_7567_;
                        v_isShared_7573_ = v_isSharedCheck_7582_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_7570_);
                        leanh::lean_inc(v_value_7569_);
                        leanh::lean_inc(v_key_7568_);
                        leanh::lean_dec(v_x_7567_);
                        v___x_7572_ = leanh::lean_box(0);
                        v_isShared_7573_ = v_isSharedCheck_7582_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7574_ = lean_string_dec_eq(v_key_7568_, v_a_7565_);
                if v___x_7574_ == 0 {
                    v___x_7575_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_7565_, v_b_7566_, v_tail_7570_);
                    if v_isShared_7573_ == 0 {
                        leanh::lean_ctor_set(v___x_7572_, 2, v___x_7575_);
                        v___x_7577_ = v___x_7572_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7578_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7578_, 0, v_key_7568_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7578_, 1, v_value_7569_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7578_, 2, v___x_7575_);
                        v___x_7577_ = v_reuseFailAlloc_7578_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_7569_);
                    leanh::lean_dec(v_key_7568_);
                    if v_isShared_7573_ == 0 {
                        leanh::lean_ctor_set(v___x_7572_, 1, v_b_7566_);
                        leanh::lean_ctor_set(v___x_7572_, 0, v_a_7565_);
                        v___x_7580_ = v___x_7572_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7581_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7581_, 0, v_a_7565_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7581_, 1, v_b_7566_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7581_, 2, v_tail_7570_);
                        v___x_7580_ = v_reuseFailAlloc_7581_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_7577_;
            }
            3 => {
                return v___x_7580_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(
    mut v_x_7583_: *mut leanh::LeanObject,
    mut v_x_7584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_7585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7590_: u8 = 0;
    let mut v___x_7591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7592_: u64 = 0;
    let mut v___x_7593_: u64 = 0;
    let mut v___x_7594_: u64 = 0;
    let mut v_fold_7595_: u64 = 0;
    let mut v___x_7596_: u64 = 0;
    let mut v___x_7597_: u64 = 0;
    let mut v___x_7598_: u64 = 0;
    let mut v___x_7599_: usize = 0;
    let mut v___x_7600_: usize = 0;
    let mut v___x_7601_: usize = 0;
    let mut v___x_7602_: usize = 0;
    let mut v___x_7603_: usize = 0;
    let mut v___x_7604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7610_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_7584_) == 0 {
                    return v_x_7583_;
                } else {
                    v_key_7585_ = leanh::lean_ctor_get(v_x_7584_, 0);
                    v_value_7586_ = leanh::lean_ctor_get(v_x_7584_, 1);
                    v_tail_7587_ = leanh::lean_ctor_get(v_x_7584_, 2);
                    v_isSharedCheck_7610_ = (!leanh::lean_is_exclusive(v_x_7584_)) as u8;
                    if v_isSharedCheck_7610_ == 0 {
                        v___x_7589_ = v_x_7584_;
                        v_isShared_7590_ = v_isSharedCheck_7610_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_7587_);
                        leanh::lean_inc(v_value_7586_);
                        leanh::lean_inc(v_key_7585_);
                        leanh::lean_dec(v_x_7584_);
                        v___x_7589_ = leanh::lean_box(0);
                        v_isShared_7590_ = v_isSharedCheck_7610_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7591_ = lean_array_get_size(v_x_7583_);
                v___x_7592_ = lean_string_hash(v_key_7585_);
                v___x_7593_ = 32u64;
                v___x_7594_ = lean_uint64_shift_right(v___x_7592_, v___x_7593_);
                v_fold_7595_ = lean_uint64_xor(v___x_7592_, v___x_7594_);
                v___x_7596_ = 16u64;
                v___x_7597_ = lean_uint64_shift_right(v_fold_7595_, v___x_7596_);
                v___x_7598_ = lean_uint64_xor(v_fold_7595_, v___x_7597_);
                v___x_7599_ = lean_uint64_to_usize(v___x_7598_);
                v___x_7600_ = lean_usize_of_nat(v___x_7591_);
                v___x_7601_ = 1usize;
                v___x_7602_ = lean_usize_sub(v___x_7600_, v___x_7601_);
                v___x_7603_ = lean_usize_land(v___x_7599_, v___x_7602_);
                v___x_7604_ = lean_array_uget_borrowed(v_x_7583_, v___x_7603_);
                leanh::lean_inc(v___x_7604_);
                if v_isShared_7590_ == 0 {
                    leanh::lean_ctor_set(v___x_7589_, 2, v___x_7604_);
                    v___x_7606_ = v___x_7589_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7609_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7609_, 0, v_key_7585_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7609_, 1, v_value_7586_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7609_, 2, v___x_7604_);
                    v___x_7606_ = v_reuseFailAlloc_7609_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7607_ = lean_array_uset(v_x_7583_, v___x_7603_, v___x_7606_);
                v_x_7583_ = v___x_7607_;
                v_x_7584_ = v_tail_7587_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(
    mut v_i_7611_: *mut leanh::LeanObject,
    mut v_source_7612_: *mut leanh::LeanObject,
    mut v_target_7613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7615_: u8 = 0;
    let mut v_es_7616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_7618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_7619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7614_ = lean_array_get_size(v_source_7612_);
                v___x_7615_ = lean_nat_dec_lt(v_i_7611_, v___x_7614_);
                if v___x_7615_ == 0 {
                    leanh::lean_dec_ref(v_source_7612_);
                    leanh::lean_dec(v_i_7611_);
                    return v_target_7613_;
                } else {
                    v_es_7616_ = lean_array_fget(v_source_7612_, v_i_7611_);
                    v___x_7617_ = leanh::lean_box(0);
                    v_source_7618_ = lean_array_fset(v_source_7612_, v_i_7611_, v___x_7617_);
                    v_target_7619_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(v_target_7613_, v_es_7616_);
                    v___x_7620_ = leanh::lean_unsigned_to_nat(1);
                    v___x_7621_ = lean_nat_add(v_i_7611_, v___x_7620_);
                    leanh::lean_dec(v_i_7611_);
                    v_i_7611_ = v___x_7621_;
                    v_source_7612_ = v_source_7618_;
                    v_target_7613_ = v_target_7619_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(
    mut v_data_7623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_7626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7624_ = lean_array_get_size(v_data_7623_);
    v___x_7625_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_7626_ = lean_nat_mul(v___x_7624_, v___x_7625_);
    v___x_7627_ = leanh::lean_unsigned_to_nat(0);
    v___x_7628_ = leanh::lean_box(0);
    v___x_7629_ = lean_mk_array(v_nbuckets_7626_, v___x_7628_);
    v___x_7630_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(v___x_7627_, v_data_7623_, v___x_7629_);
    return v___x_7630_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(
    mut v_a_7631_: *mut leanh::LeanObject,
    mut v_x_7632_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_7633_: u8 = 0;
    let mut v_key_7634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7636_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_7632_) == 0 {
                    v___x_7633_ = 0;
                    return v___x_7633_;
                } else {
                    v_key_7634_ = leanh::lean_ctor_get(v_x_7632_, 0);
                    v_tail_7635_ = leanh::lean_ctor_get(v_x_7632_, 2);
                    v___x_7636_ = lean_string_dec_eq(v_key_7634_, v_a_7631_);
                    if v___x_7636_ == 0 {
                        v_x_7632_ = v_tail_7635_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_7636_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___boxed(
    mut v_a_7638_: *mut leanh::LeanObject,
    mut v_x_7639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7640_: u8 = 0;
    let mut v_r_7641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7640_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_7638_, v_x_7639_);
    leanh::lean_dec(v_x_7639_);
    leanh::lean_dec_ref(v_a_7638_);
    v_r_7641_ = leanh::lean_box((v_res_7640_) as usize);
    return v_r_7641_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(
    mut v_m_7642_: *mut leanh::LeanObject,
    mut v_a_7643_: *mut leanh::LeanObject,
    mut v_b_7644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_7645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_7646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7649_: u8 = 0;
    let mut v___x_7650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7651_: u64 = 0;
    let mut v___x_7652_: u64 = 0;
    let mut v___x_7653_: u64 = 0;
    let mut v_fold_7654_: u64 = 0;
    let mut v___x_7655_: u64 = 0;
    let mut v___x_7656_: u64 = 0;
    let mut v___x_7657_: u64 = 0;
    let mut v___x_7658_: usize = 0;
    let mut v___x_7659_: usize = 0;
    let mut v___x_7660_: usize = 0;
    let mut v___x_7661_: usize = 0;
    let mut v___x_7662_: usize = 0;
    let mut v_bkt_7663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7664_: u8 = 0;
    let mut v___x_7665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_7666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_7668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7674_: u8 = 0;
    let mut v_val_7675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_7683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7689_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_7645_ = leanh::lean_ctor_get(v_m_7642_, 0);
                v_buckets_7646_ = leanh::lean_ctor_get(v_m_7642_, 1);
                v_isSharedCheck_7689_ = (!leanh::lean_is_exclusive(v_m_7642_)) as u8;
                if v_isSharedCheck_7689_ == 0 {
                    v___x_7648_ = v_m_7642_;
                    v_isShared_7649_ = v_isSharedCheck_7689_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_7646_);
                    leanh::lean_inc(v_size_7645_);
                    leanh::lean_dec(v_m_7642_);
                    v___x_7648_ = leanh::lean_box(0);
                    v_isShared_7649_ = v_isSharedCheck_7689_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7650_ = lean_array_get_size(v_buckets_7646_);
                v___x_7651_ = lean_string_hash(v_a_7643_);
                v___x_7652_ = 32u64;
                v___x_7653_ = lean_uint64_shift_right(v___x_7651_, v___x_7652_);
                v_fold_7654_ = lean_uint64_xor(v___x_7651_, v___x_7653_);
                v___x_7655_ = 16u64;
                v___x_7656_ = lean_uint64_shift_right(v_fold_7654_, v___x_7655_);
                v___x_7657_ = lean_uint64_xor(v_fold_7654_, v___x_7656_);
                v___x_7658_ = lean_uint64_to_usize(v___x_7657_);
                v___x_7659_ = lean_usize_of_nat(v___x_7650_);
                v___x_7660_ = 1usize;
                v___x_7661_ = lean_usize_sub(v___x_7659_, v___x_7660_);
                v___x_7662_ = lean_usize_land(v___x_7658_, v___x_7661_);
                v_bkt_7663_ = lean_array_uget_borrowed(v_buckets_7646_, v___x_7662_);
                v___x_7664_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_7643_, v_bkt_7663_);
                if v___x_7664_ == 0 {
                    v___x_7665_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_7666_ = lean_nat_add(v_size_7645_, v___x_7665_);
                    leanh::lean_dec(v_size_7645_);
                    leanh::lean_inc(v_bkt_7663_);
                    v___x_7667_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_7667_, 0, v_a_7643_);
                    leanh::lean_ctor_set(v___x_7667_, 1, v_b_7644_);
                    leanh::lean_ctor_set(v___x_7667_, 2, v_bkt_7663_);
                    v_buckets_x27_7668_ =
                        lean_array_uset(v_buckets_7646_, v___x_7662_, v___x_7667_);
                    v___x_7669_ = leanh::lean_unsigned_to_nat(4);
                    v___x_7670_ = lean_nat_mul(v_size_x27_7666_, v___x_7669_);
                    v___x_7671_ = leanh::lean_unsigned_to_nat(3);
                    v___x_7672_ = lean_nat_div(v___x_7670_, v___x_7671_);
                    leanh::lean_dec(v___x_7670_);
                    v___x_7673_ = lean_array_get_size(v_buckets_x27_7668_);
                    v___x_7674_ = lean_nat_dec_le(v___x_7672_, v___x_7673_);
                    leanh::lean_dec(v___x_7672_);
                    if v___x_7674_ == 0 {
                        v_val_7675_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(v_buckets_x27_7668_);
                        if v_isShared_7649_ == 0 {
                            leanh::lean_ctor_set(v___x_7648_, 1, v_val_7675_);
                            leanh::lean_ctor_set(v___x_7648_, 0, v_size_x27_7666_);
                            v___x_7677_ = v___x_7648_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_7678_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_7678_,
                                0,
                                v_size_x27_7666_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_7678_, 1, v_val_7675_);
                            v___x_7677_ = v_reuseFailAlloc_7678_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_7649_ == 0 {
                            leanh::lean_ctor_set(v___x_7648_, 1, v_buckets_x27_7668_);
                            leanh::lean_ctor_set(v___x_7648_, 0, v_size_x27_7666_);
                            v___x_7680_ = v___x_7648_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_7681_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_7681_,
                                0,
                                v_size_x27_7666_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_7681_,
                                1,
                                v_buckets_x27_7668_,
                            );
                            v___x_7680_ = v_reuseFailAlloc_7681_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_7663_);
                    v___x_7682_ = leanh::lean_box(0);
                    v_buckets_x27_7683_ =
                        lean_array_uset(v_buckets_7646_, v___x_7662_, v___x_7682_);
                    v___x_7684_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_7643_, v_b_7644_, v_bkt_7663_);
                    v___x_7685_ = lean_array_uset(v_buckets_x27_7683_, v___x_7662_, v___x_7684_);
                    if v_isShared_7649_ == 0 {
                        leanh::lean_ctor_set(v___x_7648_, 1, v___x_7685_);
                        v___x_7687_ = v___x_7648_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_7688_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7688_, 0, v_size_7645_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7688_, 1, v___x_7685_);
                        v___x_7687_ = v_reuseFailAlloc_7688_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_7677_;
            }
            3 => {
                return v___x_7680_;
            }
            4 => {
                return v___x_7687_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(
    mut v_m_7690_: *mut leanh::LeanObject,
    mut v_a_7691_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_7692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7694_: u64 = 0;
    let mut v___x_7695_: u64 = 0;
    let mut v___x_7696_: u64 = 0;
    let mut v_fold_7697_: u64 = 0;
    let mut v___x_7698_: u64 = 0;
    let mut v___x_7699_: u64 = 0;
    let mut v___x_7700_: u64 = 0;
    let mut v___x_7701_: usize = 0;
    let mut v___x_7702_: usize = 0;
    let mut v___x_7703_: usize = 0;
    let mut v___x_7704_: usize = 0;
    let mut v___x_7705_: usize = 0;
    let mut v___x_7706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7707_: u8 = 0;
    v_buckets_7692_ = leanh::lean_ctor_get(v_m_7690_, 1);
    v___x_7693_ = lean_array_get_size(v_buckets_7692_);
    v___x_7694_ = lean_string_hash(v_a_7691_);
    v___x_7695_ = 32u64;
    v___x_7696_ = lean_uint64_shift_right(v___x_7694_, v___x_7695_);
    v_fold_7697_ = lean_uint64_xor(v___x_7694_, v___x_7696_);
    v___x_7698_ = 16u64;
    v___x_7699_ = lean_uint64_shift_right(v_fold_7697_, v___x_7698_);
    v___x_7700_ = lean_uint64_xor(v_fold_7697_, v___x_7699_);
    v___x_7701_ = lean_uint64_to_usize(v___x_7700_);
    v___x_7702_ = lean_usize_of_nat(v___x_7693_);
    v___x_7703_ = 1usize;
    v___x_7704_ = lean_usize_sub(v___x_7702_, v___x_7703_);
    v___x_7705_ = lean_usize_land(v___x_7701_, v___x_7704_);
    v___x_7706_ = lean_array_uget_borrowed(v_buckets_7692_, v___x_7705_);
    v___x_7707_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_7691_, v___x_7706_);
    return v___x_7707_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg___boxed(
    mut v_m_7708_: *mut leanh::LeanObject,
    mut v_a_7709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7710_: u8 = 0;
    let mut v_r_7711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7710_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_m_7708_, v_a_7709_);
    leanh::lean_dec_ref(v_a_7709_);
    leanh::lean_dec_ref(v_m_7708_);
    v_r_7711_ = leanh::lean_box((v_res_7710_) as usize);
    return v_r_7711_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(
    mut v_cfg_7712_: *mut leanh::LeanObject,
    mut v_as_x27_7713_: *mut leanh::LeanObject,
    mut v_b_7714_: *mut leanh::LeanObject,
    mut v___y_7715_: *mut leanh::LeanObject,
    mut v___y_7716_: *mut leanh::LeanObject,
    mut v___y_7717_: *mut leanh::LeanObject,
    mut v___y_7718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_7721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7731_: u8 = 0;
    let mut v_a_7732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7735_: u8 = 0;
    let mut v_fst_7736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7740_: u8 = 0;
    let mut v_stopAtRfl_7741_: u8 = 0;
    let mut v_max_7742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_minHeartbeats_7743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_goal_7744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_7745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_side_7746_: u8 = 0;
    let mut v_mctx_7747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7748_: u8 = 0;
    let mut v___x_7749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7750_: u8 = 0;
    let mut v___x_7751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7767_: u8 = 0;
    let mut v_result_7768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_7769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7774_: u8 = 0;
    let mut v_eNew_7775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7790_: u8 = 0;
    let mut v___x_7791_: u8 = 0;
    let mut v___x_7792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7817_: u8 = 0;
    let mut v_a_7818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7821_: u8 = 0;
    let mut v___x_7823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7825_: u8 = 0;
    let mut v___x_7827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7836_: u8 = 0;
    let mut v___x_7838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7840_: u8 = 0;
    let mut v_isSharedCheck_7841_: u8 = 0;
    let mut v_a_7842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7845_: u8 = 0;
    let mut v___x_7847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7849_: u8 = 0;
    let mut v___x_7850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7870_: u8 = 0;
    let mut v_isSharedCheck_7871_: u8 = 0;
    let mut v_isSharedCheck_7872_: u8 = 0;
    let mut v_unused_7873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7877_: u8 = 0;
    let mut v___x_7879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7881_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_7713_) == 0 {
                    leanh::lean_dec_ref(v_cfg_7712_);
                    v___x_7720_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7720_, 0, v_b_7714_);
                    return v___x_7720_;
                } else {
                    v_head_7721_ = leanh::lean_ctor_get(v_as_x27_7713_, 0);
                    v_snd_7722_ = leanh::lean_ctor_get(v_head_7721_, 1);
                    v_tail_7723_ = leanh::lean_ctor_get(v_as_x27_7713_, 1);
                    v_fst_7724_ = leanh::lean_ctor_get(v_head_7721_, 0);
                    v_fst_7725_ = leanh::lean_ctor_get(v_snd_7722_, 0);
                    v_snd_7726_ = leanh::lean_ctor_get(v_snd_7722_, 1);
                    v___x_7727_ = l_Lean_getRemainingHeartbeats___redArg(v___y_7717_);
                    if leanh::lean_obj_tag(v___x_7727_) == 0 {
                        v_snd_7728_ = leanh::lean_ctor_get(v_b_7714_, 1);
                        v_isSharedCheck_7872_ = (!leanh::lean_is_exclusive(v_b_7714_)) as u8;
                        if v_isSharedCheck_7872_ == 0 {
                            v_unused_7873_ = leanh::lean_ctor_get(v_b_7714_, 0);
                            leanh::lean_dec(v_unused_7873_);
                            v___x_7730_ = v_b_7714_;
                            v_isShared_7731_ = v_isSharedCheck_7872_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_7728_);
                            leanh::lean_dec(v_b_7714_);
                            v___x_7730_ = leanh::lean_box(0);
                            v_isShared_7731_ = v_isSharedCheck_7872_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_7714_);
                        leanh::lean_dec_ref(v_cfg_7712_);
                        v_a_7874_ = leanh::lean_ctor_get(v___x_7727_, 0);
                        v_isSharedCheck_7881_ =
                            (!leanh::lean_is_exclusive(v___x_7727_)) as u8;
                        if v_isSharedCheck_7881_ == 0 {
                            v___x_7876_ = v___x_7727_;
                            v_isShared_7877_ = v_isSharedCheck_7881_;
                            state = 30;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7874_);
                            leanh::lean_dec(v___x_7727_);
                            v___x_7876_ = leanh::lean_box(0);
                            v_isShared_7877_ = v_isSharedCheck_7881_;
                            state = 30;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_a_7732_ = leanh::lean_ctor_get(v___x_7727_, 0);
                v_isSharedCheck_7871_ = (!leanh::lean_is_exclusive(v___x_7727_)) as u8;
                if v_isSharedCheck_7871_ == 0 {
                    v___x_7734_ = v___x_7727_;
                    v_isShared_7735_ = v_isSharedCheck_7871_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_7732_);
                    leanh::lean_dec(v___x_7727_);
                    v___x_7734_ = leanh::lean_box(0);
                    v_isShared_7735_ = v_isSharedCheck_7871_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_7736_ = leanh::lean_ctor_get(v_snd_7728_, 0);
                v_snd_7737_ = leanh::lean_ctor_get(v_snd_7728_, 1);
                v_isSharedCheck_7870_ = (!leanh::lean_is_exclusive(v_snd_7728_)) as u8;
                if v_isSharedCheck_7870_ == 0 {
                    v___x_7739_ = v_snd_7728_;
                    v_isShared_7740_ = v_isSharedCheck_7870_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_7737_);
                    leanh::lean_inc(v_fst_7736_);
                    leanh::lean_dec(v_snd_7728_);
                    v___x_7739_ = leanh::lean_box(0);
                    v_isShared_7740_ = v_isSharedCheck_7870_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_stopAtRfl_7741_ = leanh::lean_ctor_get_uint8(
                    v_cfg_7712_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                );
                v_max_7742_ = leanh::lean_ctor_get(v_cfg_7712_, 0);
                v_minHeartbeats_7743_ = leanh::lean_ctor_get(v_cfg_7712_, 1);
                v_goal_7744_ = leanh::lean_ctor_get(v_cfg_7712_, 2);
                v_target_7745_ = leanh::lean_ctor_get(v_cfg_7712_, 3);
                v_side_7746_ = leanh::lean_ctor_get_uint8(
                    v_cfg_7712_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                );
                v_mctx_7747_ = leanh::lean_ctor_get(v_cfg_7712_, 4);
                v___x_7748_ = lean_nat_dec_lt(v_a_7732_, v_minHeartbeats_7743_);
                leanh::lean_dec(v_a_7732_);
                if v___x_7748_ == 0 {
                    v___x_7749_ = lean_array_get_size(v_snd_7737_);
                    v___x_7750_ = lean_nat_dec_le(v_max_7742_, v___x_7749_);
                    if v___x_7750_ == 0 {
                        leanh::lean_del_object(v___x_7734_);
                        v___x_7751_ = leanh::lean_box((v_side_7746_) as usize);
                        leanh::lean_inc(v_snd_7726_);
                        leanh::lean_inc(v_fst_7725_);
                        leanh::lean_inc(v_fst_7724_);
                        leanh::lean_inc_ref(v_target_7745_);
                        leanh::lean_inc(v_goal_7744_);
                        leanh::lean_inc_ref_n(v_mctx_7747_, 2);
                        v___x_7752_ = leanh::lean_alloc_closure(
                            l_Lean_Meta_Rewrites_rwLemma___boxed as *mut core::ffi::c_void,
                            12,
                            7,
                        );
                        leanh::lean_closure_set(v___x_7752_, 0, v_mctx_7747_);
                        leanh::lean_closure_set(v___x_7752_, 1, v_goal_7744_);
                        leanh::lean_closure_set(v___x_7752_, 2, v_target_7745_);
                        leanh::lean_closure_set(v___x_7752_, 3, v___x_7751_);
                        leanh::lean_closure_set(v___x_7752_, 4, v_fst_7724_);
                        leanh::lean_closure_set(v___x_7752_, 5, v_fst_7725_);
                        leanh::lean_closure_set(v___x_7752_, 6, v_snd_7726_);
                        v___x_7753_ = leanh::lean_alloc_closure(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed as *mut core::ffi::c_void, 8, 3);
                        leanh::lean_closure_set(v___x_7753_, 0, leanh::lean_box(0));
                        leanh::lean_closure_set(v___x_7753_, 1, v_mctx_7747_);
                        leanh::lean_closure_set(v___x_7753_, 2, v___x_7752_);
                        v___x_7754_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_7753_, v___y_7715_, v___y_7716_, v___y_7717_, v___y_7718_);
                        if leanh::lean_obj_tag(v___x_7754_) == 0 {
                            v_a_7755_ = leanh::lean_ctor_get(v___x_7754_, 0);
                            leanh::lean_inc(v_a_7755_);
                            leanh::lean_dec_ref_known(v___x_7754_, 1);
                            v___x_7756_ = leanh::lean_box(0);
                            if leanh::lean_obj_tag(v_a_7755_) == 0 {
                                if v_isShared_7740_ == 0 {
                                    v___x_7758_ = v___x_7739_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_7763_ =
                                        leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7763_,
                                        0,
                                        v_fst_7736_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7763_,
                                        1,
                                        v_snd_7737_,
                                    );
                                    v___x_7758_ = v_reuseFailAlloc_7763_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                v_val_7764_ = leanh::lean_ctor_get(v_a_7755_, 0);
                                v_isSharedCheck_7841_ =
                                    (!leanh::lean_is_exclusive(v_a_7755_)) as u8;
                                if v_isSharedCheck_7841_ == 0 {
                                    v___x_7766_ = v_a_7755_;
                                    v_isShared_7767_ = v_isSharedCheck_7841_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_7764_);
                                    leanh::lean_dec(v_a_7755_);
                                    v___x_7766_ = leanh::lean_box(0);
                                    v_isShared_7767_ = v_isSharedCheck_7841_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_del_object(v___x_7739_);
                            leanh::lean_dec(v_snd_7737_);
                            leanh::lean_dec(v_fst_7736_);
                            leanh::lean_del_object(v___x_7730_);
                            leanh::lean_dec_ref(v_cfg_7712_);
                            v_a_7842_ = leanh::lean_ctor_get(v___x_7754_, 0);
                            v_isSharedCheck_7849_ =
                                (!leanh::lean_is_exclusive(v___x_7754_)) as u8;
                            if v_isSharedCheck_7849_ == 0 {
                                v___x_7844_ = v___x_7754_;
                                v_isShared_7845_ = v_isSharedCheck_7849_;
                                state = 22;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7842_);
                                leanh::lean_dec(v___x_7754_);
                                v___x_7844_ = leanh::lean_box(0);
                                v_isShared_7845_ = v_isSharedCheck_7849_;
                                state = 22;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_cfg_7712_);
                        leanh::lean_inc(v_snd_7737_);
                        v___x_7850_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_7850_, 0, v_snd_7737_);
                        if v_isShared_7740_ == 0 {
                            v___x_7852_ = v___x_7739_;
                            state = 24;
                            continue;
                        } else {
                            v_reuseFailAlloc_7859_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7859_, 0, v_fst_7736_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7859_, 1, v_snd_7737_);
                            v___x_7852_ = v_reuseFailAlloc_7859_;
                            state = 24;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_cfg_7712_);
                    leanh::lean_inc(v_snd_7737_);
                    v___x_7860_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7860_, 0, v_snd_7737_);
                    if v_isShared_7740_ == 0 {
                        v___x_7862_ = v___x_7739_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_7869_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7869_, 0, v_fst_7736_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7869_, 1, v_snd_7737_);
                        v___x_7862_ = v_reuseFailAlloc_7869_;
                        state = 27;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_7731_ == 0 {
                    leanh::lean_ctor_set(v___x_7730_, 1, v___x_7758_);
                    leanh::lean_ctor_set(v___x_7730_, 0, v___x_7756_);
                    v___x_7760_ = v___x_7730_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7762_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7762_, 0, v___x_7756_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7762_, 1, v___x_7758_);
                    v___x_7760_ = v_reuseFailAlloc_7762_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_as_x27_7713_ = v_tail_7723_;
                v_b_7714_ = v___x_7760_;
                state = 0;
                continue;
            }
            6 => {
                v_result_7768_ = leanh::lean_ctor_get(v_val_7764_, 2);
                v_mctx_7769_ = leanh::lean_ctor_get(v_val_7764_, 3);
                leanh::lean_inc(v_val_7764_);
                v___x_7770_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed as *mut core::ffi::c_void, 6, 1);
                leanh::lean_closure_set(v___x_7770_, 0, v_val_7764_);
                leanh::lean_inc_ref(v_mctx_7769_);
                v___x_7771_ = leanh::lean_alloc_closure(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed as *mut core::ffi::c_void, 8, 3);
                leanh::lean_closure_set(v___x_7771_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_7771_, 1, v_mctx_7769_);
                leanh::lean_closure_set(v___x_7771_, 2, v___x_7770_);
                v___x_7772_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_7771_, v___y_7715_, v___y_7716_, v___y_7717_, v___y_7718_);
                if leanh::lean_obj_tag(v___x_7772_) == 0 {
                    v_a_7773_ = leanh::lean_ctor_get(v___x_7772_, 0);
                    leanh::lean_inc(v_a_7773_);
                    leanh::lean_dec_ref_known(v___x_7772_, 1);
                    v___x_7774_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_fst_7736_, v_a_7773_);
                    if v___x_7774_ == 0 {
                        v_eNew_7775_ = leanh::lean_ctor_get(v_result_7768_, 0);
                        leanh::lean_inc_ref(v_eNew_7775_);
                        leanh::lean_inc_ref(v_mctx_7769_);
                        v___x_7776_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(
                            v_mctx_7769_,
                            v_eNew_7775_,
                            v___y_7715_,
                            v___y_7716_,
                            v___y_7717_,
                            v___y_7718_,
                        );
                        if leanh::lean_obj_tag(v___x_7776_) == 0 {
                            if v_stopAtRfl_7741_ == 0 {
                                leanh::lean_dec_ref_known(v___x_7776_, 1);
                                leanh::lean_del_object(v___x_7766_);
                                v___x_7777_ = leanh::lean_box(0);
                                v___x_7778_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_fst_7736_, v_a_7773_, v___x_7777_);
                                v___x_7779_ = lean_array_push(v_snd_7737_, v_val_7764_);
                                if v_isShared_7740_ == 0 {
                                    leanh::lean_ctor_set(v___x_7739_, 1, v___x_7779_);
                                    leanh::lean_ctor_set(v___x_7739_, 0, v___x_7778_);
                                    v___x_7781_ = v___x_7739_;
                                    state = 7;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_7786_ =
                                        leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7786_,
                                        0,
                                        v___x_7778_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7786_,
                                        1,
                                        v___x_7779_,
                                    );
                                    v___x_7781_ = v_reuseFailAlloc_7786_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_7787_ = leanh::lean_ctor_get(v___x_7776_, 0);
                                v_isSharedCheck_7817_ =
                                    (!leanh::lean_is_exclusive(v___x_7776_)) as u8;
                                if v_isSharedCheck_7817_ == 0 {
                                    v___x_7789_ = v___x_7776_;
                                    v_isShared_7790_ = v_isSharedCheck_7817_;
                                    state = 9;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_7787_);
                                    leanh::lean_dec(v___x_7776_);
                                    v___x_7789_ = leanh::lean_box(0);
                                    v_isShared_7790_ = v_isSharedCheck_7817_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_7773_);
                            leanh::lean_del_object(v___x_7766_);
                            leanh::lean_dec(v_val_7764_);
                            leanh::lean_del_object(v___x_7739_);
                            leanh::lean_dec(v_snd_7737_);
                            leanh::lean_dec(v_fst_7736_);
                            leanh::lean_del_object(v___x_7730_);
                            leanh::lean_dec_ref(v_cfg_7712_);
                            v_a_7818_ = leanh::lean_ctor_get(v___x_7776_, 0);
                            v_isSharedCheck_7825_ =
                                (!leanh::lean_is_exclusive(v___x_7776_)) as u8;
                            if v_isSharedCheck_7825_ == 0 {
                                v___x_7820_ = v___x_7776_;
                                v_isShared_7821_ = v_isSharedCheck_7825_;
                                state = 16;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7818_);
                                leanh::lean_dec(v___x_7776_);
                                v___x_7820_ = leanh::lean_box(0);
                                v_isShared_7821_ = v_isSharedCheck_7825_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_7773_);
                        leanh::lean_del_object(v___x_7766_);
                        leanh::lean_dec(v_val_7764_);
                        if v_isShared_7740_ == 0 {
                            v___x_7827_ = v___x_7739_;
                            state = 18;
                            continue;
                        } else {
                            v_reuseFailAlloc_7832_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7832_, 0, v_fst_7736_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7832_, 1, v_snd_7737_);
                            v___x_7827_ = v_reuseFailAlloc_7832_;
                            state = 18;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_7766_);
                    leanh::lean_dec(v_val_7764_);
                    leanh::lean_del_object(v___x_7739_);
                    leanh::lean_dec(v_snd_7737_);
                    leanh::lean_dec(v_fst_7736_);
                    leanh::lean_del_object(v___x_7730_);
                    leanh::lean_dec_ref(v_cfg_7712_);
                    v_a_7833_ = leanh::lean_ctor_get(v___x_7772_, 0);
                    v_isSharedCheck_7840_ = (!leanh::lean_is_exclusive(v___x_7772_)) as u8;
                    if v_isSharedCheck_7840_ == 0 {
                        v___x_7835_ = v___x_7772_;
                        v_isShared_7836_ = v_isSharedCheck_7840_;
                        state = 20;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7833_);
                        leanh::lean_dec(v___x_7772_);
                        v___x_7835_ = leanh::lean_box(0);
                        v_isShared_7836_ = v_isSharedCheck_7840_;
                        state = 20;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_7731_ == 0 {
                    leanh::lean_ctor_set(v___x_7730_, 1, v___x_7781_);
                    leanh::lean_ctor_set(v___x_7730_, 0, v___x_7756_);
                    v___x_7783_ = v___x_7730_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7785_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7785_, 0, v___x_7756_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7785_, 1, v___x_7781_);
                    v___x_7783_ = v_reuseFailAlloc_7785_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_as_x27_7713_ = v_tail_7723_;
                v_b_7714_ = v___x_7783_;
                state = 0;
                continue;
            }
            9 => {
                v___x_7791_ = (leanh::lean_unbox(v_a_7787_) as u8);
                leanh::lean_dec(v_a_7787_);
                if v___x_7791_ == 0 {
                    leanh::lean_del_object(v___x_7789_);
                    leanh::lean_del_object(v___x_7766_);
                    v___x_7792_ = leanh::lean_box(0);
                    v___x_7793_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_fst_7736_, v_a_7773_, v___x_7792_);
                    v___x_7794_ = lean_array_push(v_snd_7737_, v_val_7764_);
                    if v_isShared_7740_ == 0 {
                        leanh::lean_ctor_set(v___x_7739_, 1, v___x_7794_);
                        leanh::lean_ctor_set(v___x_7739_, 0, v___x_7793_);
                        v___x_7796_ = v___x_7739_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_7801_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7801_, 0, v___x_7793_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7801_, 1, v___x_7794_);
                        v___x_7796_ = v_reuseFailAlloc_7801_;
                        state = 10;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_7773_);
                    leanh::lean_dec_ref(v_cfg_7712_);
                    v___x_7802_ = leanh::lean_unsigned_to_nat(1);
                    v___x_7803_ = lean_mk_empty_array_with_capacity(v___x_7802_);
                    v___x_7804_ = lean_array_push(v___x_7803_, v_val_7764_);
                    if v_isShared_7767_ == 0 {
                        leanh::lean_ctor_set(v___x_7766_, 0, v___x_7804_);
                        v___x_7806_ = v___x_7766_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_7816_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7816_, 0, v___x_7804_);
                        v___x_7806_ = v_reuseFailAlloc_7816_;
                        state = 12;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_7731_ == 0 {
                    leanh::lean_ctor_set(v___x_7730_, 1, v___x_7796_);
                    leanh::lean_ctor_set(v___x_7730_, 0, v___x_7756_);
                    v___x_7798_ = v___x_7730_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_7800_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7800_, 0, v___x_7756_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7800_, 1, v___x_7796_);
                    v___x_7798_ = v_reuseFailAlloc_7800_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_as_x27_7713_ = v_tail_7723_;
                v_b_7714_ = v___x_7798_;
                state = 0;
                continue;
            }
            12 => {
                if v_isShared_7740_ == 0 {
                    v___x_7808_ = v___x_7739_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_7815_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7815_, 0, v_fst_7736_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7815_, 1, v_snd_7737_);
                    v___x_7808_ = v_reuseFailAlloc_7815_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_7731_ == 0 {
                    leanh::lean_ctor_set(v___x_7730_, 1, v___x_7808_);
                    leanh::lean_ctor_set(v___x_7730_, 0, v___x_7806_);
                    v___x_7810_ = v___x_7730_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_7814_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7814_, 0, v___x_7806_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7814_, 1, v___x_7808_);
                    v___x_7810_ = v_reuseFailAlloc_7814_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_7790_ == 0 {
                    leanh::lean_ctor_set(v___x_7789_, 0, v___x_7810_);
                    v___x_7812_ = v___x_7789_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_7813_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7813_, 0, v___x_7810_);
                    v___x_7812_ = v_reuseFailAlloc_7813_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_7812_;
            }
            16 => {
                if v_isShared_7821_ == 0 {
                    v___x_7823_ = v___x_7820_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_7824_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7824_, 0, v_a_7818_);
                    v___x_7823_ = v_reuseFailAlloc_7824_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_7823_;
            }
            18 => {
                if v_isShared_7731_ == 0 {
                    leanh::lean_ctor_set(v___x_7730_, 1, v___x_7827_);
                    leanh::lean_ctor_set(v___x_7730_, 0, v___x_7756_);
                    v___x_7829_ = v___x_7730_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_7831_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7831_, 0, v___x_7756_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7831_, 1, v___x_7827_);
                    v___x_7829_ = v_reuseFailAlloc_7831_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v_as_x27_7713_ = v_tail_7723_;
                v_b_7714_ = v___x_7829_;
                state = 0;
                continue;
            }
            20 => {
                if v_isShared_7836_ == 0 {
                    v___x_7838_ = v___x_7835_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_7839_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7839_, 0, v_a_7833_);
                    v___x_7838_ = v_reuseFailAlloc_7839_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_7838_;
            }
            22 => {
                if v_isShared_7845_ == 0 {
                    v___x_7847_ = v___x_7844_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_7848_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7848_, 0, v_a_7842_);
                    v___x_7847_ = v_reuseFailAlloc_7848_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_7847_;
            }
            24 => {
                if v_isShared_7731_ == 0 {
                    leanh::lean_ctor_set(v___x_7730_, 1, v___x_7852_);
                    leanh::lean_ctor_set(v___x_7730_, 0, v___x_7850_);
                    v___x_7854_ = v___x_7730_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_7858_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7858_, 0, v___x_7850_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7858_, 1, v___x_7852_);
                    v___x_7854_ = v_reuseFailAlloc_7858_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                if v_isShared_7735_ == 0 {
                    leanh::lean_ctor_set(v___x_7734_, 0, v___x_7854_);
                    v___x_7856_ = v___x_7734_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_7857_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7857_, 0, v___x_7854_);
                    v___x_7856_ = v_reuseFailAlloc_7857_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_7856_;
            }
            27 => {
                if v_isShared_7731_ == 0 {
                    leanh::lean_ctor_set(v___x_7730_, 1, v___x_7862_);
                    leanh::lean_ctor_set(v___x_7730_, 0, v___x_7860_);
                    v___x_7864_ = v___x_7730_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_7868_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7868_, 0, v___x_7860_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7868_, 1, v___x_7862_);
                    v___x_7864_ = v_reuseFailAlloc_7868_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_7735_ == 0 {
                    leanh::lean_ctor_set(v___x_7734_, 0, v___x_7864_);
                    v___x_7866_ = v___x_7734_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_7867_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7867_, 0, v___x_7864_);
                    v___x_7866_ = v_reuseFailAlloc_7867_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_7866_;
            }
            30 => {
                if v_isShared_7877_ == 0 {
                    v___x_7879_ = v___x_7876_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_7880_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7880_, 0, v_a_7874_);
                    v___x_7879_ = v_reuseFailAlloc_7880_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_7879_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg___boxed(
    mut v_cfg_7882_: *mut leanh::LeanObject,
    mut v_as_x27_7883_: *mut leanh::LeanObject,
    mut v_b_7884_: *mut leanh::LeanObject,
    mut v___y_7885_: *mut leanh::LeanObject,
    mut v___y_7886_: *mut leanh::LeanObject,
    mut v___y_7887_: *mut leanh::LeanObject,
    mut v___y_7888_: *mut leanh::LeanObject,
    mut v___y_7889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7890_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(
        v_cfg_7882_,
        v_as_x27_7883_,
        v_b_7884_,
        v___y_7885_,
        v___y_7886_,
        v___y_7887_,
        v___y_7888_,
    );
    leanh::lean_dec(v___y_7888_);
    leanh::lean_dec_ref(v___y_7887_);
    leanh::lean_dec(v___y_7886_);
    leanh::lean_dec_ref(v___y_7885_);
    leanh::lean_dec(v_as_x27_7883_);
    return v_res_7890_;
}
pub unsafe fn l_Lean_Meta_Rewrites_takeListAux(
    mut v_cfg_7891_: *mut leanh::LeanObject,
    mut v_seen_7892_: *mut leanh::LeanObject,
    mut v_acc_7893_: *mut leanh::LeanObject,
    mut v_xs_7894_: *mut leanh::LeanObject,
    mut v_a_7895_: *mut leanh::LeanObject,
    mut v_a_7896_: *mut leanh::LeanObject,
    mut v_a_7897_: *mut leanh::LeanObject,
    mut v_a_7898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7907_: u8 = 0;
    let mut v_fst_7908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7918_: u8 = 0;
    let mut v_a_7919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7922_: u8 = 0;
    let mut v___x_7924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7926_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7900_ = leanh::lean_box(0);
                v___x_7901_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7901_, 0, v_seen_7892_);
                leanh::lean_ctor_set(v___x_7901_, 1, v_acc_7893_);
                v___x_7902_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7902_, 0, v___x_7900_);
                leanh::lean_ctor_set(v___x_7902_, 1, v___x_7901_);
                v___x_7903_ =
                    l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(
                        v_cfg_7891_,
                        v_xs_7894_,
                        v___x_7902_,
                        v_a_7895_,
                        v_a_7896_,
                        v_a_7897_,
                        v_a_7898_,
                    );
                if leanh::lean_obj_tag(v___x_7903_) == 0 {
                    v_a_7904_ = leanh::lean_ctor_get(v___x_7903_, 0);
                    v_isSharedCheck_7918_ = (!leanh::lean_is_exclusive(v___x_7903_)) as u8;
                    if v_isSharedCheck_7918_ == 0 {
                        v___x_7906_ = v___x_7903_;
                        v_isShared_7907_ = v_isSharedCheck_7918_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7904_);
                        leanh::lean_dec(v___x_7903_);
                        v___x_7906_ = leanh::lean_box(0);
                        v_isShared_7907_ = v_isSharedCheck_7918_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7919_ = leanh::lean_ctor_get(v___x_7903_, 0);
                    v_isSharedCheck_7926_ = (!leanh::lean_is_exclusive(v___x_7903_)) as u8;
                    if v_isSharedCheck_7926_ == 0 {
                        v___x_7921_ = v___x_7903_;
                        v_isShared_7922_ = v_isSharedCheck_7926_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7919_);
                        leanh::lean_dec(v___x_7903_);
                        v___x_7921_ = leanh::lean_box(0);
                        v_isShared_7922_ = v_isSharedCheck_7926_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_7908_ = leanh::lean_ctor_get(v_a_7904_, 0);
                if leanh::lean_obj_tag(v_fst_7908_) == 0 {
                    v_snd_7909_ = leanh::lean_ctor_get(v_a_7904_, 1);
                    leanh::lean_inc(v_snd_7909_);
                    leanh::lean_dec(v_a_7904_);
                    v_snd_7910_ = leanh::lean_ctor_get(v_snd_7909_, 1);
                    leanh::lean_inc(v_snd_7910_);
                    leanh::lean_dec(v_snd_7909_);
                    if v_isShared_7907_ == 0 {
                        leanh::lean_ctor_set(v___x_7906_, 0, v_snd_7910_);
                        v___x_7912_ = v___x_7906_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7913_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7913_, 0, v_snd_7910_);
                        v___x_7912_ = v_reuseFailAlloc_7913_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_7908_);
                    leanh::lean_dec(v_a_7904_);
                    v_val_7914_ = leanh::lean_ctor_get(v_fst_7908_, 0);
                    leanh::lean_inc(v_val_7914_);
                    leanh::lean_dec_ref_known(v_fst_7908_, 1);
                    if v_isShared_7907_ == 0 {
                        leanh::lean_ctor_set(v___x_7906_, 0, v_val_7914_);
                        v___x_7916_ = v___x_7906_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7917_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7917_, 0, v_val_7914_);
                        v___x_7916_ = v_reuseFailAlloc_7917_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_7912_;
            }
            3 => {
                return v___x_7916_;
            }
            4 => {
                if v_isShared_7922_ == 0 {
                    v___x_7924_ = v___x_7921_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7925_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7925_, 0, v_a_7919_);
                    v___x_7924_ = v_reuseFailAlloc_7925_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7924_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Rewrites_takeListAux___boxed(
    mut v_cfg_7927_: *mut leanh::LeanObject,
    mut v_seen_7928_: *mut leanh::LeanObject,
    mut v_acc_7929_: *mut leanh::LeanObject,
    mut v_xs_7930_: *mut leanh::LeanObject,
    mut v_a_7931_: *mut leanh::LeanObject,
    mut v_a_7932_: *mut leanh::LeanObject,
    mut v_a_7933_: *mut leanh::LeanObject,
    mut v_a_7934_: *mut leanh::LeanObject,
    mut v_a_7935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7936_ = l_Lean_Meta_Rewrites_takeListAux(
        v_cfg_7927_,
        v_seen_7928_,
        v_acc_7929_,
        v_xs_7930_,
        v_a_7931_,
        v_a_7932_,
        v_a_7933_,
        v_a_7934_,
    );
    leanh::lean_dec(v_a_7934_);
    leanh::lean_dec_ref(v_a_7933_);
    leanh::lean_dec(v_a_7932_);
    leanh::lean_dec_ref(v_a_7931_);
    leanh::lean_dec(v_xs_7930_);
    return v_res_7936_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0(
    mut v_00_u03b2_7937_: *mut leanh::LeanObject,
    mut v_m_7938_: *mut leanh::LeanObject,
    mut v_a_7939_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_7940_: u8 = 0;
    v___x_7940_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_m_7938_, v_a_7939_);
    return v___x_7940_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___boxed(
    mut v_00_u03b2_7941_: *mut leanh::LeanObject,
    mut v_m_7942_: *mut leanh::LeanObject,
    mut v_a_7943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7944_: u8 = 0;
    let mut v_r_7945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7944_ =
        l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0(
            v_00_u03b2_7941_,
            v_m_7942_,
            v_a_7943_,
        );
    leanh::lean_dec_ref(v_a_7943_);
    leanh::lean_dec_ref(v_m_7942_);
    v_r_7945_ = leanh::lean_box((v_res_7944_) as usize);
    return v_r_7945_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1(
    mut v_00_u03b2_7946_: *mut leanh::LeanObject,
    mut v_m_7947_: *mut leanh::LeanObject,
    mut v_a_7948_: *mut leanh::LeanObject,
    mut v_b_7949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7950_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_m_7947_, v_a_7948_, v_b_7949_);
    return v___x_7950_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2(
    mut v_cfg_7951_: *mut leanh::LeanObject,
    mut v_as_7952_: *mut leanh::LeanObject,
    mut v_as_x27_7953_: *mut leanh::LeanObject,
    mut v_b_7954_: *mut leanh::LeanObject,
    mut v_a_7955_: *mut leanh::LeanObject,
    mut v___y_7956_: *mut leanh::LeanObject,
    mut v___y_7957_: *mut leanh::LeanObject,
    mut v___y_7958_: *mut leanh::LeanObject,
    mut v___y_7959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7961_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7961_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(
        v_cfg_7951_,
        v_as_x27_7953_,
        v_b_7954_,
        v___y_7956_,
        v___y_7957_,
        v___y_7958_,
        v___y_7959_,
    );
    return v___x_7961_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___boxed(
    mut v_cfg_7962_: *mut leanh::LeanObject,
    mut v_as_7963_: *mut leanh::LeanObject,
    mut v_as_x27_7964_: *mut leanh::LeanObject,
    mut v_b_7965_: *mut leanh::LeanObject,
    mut v_a_7966_: *mut leanh::LeanObject,
    mut v___y_7967_: *mut leanh::LeanObject,
    mut v___y_7968_: *mut leanh::LeanObject,
    mut v___y_7969_: *mut leanh::LeanObject,
    mut v___y_7970_: *mut leanh::LeanObject,
    mut v___y_7971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7972_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2(
        v_cfg_7962_,
        v_as_7963_,
        v_as_x27_7964_,
        v_b_7965_,
        v_a_7966_,
        v___y_7967_,
        v___y_7968_,
        v___y_7969_,
        v___y_7970_,
    );
    leanh::lean_dec(v___y_7970_);
    leanh::lean_dec_ref(v___y_7969_);
    leanh::lean_dec(v___y_7968_);
    leanh::lean_dec_ref(v___y_7967_);
    leanh::lean_dec(v_as_x27_7964_);
    leanh::lean_dec(v_as_7963_);
    return v_res_7972_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(
    mut v_00_u03b2_7973_: *mut leanh::LeanObject,
    mut v_a_7974_: *mut leanh::LeanObject,
    mut v_x_7975_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_7976_: u8 = 0;
    v___x_7976_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_7974_, v_x_7975_);
    return v___x_7976_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___boxed(
    mut v_00_u03b2_7977_: *mut leanh::LeanObject,
    mut v_a_7978_: *mut leanh::LeanObject,
    mut v_x_7979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7980_: u8 = 0;
    let mut v_r_7981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7980_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(v_00_u03b2_7977_, v_a_7978_, v_x_7979_);
    leanh::lean_dec(v_x_7979_);
    leanh::lean_dec_ref(v_a_7978_);
    v_r_7981_ = leanh::lean_box((v_res_7980_) as usize);
    return v_r_7981_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2(
    mut v_00_u03b2_7982_: *mut leanh::LeanObject,
    mut v_data_7983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7984_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(v_data_7983_);
    return v___x_7984_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3(
    mut v_00_u03b2_7985_: *mut leanh::LeanObject,
    mut v_a_7986_: *mut leanh::LeanObject,
    mut v_b_7987_: *mut leanh::LeanObject,
    mut v_x_7988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7989_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_7986_, v_b_7987_, v_x_7988_);
    return v___x_7989_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3(
    mut v_00_u03b2_7990_: *mut leanh::LeanObject,
    mut v_i_7991_: *mut leanh::LeanObject,
    mut v_source_7992_: *mut leanh::LeanObject,
    mut v_target_7993_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7994_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(v_i_7991_, v_source_7992_, v_target_7993_);
    return v___x_7994_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5(
    mut v_00_u03b2_7995_: *mut leanh::LeanObject,
    mut v_x_7996_: *mut leanh::LeanObject,
    mut v_x_7997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7998_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(v_x_7996_, v_x_7997_);
    return v___x_7998_;
}
pub unsafe fn _init_l_Lean_Meta_Rewrites_findRewrites___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_7999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8001_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7999_ = leanh::lean_box(0);
    v___x_8000_ = leanh::lean_unsigned_to_nat(16);
    v___x_8001_ = lean_mk_array(v___x_8000_, v___x_7999_);
    return v___x_8001_;
}
pub unsafe fn _init_l_Lean_Meta_Rewrites_findRewrites___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_8002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8002_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Rewrites_findRewrites___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Rewrites_findRewrites___closed__0_once),
        _init_l_Lean_Meta_Rewrites_findRewrites___closed__0,
    );
    v___x_8003_ = leanh::lean_unsigned_to_nat(0);
    v___x_8004_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_8004_, 0, v___x_8003_);
    leanh::lean_ctor_set(v___x_8004_, 1, v___x_8002_);
    return v___x_8004_;
}
pub unsafe fn l_Lean_Meta_Rewrites_findRewrites(
    mut v_hyps_8005_: *mut leanh::LeanObject,
    mut v_moduleRef_8006_: *mut leanh::LeanObject,
    mut v_goal_8007_: *mut leanh::LeanObject,
    mut v_target_8008_: *mut leanh::LeanObject,
    mut v_forbidden_8009_: *mut leanh::LeanObject,
    mut v_side_8010_: u8,
    mut v_stopAtRfl_8011_: u8,
    mut v_max_8012_: *mut leanh::LeanObject,
    mut v_leavePercentHeartbeats_8013_: *mut leanh::LeanObject,
    mut v_a_8014_: *mut leanh::LeanObject,
    mut v_a_8015_: *mut leanh::LeanObject,
    mut v_a_8016_: *mut leanh::LeanObject,
    mut v_a_8017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_8024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_minHeartbeats_8026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8039_: u8 = 0;
    let mut v___x_8040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8044_: u8 = 0;
    let mut v_a_8045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8048_: u8 = 0;
    let mut v___x_8050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8052_: u8 = 0;
    let mut v___x_8053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8054_: u8 = 0;
    let mut v___x_8055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8063_: u8 = 0;
    let mut v___x_8065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8067_: u8 = 0;
    let mut v_a_8068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8071_: u8 = 0;
    let mut v___x_8073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8075_: u8 = 0;
    let mut v_a_8076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8079_: u8 = 0;
    let mut v___x_8081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8083_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8019_ = lean_st_ref_get(v_a_8015_);
                leanh::lean_inc_ref(v_target_8008_);
                v___x_8020_ = l_Lean_Meta_Rewrites_rewriteCandidates(
                    v_hyps_8005_,
                    v_moduleRef_8006_,
                    v_target_8008_,
                    v_forbidden_8009_,
                    v_a_8014_,
                    v_a_8015_,
                    v_a_8016_,
                    v_a_8017_,
                );
                if leanh::lean_obj_tag(v___x_8020_) == 0 {
                    v_a_8021_ = leanh::lean_ctor_get(v___x_8020_, 0);
                    leanh::lean_inc(v_a_8021_);
                    leanh::lean_dec_ref_known(v___x_8020_, 1);
                    v___x_8022_ = l_Lean_getMaxHeartbeats___redArg(v_a_8016_);
                    if leanh::lean_obj_tag(v___x_8022_) == 0 {
                        v_a_8023_ = leanh::lean_ctor_get(v___x_8022_, 0);
                        leanh::lean_inc(v_a_8023_);
                        leanh::lean_dec_ref_known(v___x_8022_, 1);
                        v_mctx_8024_ = leanh::lean_ctor_get(v___x_8019_, 0);
                        leanh::lean_inc_ref(v_mctx_8024_);
                        leanh::lean_dec(v___x_8019_);
                        v___x_8053_ = leanh::lean_unsigned_to_nat(0);
                        v___x_8054_ = lean_nat_dec_eq(v_a_8023_, v___x_8053_);
                        leanh::lean_dec(v_a_8023_);
                        if v___x_8054_ == 0 {
                            v___x_8055_ = l_Lean_getRemainingHeartbeats___redArg(v_a_8016_);
                            if leanh::lean_obj_tag(v___x_8055_) == 0 {
                                v_a_8056_ = leanh::lean_ctor_get(v___x_8055_, 0);
                                leanh::lean_inc(v_a_8056_);
                                leanh::lean_dec_ref_known(v___x_8055_, 1);
                                v___x_8057_ =
                                    lean_nat_mul(v_leavePercentHeartbeats_8013_, v_a_8056_);
                                leanh::lean_dec(v_a_8056_);
                                v___x_8058_ = leanh::lean_unsigned_to_nat(100);
                                v___x_8059_ = lean_nat_div(v___x_8057_, v___x_8058_);
                                leanh::lean_dec(v___x_8057_);
                                v_minHeartbeats_8026_ = v___x_8059_;
                                v___y_8027_ = v_a_8014_;
                                v___y_8028_ = v_a_8015_;
                                v___y_8029_ = v_a_8016_;
                                v___y_8030_ = v_a_8017_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_mctx_8024_);
                                leanh::lean_dec(v_a_8021_);
                                leanh::lean_dec(v_max_8012_);
                                leanh::lean_dec_ref(v_target_8008_);
                                leanh::lean_dec(v_goal_8007_);
                                v_a_8060_ = leanh::lean_ctor_get(v___x_8055_, 0);
                                v_isSharedCheck_8067_ =
                                    (!leanh::lean_is_exclusive(v___x_8055_)) as u8;
                                if v_isSharedCheck_8067_ == 0 {
                                    v___x_8062_ = v___x_8055_;
                                    v_isShared_8063_ = v_isSharedCheck_8067_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_8060_);
                                    leanh::lean_dec(v___x_8055_);
                                    v___x_8062_ = leanh::lean_box(0);
                                    v_isShared_8063_ = v_isSharedCheck_8067_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            v_minHeartbeats_8026_ = v___x_8053_;
                            v___y_8027_ = v_a_8014_;
                            v___y_8028_ = v_a_8015_;
                            v___y_8029_ = v_a_8016_;
                            v___y_8030_ = v_a_8017_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_8021_);
                        leanh::lean_dec(v___x_8019_);
                        leanh::lean_dec(v_max_8012_);
                        leanh::lean_dec_ref(v_target_8008_);
                        leanh::lean_dec(v_goal_8007_);
                        v_a_8068_ = leanh::lean_ctor_get(v___x_8022_, 0);
                        v_isSharedCheck_8075_ =
                            (!leanh::lean_is_exclusive(v___x_8022_)) as u8;
                        if v_isSharedCheck_8075_ == 0 {
                            v___x_8070_ = v___x_8022_;
                            v_isShared_8071_ = v_isSharedCheck_8075_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_8068_);
                            leanh::lean_dec(v___x_8022_);
                            v___x_8070_ = leanh::lean_box(0);
                            v_isShared_8071_ = v_isSharedCheck_8075_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_8019_);
                    leanh::lean_dec(v_max_8012_);
                    leanh::lean_dec_ref(v_target_8008_);
                    leanh::lean_dec(v_goal_8007_);
                    v_a_8076_ = leanh::lean_ctor_get(v___x_8020_, 0);
                    v_isSharedCheck_8083_ = (!leanh::lean_is_exclusive(v___x_8020_)) as u8;
                    if v_isSharedCheck_8083_ == 0 {
                        v___x_8078_ = v___x_8020_;
                        v_isShared_8079_ = v_isSharedCheck_8083_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8076_);
                        leanh::lean_dec(v___x_8020_);
                        v___x_8078_ = leanh::lean_box(0);
                        v_isShared_8079_ = v_isSharedCheck_8083_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_max_8012_);
                v___x_8031_ = leanh::lean_alloc_ctor(0, 5, (2) as u32);
                leanh::lean_ctor_set(v___x_8031_, 0, v_max_8012_);
                leanh::lean_ctor_set(v___x_8031_, 1, v_minHeartbeats_8026_);
                leanh::lean_ctor_set(v___x_8031_, 2, v_goal_8007_);
                leanh::lean_ctor_set(v___x_8031_, 3, v_target_8008_);
                leanh::lean_ctor_set(v___x_8031_, 4, v_mctx_8024_);
                leanh::lean_ctor_set_uint8(
                    v___x_8031_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v_stopAtRfl_8011_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_8031_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v_side_8010_,
                );
                v___x_8032_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Rewrites_findRewrites___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Rewrites_findRewrites___closed__1_once),
                    _init_l_Lean_Meta_Rewrites_findRewrites___closed__1,
                );
                v___x_8033_ = lean_mk_empty_array_with_capacity(v_max_8012_);
                leanh::lean_dec(v_max_8012_);
                v___x_8034_ = lean_array_to_list(v_a_8021_);
                v___x_8035_ = l_Lean_Meta_Rewrites_takeListAux(
                    v___x_8031_,
                    v___x_8032_,
                    v___x_8033_,
                    v___x_8034_,
                    v___y_8027_,
                    v___y_8028_,
                    v___y_8029_,
                    v___y_8030_,
                );
                leanh::lean_dec(v___x_8034_);
                if leanh::lean_obj_tag(v___x_8035_) == 0 {
                    v_a_8036_ = leanh::lean_ctor_get(v___x_8035_, 0);
                    v_isSharedCheck_8044_ = (!leanh::lean_is_exclusive(v___x_8035_)) as u8;
                    if v_isSharedCheck_8044_ == 0 {
                        v___x_8038_ = v___x_8035_;
                        v_isShared_8039_ = v_isSharedCheck_8044_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8036_);
                        leanh::lean_dec(v___x_8035_);
                        v___x_8038_ = leanh::lean_box(0);
                        v_isShared_8039_ = v_isSharedCheck_8044_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_8045_ = leanh::lean_ctor_get(v___x_8035_, 0);
                    v_isSharedCheck_8052_ = (!leanh::lean_is_exclusive(v___x_8035_)) as u8;
                    if v_isSharedCheck_8052_ == 0 {
                        v___x_8047_ = v___x_8035_;
                        v_isShared_8048_ = v_isSharedCheck_8052_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8045_);
                        leanh::lean_dec(v___x_8035_);
                        v___x_8047_ = leanh::lean_box(0);
                        v_isShared_8048_ = v_isSharedCheck_8052_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_8040_ = lean_array_to_list(v_a_8036_);
                if v_isShared_8039_ == 0 {
                    leanh::lean_ctor_set(v___x_8038_, 0, v___x_8040_);
                    v___x_8042_ = v___x_8038_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8043_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8043_, 0, v___x_8040_);
                    v___x_8042_ = v_reuseFailAlloc_8043_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_8042_;
            }
            4 => {
                if v_isShared_8048_ == 0 {
                    v___x_8050_ = v___x_8047_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8051_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8051_, 0, v_a_8045_);
                    v___x_8050_ = v_reuseFailAlloc_8051_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_8050_;
            }
            6 => {
                if v_isShared_8063_ == 0 {
                    v___x_8065_ = v___x_8062_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8066_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8066_, 0, v_a_8060_);
                    v___x_8065_ = v_reuseFailAlloc_8066_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_8065_;
            }
            8 => {
                if v_isShared_8071_ == 0 {
                    v___x_8073_ = v___x_8070_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8074_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8074_, 0, v_a_8068_);
                    v___x_8073_ = v_reuseFailAlloc_8074_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_8073_;
            }
            10 => {
                if v_isShared_8079_ == 0 {
                    v___x_8081_ = v___x_8078_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_8082_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8082_, 0, v_a_8076_);
                    v___x_8081_ = v_reuseFailAlloc_8082_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_8081_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Rewrites_findRewrites___boxed(
    mut v_hyps_8084_: *mut leanh::LeanObject,
    mut v_moduleRef_8085_: *mut leanh::LeanObject,
    mut v_goal_8086_: *mut leanh::LeanObject,
    mut v_target_8087_: *mut leanh::LeanObject,
    mut v_forbidden_8088_: *mut leanh::LeanObject,
    mut v_side_8089_: *mut leanh::LeanObject,
    mut v_stopAtRfl_8090_: *mut leanh::LeanObject,
    mut v_max_8091_: *mut leanh::LeanObject,
    mut v_leavePercentHeartbeats_8092_: *mut leanh::LeanObject,
    mut v_a_8093_: *mut leanh::LeanObject,
    mut v_a_8094_: *mut leanh::LeanObject,
    mut v_a_8095_: *mut leanh::LeanObject,
    mut v_a_8096_: *mut leanh::LeanObject,
    mut v_a_8097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_side_boxed_8098_: u8 = 0;
    let mut v_stopAtRfl_boxed_8099_: u8 = 0;
    let mut v_res_8100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_side_boxed_8098_ = (leanh::lean_unbox(v_side_8089_) as u8);
    v_stopAtRfl_boxed_8099_ = (leanh::lean_unbox(v_stopAtRfl_8090_) as u8);
    v_res_8100_ = l_Lean_Meta_Rewrites_findRewrites(
        v_hyps_8084_,
        v_moduleRef_8085_,
        v_goal_8086_,
        v_target_8087_,
        v_forbidden_8088_,
        v_side_boxed_8098_,
        v_stopAtRfl_boxed_8099_,
        v_max_8091_,
        v_leavePercentHeartbeats_8092_,
        v_a_8093_,
        v_a_8094_,
        v_a_8095_,
        v_a_8096_,
    );
    leanh::lean_dec(v_a_8096_);
    leanh::lean_dec_ref(v_a_8095_);
    leanh::lean_dec(v_a_8094_);
    leanh::lean_dec_ref(v_a_8093_);
    leanh::lean_dec(v_leavePercentHeartbeats_8092_);
    leanh::lean_dec(v_forbidden_8088_);
    return v_res_8100_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Rewrites(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_LazyDiscrTree(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Rewrite(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_SolveByElim(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_TryThis(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Heartbeats(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Meta_Rewrites_forwardWeight = _init_l_Lean_Meta_Rewrites_forwardWeight();
    leanh::lean_mark_persistent(l_Lean_Meta_Rewrites_forwardWeight);
    l_Lean_Meta_Rewrites_backwardWeight = _init_l_Lean_Meta_Rewrites_backwardWeight();
    leanh::lean_mark_persistent(l_Lean_Meta_Rewrites_backwardWeight);
    res = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1202513136____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ExtState_default =
        leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(
        l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ExtState_default,
    );
    leanh::lean_dec_ref(res);
    l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState =
        _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState();
    leanh::lean_mark_persistent(
        l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState,
    );
    res = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ext =
        leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(
        l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ext,
    );
    leanh::lean_dec_ref(res);
    l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask =
        _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask();
    leanh::lean_mark_persistent(
        l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask,
    );
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Rewrites(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Rewrites(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_LazyDiscrTree(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Rewrite(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Refl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_SolveByElim(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_TryThis(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_Heartbeats(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Rewrites(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Rewrites(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Rewrites(builtin);
}