// Lean compiler output
// Module: Lean.Meta.Tactic.SplitIf
// Imports: Lean.Meta.Tactic.Cases Lean.Meta.Tactic.Simp.Rewrite Lean.Meta.Tactic.Simp.Main
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::MetaTypes::l_Lean_Meta_Simp_neutralConfig;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_num___override, l_Lean_Name_str___override,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{l_Lean_Core_mkFreshUserName, l_Lean_Exception_isRuntime};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::{l_Lean_Options_empty, lean_register_option};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_app___override,
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_constLevels_x21, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_getBoundedAppFn,
    l_Lean_Expr_getRevArg_x21, l_Lean_Expr_hasFVar, l_Lean_Expr_hasLooseBVars, l_Lean_Expr_hasMVar,
    l_Lean_Expr_hash, l_Lean_Expr_headBeta, l_Lean_Expr_isApp, l_Lean_Expr_isAppOf,
    l_Lean_Expr_isAppOfArity, l_Lean_Expr_isConstOf, l_Lean_Expr_sort___override,
    l_Lean_instBEqMVarId_beq, l_Lean_instInhabitedExpr, l_Lean_mkApp3, l_Lean_mkApp4,
    l_Lean_mkApp5, l_Lean_mkApp6, l_Lean_mkApp8, l_Lean_mkAppB, l_Lean_mkBVar, l_Lean_mkConst,
    l_Lean_mkFVar, l_Lean_mkLambda, l_Lean_mkNot,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_index, l_Lean_LocalDecl_isAuxDecl, l_Lean_LocalDecl_toExpr,
    l_Lean_LocalDecl_type, lean_local_ctx_num_indices,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_indentExpr,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{l_Lean_Meta_mkDecide, l_Lean_Meta_mkEqRefl};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_Meta_Context_config,
    l_Lean_Meta_Context_configKey, l_Lean_Meta_ParamInfo_isExplicit,
    l_Lean_Meta_SavedState_restore___redArg, l_Lean_Meta_TransparencyMode_toUInt64,
    l_Lean_Meta_instInhabitedMetaM___lam__0___boxed,
    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg, l_Lean_Meta_isExprDefEq,
    l_Lean_Meta_saveState___redArg,
};
use crate::r#gen::Lean::Meta::DiscrTree::Basic::l_Lean_Meta_DiscrTree_empty;
use crate::r#gen::Lean::Meta::FunInfo::l_Lean_Meta_getFunInfo;
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProof;
use crate::r#gen::Lean::Meta::Match::MatcherInfo::{
    l_Lean_Meta_Match_MatcherInfo_arity, l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos,
    l_Lean_Meta_isMatcherAppCore_x3f,
};
use crate::r#gen::Lean::Meta::SynthInstance::l_Lean_Meta_trySynthInstance;
use crate::r#gen::Lean::Meta::Tactic::Cases::{
    initialize_Lean_Meta_Tactic_Cases, l_Lean_MVarId_byCasesDec,
    runtime_initialize_Lean_Meta_Tactic_Cases,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Main::{
    initialize_Lean_Meta_Tactic_Simp_Main, l_Lean_Meta_simpLocalDecl, l_Lean_Meta_simpTarget,
    runtime_initialize_Lean_Meta_Tactic_Simp_Main,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Rewrite::{
    initialize_Lean_Meta_Tactic_Simp_Rewrite, runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpCongrTheorems::l_Lean_Meta_getSimpCongrTheorems___redArg;
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpTheorems::l_Lean_Meta_SimpTheorems_addConst;
use crate::r#gen::Lean::Meta::Tactic::Simp::Simproc::l_Lean_Meta_Simp_Simprocs_addCore;
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::{
    l_Lean_Meta_Simp_Result_getProof, l_Lean_Meta_Simp_mkContext___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_MVarId_getType;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::PtrSet::{
    l_Lean_instBEqPtr___lam__0___boxed, l_Lean_instHashablePtr___lam__0___boxed,
    l_Lean_mkPtrSet___redArg,
};
use crate::r#gen::Lean::Util::Recognizers::{l_Lean_Expr_isDIte, l_Lean_Expr_isIte};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_contains___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg,
};
use crate::ffi::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::ffi::{lean_array_fset, lean_array_set};
use crate::ffi::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_land, lean_usize_to_uint64,
};
use crate::ffi::{lean_usize_of_nat, lean_usize_sub};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_panic_fn_borrowed, lean_uint64_mix_hash, lean_usize_dec_eq,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::ffi::lean_ptr_addr;
use crate::ffi::lean_expr_eqv;
use crate::ffi::{lean_infer_type, lean_whnf};
use crate::ffi::lean_simp;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__2_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__1_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [105, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__1_value) as *mut crate::leanh::LeanObject,18356704233129443855 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 105, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__3_value) as *mut crate::leanh::LeanObject,8391571994004792969 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__0_value:
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
    m_fun: l_Lean_instBEqPtr___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__1_value:
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
    m_fun: l_Lean_instHashablePtr___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 112, 108, 105, 116, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__1_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__0_value) as *mut crate::leanh::LeanObject,18188493160499796729 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__1_value) as *mut crate::leanh::LeanObject,5819253486582635410 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__3_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__3_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__6_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 97, 110, 100, 105, 100, 97, 116, 101, 58, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 97, 99, 107, 119, 97, 114, 100, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,15861075605163525197 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__0_value) as *mut crate::leanh::LeanObject,3769529592764303199 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<103> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 103, m_capacity: 103, m_length: 102, m_data: [117, 115, 101, 32, 116, 104, 101, 32, 111, 108, 100, 32, 115, 101, 109, 97, 110, 116, 105, 99, 115, 32, 102, 111, 114, 32, 116, 104, 101, 32, 96, 115, 112, 108, 105, 116, 96, 32, 116, 97, 99, 116, 105, 99, 32, 119, 104, 101, 114, 101, 32, 110, 101, 115, 116, 101, 100, 32, 96, 105, 102, 45, 116, 104, 101, 110, 45, 101, 108, 115, 101, 96, 32, 116, 101, 114, 109, 115, 32, 99, 111, 117, 108, 100, 32, 98, 101, 32, 115, 105, 109, 112, 108, 105, 102, 105, 101, 100, 32, 116, 111, 111, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,10487771536523666976 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__0_value) as *mut crate::leanh::LeanObject,8425219157210402150 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_backward_split: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_SplitIf_getSimpContext___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_SplitIf_getSimpContext___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_SplitIf_getSimpContext___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_SplitIf_getSimpContext___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_SplitIf_getSimpContext___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_SplitIf_getSimpContext___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_SplitIf_getSimpContext___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_SplitIf_getSimpContext___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_SplitIf_getSimpContext___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_SplitIf_getSimpContext___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_SplitIf_getSimpContext___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_SplitIf_getSimpContext___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_SplitIf_getSimpContext___closed__6_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [105, 102, 95, 112, 111, 115, 0],
    };
static mut l_Lean_Meta_SplitIf_getSimpContext___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SplitIf_getSimpContext___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_SplitIf_getSimpContext___closed__7_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_SplitIf_getSimpContext___closed__6_value)
                as *mut crate::leanh::LeanObject,
            7709702948238413810 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_SplitIf_getSimpContext___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SplitIf_getSimpContext___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_SplitIf_getSimpContext___closed__8_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [105, 102, 95, 110, 101, 103, 0],
    };
static mut l_Lean_Meta_SplitIf_getSimpContext___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SplitIf_getSimpContext___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_SplitIf_getSimpContext___closed__9_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_SplitIf_getSimpContext___closed__8_value)
                as *mut crate::leanh::LeanObject,
            16244458485308795742 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_SplitIf_getSimpContext___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SplitIf_getSimpContext___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_SplitIf_getSimpContext___closed__10_value: crate::leanh::LeanStringObject<
    8,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [100, 105, 102, 95, 112, 111, 115, 0],
};
static mut l_Lean_Meta_SplitIf_getSimpContext___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SplitIf_getSimpContext___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_SplitIf_getSimpContext___closed__11_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_SplitIf_getSimpContext___closed__10_value)
                as *mut crate::leanh::LeanObject,
            5766869440961418022 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_SplitIf_getSimpContext___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SplitIf_getSimpContext___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_SplitIf_getSimpContext___closed__12_value: crate::leanh::LeanStringObject<
    8,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [100, 105, 102, 95, 110, 101, 103, 0],
};
static mut l_Lean_Meta_SplitIf_getSimpContext___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SplitIf_getSimpContext___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_SplitIf_getSimpContext___closed__13_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_SplitIf_getSimpContext___closed__12_value)
                as *mut crate::leanh::LeanObject,
            8042454805655286456 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_SplitIf_getSimpContext___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SplitIf_getSimpContext___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 111, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject,16612019923665488825 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [110, 111, 116, 95, 110, 111, 116, 95, 105, 110, 116, 114, 111, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__2_value) as *mut crate::leanh::LeanObject,5766767816827580045 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [66, 111, 111, 108, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__1_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__0_value) as *mut crate::leanh::LeanObject,12882480457794858234 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__1_value) as *mut crate::leanh::LeanObject,9255189395584251158 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__4_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [111, 102, 95, 100, 101, 99, 105, 100, 101, 95, 101, 113, 95, 116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__4_value) as *mut crate::leanh::LeanObject,1819210885479960519 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__5_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7:
    u64 = 0;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__8_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [115, 112, 108, 105, 116, 73, 102, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,142734480563613395 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__8_value) as *mut crate::leanh::LeanObject,15847151208953044930 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__9_value) as *mut crate::leanh::LeanObject,13120239893125619637 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 105, 115, 99, 104, 97, 114, 103, 101, 63, 32, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__16_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [60, 110, 111, 116, 45, 97, 118, 97, 105, 108, 97, 98, 108, 101, 62, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__16_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__16_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__18_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 2 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__1_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [68, 101, 99, 105, 100, 97, 98, 108, 101, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__1_value) as *mut crate::leanh::LeanObject,4342836574150310743 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__4_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [105, 116, 101, 95, 99, 111, 110, 100, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__4_value) as *mut crate::leanh::LeanObject,11737681299178901513 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [104, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__0_value) as *mut crate::leanh::LeanObject,8738205681931236784 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__1_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 112, 114, 95, 112, 114, 111, 112, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__1_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__0_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__1_value) as *mut crate::leanh::LeanObject,15841710565803995561 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__5_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [109, 112, 114, 95, 110, 111, 116, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__5_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__0_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__5_value) as *mut crate::leanh::LeanObject,13082247772038117497 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__8_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [100, 105, 116, 101, 95, 99, 111, 110, 100, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__8_value) as *mut crate::leanh::LeanObject,14499483220495375228 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__9_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__2_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__2_value) as *mut crate::leanh::LeanObject,((( 5 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__3_value: crate::leanh::LeanArrayObject<6> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*6) as u16, other: 0, tag: 246 }, m_size: 6, m_capacity: 6, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__2_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__4_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__4_value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__5_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__6_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,13556645696814629918 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__8_value) as *mut crate::leanh::LeanObject,18261494228143523011 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__9_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [83, 112, 108, 105, 116, 73, 102, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__8_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__9_value) as *mut crate::leanh::LeanObject,10458587580852067660 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__10_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,11984567506173379405 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__12_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__11_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,9858203762748082744 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__12_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,17816417683613346708 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__13_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__9_value) as *mut crate::leanh::LeanObject,9467143006277171367 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__15_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 100, 117, 99, 101, 73, 116, 101, 39, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__16_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__14_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__15_value) as *mut crate::leanh::LeanObject,6234965728059245556 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__17_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__4_value) as *mut crate::leanh::LeanObject,((( 5 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__18_value: crate::leanh::LeanArrayObject<6> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*6) as u16, other: 0, tag: 246 }, m_size: 6, m_capacity: 6, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__17_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__19_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [114, 101, 100, 117, 99, 101, 68, 73, 116, 101, 39, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__20_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__14_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__19_value) as *mut crate::leanh::LeanObject,14314620247165354919 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        115, 112, 108, 105, 116, 116, 105, 110, 103, 32, 111, 110, 32, 0,
    ],
};
static mut l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        99, 111, 117, 108, 100, 32, 110, 111, 116, 32, 102, 105, 110, 100, 32, 105, 102, 32, 116,
        111, 32, 115, 112, 108, 105, 116, 58, 0,
    ],
};
static mut l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___closed__0_value:
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
    m_fun: l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_simpIfTarget_spec__0___closed__0_value:
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
    m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Meta_simpIfTarget_spec__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_Meta_simpIfTarget_spec__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_simpIfTarget___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_simpIfTarget___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_simpIfTarget___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_simpIfTarget___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_simpIfTarget___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_simpIfTarget___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_simpIfTarget___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_simpIfTarget___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_simpIfTarget___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_simpIfTarget___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_simpIfTarget___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_simpIfTarget___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_simpIfTarget___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_simpIfTarget___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_simpIfTarget___closed__7_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 83, 112, 108,
            105, 116, 73, 102, 0,
        ],
    };
static mut l_Lean_Meta_simpIfTarget___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_simpIfTarget___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_simpIfTarget___closed__8_value: crate::leanh::LeanStringObject<23> =
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
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 115, 105, 109, 112, 73, 102, 84, 97, 114,
            103, 101, 116, 0,
        ],
    };
static mut l_Lean_Meta_simpIfTarget___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_simpIfTarget___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_simpIfTarget___closed__9_value: crate::leanh::LeanStringObject<34> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97,
            115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
        ],
    };
static mut l_Lean_Meta_simpIfTarget___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_simpIfTarget___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_simpIfTarget___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_simpIfTarget___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_simpIfTarget___closed__11_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_Meta_simpIfTarget___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_simpIfTarget___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_simpIfTarget___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_simpIfTarget___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_simpIfLocalDecl___closed__0_value: crate::leanh::LeanStringObject<26> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 115, 105, 109, 112, 73, 102, 76, 111, 99,
            97, 108, 68, 101, 99, 108, 0,
        ],
    };
static mut l_Lean_Meta_simpIfLocalDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_simpIfLocalDecl___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_simpIfLocalDecl___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_simpIfLocalDecl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_simpIfLocalDecl___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_simpIfLocalDecl___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [102, 97, 105, 108, 117, 114, 101, 0],
};
static mut l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__0_value) as *mut crate::leanh::LeanObject,18188493160499796729 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        16463169542489330205 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__3_value:
    crate::leanh::LeanStringObject<70> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 70,
    m_capacity: 70,
    m_length: 69,
    m_data: [
        96, 115, 112, 108, 105, 116, 96, 32, 116, 97, 99, 116, 105, 99, 32, 102, 97, 105, 108, 101,
        100, 32, 116, 111, 32, 115, 105, 109, 112, 108, 105, 102, 121, 32, 116, 97, 114, 103, 101,
        116, 32, 117, 115, 105, 110, 103, 32, 110, 101, 119, 32, 104, 121, 112, 111, 116, 104, 101,
        115, 101, 115, 32, 71, 111, 97, 108, 115, 58, 10, 0,
    ],
};
static mut l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__5_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [10, 0],
};
static mut l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__13_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3820868106864855377 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10561321130586085436 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,14500713028617822429 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,6341162624378599605 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__8_value) as *mut crate::leanh::LeanObject,16214063427435940748 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__9_value) as *mut crate::leanh::LeanObject,2221056674123490639 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_SplitKind_ctorIdx(mut v_x_3674_: u8) -> *mut crate::leanh::LeanObject {
    match v_x_3674_ {
        0 => {
            let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3675_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_3675_;
        }
        1 => {
            let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3676_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_3676_;
        }
        _ => {
            let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3677_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_3677_;
        }
    }
}
pub unsafe fn l_Lean_Meta_SplitKind_ctorIdx___boxed(
    mut v_x_3678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_3679_: u8 = 0;
    let mut v_res_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_3679_ = (crate::leanh::lean_unbox(v_x_3678_) as u8);
    v_res_3680_ = l_Lean_Meta_SplitKind_ctorIdx(v_x_boxed_3679_);
    return v_res_3680_;
}
pub unsafe fn l_Lean_Meta_SplitKind_toCtorIdx(mut v_x_3681_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3682_ = l_Lean_Meta_SplitKind_ctorIdx(v_x_3681_);
    return v___x_3682_;
}
pub unsafe fn l_Lean_Meta_SplitKind_toCtorIdx___boxed(
    mut v_x_3683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_3684_: u8 = 0;
    let mut v_res_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_3684_ = (crate::leanh::lean_unbox(v_x_3683_) as u8);
    v_res_3685_ = l_Lean_Meta_SplitKind_toCtorIdx(v_x_4__boxed_3684_);
    return v_res_3685_;
}
pub unsafe fn l_Lean_Meta_SplitKind_ctorElim___redArg(
    mut v_k_3686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_3686_);
    return v_k_3686_;
}
pub unsafe fn l_Lean_Meta_SplitKind_ctorElim___redArg___boxed(
    mut v_k_3687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3688_ = l_Lean_Meta_SplitKind_ctorElim___redArg(v_k_3687_);
    crate::leanh::lean_dec(v_k_3687_);
    return v_res_3688_;
}
pub unsafe fn l_Lean_Meta_SplitKind_ctorElim(
    mut v_motive_3689_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3690_: *mut crate::leanh::LeanObject,
    mut v_t_3691_: u8,
    mut v_h_3692_: *mut crate::leanh::LeanObject,
    mut v_k_3693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_3693_);
    return v_k_3693_;
}
pub unsafe fn l_Lean_Meta_SplitKind_ctorElim___boxed(
    mut v_motive_3694_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3695_: *mut crate::leanh::LeanObject,
    mut v_t_3696_: *mut crate::leanh::LeanObject,
    mut v_h_3697_: *mut crate::leanh::LeanObject,
    mut v_k_3698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3699_: u8 = 0;
    let mut v_res_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3699_ = (crate::leanh::lean_unbox(v_t_3696_) as u8);
    v_res_3700_ = l_Lean_Meta_SplitKind_ctorElim(
        v_motive_3694_,
        v_ctorIdx_3695_,
        v_t_boxed_3699_,
        v_h_3697_,
        v_k_3698_,
    );
    crate::leanh::lean_dec(v_k_3698_);
    crate::leanh::lean_dec(v_ctorIdx_3695_);
    return v_res_3700_;
}
pub unsafe fn l_Lean_Meta_SplitKind_ite_elim___redArg(
    mut v_ite_3701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_ite_3701_);
    return v_ite_3701_;
}
pub unsafe fn l_Lean_Meta_SplitKind_ite_elim___redArg___boxed(
    mut v_ite_3702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3703_ = l_Lean_Meta_SplitKind_ite_elim___redArg(v_ite_3702_);
    crate::leanh::lean_dec(v_ite_3702_);
    return v_res_3703_;
}
pub unsafe fn l_Lean_Meta_SplitKind_ite_elim(
    mut v_motive_3704_: *mut crate::leanh::LeanObject,
    mut v_t_3705_: u8,
    mut v_h_3706_: *mut crate::leanh::LeanObject,
    mut v_ite_3707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_ite_3707_);
    return v_ite_3707_;
}
pub unsafe fn l_Lean_Meta_SplitKind_ite_elim___boxed(
    mut v_motive_3708_: *mut crate::leanh::LeanObject,
    mut v_t_3709_: *mut crate::leanh::LeanObject,
    mut v_h_3710_: *mut crate::leanh::LeanObject,
    mut v_ite_3711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3712_: u8 = 0;
    let mut v_res_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3712_ = (crate::leanh::lean_unbox(v_t_3709_) as u8);
    v_res_3713_ =
        l_Lean_Meta_SplitKind_ite_elim(v_motive_3708_, v_t_boxed_3712_, v_h_3710_, v_ite_3711_);
    crate::leanh::lean_dec(v_ite_3711_);
    return v_res_3713_;
}
pub unsafe fn l_Lean_Meta_SplitKind_match_elim___redArg(
    mut v_match_3714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_match_3714_);
    return v_match_3714_;
}
pub unsafe fn l_Lean_Meta_SplitKind_match_elim___redArg___boxed(
    mut v_match_3715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3716_ = l_Lean_Meta_SplitKind_match_elim___redArg(v_match_3715_);
    crate::leanh::lean_dec(v_match_3715_);
    return v_res_3716_;
}
pub unsafe fn l_Lean_Meta_SplitKind_match_elim(
    mut v_motive_3717_: *mut crate::leanh::LeanObject,
    mut v_t_3718_: u8,
    mut v_h_3719_: *mut crate::leanh::LeanObject,
    mut v_match_3720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_match_3720_);
    return v_match_3720_;
}
pub unsafe fn l_Lean_Meta_SplitKind_match_elim___boxed(
    mut v_motive_3721_: *mut crate::leanh::LeanObject,
    mut v_t_3722_: *mut crate::leanh::LeanObject,
    mut v_h_3723_: *mut crate::leanh::LeanObject,
    mut v_match_3724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3725_: u8 = 0;
    let mut v_res_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3725_ = (crate::leanh::lean_unbox(v_t_3722_) as u8);
    v_res_3726_ =
        l_Lean_Meta_SplitKind_match_elim(v_motive_3721_, v_t_boxed_3725_, v_h_3723_, v_match_3724_);
    crate::leanh::lean_dec(v_match_3724_);
    return v_res_3726_;
}
pub unsafe fn l_Lean_Meta_SplitKind_both_elim___redArg(
    mut v_both_3727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_both_3727_);
    return v_both_3727_;
}
pub unsafe fn l_Lean_Meta_SplitKind_both_elim___redArg___boxed(
    mut v_both_3728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3729_ = l_Lean_Meta_SplitKind_both_elim___redArg(v_both_3728_);
    crate::leanh::lean_dec(v_both_3728_);
    return v_res_3729_;
}
pub unsafe fn l_Lean_Meta_SplitKind_both_elim(
    mut v_motive_3730_: *mut crate::leanh::LeanObject,
    mut v_t_3731_: u8,
    mut v_h_3732_: *mut crate::leanh::LeanObject,
    mut v_both_3733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_both_3733_);
    return v_both_3733_;
}
pub unsafe fn l_Lean_Meta_SplitKind_both_elim___boxed(
    mut v_motive_3734_: *mut crate::leanh::LeanObject,
    mut v_t_3735_: *mut crate::leanh::LeanObject,
    mut v_h_3736_: *mut crate::leanh::LeanObject,
    mut v_both_3737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_3738_: u8 = 0;
    let mut v_res_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3738_ = (crate::leanh::lean_unbox(v_t_3735_) as u8);
    v_res_3739_ =
        l_Lean_Meta_SplitKind_both_elim(v_motive_3734_, v_t_boxed_3738_, v_h_3736_, v_both_3737_);
    crate::leanh::lean_dec(v_both_3737_);
    return v_res_3739_;
}
pub unsafe fn l_Lean_Meta_SplitKind_considerIte(mut v_x_3740_: u8) -> u8 {
    match v_x_3740_ {
        0 => {
            let mut v___x_3741_: u8 = 0;
            v___x_3741_ = 1;
            return v___x_3741_;
        }
        2 => {
            let mut v___x_3742_: u8 = 0;
            v___x_3742_ = 1;
            return v___x_3742_;
        }
        _ => {
            let mut v___x_3743_: u8 = 0;
            v___x_3743_ = 0;
            return v___x_3743_;
        }
    }
}
pub unsafe fn l_Lean_Meta_SplitKind_considerIte___boxed(
    mut v_x_3744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_26__boxed_3745_: u8 = 0;
    let mut v_res_3746_: u8 = 0;
    let mut v_r_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_3745_ = (crate::leanh::lean_unbox(v_x_3744_) as u8);
    v_res_3746_ = l_Lean_Meta_SplitKind_considerIte(v_x_26__boxed_3745_);
    v_r_3747_ = crate::leanh::lean_box((v_res_3746_) as usize);
    return v_r_3747_;
}
pub unsafe fn l_Lean_Meta_SplitKind_considerMatch(mut v_x_3748_: u8) -> u8 {
    match v_x_3748_ {
        1 => {
            let mut v___x_3749_: u8 = 0;
            v___x_3749_ = 1;
            return v___x_3749_;
        }
        2 => {
            let mut v___x_3750_: u8 = 0;
            v___x_3750_ = 1;
            return v___x_3750_;
        }
        _ => {
            let mut v___x_3751_: u8 = 0;
            v___x_3751_ = 0;
            return v___x_3751_;
        }
    }
}
pub unsafe fn l_Lean_Meta_SplitKind_considerMatch___boxed(
    mut v_x_3752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_26__boxed_3753_: u8 = 0;
    let mut v_res_3754_: u8 = 0;
    let mut v_r_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_3753_ = (crate::leanh::lean_unbox(v_x_3752_) as u8);
    v_res_3754_ = l_Lean_Meta_SplitKind_considerMatch(v_x_26__boxed_3753_);
    v_r_3755_ = crate::leanh::lean_box((v_res_3754_) as usize);
    return v_r_3755_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg(
    mut v_a_3756_: *mut crate::leanh::LeanObject,
    mut v_x_3757_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3758_: u8 = 0;
    let mut v_key_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3757_) == 0 {
                    v___x_3758_ = 0;
                    return v___x_3758_;
                } else {
                    v_key_3759_ = crate::leanh::lean_ctor_get(v_x_3757_, 0);
                    v_tail_3760_ = crate::leanh::lean_ctor_get(v_x_3757_, 2);
                    v___x_3761_ = lean_expr_eqv(v_key_3759_, v_a_3756_);
                    if v___x_3761_ == 0 {
                        v_x_3757_ = v_tail_3760_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3761_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg___boxed(
    mut v_a_3763_: *mut crate::leanh::LeanObject,
    mut v_x_3764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3765_: u8 = 0;
    let mut v_r_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3765_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg(v_a_3763_, v_x_3764_);
    crate::leanh::lean_dec(v_x_3764_);
    crate::leanh::lean_dec_ref(v_a_3763_);
    v_r_3766_ = crate::leanh::lean_box((v_res_3765_) as usize);
    return v_r_3766_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(
    mut v_m_3767_: *mut crate::leanh::LeanObject,
    mut v_a_3768_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: u64 = 0;
    let mut v___x_3772_: u64 = 0;
    let mut v___x_3773_: u64 = 0;
    let mut v_fold_3774_: u64 = 0;
    let mut v___x_3775_: u64 = 0;
    let mut v___x_3776_: u64 = 0;
    let mut v___x_3777_: u64 = 0;
    let mut v___x_3778_: usize = 0;
    let mut v___x_3779_: usize = 0;
    let mut v___x_3780_: usize = 0;
    let mut v___x_3781_: usize = 0;
    let mut v___x_3782_: usize = 0;
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: u8 = 0;
    v_buckets_3769_ = crate::leanh::lean_ctor_get(v_m_3767_, 1);
    v___x_3770_ = lean_array_get_size(v_buckets_3769_);
    v___x_3771_ = l_Lean_Expr_hash(v_a_3768_);
    v___x_3772_ = 32u64;
    v___x_3773_ = lean_uint64_shift_right(v___x_3771_, v___x_3772_);
    v_fold_3774_ = lean_uint64_xor(v___x_3771_, v___x_3773_);
    v___x_3775_ = 16u64;
    v___x_3776_ = lean_uint64_shift_right(v_fold_3774_, v___x_3775_);
    v___x_3777_ = lean_uint64_xor(v_fold_3774_, v___x_3776_);
    v___x_3778_ = lean_uint64_to_usize(v___x_3777_);
    v___x_3779_ = lean_usize_of_nat(v___x_3770_);
    v___x_3780_ = 1usize;
    v___x_3781_ = lean_usize_sub(v___x_3779_, v___x_3780_);
    v___x_3782_ = lean_usize_land(v___x_3778_, v___x_3781_);
    v___x_3783_ = lean_array_uget_borrowed(v_buckets_3769_, v___x_3782_);
    v___x_3784_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg(v_a_3768_, v___x_3783_);
    return v___x_3784_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg___boxed(
    mut v_m_3785_: *mut crate::leanh::LeanObject,
    mut v_a_3786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3787_: u8 = 0;
    let mut v_r_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3787_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(v_m_3785_, v_a_3786_);
    crate::leanh::lean_dec_ref(v_a_3786_);
    crate::leanh::lean_dec_ref(v_m_3785_);
    v_r_3788_ = crate::leanh::lean_box((v_res_3787_) as usize);
    return v_r_3788_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg(
    mut v_upperBound_3797_: *mut crate::leanh::LeanObject,
    mut v_args_3798_: *mut crate::leanh::LeanObject,
    mut v_a_3799_: *mut crate::leanh::LeanObject,
    mut v_b_3800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3801_: u8 = 0;
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: u8 = 0;
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3801_ = lean_nat_dec_lt(v_a_3799_, v_upperBound_3797_);
                if v___x_3801_ == 0 {
                    crate::leanh::lean_dec(v_a_3799_);
                    crate::leanh::lean_inc_ref(v_b_3800_);
                    return v_b_3800_;
                } else {
                    v___x_3802_ = l_Lean_instInhabitedExpr;
                    v___x_3803_ = lean_array_get_borrowed(v___x_3802_, v_args_3798_, v_a_3799_);
                    v___x_3804_ = l_Lean_Expr_hasLooseBVars(v___x_3803_);
                    if v___x_3804_ == 0 {
                        v___x_3805_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0;
                        v___x_3806_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3807_ = lean_nat_add(v_a_3799_, v___x_3806_);
                        crate::leanh::lean_dec(v_a_3799_);
                        v_a_3799_ = v___x_3807_;
                        v_b_3800_ = v___x_3805_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_3799_);
                        v___x_3809_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__2;
                        return v___x_3809_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___boxed(
    mut v_upperBound_3810_: *mut crate::leanh::LeanObject,
    mut v_args_3811_: *mut crate::leanh::LeanObject,
    mut v_a_3812_: *mut crate::leanh::LeanObject,
    mut v_b_3813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3814_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg(v_upperBound_3810_, v_args_3811_, v_a_3812_, v_b_3813_);
    crate::leanh::lean_dec_ref(v_b_3813_);
    crate::leanh::lean_dec_ref(v_args_3811_);
    crate::leanh::lean_dec(v_upperBound_3810_);
    return v_res_3814_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3815_ = crate::leanh::lean_box(0);
    v_dummy_3816_ = l_Lean_Expr_sort___override(v___x_3815_);
    return v_dummy_3816_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f(
    mut v_env_3823_: *mut crate::leanh::LeanObject,
    mut v_ctx_3824_: *mut crate::leanh::LeanObject,
    mut v_e_3825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_exceptionSet_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3827_: u8 = 0;
    let mut v_e_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: u8 = 0;
    let mut v___x_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: u8 = 0;
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numDiscrs_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3859_: u8 = 0;
    let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numArgs_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: u8 = 0;
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: u8 = 0;
    let mut v___x_3869_: u8 = 0;
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: u8 = 0;
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_exceptionSet_3826_ = crate::leanh::lean_ctor_get(v_ctx_3824_, 0);
                v_kind_3827_ = crate::leanh::lean_ctor_get_uint8(
                    v_ctx_3824_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v___x_3869_ = l_Lean_Meta_SplitKind_considerIte(v_kind_3827_);
                if v___x_3869_ == 0 {
                    state = 2;
                    continue;
                } else {
                    v___x_3870_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__2;
                    v___x_3871_ = l_Lean_Expr_isAppOf(v_e_3825_, v___x_3870_);
                    if v___x_3871_ == 0 {
                        v___x_3872_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__4;
                        v___x_3873_ = l_Lean_Expr_isAppOf(v_e_3825_, v___x_3872_);
                        if v___x_3873_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            state = 4;
                            continue;
                        }
                    } else {
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3830_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(v_exceptionSet_3826_, v_e_3829_);
                if v___x_3830_ == 0 {
                    v___x_3831_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3831_, 0, v_e_3829_);
                    return v___x_3831_;
                } else {
                    crate::leanh::lean_dec_ref(v_e_3829_);
                    v___x_3832_ = crate::leanh::lean_box(0);
                    return v___x_3832_;
                }
            }
            2 => {
                v___x_3834_ = l_Lean_Meta_SplitKind_considerMatch(v_kind_3827_);
                if v___x_3834_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_3825_);
                    crate::leanh::lean_dec_ref(v_env_3823_);
                    v___x_3835_ = crate::leanh::lean_box(0);
                    return v___x_3835_;
                } else {
                    v___x_3836_ = l_Lean_Meta_isMatcherAppCore_x3f(v_env_3823_, v_e_3825_);
                    if crate::leanh::lean_obj_tag(v___x_3836_) == 1 {
                        v_val_3837_ = crate::leanh::lean_ctor_get(v___x_3836_, 0);
                        crate::leanh::lean_inc(v_val_3837_);
                        crate::leanh::lean_dec_ref_known(v___x_3836_, 1);
                        v_numDiscrs_3838_ = crate::leanh::lean_ctor_get(v_val_3837_, 1);
                        v_nargs_3839_ = l_Lean_Expr_getAppNumArgs(v_e_3825_);
                        v___x_3840_ = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(v_val_3837_);
                        v___x_3841_ = lean_nat_add(v___x_3840_, v_numDiscrs_3838_);
                        v_dummy_3842_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0_once), _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0);
                        crate::leanh::lean_inc(v_nargs_3839_);
                        v___x_3843_ = lean_mk_array(v_nargs_3839_, v_dummy_3842_);
                        v___x_3844_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3845_ = lean_nat_sub(v_nargs_3839_, v___x_3844_);
                        crate::leanh::lean_dec(v_nargs_3839_);
                        crate::leanh::lean_inc_ref(v_e_3825_);
                        v_args_3846_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                            v_e_3825_,
                            v___x_3843_,
                            v___x_3845_,
                        );
                        v___x_3847_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0;
                        v___x_3848_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg(v___x_3841_, v_args_3846_, v___x_3840_, v___x_3847_);
                        crate::leanh::lean_dec(v___x_3841_);
                        v_fst_3849_ = crate::leanh::lean_ctor_get(v___x_3848_, 0);
                        crate::leanh::lean_inc(v_fst_3849_);
                        crate::leanh::lean_dec_ref(v___x_3848_);
                        if crate::leanh::lean_obj_tag(v_fst_3849_) == 0 {
                            v___x_3850_ = lean_array_get_size(v_args_3846_);
                            crate::leanh::lean_dec_ref(v_args_3846_);
                            v___x_3851_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_3837_);
                            crate::leanh::lean_dec(v_val_3837_);
                            v___x_3852_ = lean_nat_sub(v___x_3850_, v___x_3851_);
                            crate::leanh::lean_dec(v___x_3851_);
                            v___x_3853_ = l_Lean_Expr_getBoundedAppFn(v___x_3852_, v_e_3825_);
                            crate::leanh::lean_dec_ref(v_e_3825_);
                            v_e_3829_ = v___x_3853_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_args_3846_);
                            crate::leanh::lean_dec(v_val_3837_);
                            crate::leanh::lean_dec_ref(v_e_3825_);
                            v_val_3854_ = crate::leanh::lean_ctor_get(v_fst_3849_, 0);
                            crate::leanh::lean_inc(v_val_3854_);
                            crate::leanh::lean_dec_ref_known(v_fst_3849_, 1);
                            return v_val_3854_;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3836_);
                        crate::leanh::lean_dec_ref(v_e_3825_);
                        v___x_3855_ = crate::leanh::lean_box(0);
                        return v___x_3855_;
                    }
                }
            }
            3 => {
                if v___y_3859_ == 0 {
                    crate::leanh::lean_dec(v___y_3857_);
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_env_3823_);
                    v___x_3860_ = lean_nat_sub(v___y_3857_, v___y_3858_);
                    crate::leanh::lean_dec(v___y_3857_);
                    v___x_3861_ = l_Lean_Expr_getBoundedAppFn(v___x_3860_, v_e_3825_);
                    crate::leanh::lean_dec_ref(v_e_3825_);
                    v_e_3829_ = v___x_3861_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                v_numArgs_3863_ = l_Lean_Expr_getAppNumArgs(v_e_3825_);
                v___x_3864_ = crate::leanh::lean_unsigned_to_nat(5);
                v___x_3865_ = lean_nat_dec_le(v___x_3864_, v_numArgs_3863_);
                if v___x_3865_ == 0 {
                    v___y_3857_ = v_numArgs_3863_;
                    v___y_3858_ = v___x_3864_;
                    v___y_3859_ = v___x_3865_;
                    state = 3;
                    continue;
                } else {
                    v___x_3866_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_3867_ = l_Lean_Expr_getRevArg_x21(v_e_3825_, v___x_3866_);
                    v___x_3868_ = l_Lean_Expr_hasLooseBVars(v___x_3867_);
                    crate::leanh::lean_dec_ref(v___x_3867_);
                    if v___x_3868_ == 0 {
                        v___y_3857_ = v_numArgs_3863_;
                        v___y_3858_ = v___x_3864_;
                        v___y_3859_ = v___x_3865_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_numArgs_3863_);
                        state = 2;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___boxed(
    mut v_env_3874_: *mut crate::leanh::LeanObject,
    mut v_ctx_3875_: *mut crate::leanh::LeanObject,
    mut v_e_3876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3877_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f(
        v_env_3874_,
        v_ctx_3875_,
        v_e_3876_,
    );
    crate::leanh::lean_dec_ref(v_ctx_3875_);
    return v_res_3877_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0(
    mut v_00_u03b2_3878_: *mut crate::leanh::LeanObject,
    mut v_m_3879_: *mut crate::leanh::LeanObject,
    mut v_a_3880_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3881_: u8 = 0;
    v___x_3881_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___redArg(v_m_3879_, v_a_3880_);
    return v___x_3881_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0___boxed(
    mut v_00_u03b2_3882_: *mut crate::leanh::LeanObject,
    mut v_m_3883_: *mut crate::leanh::LeanObject,
    mut v_a_3884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3885_: u8 = 0;
    let mut v_r_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3885_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0(v_00_u03b2_3882_, v_m_3883_, v_a_3884_);
    crate::leanh::lean_dec_ref(v_a_3884_);
    crate::leanh::lean_dec_ref(v_m_3883_);
    v_r_3886_ = crate::leanh::lean_box((v_res_3885_) as usize);
    return v_r_3886_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1(
    mut v_upperBound_3887_: *mut crate::leanh::LeanObject,
    mut v_args_3888_: *mut crate::leanh::LeanObject,
    mut v_inst_3889_: *mut crate::leanh::LeanObject,
    mut v_R_3890_: *mut crate::leanh::LeanObject,
    mut v_a_3891_: *mut crate::leanh::LeanObject,
    mut v_b_3892_: *mut crate::leanh::LeanObject,
    mut v_c_3893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3894_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg(v_upperBound_3887_, v_args_3888_, v_a_3891_, v_b_3892_);
    return v___x_3894_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___boxed(
    mut v_upperBound_3895_: *mut crate::leanh::LeanObject,
    mut v_args_3896_: *mut crate::leanh::LeanObject,
    mut v_inst_3897_: *mut crate::leanh::LeanObject,
    mut v_R_3898_: *mut crate::leanh::LeanObject,
    mut v_a_3899_: *mut crate::leanh::LeanObject,
    mut v_b_3900_: *mut crate::leanh::LeanObject,
    mut v_c_3901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3902_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1(v_upperBound_3895_, v_args_3896_, v_inst_3897_, v_R_3898_, v_a_3899_, v_b_3900_, v_c_3901_);
    crate::leanh::lean_dec_ref(v_b_3900_);
    crate::leanh::lean_dec_ref(v_args_3896_);
    crate::leanh::lean_dec(v_upperBound_3895_);
    return v_res_3902_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0(
    mut v_00_u03b2_3903_: *mut crate::leanh::LeanObject,
    mut v_a_3904_: *mut crate::leanh::LeanObject,
    mut v_x_3905_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3906_: u8 = 0;
    v___x_3906_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___redArg(v_a_3904_, v_x_3905_);
    return v___x_3906_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_3907_: *mut crate::leanh::LeanObject,
    mut v_a_3908_: *mut crate::leanh::LeanObject,
    mut v_x_3909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3910_: u8 = 0;
    let mut v_r_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3910_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__0_spec__0(v_00_u03b2_3907_, v_a_3908_, v_x_3909_);
    crate::leanh::lean_dec(v_x_3909_);
    crate::leanh::lean_dec_ref(v_a_3908_);
    v_r_3911_ = crate::leanh::lean_box((v_res_3910_) as usize);
    return v_r_3911_;
}
pub unsafe fn l_Lean_Meta_FindSplitImpl_checkVisited___redArg(
    mut v_e_3916_: *mut crate::leanh::LeanObject,
    mut v_a_3917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: u8 = 0;
    v___f_3919_ = l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__0;
    v___f_3920_ = l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__1;
    crate::leanh::lean_inc_ref(v_e_3916_);
    v___x_3921_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v___f_3919_,
        v___f_3920_,
        v_a_3917_,
        v_e_3916_,
    );
    if v___x_3921_ == 0 {
        let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3922_ = crate::leanh::lean_box(0);
        v___x_3923_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
            v___f_3919_,
            v___f_3920_,
            v_a_3917_,
            v_e_3916_,
            v___x_3922_,
        );
        v___x_3924_ = l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__2;
        v___x_3925_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3925_, 0, v___x_3924_);
        crate::leanh::lean_ctor_set(v___x_3925_, 1, v___x_3923_);
        v___x_3926_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3926_, 0, v___x_3925_);
        return v___x_3926_;
    } else {
        let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_e_3916_);
        v___x_3927_ = crate::leanh::lean_box(0);
        v___x_3928_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3928_, 0, v___x_3927_);
        crate::leanh::lean_ctor_set(v___x_3928_, 1, v_a_3917_);
        v___x_3929_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3929_, 0, v___x_3928_);
        return v___x_3929_;
    }
}
pub unsafe fn l_Lean_Meta_FindSplitImpl_checkVisited___redArg___boxed(
    mut v_e_3930_: *mut crate::leanh::LeanObject,
    mut v_a_3931_: *mut crate::leanh::LeanObject,
    mut v_a_3932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3933_ = l_Lean_Meta_FindSplitImpl_checkVisited___redArg(v_e_3930_, v_a_3931_);
    return v_res_3933_;
}
pub unsafe fn l_Lean_Meta_FindSplitImpl_checkVisited(
    mut v_e_3934_: *mut crate::leanh::LeanObject,
    mut v_a_3935_: *mut crate::leanh::LeanObject,
    mut v_a_3936_: *mut crate::leanh::LeanObject,
    mut v_a_3937_: *mut crate::leanh::LeanObject,
    mut v_a_3938_: *mut crate::leanh::LeanObject,
    mut v_a_3939_: *mut crate::leanh::LeanObject,
    mut v_a_3940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: u8 = 0;
    v___f_3942_ = l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__0;
    v___f_3943_ = l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__1;
    crate::leanh::lean_inc_ref(v_e_3934_);
    v___x_3944_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v___f_3942_,
        v___f_3943_,
        v_a_3936_,
        v_e_3934_,
    );
    if v___x_3944_ == 0 {
        let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3945_ = crate::leanh::lean_box(0);
        v___x_3946_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
            v___f_3942_,
            v___f_3943_,
            v_a_3936_,
            v_e_3934_,
            v___x_3945_,
        );
        v___x_3947_ = l_Lean_Meta_FindSplitImpl_checkVisited___redArg___closed__2;
        v___x_3948_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3948_, 0, v___x_3947_);
        crate::leanh::lean_ctor_set(v___x_3948_, 1, v___x_3946_);
        v___x_3949_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3949_, 0, v___x_3948_);
        return v___x_3949_;
    } else {
        let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_e_3934_);
        v___x_3950_ = crate::leanh::lean_box(0);
        v___x_3951_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3951_, 0, v___x_3950_);
        crate::leanh::lean_ctor_set(v___x_3951_, 1, v_a_3936_);
        v___x_3952_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3952_, 0, v___x_3951_);
        return v___x_3952_;
    }
}
pub unsafe fn l_Lean_Meta_FindSplitImpl_checkVisited___boxed(
    mut v_e_3953_: *mut crate::leanh::LeanObject,
    mut v_a_3954_: *mut crate::leanh::LeanObject,
    mut v_a_3955_: *mut crate::leanh::LeanObject,
    mut v_a_3956_: *mut crate::leanh::LeanObject,
    mut v_a_3957_: *mut crate::leanh::LeanObject,
    mut v_a_3958_: *mut crate::leanh::LeanObject,
    mut v_a_3959_: *mut crate::leanh::LeanObject,
    mut v_a_3960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3961_ = l_Lean_Meta_FindSplitImpl_checkVisited(
        v_e_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_,
    );
    crate::leanh::lean_dec(v_a_3959_);
    crate::leanh::lean_dec_ref(v_a_3958_);
    crate::leanh::lean_dec(v_a_3957_);
    crate::leanh::lean_dec_ref(v_a_3956_);
    crate::leanh::lean_dec_ref(v_a_3954_);
    return v_res_3961_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(
    mut v_a_3962_: *mut crate::leanh::LeanObject,
    mut v_x_3963_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3964_: u8 = 0;
    let mut v_key_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: usize = 0;
    let mut v___x_3968_: usize = 0;
    let mut v___x_3969_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3963_) == 0 {
                    v___x_3964_ = 0;
                    return v___x_3964_;
                } else {
                    v_key_3965_ = crate::leanh::lean_ctor_get(v_x_3963_, 0);
                    v_tail_3966_ = crate::leanh::lean_ctor_get(v_x_3963_, 2);
                    v___x_3967_ = lean_ptr_addr(v_key_3965_);
                    v___x_3968_ = lean_ptr_addr(v_a_3962_);
                    v___x_3969_ = lean_usize_dec_eq(v___x_3967_, v___x_3968_);
                    if v___x_3969_ == 0 {
                        v_x_3963_ = v_tail_3966_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3969_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg___boxed(
    mut v_a_3971_: *mut crate::leanh::LeanObject,
    mut v_x_3972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3973_: u8 = 0;
    let mut v_r_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3973_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(v_a_3971_, v_x_3972_);
    crate::leanh::lean_dec(v_x_3972_);
    crate::leanh::lean_dec_ref(v_a_3971_);
    v_r_3974_ = crate::leanh::lean_box((v_res_3973_) as usize);
    return v_r_3974_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6_spec__7___redArg(
    mut v_x_3975_: *mut crate::leanh::LeanObject,
    mut v_x_3976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3982_: u8 = 0;
    let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: usize = 0;
    let mut v___x_3985_: u64 = 0;
    let mut v___x_3986_: u64 = 0;
    let mut v___x_3987_: u64 = 0;
    let mut v___x_3988_: u64 = 0;
    let mut v___x_3989_: u64 = 0;
    let mut v_fold_3990_: u64 = 0;
    let mut v___x_3991_: u64 = 0;
    let mut v___x_3992_: u64 = 0;
    let mut v___x_3993_: u64 = 0;
    let mut v___x_3994_: usize = 0;
    let mut v___x_3995_: usize = 0;
    let mut v___x_3996_: usize = 0;
    let mut v___x_3997_: usize = 0;
    let mut v___x_3998_: usize = 0;
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4005_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3976_) == 0 {
                    return v_x_3975_;
                } else {
                    v_key_3977_ = crate::leanh::lean_ctor_get(v_x_3976_, 0);
                    v_value_3978_ = crate::leanh::lean_ctor_get(v_x_3976_, 1);
                    v_tail_3979_ = crate::leanh::lean_ctor_get(v_x_3976_, 2);
                    v_isSharedCheck_4005_ = (!crate::leanh::lean_is_exclusive(v_x_3976_)) as u8;
                    if v_isSharedCheck_4005_ == 0 {
                        v___x_3981_ = v_x_3976_;
                        v_isShared_3982_ = v_isSharedCheck_4005_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3979_);
                        crate::leanh::lean_inc(v_value_3978_);
                        crate::leanh::lean_inc(v_key_3977_);
                        crate::leanh::lean_dec(v_x_3976_);
                        v___x_3981_ = crate::leanh::lean_box(0);
                        v_isShared_3982_ = v_isSharedCheck_4005_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3983_ = lean_array_get_size(v_x_3975_);
                v___x_3984_ = lean_ptr_addr(v_key_3977_);
                v___x_3985_ = lean_usize_to_uint64(v___x_3984_);
                v___x_3986_ = 11u64;
                v___x_3987_ = lean_uint64_mix_hash(v___x_3985_, v___x_3986_);
                v___x_3988_ = 32u64;
                v___x_3989_ = lean_uint64_shift_right(v___x_3987_, v___x_3988_);
                v_fold_3990_ = lean_uint64_xor(v___x_3987_, v___x_3989_);
                v___x_3991_ = 16u64;
                v___x_3992_ = lean_uint64_shift_right(v_fold_3990_, v___x_3991_);
                v___x_3993_ = lean_uint64_xor(v_fold_3990_, v___x_3992_);
                v___x_3994_ = lean_uint64_to_usize(v___x_3993_);
                v___x_3995_ = lean_usize_of_nat(v___x_3983_);
                v___x_3996_ = 1usize;
                v___x_3997_ = lean_usize_sub(v___x_3995_, v___x_3996_);
                v___x_3998_ = lean_usize_land(v___x_3994_, v___x_3997_);
                v___x_3999_ = lean_array_uget_borrowed(v_x_3975_, v___x_3998_);
                crate::leanh::lean_inc(v___x_3999_);
                if v_isShared_3982_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3981_, 2, v___x_3999_);
                    v___x_4001_ = v___x_3981_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4004_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_key_3977_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4004_, 1, v_value_3978_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4004_, 2, v___x_3999_);
                    v___x_4001_ = v_reuseFailAlloc_4004_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4002_ = lean_array_uset(v_x_3975_, v___x_3998_, v___x_4001_);
                v_x_3975_ = v___x_4002_;
                v_x_3976_ = v_tail_3979_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6___redArg(
    mut v_i_4006_: *mut crate::leanh::LeanObject,
    mut v_source_4007_: *mut crate::leanh::LeanObject,
    mut v_target_4008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: u8 = 0;
    let mut v_es_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4009_ = lean_array_get_size(v_source_4007_);
                v___x_4010_ = lean_nat_dec_lt(v_i_4006_, v___x_4009_);
                if v___x_4010_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_4007_);
                    crate::leanh::lean_dec(v_i_4006_);
                    return v_target_4008_;
                } else {
                    v_es_4011_ = lean_array_fget(v_source_4007_, v_i_4006_);
                    v___x_4012_ = crate::leanh::lean_box(0);
                    v_source_4013_ = lean_array_fset(v_source_4007_, v_i_4006_, v___x_4012_);
                    v_target_4014_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6_spec__7___redArg(v_target_4008_, v_es_4011_);
                    v___x_4015_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4016_ = lean_nat_add(v_i_4006_, v___x_4015_);
                    crate::leanh::lean_dec(v_i_4006_);
                    v_i_4006_ = v___x_4016_;
                    v_source_4007_ = v_source_4013_;
                    v_target_4008_ = v_target_4014_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5___redArg(
    mut v_data_4018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4019_ = lean_array_get_size(v_data_4018_);
    v___x_4020_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_4021_ = lean_nat_mul(v___x_4019_, v___x_4020_);
    v___x_4022_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4023_ = crate::leanh::lean_box(0);
    v___x_4024_ = lean_mk_array(v_nbuckets_4021_, v___x_4023_);
    v___x_4025_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6___redArg(v___x_4022_, v_data_4018_, v___x_4024_);
    return v___x_4025_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4___redArg(
    mut v_m_4026_: *mut crate::leanh::LeanObject,
    mut v_a_4027_: *mut crate::leanh::LeanObject,
    mut v_b_4028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: usize = 0;
    let mut v___x_4033_: u64 = 0;
    let mut v___x_4034_: u64 = 0;
    let mut v___x_4035_: u64 = 0;
    let mut v___x_4036_: u64 = 0;
    let mut v___x_4037_: u64 = 0;
    let mut v_fold_4038_: u64 = 0;
    let mut v___x_4039_: u64 = 0;
    let mut v___x_4040_: u64 = 0;
    let mut v___x_4041_: u64 = 0;
    let mut v___x_4042_: usize = 0;
    let mut v___x_4043_: usize = 0;
    let mut v___x_4044_: usize = 0;
    let mut v___x_4045_: usize = 0;
    let mut v___x_4046_: usize = 0;
    let mut v_bkt_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: u8 = 0;
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4051_: u8 = 0;
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: u8 = 0;
    let mut v_val_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4069_: u8 = 0;
    let mut v_unused_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4029_ = crate::leanh::lean_ctor_get(v_m_4026_, 0);
                v_buckets_4030_ = crate::leanh::lean_ctor_get(v_m_4026_, 1);
                v___x_4031_ = lean_array_get_size(v_buckets_4030_);
                v___x_4032_ = lean_ptr_addr(v_a_4027_);
                v___x_4033_ = lean_usize_to_uint64(v___x_4032_);
                v___x_4034_ = 11u64;
                v___x_4035_ = lean_uint64_mix_hash(v___x_4033_, v___x_4034_);
                v___x_4036_ = 32u64;
                v___x_4037_ = lean_uint64_shift_right(v___x_4035_, v___x_4036_);
                v_fold_4038_ = lean_uint64_xor(v___x_4035_, v___x_4037_);
                v___x_4039_ = 16u64;
                v___x_4040_ = lean_uint64_shift_right(v_fold_4038_, v___x_4039_);
                v___x_4041_ = lean_uint64_xor(v_fold_4038_, v___x_4040_);
                v___x_4042_ = lean_uint64_to_usize(v___x_4041_);
                v___x_4043_ = lean_usize_of_nat(v___x_4031_);
                v___x_4044_ = 1usize;
                v___x_4045_ = lean_usize_sub(v___x_4043_, v___x_4044_);
                v___x_4046_ = lean_usize_land(v___x_4042_, v___x_4045_);
                v_bkt_4047_ = lean_array_uget_borrowed(v_buckets_4030_, v___x_4046_);
                v___x_4048_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(v_a_4027_, v_bkt_4047_);
                if v___x_4048_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_4030_);
                    crate::leanh::lean_inc(v_size_4029_);
                    v_isSharedCheck_4069_ = (!crate::leanh::lean_is_exclusive(v_m_4026_)) as u8;
                    if v_isSharedCheck_4069_ == 0 {
                        v_unused_4070_ = crate::leanh::lean_ctor_get(v_m_4026_, 1);
                        crate::leanh::lean_dec(v_unused_4070_);
                        v_unused_4071_ = crate::leanh::lean_ctor_get(v_m_4026_, 0);
                        crate::leanh::lean_dec(v_unused_4071_);
                        v___x_4050_ = v_m_4026_;
                        v_isShared_4051_ = v_isSharedCheck_4069_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_4026_);
                        v___x_4050_ = crate::leanh::lean_box(0);
                        v_isShared_4051_ = v_isSharedCheck_4069_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_4028_);
                    crate::leanh::lean_dec_ref(v_a_4027_);
                    return v_m_4026_;
                }
            }
            1 => {
                v___x_4052_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_4053_ = lean_nat_add(v_size_4029_, v___x_4052_);
                crate::leanh::lean_dec(v_size_4029_);
                crate::leanh::lean_inc(v_bkt_4047_);
                v___x_4054_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4054_, 0, v_a_4027_);
                crate::leanh::lean_ctor_set(v___x_4054_, 1, v_b_4028_);
                crate::leanh::lean_ctor_set(v___x_4054_, 2, v_bkt_4047_);
                v_buckets_x27_4055_ = lean_array_uset(v_buckets_4030_, v___x_4046_, v___x_4054_);
                v___x_4056_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_4057_ = lean_nat_mul(v_size_x27_4053_, v___x_4056_);
                v___x_4058_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_4059_ = lean_nat_div(v___x_4057_, v___x_4058_);
                crate::leanh::lean_dec(v___x_4057_);
                v___x_4060_ = lean_array_get_size(v_buckets_x27_4055_);
                v___x_4061_ = lean_nat_dec_le(v___x_4059_, v___x_4060_);
                crate::leanh::lean_dec(v___x_4059_);
                if v___x_4061_ == 0 {
                    v_val_4062_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5___redArg(v_buckets_x27_4055_);
                    if v_isShared_4051_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4050_, 1, v_val_4062_);
                        crate::leanh::lean_ctor_set(v___x_4050_, 0, v_size_x27_4053_);
                        v___x_4064_ = v___x_4050_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4065_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_size_x27_4053_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4065_, 1, v_val_4062_);
                        v___x_4064_ = v_reuseFailAlloc_4065_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_4051_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4050_, 1, v_buckets_x27_4055_);
                        crate::leanh::lean_ctor_set(v___x_4050_, 0, v_size_x27_4053_);
                        v___x_4067_ = v___x_4050_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4068_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_size_x27_4053_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4068_, 1, v_buckets_x27_4055_);
                        v___x_4067_ = v_reuseFailAlloc_4068_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4064_;
            }
            3 => {
                return v___x_4067_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg(
    mut v_m_4072_: *mut crate::leanh::LeanObject,
    mut v_a_4073_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: usize = 0;
    let mut v___x_4077_: u64 = 0;
    let mut v___x_4078_: u64 = 0;
    let mut v___x_4079_: u64 = 0;
    let mut v___x_4080_: u64 = 0;
    let mut v___x_4081_: u64 = 0;
    let mut v_fold_4082_: u64 = 0;
    let mut v___x_4083_: u64 = 0;
    let mut v___x_4084_: u64 = 0;
    let mut v___x_4085_: u64 = 0;
    let mut v___x_4086_: usize = 0;
    let mut v___x_4087_: usize = 0;
    let mut v___x_4088_: usize = 0;
    let mut v___x_4089_: usize = 0;
    let mut v___x_4090_: usize = 0;
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: u8 = 0;
    v_buckets_4074_ = crate::leanh::lean_ctor_get(v_m_4072_, 1);
    v___x_4075_ = lean_array_get_size(v_buckets_4074_);
    v___x_4076_ = lean_ptr_addr(v_a_4073_);
    v___x_4077_ = lean_usize_to_uint64(v___x_4076_);
    v___x_4078_ = 11u64;
    v___x_4079_ = lean_uint64_mix_hash(v___x_4077_, v___x_4078_);
    v___x_4080_ = 32u64;
    v___x_4081_ = lean_uint64_shift_right(v___x_4079_, v___x_4080_);
    v_fold_4082_ = lean_uint64_xor(v___x_4079_, v___x_4081_);
    v___x_4083_ = 16u64;
    v___x_4084_ = lean_uint64_shift_right(v_fold_4082_, v___x_4083_);
    v___x_4085_ = lean_uint64_xor(v_fold_4082_, v___x_4084_);
    v___x_4086_ = lean_uint64_to_usize(v___x_4085_);
    v___x_4087_ = lean_usize_of_nat(v___x_4075_);
    v___x_4088_ = 1usize;
    v___x_4089_ = lean_usize_sub(v___x_4087_, v___x_4088_);
    v___x_4090_ = lean_usize_land(v___x_4086_, v___x_4089_);
    v___x_4091_ = lean_array_uget_borrowed(v_buckets_4074_, v___x_4090_);
    v___x_4092_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(v_a_4073_, v___x_4091_);
    return v___x_4092_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg___boxed(
    mut v_m_4093_: *mut crate::leanh::LeanObject,
    mut v_a_4094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4095_: u8 = 0;
    let mut v_r_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4095_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg(v_m_4093_, v_a_4094_);
    crate::leanh::lean_dec_ref(v_a_4094_);
    crate::leanh::lean_dec_ref(v_m_4093_);
    v_r_4096_ = crate::leanh::lean_box((v_res_4095_) as usize);
    return v_r_4096_;
}
pub unsafe fn l_Lean_Meta_FindSplitImpl_visit(
    mut v_e_4097_: *mut crate::leanh::LeanObject,
    mut v_a_4098_: *mut crate::leanh::LeanObject,
    mut v_a_4099_: *mut crate::leanh::LeanObject,
    mut v_a_4100_: *mut crate::leanh::LeanObject,
    mut v_a_4101_: *mut crate::leanh::LeanObject,
    mut v_a_4102_: *mut crate::leanh::LeanObject,
    mut v_a_4103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: u8 = 0;
    let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: u8 = 0;
    let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4149_: u8 = 0;
    let mut v___x_4150_: u8 = 0;
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4156_: u8 = 0;
    let mut v_a_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4160_: u8 = 0;
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4164_: u8 = 0;
    let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4136_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg(v_a_4099_, v_e_4097_);
                if v___x_4136_ == 0 {
                    v___x_4137_ = lean_st_ref_get(v_a_4103_);
                    v_env_4138_ = crate::leanh::lean_ctor_get(v___x_4137_, 0);
                    crate::leanh::lean_inc_ref(v_env_4138_);
                    crate::leanh::lean_dec(v___x_4137_);
                    v___x_4139_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref_n(v_e_4097_, 2);
                    v___x_4140_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4___redArg(v_a_4099_, v_e_4097_, v___x_4139_);
                    v___x_4141_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f(v_env_4138_, v_a_4098_, v_e_4097_);
                    if crate::leanh::lean_obj_tag(v___x_4141_) == 1 {
                        crate::leanh::lean_dec_ref(v_e_4097_);
                        v___x_4142_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4142_, 0, v___x_4141_);
                        crate::leanh::lean_ctor_set(v___x_4142_, 1, v___x_4140_);
                        v___x_4143_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4143_, 0, v___x_4142_);
                        return v___x_4143_;
                    } else {
                        crate::leanh::lean_dec(v___x_4141_);
                        v___x_4144_ = l_Lean_Expr_hasLooseBVars(v_e_4097_);
                        if v___x_4144_ == 0 {
                            crate::leanh::lean_inc_ref(v_e_4097_);
                            v___x_4145_ = l_Lean_Meta_isProof(
                                v_e_4097_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4103_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4145_) == 0 {
                                v_a_4146_ = crate::leanh::lean_ctor_get(v___x_4145_, 0);
                                v_isSharedCheck_4156_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4145_)) as u8;
                                if v_isSharedCheck_4156_ == 0 {
                                    v___x_4148_ = v___x_4145_;
                                    v_isShared_4149_ = v_isSharedCheck_4156_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4146_);
                                    crate::leanh::lean_dec(v___x_4145_);
                                    v___x_4148_ = crate::leanh::lean_box(0);
                                    v_isShared_4149_ = v_isSharedCheck_4156_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_4140_);
                                crate::leanh::lean_dec_ref(v_e_4097_);
                                v_a_4157_ = crate::leanh::lean_ctor_get(v___x_4145_, 0);
                                v_isSharedCheck_4164_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4145_)) as u8;
                                if v_isSharedCheck_4164_ == 0 {
                                    v___x_4159_ = v___x_4145_;
                                    v_isShared_4160_ = v_isSharedCheck_4164_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4157_);
                                    crate::leanh::lean_dec(v___x_4145_);
                                    v___x_4159_ = crate::leanh::lean_box(0);
                                    v_isShared_4160_ = v_isSharedCheck_4164_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            v___y_4106_ = v_a_4098_;
                            v___y_4107_ = v___x_4140_;
                            v___y_4108_ = v_a_4100_;
                            v___y_4109_ = v_a_4101_;
                            v___y_4110_ = v_a_4102_;
                            v___y_4111_ = v_a_4103_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_4097_);
                    v___x_4165_ = crate::leanh::lean_box(0);
                    v___x_4166_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4166_, 0, v___x_4165_);
                    crate::leanh::lean_ctor_set(v___x_4166_, 1, v_a_4099_);
                    v___x_4167_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4167_, 0, v___x_4166_);
                    return v___x_4167_;
                }
            }
            1 => match crate::leanh::lean_obj_tag(v_e_4097_) {
                6 => {
                    v_body_4112_ = crate::leanh::lean_ctor_get(v_e_4097_, 2);
                    crate::leanh::lean_inc_ref(v_body_4112_);
                    crate::leanh::lean_dec_ref_known(v_e_4097_, 3);
                    v_e_4097_ = v_body_4112_;
                    v_a_4098_ = v___y_4106_;
                    v_a_4099_ = v___y_4107_;
                    v_a_4100_ = v___y_4108_;
                    v_a_4101_ = v___y_4109_;
                    v_a_4102_ = v___y_4110_;
                    v_a_4103_ = v___y_4111_;
                    state = 0;
                    continue;
                }
                11 => {
                    v_struct_4114_ = crate::leanh::lean_ctor_get(v_e_4097_, 2);
                    crate::leanh::lean_inc_ref(v_struct_4114_);
                    crate::leanh::lean_dec_ref_known(v_e_4097_, 3);
                    v_e_4097_ = v_struct_4114_;
                    v_a_4098_ = v___y_4106_;
                    v_a_4099_ = v___y_4107_;
                    v_a_4100_ = v___y_4108_;
                    v_a_4101_ = v___y_4109_;
                    v_a_4102_ = v___y_4110_;
                    v_a_4103_ = v___y_4111_;
                    state = 0;
                    continue;
                }
                10 => {
                    v_expr_4116_ = crate::leanh::lean_ctor_get(v_e_4097_, 1);
                    crate::leanh::lean_inc_ref(v_expr_4116_);
                    crate::leanh::lean_dec_ref_known(v_e_4097_, 2);
                    v_e_4097_ = v_expr_4116_;
                    v_a_4098_ = v___y_4106_;
                    v_a_4099_ = v___y_4107_;
                    v_a_4100_ = v___y_4108_;
                    v_a_4101_ = v___y_4109_;
                    v_a_4102_ = v___y_4110_;
                    v_a_4103_ = v___y_4111_;
                    state = 0;
                    continue;
                }
                7 => {
                    v_binderType_4118_ = crate::leanh::lean_ctor_get(v_e_4097_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_4118_);
                    v_body_4119_ = crate::leanh::lean_ctor_get(v_e_4097_, 2);
                    crate::leanh::lean_inc_ref(v_body_4119_);
                    crate::leanh::lean_dec_ref_known(v_e_4097_, 3);
                    v___x_4120_ = l_Lean_Meta_FindSplitImpl_visit(
                        v_binderType_4118_,
                        v___y_4106_,
                        v___y_4107_,
                        v___y_4108_,
                        v___y_4109_,
                        v___y_4110_,
                        v___y_4111_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4120_) == 0 {
                        v_a_4121_ = crate::leanh::lean_ctor_get(v___x_4120_, 0);
                        crate::leanh::lean_inc(v_a_4121_);
                        v_fst_4122_ = crate::leanh::lean_ctor_get(v_a_4121_, 0);
                        if crate::leanh::lean_obj_tag(v_fst_4122_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4120_, 1);
                            v_snd_4123_ = crate::leanh::lean_ctor_get(v_a_4121_, 1);
                            crate::leanh::lean_inc(v_snd_4123_);
                            crate::leanh::lean_dec(v_a_4121_);
                            v_e_4097_ = v_body_4119_;
                            v_a_4098_ = v___y_4106_;
                            v_a_4099_ = v_snd_4123_;
                            v_a_4100_ = v___y_4108_;
                            v_a_4101_ = v___y_4109_;
                            v_a_4102_ = v___y_4110_;
                            v_a_4103_ = v___y_4111_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_4121_);
                            crate::leanh::lean_dec_ref(v_body_4119_);
                            return v___x_4120_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_body_4119_);
                        return v___x_4120_;
                    }
                }
                8 => {
                    v_value_4125_ = crate::leanh::lean_ctor_get(v_e_4097_, 2);
                    crate::leanh::lean_inc_ref(v_value_4125_);
                    v_body_4126_ = crate::leanh::lean_ctor_get(v_e_4097_, 3);
                    crate::leanh::lean_inc_ref(v_body_4126_);
                    crate::leanh::lean_dec_ref_known(v_e_4097_, 4);
                    v___x_4127_ = l_Lean_Meta_FindSplitImpl_visit(
                        v_value_4125_,
                        v___y_4106_,
                        v___y_4107_,
                        v___y_4108_,
                        v___y_4109_,
                        v___y_4110_,
                        v___y_4111_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4127_) == 0 {
                        v_a_4128_ = crate::leanh::lean_ctor_get(v___x_4127_, 0);
                        crate::leanh::lean_inc(v_a_4128_);
                        v_fst_4129_ = crate::leanh::lean_ctor_get(v_a_4128_, 0);
                        if crate::leanh::lean_obj_tag(v_fst_4129_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4127_, 1);
                            v_snd_4130_ = crate::leanh::lean_ctor_get(v_a_4128_, 1);
                            crate::leanh::lean_inc(v_snd_4130_);
                            crate::leanh::lean_dec(v_a_4128_);
                            v_e_4097_ = v_body_4126_;
                            v_a_4098_ = v___y_4106_;
                            v_a_4099_ = v_snd_4130_;
                            v_a_4100_ = v___y_4108_;
                            v_a_4101_ = v___y_4109_;
                            v_a_4102_ = v___y_4110_;
                            v_a_4103_ = v___y_4111_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_4128_);
                            crate::leanh::lean_dec_ref(v_body_4126_);
                            return v___x_4127_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_body_4126_);
                        return v___x_4127_;
                    }
                }
                5 => {
                    v___x_4132_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f(v_e_4097_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_);
                    return v___x_4132_;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_e_4097_);
                    v___x_4133_ = crate::leanh::lean_box(0);
                    v___x_4134_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4134_, 0, v___x_4133_);
                    crate::leanh::lean_ctor_set(v___x_4134_, 1, v___y_4107_);
                    v___x_4135_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4135_, 0, v___x_4134_);
                    return v___x_4135_;
                }
            },
            2 => {
                v___x_4150_ = (crate::leanh::lean_unbox(v_a_4146_) as u8);
                crate::leanh::lean_dec(v_a_4146_);
                if v___x_4150_ == 0 {
                    crate::leanh::lean_del_object(v___x_4148_);
                    v___y_4106_ = v_a_4098_;
                    v___y_4107_ = v___x_4140_;
                    v___y_4108_ = v_a_4100_;
                    v___y_4109_ = v_a_4101_;
                    v___y_4110_ = v_a_4102_;
                    v___y_4111_ = v_a_4103_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_e_4097_);
                    v___x_4151_ = crate::leanh::lean_box(0);
                    v___x_4152_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4152_, 0, v___x_4151_);
                    crate::leanh::lean_ctor_set(v___x_4152_, 1, v___x_4140_);
                    if v_isShared_4149_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4148_, 0, v___x_4152_);
                        v___x_4154_ = v___x_4148_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4155_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4155_, 0, v___x_4152_);
                        v___x_4154_ = v_reuseFailAlloc_4155_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4154_;
            }
            4 => {
                if v_isShared_4160_ == 0 {
                    v___x_4162_ = v___x_4159_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4163_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_a_4157_);
                    v___x_4162_ = v_reuseFailAlloc_4163_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4162_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(
    mut v_upperBound_4168_: *mut crate::leanh::LeanObject,
    mut v_args_4169_: *mut crate::leanh::LeanObject,
    mut v_info_4170_: *mut crate::leanh::LeanObject,
    mut v_a_4171_: *mut crate::leanh::LeanObject,
    mut v_b_4172_: *mut crate::leanh::LeanObject,
    mut v___y_4173_: *mut crate::leanh::LeanObject,
    mut v___y_4174_: *mut crate::leanh::LeanObject,
    mut v___y_4175_: *mut crate::leanh::LeanObject,
    mut v___y_4176_: *mut crate::leanh::LeanObject,
    mut v___y_4177_: *mut crate::leanh::LeanObject,
    mut v___y_4178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: u8 = 0;
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramInfo_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: u8 = 0;
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4206_: u8 = 0;
    let mut v___x_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4211_: u8 = 0;
    let mut v_unused_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4217_: u8 = 0;
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4221_: u8 = 0;
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isProp_4223_: u8 = 0;
    let mut v___x_4224_: u8 = 0;
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4231_: u8 = 0;
    let mut v___x_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4236_: u8 = 0;
    let mut v_unused_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4242_: u8 = 0;
    let mut v___x_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4246_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4191_ = lean_nat_dec_lt(v_a_4171_, v_upperBound_4168_);
                if v___x_4191_ == 0 {
                    crate::leanh::lean_dec(v_a_4171_);
                    v___x_4192_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4192_, 0, v_b_4172_);
                    crate::leanh::lean_ctor_set(v___x_4192_, 1, v___y_4174_);
                    v___x_4193_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4193_, 0, v___x_4192_);
                    return v___x_4193_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_4172_);
                    v_paramInfo_4194_ = crate::leanh::lean_ctor_get(v_info_4170_, 0);
                    v___x_4195_ = crate::leanh::lean_box(0);
                    v___x_4196_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0;
                    v___x_4197_ = lean_array_fget_borrowed(v_args_4169_, v_a_4171_);
                    v___x_4198_ = lean_array_get_size(v_paramInfo_4194_);
                    v___x_4199_ = lean_nat_dec_lt(v_a_4171_, v___x_4198_);
                    if v___x_4199_ == 0 {
                        crate::leanh::lean_inc(v___x_4197_);
                        v___x_4200_ = l_Lean_Meta_FindSplitImpl_visit(
                            v___x_4197_,
                            v___y_4173_,
                            v___y_4174_,
                            v___y_4175_,
                            v___y_4176_,
                            v___y_4177_,
                            v___y_4178_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4200_) == 0 {
                            v_a_4201_ = crate::leanh::lean_ctor_get(v___x_4200_, 0);
                            crate::leanh::lean_inc(v_a_4201_);
                            crate::leanh::lean_dec_ref_known(v___x_4200_, 1);
                            v_fst_4202_ = crate::leanh::lean_ctor_get(v_a_4201_, 0);
                            if crate::leanh::lean_obj_tag(v_fst_4202_) == 1 {
                                crate::leanh::lean_inc_ref(v_fst_4202_);
                                crate::leanh::lean_dec(v_a_4171_);
                                v_snd_4203_ = crate::leanh::lean_ctor_get(v_a_4201_, 1);
                                v_isSharedCheck_4211_ =
                                    (!crate::leanh::lean_is_exclusive(v_a_4201_)) as u8;
                                if v_isSharedCheck_4211_ == 0 {
                                    v_unused_4212_ = crate::leanh::lean_ctor_get(v_a_4201_, 0);
                                    crate::leanh::lean_dec(v_unused_4212_);
                                    v___x_4205_ = v_a_4201_;
                                    v_isShared_4206_ = v_isSharedCheck_4211_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_snd_4203_);
                                    crate::leanh::lean_dec(v_a_4201_);
                                    v___x_4205_ = crate::leanh::lean_box(0);
                                    v_isShared_4206_ = v_isSharedCheck_4211_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                v_snd_4213_ = crate::leanh::lean_ctor_get(v_a_4201_, 1);
                                crate::leanh::lean_inc(v_snd_4213_);
                                crate::leanh::lean_dec(v_a_4201_);
                                v_a_4186_ = v___x_4196_;
                                v_snd_4187_ = v_snd_4213_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4171_);
                            v_a_4214_ = crate::leanh::lean_ctor_get(v___x_4200_, 0);
                            v_isSharedCheck_4221_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4200_)) as u8;
                            if v_isSharedCheck_4221_ == 0 {
                                v___x_4216_ = v___x_4200_;
                                v_isShared_4217_ = v_isSharedCheck_4221_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4214_);
                                crate::leanh::lean_dec(v___x_4200_);
                                v___x_4216_ = crate::leanh::lean_box(0);
                                v_isShared_4217_ = v_isSharedCheck_4221_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        v___x_4222_ = lean_array_fget_borrowed(v_paramInfo_4194_, v_a_4171_);
                        v_isProp_4223_ = crate::leanh::lean_ctor_get_uint8(
                            v___x_4222_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 2) as u32,
                        );
                        if v_isProp_4223_ == 0 {
                            v___x_4224_ = l_Lean_Meta_ParamInfo_isExplicit(v___x_4222_);
                            if v___x_4224_ == 0 {
                                v_a_4186_ = v___x_4196_;
                                v_snd_4187_ = v___y_4174_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v___x_4197_);
                                v___x_4225_ = l_Lean_Meta_FindSplitImpl_visit(
                                    v___x_4197_,
                                    v___y_4173_,
                                    v___y_4174_,
                                    v___y_4175_,
                                    v___y_4176_,
                                    v___y_4177_,
                                    v___y_4178_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_4225_) == 0 {
                                    v_a_4226_ = crate::leanh::lean_ctor_get(v___x_4225_, 0);
                                    crate::leanh::lean_inc(v_a_4226_);
                                    crate::leanh::lean_dec_ref_known(v___x_4225_, 1);
                                    v_fst_4227_ = crate::leanh::lean_ctor_get(v_a_4226_, 0);
                                    if crate::leanh::lean_obj_tag(v_fst_4227_) == 1 {
                                        crate::leanh::lean_inc_ref(v_fst_4227_);
                                        crate::leanh::lean_dec(v_a_4171_);
                                        v_snd_4228_ = crate::leanh::lean_ctor_get(v_a_4226_, 1);
                                        v_isSharedCheck_4236_ =
                                            (!crate::leanh::lean_is_exclusive(v_a_4226_)) as u8;
                                        if v_isSharedCheck_4236_ == 0 {
                                            v_unused_4237_ =
                                                crate::leanh::lean_ctor_get(v_a_4226_, 0);
                                            crate::leanh::lean_dec(v_unused_4237_);
                                            v___x_4230_ = v_a_4226_;
                                            v_isShared_4231_ = v_isSharedCheck_4236_;
                                            state = 7;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_snd_4228_);
                                            crate::leanh::lean_dec(v_a_4226_);
                                            v___x_4230_ = crate::leanh::lean_box(0);
                                            v_isShared_4231_ = v_isSharedCheck_4236_;
                                            state = 7;
                                            continue;
                                        }
                                    } else {
                                        v_snd_4238_ = crate::leanh::lean_ctor_get(v_a_4226_, 1);
                                        crate::leanh::lean_inc(v_snd_4238_);
                                        crate::leanh::lean_dec(v_a_4226_);
                                        v_a_4186_ = v___x_4196_;
                                        v_snd_4187_ = v_snd_4238_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_4171_);
                                    v_a_4239_ = crate::leanh::lean_ctor_get(v___x_4225_, 0);
                                    v_isSharedCheck_4246_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4225_)) as u8;
                                    if v_isSharedCheck_4246_ == 0 {
                                        v___x_4241_ = v___x_4225_;
                                        v_isShared_4242_ = v_isSharedCheck_4246_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4239_);
                                        crate::leanh::lean_dec(v___x_4225_);
                                        v___x_4241_ = crate::leanh::lean_box(0);
                                        v_isShared_4242_ = v_isSharedCheck_4246_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            v_a_4186_ = v___x_4196_;
                            v_snd_4187_ = v___y_4174_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4183_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4183_, 0, v_a_4181_);
                crate::leanh::lean_ctor_set(v___x_4183_, 1, v_snd_4182_);
                v___x_4184_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4184_, 0, v___x_4183_);
                return v___x_4184_;
            }
            2 => {
                v___x_4188_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4189_ = lean_nat_add(v_a_4171_, v___x_4188_);
                crate::leanh::lean_dec(v_a_4171_);
                crate::leanh::lean_inc_ref(v_a_4186_);
                v_a_4171_ = v___x_4189_;
                v_b_4172_ = v_a_4186_;
                v___y_4174_ = v_snd_4187_;
                state = 0;
                continue;
            }
            3 => {
                v___x_4207_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4207_, 0, v_fst_4202_);
                if v_isShared_4206_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4205_, 1, v___x_4195_);
                    crate::leanh::lean_ctor_set(v___x_4205_, 0, v___x_4207_);
                    v___x_4209_ = v___x_4205_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4210_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4210_, 0, v___x_4207_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4210_, 1, v___x_4195_);
                    v___x_4209_ = v_reuseFailAlloc_4210_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_4181_ = v___x_4209_;
                v_snd_4182_ = v_snd_4203_;
                state = 1;
                continue;
            }
            5 => {
                if v_isShared_4217_ == 0 {
                    v___x_4219_ = v___x_4216_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4220_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_a_4214_);
                    v___x_4219_ = v_reuseFailAlloc_4220_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4219_;
            }
            7 => {
                v___x_4232_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4232_, 0, v_fst_4227_);
                if v_isShared_4231_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4230_, 1, v___x_4195_);
                    crate::leanh::lean_ctor_set(v___x_4230_, 0, v___x_4232_);
                    v___x_4234_ = v___x_4230_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4235_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4235_, 0, v___x_4232_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4235_, 1, v___x_4195_);
                    v___x_4234_ = v_reuseFailAlloc_4235_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_a_4181_ = v___x_4234_;
                v_snd_4182_ = v_snd_4228_;
                state = 1;
                continue;
            }
            9 => {
                if v_isShared_4242_ == 0 {
                    v___x_4244_ = v___x_4241_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4245_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4245_, 0, v_a_4239_);
                    v___x_4244_ = v_reuseFailAlloc_4245_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4244_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1(
    mut v_x_4251_: *mut crate::leanh::LeanObject,
    mut v_x_4252_: *mut crate::leanh::LeanObject,
    mut v_x_4253_: *mut crate::leanh::LeanObject,
    mut v___y_4254_: *mut crate::leanh::LeanObject,
    mut v___y_4255_: *mut crate::leanh::LeanObject,
    mut v___y_4256_: *mut crate::leanh::LeanObject,
    mut v___y_4257_: *mut crate::leanh::LeanObject,
    mut v___y_4258_: *mut crate::leanh::LeanObject,
    mut v___y_4259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_info_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4276_: u8 = 0;
    let mut v_fst_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4281_: u8 = 0;
    let mut v_snd_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4292_: u8 = 0;
    let mut v_unused_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4294_: u8 = 0;
    let mut v_a_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4298_: u8 = 0;
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4302_: u8 = 0;
    let mut v_fn_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: u8 = 0;
    let mut v___x_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4316_: u8 = 0;
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4320_: u8 = 0;
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4251_) == 5 {
                    v_fn_4303_ = crate::leanh::lean_ctor_get(v_x_4251_, 0);
                    crate::leanh::lean_inc_ref(v_fn_4303_);
                    v_arg_4304_ = crate::leanh::lean_ctor_get(v_x_4251_, 1);
                    crate::leanh::lean_inc_ref(v_arg_4304_);
                    crate::leanh::lean_dec_ref_known(v_x_4251_, 2);
                    v___x_4305_ = lean_array_set(v_x_4252_, v_x_4253_, v_arg_4304_);
                    v___x_4306_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4307_ = lean_nat_sub(v_x_4253_, v___x_4306_);
                    crate::leanh::lean_dec(v_x_4253_);
                    v_x_4251_ = v_fn_4303_;
                    v_x_4252_ = v___x_4305_;
                    v_x_4253_ = v___x_4307_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_4253_);
                    v___x_4309_ = l_Lean_Expr_hasLooseBVars(v_x_4251_);
                    if v___x_4309_ == 0 {
                        v___x_4310_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc_ref(v_x_4251_);
                        v___x_4311_ = l_Lean_Meta_getFunInfo(
                            v_x_4251_,
                            v___x_4310_,
                            v___y_4256_,
                            v___y_4257_,
                            v___y_4258_,
                            v___y_4259_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4311_) == 0 {
                            v_a_4312_ = crate::leanh::lean_ctor_get(v___x_4311_, 0);
                            crate::leanh::lean_inc(v_a_4312_);
                            crate::leanh::lean_dec_ref_known(v___x_4311_, 1);
                            v_info_4262_ = v_a_4312_;
                            v___y_4263_ = v___y_4254_;
                            v___y_4264_ = v___y_4255_;
                            v___y_4265_ = v___y_4256_;
                            v___y_4266_ = v___y_4257_;
                            v___y_4267_ = v___y_4258_;
                            v___y_4268_ = v___y_4259_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___y_4255_);
                            crate::leanh::lean_dec_ref(v_x_4252_);
                            crate::leanh::lean_dec_ref(v_x_4251_);
                            v_a_4313_ = crate::leanh::lean_ctor_get(v___x_4311_, 0);
                            v_isSharedCheck_4320_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4311_)) as u8;
                            if v_isSharedCheck_4320_ == 0 {
                                v___x_4315_ = v___x_4311_;
                                v_isShared_4316_ = v_isSharedCheck_4320_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4313_);
                                crate::leanh::lean_dec(v___x_4311_);
                                v___x_4315_ = crate::leanh::lean_box(0);
                                v_isShared_4316_ = v_isSharedCheck_4320_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        v___x_4321_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___closed__1;
                        v_info_4262_ = v___x_4321_;
                        v___y_4263_ = v___y_4254_;
                        v___y_4264_ = v___y_4255_;
                        v___y_4265_ = v___y_4256_;
                        v___y_4266_ = v___y_4257_;
                        v___y_4267_ = v___y_4258_;
                        v___y_4268_ = v___y_4259_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4269_ = lean_array_get_size(v_x_4252_);
                v___x_4270_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4271_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f_spec__1___redArg___closed__0;
                v___x_4272_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(v___x_4269_, v_x_4252_, v_info_4262_, v___x_4270_, v___x_4271_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_);
                crate::leanh::lean_dec_ref(v_info_4262_);
                crate::leanh::lean_dec_ref(v_x_4252_);
                if crate::leanh::lean_obj_tag(v___x_4272_) == 0 {
                    v_a_4273_ = crate::leanh::lean_ctor_get(v___x_4272_, 0);
                    v_isSharedCheck_4294_ = (!crate::leanh::lean_is_exclusive(v___x_4272_)) as u8;
                    if v_isSharedCheck_4294_ == 0 {
                        v___x_4275_ = v___x_4272_;
                        v_isShared_4276_ = v_isSharedCheck_4294_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4273_);
                        crate::leanh::lean_dec(v___x_4272_);
                        v___x_4275_ = crate::leanh::lean_box(0);
                        v_isShared_4276_ = v_isSharedCheck_4294_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_4251_);
                    v_a_4295_ = crate::leanh::lean_ctor_get(v___x_4272_, 0);
                    v_isSharedCheck_4302_ = (!crate::leanh::lean_is_exclusive(v___x_4272_)) as u8;
                    if v_isSharedCheck_4302_ == 0 {
                        v___x_4297_ = v___x_4272_;
                        v_isShared_4298_ = v_isSharedCheck_4302_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4295_);
                        crate::leanh::lean_dec(v___x_4272_);
                        v___x_4297_ = crate::leanh::lean_box(0);
                        v_isShared_4298_ = v_isSharedCheck_4302_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_4277_ = crate::leanh::lean_ctor_get(v_a_4273_, 0);
                crate::leanh::lean_inc(v_fst_4277_);
                v_fst_4278_ = crate::leanh::lean_ctor_get(v_fst_4277_, 0);
                v_isSharedCheck_4292_ = (!crate::leanh::lean_is_exclusive(v_fst_4277_)) as u8;
                if v_isSharedCheck_4292_ == 0 {
                    v_unused_4293_ = crate::leanh::lean_ctor_get(v_fst_4277_, 1);
                    crate::leanh::lean_dec(v_unused_4293_);
                    v___x_4280_ = v_fst_4277_;
                    v_isShared_4281_ = v_isSharedCheck_4292_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_4278_);
                    crate::leanh::lean_dec(v_fst_4277_);
                    v___x_4280_ = crate::leanh::lean_box(0);
                    v_isShared_4281_ = v_isSharedCheck_4292_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_fst_4278_) == 0 {
                    crate::leanh::lean_del_object(v___x_4280_);
                    crate::leanh::lean_del_object(v___x_4275_);
                    v_snd_4282_ = crate::leanh::lean_ctor_get(v_a_4273_, 1);
                    crate::leanh::lean_inc(v_snd_4282_);
                    crate::leanh::lean_dec(v_a_4273_);
                    v___x_4283_ = l_Lean_Meta_FindSplitImpl_visit(
                        v_x_4251_,
                        v___y_4263_,
                        v_snd_4282_,
                        v___y_4265_,
                        v___y_4266_,
                        v___y_4267_,
                        v___y_4268_,
                    );
                    return v___x_4283_;
                } else {
                    crate::leanh::lean_dec_ref(v_x_4251_);
                    v_snd_4284_ = crate::leanh::lean_ctor_get(v_a_4273_, 1);
                    crate::leanh::lean_inc(v_snd_4284_);
                    crate::leanh::lean_dec(v_a_4273_);
                    v_val_4285_ = crate::leanh::lean_ctor_get(v_fst_4278_, 0);
                    crate::leanh::lean_inc(v_val_4285_);
                    crate::leanh::lean_dec_ref_known(v_fst_4278_, 1);
                    if v_isShared_4281_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4280_, 1, v_snd_4284_);
                        crate::leanh::lean_ctor_set(v___x_4280_, 0, v_val_4285_);
                        v___x_4287_ = v___x_4280_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4291_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4291_, 0, v_val_4285_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4291_, 1, v_snd_4284_);
                        v___x_4287_ = v_reuseFailAlloc_4291_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4276_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4275_, 0, v___x_4287_);
                    v___x_4289_ = v___x_4275_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4290_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4290_, 0, v___x_4287_);
                    v___x_4289_ = v_reuseFailAlloc_4290_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4289_;
            }
            6 => {
                if v_isShared_4298_ == 0 {
                    v___x_4300_ = v___x_4297_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4301_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4301_, 0, v_a_4295_);
                    v___x_4300_ = v_reuseFailAlloc_4301_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4300_;
            }
            8 => {
                if v_isShared_4316_ == 0 {
                    v___x_4318_ = v___x_4315_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4319_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_a_4313_);
                    v___x_4318_ = v_reuseFailAlloc_4319_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4318_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f(
    mut v_e_4322_: *mut crate::leanh::LeanObject,
    mut v_a_4323_: *mut crate::leanh::LeanObject,
    mut v_a_4324_: *mut crate::leanh::LeanObject,
    mut v_a_4325_: *mut crate::leanh::LeanObject,
    mut v_a_4326_: *mut crate::leanh::LeanObject,
    mut v_a_4327_: *mut crate::leanh::LeanObject,
    mut v_a_4328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dummy_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dummy_4330_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0_once), _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__0);
    v_nargs_4331_ = l_Lean_Expr_getAppNumArgs(v_e_4322_);
    crate::leanh::lean_inc(v_nargs_4331_);
    v___x_4332_ = lean_mk_array(v_nargs_4331_, v_dummy_4330_);
    v___x_4333_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_4334_ = lean_nat_sub(v_nargs_4331_, v___x_4333_);
    crate::leanh::lean_dec(v_nargs_4331_);
    v___x_4335_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1(v_e_4322_, v___x_4332_, v___x_4334_, v_a_4323_, v_a_4324_, v_a_4325_, v_a_4326_, v_a_4327_, v_a_4328_);
    return v___x_4335_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f___boxed(
    mut v_e_4336_: *mut crate::leanh::LeanObject,
    mut v_a_4337_: *mut crate::leanh::LeanObject,
    mut v_a_4338_: *mut crate::leanh::LeanObject,
    mut v_a_4339_: *mut crate::leanh::LeanObject,
    mut v_a_4340_: *mut crate::leanh::LeanObject,
    mut v_a_4341_: *mut crate::leanh::LeanObject,
    mut v_a_4342_: *mut crate::leanh::LeanObject,
    mut v_a_4343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4344_ =
        l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f(
            v_e_4336_, v_a_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_,
        );
    crate::leanh::lean_dec(v_a_4342_);
    crate::leanh::lean_dec_ref(v_a_4341_);
    crate::leanh::lean_dec(v_a_4340_);
    crate::leanh::lean_dec_ref(v_a_4339_);
    crate::leanh::lean_dec_ref(v_a_4337_);
    return v_res_4344_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1___boxed(
    mut v_x_4345_: *mut crate::leanh::LeanObject,
    mut v_x_4346_: *mut crate::leanh::LeanObject,
    mut v_x_4347_: *mut crate::leanh::LeanObject,
    mut v___y_4348_: *mut crate::leanh::LeanObject,
    mut v___y_4349_: *mut crate::leanh::LeanObject,
    mut v___y_4350_: *mut crate::leanh::LeanObject,
    mut v___y_4351_: *mut crate::leanh::LeanObject,
    mut v___y_4352_: *mut crate::leanh::LeanObject,
    mut v___y_4353_: *mut crate::leanh::LeanObject,
    mut v___y_4354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4355_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__1(v_x_4345_, v_x_4346_, v_x_4347_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_, v___y_4352_, v___y_4353_);
    crate::leanh::lean_dec(v___y_4353_);
    crate::leanh::lean_dec_ref(v___y_4352_);
    crate::leanh::lean_dec(v___y_4351_);
    crate::leanh::lean_dec_ref(v___y_4350_);
    crate::leanh::lean_dec_ref(v___y_4348_);
    return v_res_4355_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg___boxed(
    mut v_upperBound_4356_: *mut crate::leanh::LeanObject,
    mut v_args_4357_: *mut crate::leanh::LeanObject,
    mut v_info_4358_: *mut crate::leanh::LeanObject,
    mut v_a_4359_: *mut crate::leanh::LeanObject,
    mut v_b_4360_: *mut crate::leanh::LeanObject,
    mut v___y_4361_: *mut crate::leanh::LeanObject,
    mut v___y_4362_: *mut crate::leanh::LeanObject,
    mut v___y_4363_: *mut crate::leanh::LeanObject,
    mut v___y_4364_: *mut crate::leanh::LeanObject,
    mut v___y_4365_: *mut crate::leanh::LeanObject,
    mut v___y_4366_: *mut crate::leanh::LeanObject,
    mut v___y_4367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4368_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(v_upperBound_4356_, v_args_4357_, v_info_4358_, v_a_4359_, v_b_4360_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_);
    crate::leanh::lean_dec(v___y_4366_);
    crate::leanh::lean_dec_ref(v___y_4365_);
    crate::leanh::lean_dec(v___y_4364_);
    crate::leanh::lean_dec_ref(v___y_4363_);
    crate::leanh::lean_dec_ref(v___y_4361_);
    crate::leanh::lean_dec_ref(v_info_4358_);
    crate::leanh::lean_dec_ref(v_args_4357_);
    crate::leanh::lean_dec(v_upperBound_4356_);
    return v_res_4368_;
}
pub unsafe fn l_Lean_Meta_FindSplitImpl_visit___boxed(
    mut v_e_4369_: *mut crate::leanh::LeanObject,
    mut v_a_4370_: *mut crate::leanh::LeanObject,
    mut v_a_4371_: *mut crate::leanh::LeanObject,
    mut v_a_4372_: *mut crate::leanh::LeanObject,
    mut v_a_4373_: *mut crate::leanh::LeanObject,
    mut v_a_4374_: *mut crate::leanh::LeanObject,
    mut v_a_4375_: *mut crate::leanh::LeanObject,
    mut v_a_4376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4377_ = l_Lean_Meta_FindSplitImpl_visit(
        v_e_4369_, v_a_4370_, v_a_4371_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_,
    );
    crate::leanh::lean_dec(v_a_4375_);
    crate::leanh::lean_dec_ref(v_a_4374_);
    crate::leanh::lean_dec(v_a_4373_);
    crate::leanh::lean_dec_ref(v_a_4372_);
    crate::leanh::lean_dec_ref(v_a_4370_);
    return v_res_4377_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0(
    mut v_upperBound_4378_: *mut crate::leanh::LeanObject,
    mut v_args_4379_: *mut crate::leanh::LeanObject,
    mut v_info_4380_: *mut crate::leanh::LeanObject,
    mut v_inst_4381_: *mut crate::leanh::LeanObject,
    mut v_R_4382_: *mut crate::leanh::LeanObject,
    mut v_a_4383_: *mut crate::leanh::LeanObject,
    mut v_b_4384_: *mut crate::leanh::LeanObject,
    mut v_c_4385_: *mut crate::leanh::LeanObject,
    mut v___y_4386_: *mut crate::leanh::LeanObject,
    mut v___y_4387_: *mut crate::leanh::LeanObject,
    mut v___y_4388_: *mut crate::leanh::LeanObject,
    mut v___y_4389_: *mut crate::leanh::LeanObject,
    mut v___y_4390_: *mut crate::leanh::LeanObject,
    mut v___y_4391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4393_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___redArg(v_upperBound_4378_, v_args_4379_, v_info_4380_, v_a_4383_, v_b_4384_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
    return v___x_4393_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0___boxed(
    mut v_upperBound_4394_: *mut crate::leanh::LeanObject,
    mut v_args_4395_: *mut crate::leanh::LeanObject,
    mut v_info_4396_: *mut crate::leanh::LeanObject,
    mut v_inst_4397_: *mut crate::leanh::LeanObject,
    mut v_R_4398_: *mut crate::leanh::LeanObject,
    mut v_a_4399_: *mut crate::leanh::LeanObject,
    mut v_b_4400_: *mut crate::leanh::LeanObject,
    mut v_c_4401_: *mut crate::leanh::LeanObject,
    mut v___y_4402_: *mut crate::leanh::LeanObject,
    mut v___y_4403_: *mut crate::leanh::LeanObject,
    mut v___y_4404_: *mut crate::leanh::LeanObject,
    mut v___y_4405_: *mut crate::leanh::LeanObject,
    mut v___y_4406_: *mut crate::leanh::LeanObject,
    mut v___y_4407_: *mut crate::leanh::LeanObject,
    mut v___y_4408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4409_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_visit_visitApp_x3f_spec__0(v_upperBound_4394_, v_args_4395_, v_info_4396_, v_inst_4397_, v_R_4398_, v_a_4399_, v_b_4400_, v_c_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_);
    crate::leanh::lean_dec(v___y_4407_);
    crate::leanh::lean_dec_ref(v___y_4406_);
    crate::leanh::lean_dec(v___y_4405_);
    crate::leanh::lean_dec_ref(v___y_4404_);
    crate::leanh::lean_dec_ref(v___y_4402_);
    crate::leanh::lean_dec_ref(v_info_4396_);
    crate::leanh::lean_dec_ref(v_args_4395_);
    crate::leanh::lean_dec(v_upperBound_4394_);
    return v_res_4409_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3(
    mut v_00_u03b2_4410_: *mut crate::leanh::LeanObject,
    mut v_m_4411_: *mut crate::leanh::LeanObject,
    mut v_a_4412_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4413_: u8 = 0;
    v___x_4413_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___redArg(v_m_4411_, v_a_4412_);
    return v___x_4413_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3___boxed(
    mut v_00_u03b2_4414_: *mut crate::leanh::LeanObject,
    mut v_m_4415_: *mut crate::leanh::LeanObject,
    mut v_a_4416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4417_: u8 = 0;
    let mut v_r_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4417_ =
        l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3(
            v_00_u03b2_4414_,
            v_m_4415_,
            v_a_4416_,
        );
    crate::leanh::lean_dec_ref(v_a_4416_);
    crate::leanh::lean_dec_ref(v_m_4415_);
    v_r_4418_ = crate::leanh::lean_box((v_res_4417_) as usize);
    return v_r_4418_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4(
    mut v_00_u03b2_4419_: *mut crate::leanh::LeanObject,
    mut v_m_4420_: *mut crate::leanh::LeanObject,
    mut v_a_4421_: *mut crate::leanh::LeanObject,
    mut v_b_4422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4423_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4___redArg(v_m_4420_, v_a_4421_, v_b_4422_);
    return v___x_4423_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3(
    mut v_00_u03b2_4424_: *mut crate::leanh::LeanObject,
    mut v_a_4425_: *mut crate::leanh::LeanObject,
    mut v_x_4426_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4427_: u8 = 0;
    v___x_4427_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___redArg(v_a_4425_, v_x_4426_);
    return v___x_4427_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3___boxed(
    mut v_00_u03b2_4428_: *mut crate::leanh::LeanObject,
    mut v_a_4429_: *mut crate::leanh::LeanObject,
    mut v_x_4430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4431_: u8 = 0;
    let mut v_r_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4431_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_FindSplitImpl_visit_spec__3_spec__3(v_00_u03b2_4428_, v_a_4429_, v_x_4430_);
    crate::leanh::lean_dec(v_x_4430_);
    crate::leanh::lean_dec_ref(v_a_4429_);
    v_r_4432_ = crate::leanh::lean_box((v_res_4431_) as usize);
    return v_r_4432_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5(
    mut v_00_u03b2_4433_: *mut crate::leanh::LeanObject,
    mut v_data_4434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4435_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5___redArg(v_data_4434_);
    return v___x_4435_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6(
    mut v_00_u03b2_4436_: *mut crate::leanh::LeanObject,
    mut v_i_4437_: *mut crate::leanh::LeanObject,
    mut v_source_4438_: *mut crate::leanh::LeanObject,
    mut v_target_4439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4440_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6___redArg(v_i_4437_, v_source_4438_, v_target_4439_);
    return v___x_4440_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6_spec__7(
    mut v_00_u03b2_4441_: *mut crate::leanh::LeanObject,
    mut v_x_4442_: *mut crate::leanh::LeanObject,
    mut v_x_4443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4444_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_FindSplitImpl_visit_spec__4_spec__5_spec__6_spec__7___redArg(v_x_4442_, v_x_4443_);
    return v___x_4444_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4445_ = crate::leanh::lean_unsigned_to_nat(64);
    v___x_4446_ = l_Lean_mkPtrSet___redArg(v___x_4445_);
    return v___x_4446_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1(
    mut v_kind_4447_: u8,
    mut v_exceptionSet_4448_: *mut crate::leanh::LeanObject,
    mut v_e_4449_: *mut crate::leanh::LeanObject,
    mut v_a_4450_: *mut crate::leanh::LeanObject,
    mut v_a_4451_: *mut crate::leanh::LeanObject,
    mut v_a_4452_: *mut crate::leanh::LeanObject,
    mut v_a_4453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4461_: u8 = 0;
    let mut v_fst_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4466_: u8 = 0;
    let mut v_a_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4470_: u8 = 0;
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4474_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4455_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4455_, 0, v_exceptionSet_4448_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4455_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_kind_4447_,
                );
                v___x_4456_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0_once), _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___closed__0);
                v___x_4457_ = l_Lean_Meta_FindSplitImpl_visit(
                    v_e_4449_,
                    v___x_4455_,
                    v___x_4456_,
                    v_a_4450_,
                    v_a_4451_,
                    v_a_4452_,
                    v_a_4453_,
                );
                crate::leanh::lean_dec_ref_known(v___x_4455_, 1);
                if crate::leanh::lean_obj_tag(v___x_4457_) == 0 {
                    v_a_4458_ = crate::leanh::lean_ctor_get(v___x_4457_, 0);
                    v_isSharedCheck_4466_ = (!crate::leanh::lean_is_exclusive(v___x_4457_)) as u8;
                    if v_isSharedCheck_4466_ == 0 {
                        v___x_4460_ = v___x_4457_;
                        v_isShared_4461_ = v_isSharedCheck_4466_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4458_);
                        crate::leanh::lean_dec(v___x_4457_);
                        v___x_4460_ = crate::leanh::lean_box(0);
                        v_isShared_4461_ = v_isSharedCheck_4466_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4467_ = crate::leanh::lean_ctor_get(v___x_4457_, 0);
                    v_isSharedCheck_4474_ = (!crate::leanh::lean_is_exclusive(v___x_4457_)) as u8;
                    if v_isSharedCheck_4474_ == 0 {
                        v___x_4469_ = v___x_4457_;
                        v_isShared_4470_ = v_isSharedCheck_4474_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4467_);
                        crate::leanh::lean_dec(v___x_4457_);
                        v___x_4469_ = crate::leanh::lean_box(0);
                        v_isShared_4470_ = v_isSharedCheck_4474_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4462_ = crate::leanh::lean_ctor_get(v_a_4458_, 0);
                crate::leanh::lean_inc(v_fst_4462_);
                crate::leanh::lean_dec(v_a_4458_);
                if v_isShared_4461_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4460_, 0, v_fst_4462_);
                    v___x_4464_ = v___x_4460_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4465_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4465_, 0, v_fst_4462_);
                    v___x_4464_ = v_reuseFailAlloc_4465_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4464_;
            }
            3 => {
                if v_isShared_4470_ == 0 {
                    v___x_4472_ = v___x_4469_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4473_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4473_, 0, v_a_4467_);
                    v___x_4472_ = v_reuseFailAlloc_4473_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4472_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1___boxed(
    mut v_kind_4475_: *mut crate::leanh::LeanObject,
    mut v_exceptionSet_4476_: *mut crate::leanh::LeanObject,
    mut v_e_4477_: *mut crate::leanh::LeanObject,
    mut v_a_4478_: *mut crate::leanh::LeanObject,
    mut v_a_4479_: *mut crate::leanh::LeanObject,
    mut v_a_4480_: *mut crate::leanh::LeanObject,
    mut v_a_4481_: *mut crate::leanh::LeanObject,
    mut v_a_4482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_4483_: u8 = 0;
    let mut v_res_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_4483_ = (crate::leanh::lean_unbox(v_kind_4475_) as u8);
    v_res_4484_ =
        l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1(
            v_kind_boxed_4483_,
            v_exceptionSet_4476_,
            v_e_4477_,
            v_a_4478_,
            v_a_4479_,
            v_a_4480_,
            v_a_4481_,
        );
    crate::leanh::lean_dec(v_a_4481_);
    crate::leanh::lean_dec_ref(v_a_4480_);
    crate::leanh::lean_dec(v_a_4479_);
    crate::leanh::lean_dec_ref(v_a_4478_);
    return v_res_4484_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(
    mut v_msgData_4485_: *mut crate::leanh::LeanObject,
    mut v___y_4486_: *mut crate::leanh::LeanObject,
    mut v___y_4487_: *mut crate::leanh::LeanObject,
    mut v___y_4488_: *mut crate::leanh::LeanObject,
    mut v___y_4489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4491_ = lean_st_ref_get(v___y_4489_);
    v_env_4492_ = crate::leanh::lean_ctor_get(v___x_4491_, 0);
    crate::leanh::lean_inc_ref(v_env_4492_);
    crate::leanh::lean_dec(v___x_4491_);
    v___x_4493_ = lean_st_ref_get(v___y_4487_);
    v_mctx_4494_ = crate::leanh::lean_ctor_get(v___x_4493_, 0);
    crate::leanh::lean_inc_ref(v_mctx_4494_);
    crate::leanh::lean_dec(v___x_4493_);
    v_lctx_4495_ = crate::leanh::lean_ctor_get(v___y_4486_, 2);
    v_options_4496_ = crate::leanh::lean_ctor_get(v___y_4488_, 2);
    crate::leanh::lean_inc_ref(v_options_4496_);
    crate::leanh::lean_inc_ref(v_lctx_4495_);
    v___x_4497_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4497_, 0, v_env_4492_);
    crate::leanh::lean_ctor_set(v___x_4497_, 1, v_mctx_4494_);
    crate::leanh::lean_ctor_set(v___x_4497_, 2, v_lctx_4495_);
    crate::leanh::lean_ctor_set(v___x_4497_, 3, v_options_4496_);
    v___x_4498_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4498_, 0, v___x_4497_);
    crate::leanh::lean_ctor_set(v___x_4498_, 1, v_msgData_4485_);
    v___x_4499_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4499_, 0, v___x_4498_);
    return v___x_4499_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0___boxed(
    mut v_msgData_4500_: *mut crate::leanh::LeanObject,
    mut v___y_4501_: *mut crate::leanh::LeanObject,
    mut v___y_4502_: *mut crate::leanh::LeanObject,
    mut v___y_4503_: *mut crate::leanh::LeanObject,
    mut v___y_4504_: *mut crate::leanh::LeanObject,
    mut v___y_4505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4506_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(v_msgData_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_);
    crate::leanh::lean_dec(v___y_4504_);
    crate::leanh::lean_dec_ref(v___y_4503_);
    crate::leanh::lean_dec(v___y_4502_);
    crate::leanh::lean_dec_ref(v___y_4501_);
    return v_res_4506_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0()
-> f64 {
    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: f64 = 0.0;
    v___x_4507_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4508_ = lean_float_of_nat(v___x_4507_);
    return v___x_4508_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(
    mut v_cls_4512_: *mut crate::leanh::LeanObject,
    mut v_msg_4513_: *mut crate::leanh::LeanObject,
    mut v___y_4514_: *mut crate::leanh::LeanObject,
    mut v___y_4515_: *mut crate::leanh::LeanObject,
    mut v___y_4516_: *mut crate::leanh::LeanObject,
    mut v___y_4517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4524_: u8 = 0;
    let mut v___x_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4537_: u8 = 0;
    let mut v_tid_4538_: u64 = 0;
    let mut v_traces_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4542_: u8 = 0;
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: f64 = 0.0;
    let mut v___x_4545_: u8 = 0;
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4563_: u8 = 0;
    let mut v_isSharedCheck_4564_: u8 = 0;
    let mut v_isSharedCheck_4565_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4519_ = crate::leanh::lean_ctor_get(v___y_4516_, 5);
                v___x_4520_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(v_msg_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_);
                v_a_4521_ = crate::leanh::lean_ctor_get(v___x_4520_, 0);
                v_isSharedCheck_4565_ = (!crate::leanh::lean_is_exclusive(v___x_4520_)) as u8;
                if v_isSharedCheck_4565_ == 0 {
                    v___x_4523_ = v___x_4520_;
                    v_isShared_4524_ = v_isSharedCheck_4565_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4521_);
                    crate::leanh::lean_dec(v___x_4520_);
                    v___x_4523_ = crate::leanh::lean_box(0);
                    v_isShared_4524_ = v_isSharedCheck_4565_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4525_ = lean_st_ref_take(v___y_4517_);
                v_traceState_4526_ = crate::leanh::lean_ctor_get(v___x_4525_, 4);
                v_env_4527_ = crate::leanh::lean_ctor_get(v___x_4525_, 0);
                v_nextMacroScope_4528_ = crate::leanh::lean_ctor_get(v___x_4525_, 1);
                v_ngen_4529_ = crate::leanh::lean_ctor_get(v___x_4525_, 2);
                v_auxDeclNGen_4530_ = crate::leanh::lean_ctor_get(v___x_4525_, 3);
                v_cache_4531_ = crate::leanh::lean_ctor_get(v___x_4525_, 5);
                v_messages_4532_ = crate::leanh::lean_ctor_get(v___x_4525_, 6);
                v_infoState_4533_ = crate::leanh::lean_ctor_get(v___x_4525_, 7);
                v_snapshotTasks_4534_ = crate::leanh::lean_ctor_get(v___x_4525_, 8);
                v_isSharedCheck_4564_ = (!crate::leanh::lean_is_exclusive(v___x_4525_)) as u8;
                if v_isSharedCheck_4564_ == 0 {
                    v___x_4536_ = v___x_4525_;
                    v_isShared_4537_ = v_isSharedCheck_4564_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4534_);
                    crate::leanh::lean_inc(v_infoState_4533_);
                    crate::leanh::lean_inc(v_messages_4532_);
                    crate::leanh::lean_inc(v_cache_4531_);
                    crate::leanh::lean_inc(v_traceState_4526_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4530_);
                    crate::leanh::lean_inc(v_ngen_4529_);
                    crate::leanh::lean_inc(v_nextMacroScope_4528_);
                    crate::leanh::lean_inc(v_env_4527_);
                    crate::leanh::lean_dec(v___x_4525_);
                    v___x_4536_ = crate::leanh::lean_box(0);
                    v_isShared_4537_ = v_isSharedCheck_4564_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_4538_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_4526_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_4539_ = crate::leanh::lean_ctor_get(v_traceState_4526_, 0);
                v_isSharedCheck_4563_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_4526_)) as u8;
                if v_isSharedCheck_4563_ == 0 {
                    v___x_4541_ = v_traceState_4526_;
                    v_isShared_4542_ = v_isSharedCheck_4563_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_4539_);
                    crate::leanh::lean_dec(v_traceState_4526_);
                    v___x_4541_ = crate::leanh::lean_box(0);
                    v_isShared_4542_ = v_isSharedCheck_4563_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4543_ = crate::leanh::lean_box(0);
                v___x_4544_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0);
                v___x_4545_ = 0;
                v___x_4546_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__1;
                v___x_4547_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_4547_, 0, v_cls_4512_);
                crate::leanh::lean_ctor_set(v___x_4547_, 1, v___x_4543_);
                crate::leanh::lean_ctor_set(v___x_4547_, 2, v___x_4546_);
                crate::leanh::lean_ctor_set_float(
                    v___x_4547_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_4544_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_4547_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_4544_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4547_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_4545_,
                );
                v___x_4548_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__2;
                v___x_4549_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4549_, 0, v___x_4547_);
                crate::leanh::lean_ctor_set(v___x_4549_, 1, v_a_4521_);
                crate::leanh::lean_ctor_set(v___x_4549_, 2, v___x_4548_);
                crate::leanh::lean_inc(v_ref_4519_);
                v___x_4550_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4550_, 0, v_ref_4519_);
                crate::leanh::lean_ctor_set(v___x_4550_, 1, v___x_4549_);
                v___x_4551_ = l_Lean_PersistentArray_push___redArg(v_traces_4539_, v___x_4550_);
                if v_isShared_4542_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4541_, 0, v___x_4551_);
                    v___x_4553_ = v___x_4541_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4562_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4562_, 0, v___x_4551_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_4562_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_4538_,
                    );
                    v___x_4553_ = v_reuseFailAlloc_4562_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4537_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4536_, 4, v___x_4553_);
                    v___x_4555_ = v___x_4536_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4561_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_env_4527_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4561_, 1, v_nextMacroScope_4528_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4561_, 2, v_ngen_4529_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4561_, 3, v_auxDeclNGen_4530_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4561_, 4, v___x_4553_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4561_, 5, v_cache_4531_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4561_, 6, v_messages_4532_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4561_, 7, v_infoState_4533_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4561_, 8, v_snapshotTasks_4534_);
                    v___x_4555_ = v_reuseFailAlloc_4561_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4556_ = lean_st_ref_set(v___y_4517_, v___x_4555_);
                v___x_4557_ = crate::leanh::lean_box(0);
                if v_isShared_4524_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4523_, 0, v___x_4557_);
                    v___x_4559_ = v___x_4523_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4560_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4560_, 0, v___x_4557_);
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
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___boxed(
    mut v_cls_4566_: *mut crate::leanh::LeanObject,
    mut v_msg_4567_: *mut crate::leanh::LeanObject,
    mut v___y_4568_: *mut crate::leanh::LeanObject,
    mut v___y_4569_: *mut crate::leanh::LeanObject,
    mut v___y_4570_: *mut crate::leanh::LeanObject,
    mut v___y_4571_: *mut crate::leanh::LeanObject,
    mut v___y_4572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4573_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v_cls_4566_, v_msg_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_);
    crate::leanh::lean_dec(v___y_4571_);
    crate::leanh::lean_dec_ref(v___y_4570_);
    crate::leanh::lean_dec(v___y_4569_);
    crate::leanh::lean_dec_ref(v___y_4568_);
    return v_res_4573_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4582_ =
        l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__2;
    v___x_4583_ =
        l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4;
    v___x_4584_ = l_Lean_Name_append(v___x_4583_, v___x_4582_);
    return v___x_4584_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4586_ =
        l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__6;
    v___x_4587_ = l_Lean_stringToMessageData(v___x_4586_);
    return v___x_4587_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f(
    mut v_kind_4588_: u8,
    mut v_exceptionSet_4589_: *mut crate::leanh::LeanObject,
    mut v_e_4590_: *mut crate::leanh::LeanObject,
    mut v_a_4591_: *mut crate::leanh::LeanObject,
    mut v_a_4592_: *mut crate::leanh::LeanObject,
    mut v_a_4593_: *mut crate::leanh::LeanObject,
    mut v_a_4594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4599_: u8 = 0;
    let mut v_val_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: u8 = 0;
    let mut v___x_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4611_: u8 = 0;
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4615_: u8 = 0;
    let mut v_unused_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4620_: u8 = 0;
    let mut v___x_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4624_: u8 = 0;
    let mut v___x_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4627_: u8 = 0;
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4632_: u8 = 0;
    let mut v_unused_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4596_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_unsafe__1(v_kind_4588_, v_exceptionSet_4589_, v_e_4590_, v_a_4591_, v_a_4592_, v_a_4593_, v_a_4594_);
                if crate::leanh::lean_obj_tag(v___x_4596_) == 0 {
                    v_a_4597_ = crate::leanh::lean_ctor_get(v___x_4596_, 0);
                    crate::leanh::lean_inc(v_a_4597_);
                    if crate::leanh::lean_obj_tag(v_a_4597_) == 1 {
                        v_options_4598_ = crate::leanh::lean_ctor_get(v_a_4593_, 2);
                        v_hasTrace_4599_ = crate::leanh::lean_ctor_get_uint8(
                            v_options_4598_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_4599_ == 0 {
                            crate::leanh::lean_dec_ref_known(v_a_4597_, 1);
                            return v___x_4596_;
                        } else {
                            v_val_4600_ = crate::leanh::lean_ctor_get(v_a_4597_, 0);
                            v_inheritedTraceOptions_4601_ =
                                crate::leanh::lean_ctor_get(v_a_4593_, 13);
                            v___x_4602_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__2;
                            v___x_4603_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5_once), _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__5);
                            v___x_4604_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_4601_,
                                v_options_4598_,
                                v___x_4603_,
                            );
                            if v___x_4604_ == 0 {
                                crate::leanh::lean_dec_ref_known(v_a_4597_, 1);
                                return v___x_4596_;
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_4596_, 1);
                                v___x_4605_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7_once), _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__7);
                                crate::leanh::lean_inc(v_val_4600_);
                                v___x_4606_ = l_Lean_indentExpr(v_val_4600_);
                                v___x_4607_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4607_, 0, v___x_4605_);
                                crate::leanh::lean_ctor_set(v___x_4607_, 1, v___x_4606_);
                                v___x_4608_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_4602_, v___x_4607_, v_a_4591_, v_a_4592_, v_a_4593_, v_a_4594_);
                                if crate::leanh::lean_obj_tag(v___x_4608_) == 0 {
                                    v_isSharedCheck_4615_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4608_)) as u8;
                                    if v_isSharedCheck_4615_ == 0 {
                                        v_unused_4616_ =
                                            crate::leanh::lean_ctor_get(v___x_4608_, 0);
                                        crate::leanh::lean_dec(v_unused_4616_);
                                        v___x_4610_ = v___x_4608_;
                                        v_isShared_4611_ = v_isSharedCheck_4615_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_4608_);
                                        v___x_4610_ = crate::leanh::lean_box(0);
                                        v_isShared_4611_ = v_isSharedCheck_4615_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref_known(v_a_4597_, 1);
                                    v_a_4617_ = crate::leanh::lean_ctor_get(v___x_4608_, 0);
                                    v_isSharedCheck_4624_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4608_)) as u8;
                                    if v_isSharedCheck_4624_ == 0 {
                                        v___x_4619_ = v___x_4608_;
                                        v_isShared_4620_ = v_isSharedCheck_4624_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4617_);
                                        crate::leanh::lean_dec(v___x_4608_);
                                        v___x_4619_ = crate::leanh::lean_box(0);
                                        v_isShared_4620_ = v_isSharedCheck_4624_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4597_);
                        v_isSharedCheck_4632_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4596_)) as u8;
                        if v_isSharedCheck_4632_ == 0 {
                            v_unused_4633_ = crate::leanh::lean_ctor_get(v___x_4596_, 0);
                            crate::leanh::lean_dec(v_unused_4633_);
                            v___x_4626_ = v___x_4596_;
                            v_isShared_4627_ = v_isSharedCheck_4632_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4596_);
                            v___x_4626_ = crate::leanh::lean_box(0);
                            v_isShared_4627_ = v_isSharedCheck_4632_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    return v___x_4596_;
                }
            }
            1 => {
                if v_isShared_4611_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4610_, 0, v_a_4597_);
                    v___x_4613_ = v___x_4610_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4614_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4614_, 0, v_a_4597_);
                    v___x_4613_ = v_reuseFailAlloc_4614_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4613_;
            }
            3 => {
                if v_isShared_4620_ == 0 {
                    v___x_4622_ = v___x_4619_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4623_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4623_, 0, v_a_4617_);
                    v___x_4622_ = v_reuseFailAlloc_4623_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4622_;
            }
            5 => {
                v___x_4628_ = crate::leanh::lean_box(0);
                if v_isShared_4627_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4626_, 0, v___x_4628_);
                    v___x_4630_ = v___x_4626_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4631_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4631_, 0, v___x_4628_);
                    v___x_4630_ = v_reuseFailAlloc_4631_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4630_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___boxed(
    mut v_kind_4634_: *mut crate::leanh::LeanObject,
    mut v_exceptionSet_4635_: *mut crate::leanh::LeanObject,
    mut v_e_4636_: *mut crate::leanh::LeanObject,
    mut v_a_4637_: *mut crate::leanh::LeanObject,
    mut v_a_4638_: *mut crate::leanh::LeanObject,
    mut v_a_4639_: *mut crate::leanh::LeanObject,
    mut v_a_4640_: *mut crate::leanh::LeanObject,
    mut v_a_4641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_4642_: u8 = 0;
    let mut v_res_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_4642_ = (crate::leanh::lean_unbox(v_kind_4634_) as u8);
    v_res_4643_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f(
        v_kind_boxed_4642_,
        v_exceptionSet_4635_,
        v_e_4636_,
        v_a_4637_,
        v_a_4638_,
        v_a_4639_,
        v_a_4640_,
    );
    crate::leanh::lean_dec(v_a_4640_);
    crate::leanh::lean_dec_ref(v_a_4639_);
    crate::leanh::lean_dec(v_a_4638_);
    crate::leanh::lean_dec_ref(v_a_4637_);
    return v_res_4643_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(
    mut v_kind_4644_: u8,
    mut v_exceptionSet_4645_: *mut crate::leanh::LeanObject,
    mut v_e_4646_: *mut crate::leanh::LeanObject,
    mut v_a_4647_: *mut crate::leanh::LeanObject,
    mut v_a_4648_: *mut crate::leanh::LeanObject,
    mut v_a_4649_: *mut crate::leanh::LeanObject,
    mut v_a_4650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4660_: u8 = 0;
    let mut v___x_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: u8 = 0;
    let mut v___x_4667_: u8 = 0;
    let mut v___x_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4670_: u8 = 0;
    let mut v___x_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4675_: u8 = 0;
    let mut v_unused_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_exceptionSet_4645_);
                v___x_4656_ =
                    l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f(
                        v_kind_4644_,
                        v_exceptionSet_4645_,
                        v_e_4646_,
                        v_a_4647_,
                        v_a_4648_,
                        v_a_4649_,
                        v_a_4650_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4656_) == 0 {
                    v_a_4657_ = crate::leanh::lean_ctor_get(v___x_4656_, 0);
                    crate::leanh::lean_inc(v_a_4657_);
                    if crate::leanh::lean_obj_tag(v_a_4657_) == 1 {
                        v_val_4658_ = crate::leanh::lean_ctor_get(v_a_4657_, 0);
                        crate::leanh::lean_inc(v_val_4658_);
                        crate::leanh::lean_dec_ref_known(v_a_4657_, 1);
                        v___x_4666_ = l_Lean_Expr_isIte(v_val_4658_);
                        if v___x_4666_ == 0 {
                            v___x_4667_ = l_Lean_Expr_isDIte(v_val_4658_);
                            v___y_4660_ = v___x_4667_;
                            state = 2;
                            continue;
                        } else {
                            v___y_4660_ = v___x_4666_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4657_);
                        crate::leanh::lean_dec_ref(v_exceptionSet_4645_);
                        v_isSharedCheck_4675_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4656_)) as u8;
                        if v_isSharedCheck_4675_ == 0 {
                            v_unused_4676_ = crate::leanh::lean_ctor_get(v___x_4656_, 0);
                            crate::leanh::lean_dec(v_unused_4676_);
                            v___x_4669_ = v___x_4656_;
                            v_isShared_4670_ = v_isSharedCheck_4675_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4656_);
                            v___x_4669_ = crate::leanh::lean_box(0);
                            v_isShared_4670_ = v_isSharedCheck_4675_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_exceptionSet_4645_);
                    return v___x_4656_;
                }
            }
            1 => {
                v___x_4654_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4654_, 0, v___y_4653_);
                v___x_4655_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4655_, 0, v___x_4654_);
                return v___x_4655_;
            }
            2 => {
                if v___y_4660_ == 0 {
                    crate::leanh::lean_dec(v_val_4658_);
                    crate::leanh::lean_dec_ref(v_exceptionSet_4645_);
                    return v___x_4656_;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_4656_, 1);
                    v___x_4661_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_4662_ = l_Lean_Expr_getRevArg_x21(v_val_4658_, v___x_4661_);
                    v___x_4663_ =
                        l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(
                            v_kind_4644_,
                            v_exceptionSet_4645_,
                            v___x_4662_,
                            v_a_4647_,
                            v_a_4648_,
                            v_a_4649_,
                            v_a_4650_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_4663_) == 0 {
                        v_a_4664_ = crate::leanh::lean_ctor_get(v___x_4663_, 0);
                        crate::leanh::lean_inc(v_a_4664_);
                        crate::leanh::lean_dec_ref_known(v___x_4663_, 1);
                        if crate::leanh::lean_obj_tag(v_a_4664_) == 0 {
                            v___y_4653_ = v_val_4658_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_val_4658_);
                            v_val_4665_ = crate::leanh::lean_ctor_get(v_a_4664_, 0);
                            crate::leanh::lean_inc(v_val_4665_);
                            crate::leanh::lean_dec_ref_known(v_a_4664_, 1);
                            v___y_4653_ = v_val_4665_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_4658_);
                        return v___x_4663_;
                    }
                }
            }
            3 => {
                v___x_4671_ = crate::leanh::lean_box(0);
                if v_isShared_4670_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4669_, 0, v___x_4671_);
                    v___x_4673_ = v___x_4669_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4674_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4674_, 0, v___x_4671_);
                    v___x_4673_ = v_reuseFailAlloc_4674_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4673_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go___boxed(
    mut v_kind_4677_: *mut crate::leanh::LeanObject,
    mut v_exceptionSet_4678_: *mut crate::leanh::LeanObject,
    mut v_e_4679_: *mut crate::leanh::LeanObject,
    mut v_a_4680_: *mut crate::leanh::LeanObject,
    mut v_a_4681_: *mut crate::leanh::LeanObject,
    mut v_a_4682_: *mut crate::leanh::LeanObject,
    mut v_a_4683_: *mut crate::leanh::LeanObject,
    mut v_a_4684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_4685_: u8 = 0;
    let mut v_res_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_4685_ = (crate::leanh::lean_unbox(v_kind_4677_) as u8);
    v_res_4686_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(
        v_kind_boxed_4685_,
        v_exceptionSet_4678_,
        v_e_4679_,
        v_a_4680_,
        v_a_4681_,
        v_a_4682_,
        v_a_4683_,
    );
    crate::leanh::lean_dec(v_a_4683_);
    crate::leanh::lean_dec_ref(v_a_4682_);
    crate::leanh::lean_dec(v_a_4681_);
    crate::leanh::lean_dec_ref(v_a_4680_);
    return v_res_4686_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(
    mut v_e_4687_: *mut crate::leanh::LeanObject,
    mut v___y_4688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4690_: u8 = 0;
    let mut v___x_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4704_: u8 = 0;
    let mut v___x_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4710_: u8 = 0;
    let mut v_unused_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4690_ = l_Lean_Expr_hasMVar(v_e_4687_);
                if v___x_4690_ == 0 {
                    v___x_4691_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4691_, 0, v_e_4687_);
                    return v___x_4691_;
                } else {
                    v___x_4692_ = lean_st_ref_get(v___y_4688_);
                    v_mctx_4693_ = crate::leanh::lean_ctor_get(v___x_4692_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_4693_);
                    crate::leanh::lean_dec(v___x_4692_);
                    v___x_4694_ = l_Lean_instantiateMVarsCore(v_mctx_4693_, v_e_4687_);
                    v_fst_4695_ = crate::leanh::lean_ctor_get(v___x_4694_, 0);
                    crate::leanh::lean_inc(v_fst_4695_);
                    v_snd_4696_ = crate::leanh::lean_ctor_get(v___x_4694_, 1);
                    crate::leanh::lean_inc(v_snd_4696_);
                    crate::leanh::lean_dec_ref(v___x_4694_);
                    v___x_4697_ = lean_st_ref_take(v___y_4688_);
                    v_cache_4698_ = crate::leanh::lean_ctor_get(v___x_4697_, 1);
                    v_zetaDeltaFVarIds_4699_ = crate::leanh::lean_ctor_get(v___x_4697_, 2);
                    v_postponed_4700_ = crate::leanh::lean_ctor_get(v___x_4697_, 3);
                    v_diag_4701_ = crate::leanh::lean_ctor_get(v___x_4697_, 4);
                    v_isSharedCheck_4710_ = (!crate::leanh::lean_is_exclusive(v___x_4697_)) as u8;
                    if v_isSharedCheck_4710_ == 0 {
                        v_unused_4711_ = crate::leanh::lean_ctor_get(v___x_4697_, 0);
                        crate::leanh::lean_dec(v_unused_4711_);
                        v___x_4703_ = v___x_4697_;
                        v_isShared_4704_ = v_isSharedCheck_4710_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_4701_);
                        crate::leanh::lean_inc(v_postponed_4700_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_4699_);
                        crate::leanh::lean_inc(v_cache_4698_);
                        crate::leanh::lean_dec(v___x_4697_);
                        v___x_4703_ = crate::leanh::lean_box(0);
                        v_isShared_4704_ = v_isSharedCheck_4710_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4704_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4703_, 0, v_snd_4696_);
                    v___x_4706_ = v___x_4703_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4709_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4709_, 0, v_snd_4696_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4709_, 1, v_cache_4698_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4709_,
                        2,
                        v_zetaDeltaFVarIds_4699_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4709_, 3, v_postponed_4700_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4709_, 4, v_diag_4701_);
                    v___x_4706_ = v_reuseFailAlloc_4709_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4707_ = lean_st_ref_set(v___y_4688_, v___x_4706_);
                v___x_4708_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4708_, 0, v_fst_4695_);
                return v___x_4708_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg___boxed(
    mut v_e_4712_: *mut crate::leanh::LeanObject,
    mut v___y_4713_: *mut crate::leanh::LeanObject,
    mut v___y_4714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4715_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(
        v_e_4712_,
        v___y_4713_,
    );
    crate::leanh::lean_dec(v___y_4713_);
    return v_res_4715_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0(
    mut v_e_4716_: *mut crate::leanh::LeanObject,
    mut v___y_4717_: *mut crate::leanh::LeanObject,
    mut v___y_4718_: *mut crate::leanh::LeanObject,
    mut v___y_4719_: *mut crate::leanh::LeanObject,
    mut v___y_4720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4722_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(
        v_e_4716_,
        v___y_4718_,
    );
    return v___x_4722_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___boxed(
    mut v_e_4723_: *mut crate::leanh::LeanObject,
    mut v___y_4724_: *mut crate::leanh::LeanObject,
    mut v___y_4725_: *mut crate::leanh::LeanObject,
    mut v___y_4726_: *mut crate::leanh::LeanObject,
    mut v___y_4727_: *mut crate::leanh::LeanObject,
    mut v___y_4728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4729_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0(
        v_e_4723_,
        v___y_4724_,
        v___y_4725_,
        v___y_4726_,
        v___y_4727_,
    );
    crate::leanh::lean_dec(v___y_4727_);
    crate::leanh::lean_dec_ref(v___y_4726_);
    crate::leanh::lean_dec(v___y_4725_);
    crate::leanh::lean_dec_ref(v___y_4724_);
    return v_res_4729_;
}
pub unsafe fn l_Lean_Meta_findSplit_x3f(
    mut v_e_4730_: *mut crate::leanh::LeanObject,
    mut v_kind_4731_: u8,
    mut v_exceptionSet_4732_: *mut crate::leanh::LeanObject,
    mut v_a_4733_: *mut crate::leanh::LeanObject,
    mut v_a_4734_: *mut crate::leanh::LeanObject,
    mut v_a_4735_: *mut crate::leanh::LeanObject,
    mut v_a_4736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4738_ = l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(
        v_e_4730_, v_a_4734_,
    );
    v_a_4739_ = crate::leanh::lean_ctor_get(v___x_4738_, 0);
    crate::leanh::lean_inc(v_a_4739_);
    crate::leanh::lean_dec_ref(v___x_4738_);
    v___x_4740_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_go(
        v_kind_4731_,
        v_exceptionSet_4732_,
        v_a_4739_,
        v_a_4733_,
        v_a_4734_,
        v_a_4735_,
        v_a_4736_,
    );
    return v___x_4740_;
}
pub unsafe fn l_Lean_Meta_findSplit_x3f___boxed(
    mut v_e_4741_: *mut crate::leanh::LeanObject,
    mut v_kind_4742_: *mut crate::leanh::LeanObject,
    mut v_exceptionSet_4743_: *mut crate::leanh::LeanObject,
    mut v_a_4744_: *mut crate::leanh::LeanObject,
    mut v_a_4745_: *mut crate::leanh::LeanObject,
    mut v_a_4746_: *mut crate::leanh::LeanObject,
    mut v_a_4747_: *mut crate::leanh::LeanObject,
    mut v_a_4748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_4749_: u8 = 0;
    let mut v_res_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_4749_ = (crate::leanh::lean_unbox(v_kind_4742_) as u8);
    v_res_4750_ = l_Lean_Meta_findSplit_x3f(
        v_e_4741_,
        v_kind_boxed_4749_,
        v_exceptionSet_4743_,
        v_a_4744_,
        v_a_4745_,
        v_a_4746_,
        v_a_4747_,
    );
    crate::leanh::lean_dec(v_a_4747_);
    crate::leanh::lean_dec_ref(v_a_4746_);
    crate::leanh::lean_dec(v_a_4745_);
    crate::leanh::lean_dec_ref(v_a_4744_);
    return v_res_4750_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4751_ = crate::leanh::lean_box(0);
    v___x_4752_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_4753_ = lean_mk_array(v___x_4752_, v___x_4751_);
    return v___x_4753_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4754_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0_once
        ),
        _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__0,
    );
    v___x_4755_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4756_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4756_, 0, v___x_4755_);
    crate::leanh::lean_ctor_set(v___x_4756_, 1, v___x_4754_);
    return v___x_4756_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(
    mut v_e_4757_: *mut crate::leanh::LeanObject,
    mut v_a_4758_: *mut crate::leanh::LeanObject,
    mut v_a_4759_: *mut crate::leanh::LeanObject,
    mut v_a_4760_: *mut crate::leanh::LeanObject,
    mut v_a_4761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4763_: u8 = 0;
    let mut v___x_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4769_: u8 = 0;
    let mut v_val_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4773_: u8 = 0;
    let mut v___x_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4785_: u8 = 0;
    let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4790_: u8 = 0;
    let mut v_a_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4794_: u8 = 0;
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4798_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4763_ = 0;
                v___x_4764_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1_once), _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___closed__1);
                v___x_4765_ = l_Lean_Meta_findSplit_x3f(
                    v_e_4757_,
                    v___x_4763_,
                    v___x_4764_,
                    v_a_4758_,
                    v_a_4759_,
                    v_a_4760_,
                    v_a_4761_,
                );
                if crate::leanh::lean_obj_tag(v___x_4765_) == 0 {
                    v_a_4766_ = crate::leanh::lean_ctor_get(v___x_4765_, 0);
                    v_isSharedCheck_4790_ = (!crate::leanh::lean_is_exclusive(v___x_4765_)) as u8;
                    if v_isSharedCheck_4790_ == 0 {
                        v___x_4768_ = v___x_4765_;
                        v_isShared_4769_ = v_isSharedCheck_4790_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4766_);
                        crate::leanh::lean_dec(v___x_4765_);
                        v___x_4768_ = crate::leanh::lean_box(0);
                        v_isShared_4769_ = v_isSharedCheck_4790_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4791_ = crate::leanh::lean_ctor_get(v___x_4765_, 0);
                    v_isSharedCheck_4798_ = (!crate::leanh::lean_is_exclusive(v___x_4765_)) as u8;
                    if v_isSharedCheck_4798_ == 0 {
                        v___x_4793_ = v___x_4765_;
                        v_isShared_4794_ = v_isSharedCheck_4798_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4791_);
                        crate::leanh::lean_dec(v___x_4765_);
                        v___x_4793_ = crate::leanh::lean_box(0);
                        v_isShared_4794_ = v_isSharedCheck_4798_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4766_) == 1 {
                    v_val_4770_ = crate::leanh::lean_ctor_get(v_a_4766_, 0);
                    v_isSharedCheck_4785_ = (!crate::leanh::lean_is_exclusive(v_a_4766_)) as u8;
                    if v_isSharedCheck_4785_ == 0 {
                        v___x_4772_ = v_a_4766_;
                        v_isShared_4773_ = v_isSharedCheck_4785_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4770_);
                        crate::leanh::lean_dec(v_a_4766_);
                        v___x_4772_ = crate::leanh::lean_box(0);
                        v_isShared_4773_ = v_isSharedCheck_4785_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4766_);
                    v___x_4786_ = crate::leanh::lean_box(0);
                    if v_isShared_4769_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4768_, 0, v___x_4786_);
                        v___x_4788_ = v___x_4768_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4789_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4789_, 0, v___x_4786_);
                        v___x_4788_ = v_reuseFailAlloc_4789_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4774_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_4775_ = l_Lean_Expr_getRevArg_x21(v_val_4770_, v___x_4774_);
                v___x_4776_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_4777_ = l_Lean_Expr_getRevArg_x21(v_val_4770_, v___x_4776_);
                crate::leanh::lean_dec(v_val_4770_);
                v___x_4778_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4778_, 0, v___x_4775_);
                crate::leanh::lean_ctor_set(v___x_4778_, 1, v___x_4777_);
                if v_isShared_4773_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4772_, 0, v___x_4778_);
                    v___x_4780_ = v___x_4772_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4784_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4784_, 0, v___x_4778_);
                    v___x_4780_ = v_reuseFailAlloc_4784_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4769_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4768_, 0, v___x_4780_);
                    v___x_4782_ = v___x_4768_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4783_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4783_, 0, v___x_4780_);
                    v___x_4782_ = v_reuseFailAlloc_4783_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4782_;
            }
            5 => {
                return v___x_4788_;
            }
            6 => {
                if v_isShared_4794_ == 0 {
                    v___x_4796_ = v___x_4793_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4797_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4797_, 0, v_a_4791_);
                    v___x_4796_ = v_reuseFailAlloc_4797_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4796_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f___boxed(
    mut v_e_4799_: *mut crate::leanh::LeanObject,
    mut v_a_4800_: *mut crate::leanh::LeanObject,
    mut v_a_4801_: *mut crate::leanh::LeanObject,
    mut v_a_4802_: *mut crate::leanh::LeanObject,
    mut v_a_4803_: *mut crate::leanh::LeanObject,
    mut v_a_4804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4805_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(
        v_e_4799_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_,
    );
    crate::leanh::lean_dec(v_a_4803_);
    crate::leanh::lean_dec_ref(v_a_4802_);
    crate::leanh::lean_dec(v_a_4801_);
    crate::leanh::lean_dec_ref(v_a_4800_);
    return v_res_4805_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(
    mut v_name_4806_: *mut crate::leanh::LeanObject,
    mut v_decl_4807_: *mut crate::leanh::LeanObject,
    mut v_ref_4808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: u8 = 0;
    let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4819_: u8 = 0;
    let mut v___x_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4824_: u8 = 0;
    let mut v_unused_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4829_: u8 = 0;
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4833_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_4810_ = crate::leanh::lean_ctor_get(v_decl_4807_, 0);
                v_descr_4811_ = crate::leanh::lean_ctor_get(v_decl_4807_, 1);
                v_deprecation_x3f_4812_ = crate::leanh::lean_ctor_get(v_decl_4807_, 2);
                v___x_4813_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_4814_ = (crate::leanh::lean_unbox(v_defValue_4810_) as u8);
                crate::leanh::lean_ctor_set_uint8(v___x_4813_, 0 as u32, v___x_4814_);
                crate::leanh::lean_inc(v_deprecation_x3f_4812_);
                crate::leanh::lean_inc_ref(v_descr_4811_);
                crate::leanh::lean_inc_n(v_name_4806_, 2);
                v___x_4815_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4815_, 0, v_name_4806_);
                crate::leanh::lean_ctor_set(v___x_4815_, 1, v_ref_4808_);
                crate::leanh::lean_ctor_set(v___x_4815_, 2, v___x_4813_);
                crate::leanh::lean_ctor_set(v___x_4815_, 3, v_descr_4811_);
                crate::leanh::lean_ctor_set(v___x_4815_, 4, v_deprecation_x3f_4812_);
                v___x_4816_ = lean_register_option(v_name_4806_, v___x_4815_);
                if crate::leanh::lean_obj_tag(v___x_4816_) == 0 {
                    v_isSharedCheck_4824_ = (!crate::leanh::lean_is_exclusive(v___x_4816_)) as u8;
                    if v_isSharedCheck_4824_ == 0 {
                        v_unused_4825_ = crate::leanh::lean_ctor_get(v___x_4816_, 0);
                        crate::leanh::lean_dec(v_unused_4825_);
                        v___x_4818_ = v___x_4816_;
                        v_isShared_4819_ = v_isSharedCheck_4824_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4816_);
                        v___x_4818_ = crate::leanh::lean_box(0);
                        v_isShared_4819_ = v_isSharedCheck_4824_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_4806_);
                    v_a_4826_ = crate::leanh::lean_ctor_get(v___x_4816_, 0);
                    v_isSharedCheck_4833_ = (!crate::leanh::lean_is_exclusive(v___x_4816_)) as u8;
                    if v_isSharedCheck_4833_ == 0 {
                        v___x_4828_ = v___x_4816_;
                        v_isShared_4829_ = v_isSharedCheck_4833_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4826_);
                        crate::leanh::lean_dec(v___x_4816_);
                        v___x_4828_ = crate::leanh::lean_box(0);
                        v_isShared_4829_ = v_isSharedCheck_4833_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_4810_);
                v___x_4820_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4820_, 0, v_name_4806_);
                crate::leanh::lean_ctor_set(v___x_4820_, 1, v_defValue_4810_);
                if v_isShared_4819_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4818_, 0, v___x_4820_);
                    v___x_4822_ = v___x_4818_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4823_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4823_, 0, v___x_4820_);
                    v___x_4822_ = v_reuseFailAlloc_4823_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4822_;
            }
            3 => {
                if v_isShared_4829_ == 0 {
                    v___x_4831_ = v___x_4828_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4832_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4832_, 0, v_a_4826_);
                    v___x_4831_ = v_reuseFailAlloc_4832_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4831_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_4834_: *mut crate::leanh::LeanObject,
    mut v_decl_4835_: *mut crate::leanh::LeanObject,
    mut v_ref_4836_: *mut crate::leanh::LeanObject,
    mut v_a_4837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4838_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(v_name_4834_, v_decl_4835_, v_ref_4836_);
    crate::leanh::lean_dec_ref(v_decl_4835_);
    return v_res_4838_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4857_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_;
    v___x_4858_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_;
    v___x_4859_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_;
    v___x_4860_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4__spec__0(v___x_4857_, v___x_4858_, v___x_4859_);
    return v___x_4860_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4____boxed(
    mut v_a_4861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4862_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_();
    return v_res_4862_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4863_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4863_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4864_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__0);
    v___x_4865_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4865_, 0, v___x_4864_);
    return v___x_4865_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0(
    mut v_00_u03b2_4866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4867_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0___closed__1);
    return v___x_4867_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4868_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4868_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4869_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__0);
    v___x_4870_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4870_, 0, v___x_4869_);
    return v___x_4870_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1(
    mut v_00_u03b2_4871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4872_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1___closed__1);
    return v___x_4872_;
}
pub unsafe fn _init_l_Lean_Meta_SplitIf_getSimpContext___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4873_ = l_Lean_Meta_DiscrTree_empty(crate::leanh::lean_box(0));
    return v___x_4873_;
}
pub unsafe fn _init_l_Lean_Meta_SplitIf_getSimpContext___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4874_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__0(
        crate::leanh::lean_box(0),
    );
    return v___x_4874_;
}
pub unsafe fn _init_l_Lean_Meta_SplitIf_getSimpContext___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4875_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_SplitIf_getSimpContext_spec__1(
        crate::leanh::lean_box(0),
    );
    return v___x_4875_;
}
pub unsafe fn _init_l_Lean_Meta_SplitIf_getSimpContext___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4876_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4876_;
}
pub unsafe fn _init_l_Lean_Meta_SplitIf_getSimpContext___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4877_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_SplitIf_getSimpContext___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_SplitIf_getSimpContext___closed__3_once),
        _init_l_Lean_Meta_SplitIf_getSimpContext___closed__3,
    );
    v___x_4878_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4878_, 0, v___x_4877_);
    return v___x_4878_;
}
pub unsafe fn _init_l_Lean_Meta_SplitIf_getSimpContext___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4879_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_SplitIf_getSimpContext___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_SplitIf_getSimpContext___closed__4_once),
        _init_l_Lean_Meta_SplitIf_getSimpContext___closed__4,
    );
    v___x_4880_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_SplitIf_getSimpContext___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_SplitIf_getSimpContext___closed__2_once),
        _init_l_Lean_Meta_SplitIf_getSimpContext___closed__2,
    );
    v___x_4881_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_SplitIf_getSimpContext___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_SplitIf_getSimpContext___closed__1_once),
        _init_l_Lean_Meta_SplitIf_getSimpContext___closed__1,
    );
    v___x_4882_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_SplitIf_getSimpContext___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_SplitIf_getSimpContext___closed__0_once),
        _init_l_Lean_Meta_SplitIf_getSimpContext___closed__0,
    );
    v_s_4883_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v_s_4883_, 0, v___x_4882_);
    crate::leanh::lean_ctor_set(v_s_4883_, 1, v___x_4882_);
    crate::leanh::lean_ctor_set(v_s_4883_, 2, v___x_4881_);
    crate::leanh::lean_ctor_set(v_s_4883_, 3, v___x_4880_);
    crate::leanh::lean_ctor_set(v_s_4883_, 4, v___x_4881_);
    crate::leanh::lean_ctor_set(v_s_4883_, 5, v___x_4879_);
    return v_s_4883_;
}
pub unsafe fn l_Lean_Meta_SplitIf_getSimpContext(
    mut v_a_4896_: *mut crate::leanh::LeanObject,
    mut v_a_4897_: *mut crate::leanh::LeanObject,
    mut v_a_4898_: *mut crate::leanh::LeanObject,
    mut v_a_4899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: u8 = 0;
    let mut v___x_4904_: u8 = 0;
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxSteps_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxDischargeDepth_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextual_4922_: u8 = 0;
    let mut v_memoize_4923_: u8 = 0;
    let mut v_singlePass_4924_: u8 = 0;
    let mut v_zeta_4925_: u8 = 0;
    let mut v_beta_4926_: u8 = 0;
    let mut v_eta_4927_: u8 = 0;
    let mut v_etaStruct_4928_: u8 = 0;
    let mut v_iota_4929_: u8 = 0;
    let mut v_proj_4930_: u8 = 0;
    let mut v_decide_4931_: u8 = 0;
    let mut v_arith_4932_: u8 = 0;
    let mut v_autoUnfold_4933_: u8 = 0;
    let mut v_failIfUnchanged_4934_: u8 = 0;
    let mut v_ground_4935_: u8 = 0;
    let mut v_unfoldPartialApp_4936_: u8 = 0;
    let mut v_zetaDelta_4937_: u8 = 0;
    let mut v_index_4938_: u8 = 0;
    let mut v_implicitDefEqProofs_4939_: u8 = 0;
    let mut v_zetaUnused_4940_: u8 = 0;
    let mut v_catchRuntime_4941_: u8 = 0;
    let mut v_zetaHave_4942_: u8 = 0;
    let mut v_congrConsts_4943_: u8 = 0;
    let mut v_bitVecOfNat_4944_: u8 = 0;
    let mut v_warnExponents_4945_: u8 = 0;
    let mut v_suggestions_4946_: u8 = 0;
    let mut v_maxSuggestions_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_locals_4948_: u8 = 0;
    let mut v_instances_4949_: u8 = 0;
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4959_: u8 = 0;
    let mut v___x_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4963_: u8 = 0;
    let mut v_a_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4967_: u8 = 0;
    let mut v___x_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4971_: u8 = 0;
    let mut v_a_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4975_: u8 = 0;
    let mut v___x_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4979_: u8 = 0;
    let mut v_a_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4983_: u8 = 0;
    let mut v___x_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4987_: u8 = 0;
    let mut v_a_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4991_: u8 = 0;
    let mut v___x_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4995_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_4901_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_SplitIf_getSimpContext___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_Meta_SplitIf_getSimpContext___closed__5_once),
                    _init_l_Lean_Meta_SplitIf_getSimpContext___closed__5,
                );
                v___x_4902_ = l_Lean_Meta_SplitIf_getSimpContext___closed__7;
                v___x_4903_ = 1;
                v___x_4904_ = 0;
                v___x_4905_ = crate::leanh::lean_unsigned_to_nat(1000);
                v___x_4906_ = l_Lean_Meta_SimpTheorems_addConst(
                    v_s_4901_,
                    v___x_4902_,
                    v___x_4903_,
                    v___x_4904_,
                    v___x_4905_,
                    v_a_4896_,
                    v_a_4897_,
                    v_a_4898_,
                    v_a_4899_,
                );
                if crate::leanh::lean_obj_tag(v___x_4906_) == 0 {
                    v_a_4907_ = crate::leanh::lean_ctor_get(v___x_4906_, 0);
                    crate::leanh::lean_inc(v_a_4907_);
                    crate::leanh::lean_dec_ref_known(v___x_4906_, 1);
                    v___x_4908_ = l_Lean_Meta_SplitIf_getSimpContext___closed__9;
                    v___x_4909_ = l_Lean_Meta_SimpTheorems_addConst(
                        v_a_4907_,
                        v___x_4908_,
                        v___x_4903_,
                        v___x_4904_,
                        v___x_4905_,
                        v_a_4896_,
                        v_a_4897_,
                        v_a_4898_,
                        v_a_4899_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4909_) == 0 {
                        v_a_4910_ = crate::leanh::lean_ctor_get(v___x_4909_, 0);
                        crate::leanh::lean_inc(v_a_4910_);
                        crate::leanh::lean_dec_ref_known(v___x_4909_, 1);
                        v___x_4911_ = l_Lean_Meta_SplitIf_getSimpContext___closed__11;
                        v___x_4912_ = l_Lean_Meta_SimpTheorems_addConst(
                            v_a_4910_,
                            v___x_4911_,
                            v___x_4903_,
                            v___x_4904_,
                            v___x_4905_,
                            v_a_4896_,
                            v_a_4897_,
                            v_a_4898_,
                            v_a_4899_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4912_) == 0 {
                            v_a_4913_ = crate::leanh::lean_ctor_get(v___x_4912_, 0);
                            crate::leanh::lean_inc(v_a_4913_);
                            crate::leanh::lean_dec_ref_known(v___x_4912_, 1);
                            v___x_4914_ = l_Lean_Meta_SplitIf_getSimpContext___closed__13;
                            v___x_4915_ = l_Lean_Meta_SimpTheorems_addConst(
                                v_a_4913_,
                                v___x_4914_,
                                v___x_4903_,
                                v___x_4904_,
                                v___x_4905_,
                                v_a_4896_,
                                v_a_4897_,
                                v_a_4898_,
                                v_a_4899_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4915_) == 0 {
                                v_a_4916_ = crate::leanh::lean_ctor_get(v___x_4915_, 0);
                                crate::leanh::lean_inc(v_a_4916_);
                                crate::leanh::lean_dec_ref_known(v___x_4915_, 1);
                                v___x_4917_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_4899_);
                                if crate::leanh::lean_obj_tag(v___x_4917_) == 0 {
                                    v_a_4918_ = crate::leanh::lean_ctor_get(v___x_4917_, 0);
                                    crate::leanh::lean_inc(v_a_4918_);
                                    crate::leanh::lean_dec_ref_known(v___x_4917_, 1);
                                    v___x_4919_ = l_Lean_Meta_Simp_neutralConfig;
                                    v_maxSteps_4920_ = crate::leanh::lean_ctor_get(v___x_4919_, 0);
                                    v_maxDischargeDepth_4921_ =
                                        crate::leanh::lean_ctor_get(v___x_4919_, 1);
                                    v_contextual_4922_ = crate::leanh::lean_ctor_get_uint8(
                                        v___x_4919_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3)
                                            as u32,
                                    );
                                    v_memoize_4923_ = crate::leanh::lean_ctor_get_uint8(
                                        v___x_4919_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 1) as u32,
                                    );
                                    v_singlePass_4924_ = crate::leanh::lean_ctor_get_uint8(
                                        v___x_4919_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 2) as u32,
                                    );
                                    v_zeta_4925_ = crate::leanh::lean_ctor_get_uint8(
                                        v___x_4919_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 3) as u32,
                                    );
                                    v_beta_4926_ = crate::leanh::lean_ctor_get_uint8(
                                        v___x_4919_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 4) as u32,
                                    );
                                    v_eta_4927_ = crate::leanh::lean_ctor_get_uint8(
                                        v___x_4919_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 5) as u32,
                                    );
                                    v_etaStruct_4928_ = crate::leanh::lean_ctor_get_uint8(
                                        v___x_4919_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 6) as u32,
                                    );
                                    v_iota_4929_ = crate::leanh::lean_ctor_get_uint8(
                                        v___x_4919_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 7) as u32,
                                    );
                                    v_proj_4930_ = crate::leanh::lean_ctor_get_uint8(
                                        v___x_4919_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 8) as u32,
                                    );
                                    v_decide_4931_ = crate::leanh::lean_ctor_get_uint8(
                                        v___x_4919_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 9) as u32,
                                    );
                                    v_arith_4932_ = crate::leanh::lean_ctor_get_uint8(
                                        v___x_4919_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 10) as u32,
                                    );
                                    v_autoUnfold_4933_ = crate::leanh::lean_ctor_get_uint8(
                                        v___x_4919_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 11) as u32,
                                    );
                                    v_failIfUnchanged_4934_ = crate::leanh::lean_ctor_get_uint8(
                                        v___x_4919_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 13) as u32,
                                    );
                                    v_ground_4935_ = crate::leanh::lean_ctor_get_uint8(
                                        v___x_4919_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 14) as u32,
                                    );
                                    v_unfoldPartialApp_4936_ = crate::leanh::lean_ctor_get_uint8(
                                        v___x_4919_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 15) as u32,
                                    );
                                    v_zetaDelta_4937_ = crate::leanh::lean_ctor_get_uint8(
                                        v___x_4919_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 16) as u32,
                                    );
                                    v_index_4938_ = crate::leanh::lean_ctor_get_uint8(
                                        v___x_4919_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 17) as u32,
                                    );
                                    v_implicitDefEqProofs_4939_ = crate::leanh::lean_ctor_get_uint8(
                                        v___x_4919_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 18) as u32,
                                    );
                                    v_zetaUnused_4940_ = crate::leanh::lean_ctor_get_uint8(
                                        v___x_4919_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 19) as u32,
                                    );
                                    v_catchRuntime_4941_ = crate::leanh::lean_ctor_get_uint8(
                                        v___x_4919_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 20) as u32,
                                    );
                                    v_zetaHave_4942_ = crate::leanh::lean_ctor_get_uint8(
                                        v___x_4919_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 21) as u32,
                                    );
                                    v_congrConsts_4943_ = crate::leanh::lean_ctor_get_uint8(
                                        v___x_4919_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 23) as u32,
                                    );
                                    v_bitVecOfNat_4944_ = crate::leanh::lean_ctor_get_uint8(
                                        v___x_4919_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 24) as u32,
                                    );
                                    v_warnExponents_4945_ = crate::leanh::lean_ctor_get_uint8(
                                        v___x_4919_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 25) as u32,
                                    );
                                    v_suggestions_4946_ = crate::leanh::lean_ctor_get_uint8(
                                        v___x_4919_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 26) as u32,
                                    );
                                    v_maxSuggestions_4947_ =
                                        crate::leanh::lean_ctor_get(v___x_4919_, 2);
                                    v_locals_4948_ = crate::leanh::lean_ctor_get_uint8(
                                        v___x_4919_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 27) as u32,
                                    );
                                    v_instances_4949_ = crate::leanh::lean_ctor_get_uint8(
                                        v___x_4919_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 28) as u32,
                                    );
                                    crate::leanh::lean_inc(v_maxSuggestions_4947_);
                                    crate::leanh::lean_inc(v_maxDischargeDepth_4921_);
                                    crate::leanh::lean_inc(v_maxSteps_4920_);
                                    v___x_4950_ = crate::leanh::lean_alloc_ctor(0, 3, (29) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4950_, 0, v_maxSteps_4920_);
                                    crate::leanh::lean_ctor_set(
                                        v___x_4950_,
                                        1,
                                        v_maxDischargeDepth_4921_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v___x_4950_,
                                        2,
                                        v_maxSuggestions_4947_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_4950_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3)
                                            as u32,
                                        v_contextual_4922_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_4950_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 1) as u32,
                                        v_memoize_4923_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_4950_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 2) as u32,
                                        v_singlePass_4924_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_4950_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 3) as u32,
                                        v_zeta_4925_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_4950_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 4) as u32,
                                        v_beta_4926_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_4950_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 5) as u32,
                                        v_eta_4927_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_4950_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 6) as u32,
                                        v_etaStruct_4928_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_4950_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 7) as u32,
                                        v_iota_4929_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_4950_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 8) as u32,
                                        v_proj_4930_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_4950_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 9) as u32,
                                        v_decide_4931_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_4950_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 10) as u32,
                                        v_arith_4932_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_4950_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 11) as u32,
                                        v_autoUnfold_4933_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_4950_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 12) as u32,
                                        v___x_4904_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_4950_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 13) as u32,
                                        v_failIfUnchanged_4934_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_4950_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 14) as u32,
                                        v_ground_4935_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_4950_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 15) as u32,
                                        v_unfoldPartialApp_4936_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_4950_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 16) as u32,
                                        v_zetaDelta_4937_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_4950_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 17) as u32,
                                        v_index_4938_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_4950_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 18) as u32,
                                        v_implicitDefEqProofs_4939_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_4950_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 19) as u32,
                                        v_zetaUnused_4940_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_4950_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 20) as u32,
                                        v_catchRuntime_4941_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_4950_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 21) as u32,
                                        v_zetaHave_4942_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_4950_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 22) as u32,
                                        v___x_4903_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_4950_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 23) as u32,
                                        v_congrConsts_4943_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_4950_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 24) as u32,
                                        v_bitVecOfNat_4944_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_4950_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 25) as u32,
                                        v_warnExponents_4945_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_4950_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 26) as u32,
                                        v_suggestions_4946_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_4950_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 27) as u32,
                                        v_locals_4948_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_4950_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 28) as u32,
                                        v_instances_4949_,
                                    );
                                    v___x_4951_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_4952_ = lean_mk_empty_array_with_capacity(v___x_4951_);
                                    v___x_4953_ = lean_array_push(v___x_4952_, v_a_4916_);
                                    v___x_4954_ = l_Lean_Options_empty;
                                    v___x_4955_ = l_Lean_Meta_Simp_mkContext___redArg(
                                        v___x_4950_,
                                        v___x_4953_,
                                        v_a_4918_,
                                        v___x_4954_,
                                        v_a_4896_,
                                        v_a_4898_,
                                        v_a_4899_,
                                    );
                                    return v___x_4955_;
                                } else {
                                    crate::leanh::lean_dec(v_a_4916_);
                                    v_a_4956_ = crate::leanh::lean_ctor_get(v___x_4917_, 0);
                                    v_isSharedCheck_4963_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4917_)) as u8;
                                    if v_isSharedCheck_4963_ == 0 {
                                        v___x_4958_ = v___x_4917_;
                                        v_isShared_4959_ = v_isSharedCheck_4963_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4956_);
                                        crate::leanh::lean_dec(v___x_4917_);
                                        v___x_4958_ = crate::leanh::lean_box(0);
                                        v_isShared_4959_ = v_isSharedCheck_4963_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                v_a_4964_ = crate::leanh::lean_ctor_get(v___x_4915_, 0);
                                v_isSharedCheck_4971_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4915_)) as u8;
                                if v_isSharedCheck_4971_ == 0 {
                                    v___x_4966_ = v___x_4915_;
                                    v_isShared_4967_ = v_isSharedCheck_4971_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4964_);
                                    crate::leanh::lean_dec(v___x_4915_);
                                    v___x_4966_ = crate::leanh::lean_box(0);
                                    v_isShared_4967_ = v_isSharedCheck_4971_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_a_4972_ = crate::leanh::lean_ctor_get(v___x_4912_, 0);
                            v_isSharedCheck_4979_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4912_)) as u8;
                            if v_isSharedCheck_4979_ == 0 {
                                v___x_4974_ = v___x_4912_;
                                v_isShared_4975_ = v_isSharedCheck_4979_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4972_);
                                crate::leanh::lean_dec(v___x_4912_);
                                v___x_4974_ = crate::leanh::lean_box(0);
                                v_isShared_4975_ = v_isSharedCheck_4979_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        v_a_4980_ = crate::leanh::lean_ctor_get(v___x_4909_, 0);
                        v_isSharedCheck_4987_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4909_)) as u8;
                        if v_isSharedCheck_4987_ == 0 {
                            v___x_4982_ = v___x_4909_;
                            v_isShared_4983_ = v_isSharedCheck_4987_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4980_);
                            crate::leanh::lean_dec(v___x_4909_);
                            v___x_4982_ = crate::leanh::lean_box(0);
                            v_isShared_4983_ = v_isSharedCheck_4987_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v_a_4988_ = crate::leanh::lean_ctor_get(v___x_4906_, 0);
                    v_isSharedCheck_4995_ = (!crate::leanh::lean_is_exclusive(v___x_4906_)) as u8;
                    if v_isSharedCheck_4995_ == 0 {
                        v___x_4990_ = v___x_4906_;
                        v_isShared_4991_ = v_isSharedCheck_4995_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4988_);
                        crate::leanh::lean_dec(v___x_4906_);
                        v___x_4990_ = crate::leanh::lean_box(0);
                        v_isShared_4991_ = v_isSharedCheck_4995_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4959_ == 0 {
                    v___x_4961_ = v___x_4958_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4962_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4962_, 0, v_a_4956_);
                    v___x_4961_ = v_reuseFailAlloc_4962_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4961_;
            }
            3 => {
                if v_isShared_4967_ == 0 {
                    v___x_4969_ = v___x_4966_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4970_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4970_, 0, v_a_4964_);
                    v___x_4969_ = v_reuseFailAlloc_4970_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4969_;
            }
            5 => {
                if v_isShared_4975_ == 0 {
                    v___x_4977_ = v___x_4974_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4978_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4978_, 0, v_a_4972_);
                    v___x_4977_ = v_reuseFailAlloc_4978_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4977_;
            }
            7 => {
                if v_isShared_4983_ == 0 {
                    v___x_4985_ = v___x_4982_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4986_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4986_, 0, v_a_4980_);
                    v___x_4985_ = v_reuseFailAlloc_4986_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4985_;
            }
            9 => {
                if v_isShared_4991_ == 0 {
                    v___x_4993_ = v___x_4990_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4994_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4994_, 0, v_a_4988_);
                    v___x_4993_ = v_reuseFailAlloc_4994_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4993_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_SplitIf_getSimpContext___boxed(
    mut v_a_4996_: *mut crate::leanh::LeanObject,
    mut v_a_4997_: *mut crate::leanh::LeanObject,
    mut v_a_4998_: *mut crate::leanh::LeanObject,
    mut v_a_4999_: *mut crate::leanh::LeanObject,
    mut v_a_5000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5001_ = l_Lean_Meta_SplitIf_getSimpContext(v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_);
    crate::leanh::lean_dec(v_a_4999_);
    crate::leanh::lean_dec_ref(v_a_4998_);
    crate::leanh::lean_dec(v_a_4997_);
    crate::leanh::lean_dec_ref(v_a_4996_);
    return v_res_5001_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(
    mut v_a_5004_: *mut crate::leanh::LeanObject,
    mut v_a_5005_: *mut crate::leanh::LeanObject,
    mut v_a_5006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxSteps_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxDischargeDepth_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextual_5013_: u8 = 0;
    let mut v_memoize_5014_: u8 = 0;
    let mut v_singlePass_5015_: u8 = 0;
    let mut v_zeta_5016_: u8 = 0;
    let mut v_beta_5017_: u8 = 0;
    let mut v_eta_5018_: u8 = 0;
    let mut v_etaStruct_5019_: u8 = 0;
    let mut v_iota_5020_: u8 = 0;
    let mut v_proj_5021_: u8 = 0;
    let mut v_decide_5022_: u8 = 0;
    let mut v_arith_5023_: u8 = 0;
    let mut v_autoUnfold_5024_: u8 = 0;
    let mut v_failIfUnchanged_5025_: u8 = 0;
    let mut v_ground_5026_: u8 = 0;
    let mut v_unfoldPartialApp_5027_: u8 = 0;
    let mut v_zetaDelta_5028_: u8 = 0;
    let mut v_index_5029_: u8 = 0;
    let mut v_implicitDefEqProofs_5030_: u8 = 0;
    let mut v_zetaUnused_5031_: u8 = 0;
    let mut v_catchRuntime_5032_: u8 = 0;
    let mut v_zetaHave_5033_: u8 = 0;
    let mut v_congrConsts_5034_: u8 = 0;
    let mut v_bitVecOfNat_5035_: u8 = 0;
    let mut v_warnExponents_5036_: u8 = 0;
    let mut v_suggestions_5037_: u8 = 0;
    let mut v_maxSuggestions_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_locals_5039_: u8 = 0;
    let mut v_instances_5040_: u8 = 0;
    let mut v___x_5041_: u8 = 0;
    let mut v___x_5042_: u8 = 0;
    let mut v___x_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5050_: u8 = 0;
    let mut v___x_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5054_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5008_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_5006_);
                if crate::leanh::lean_obj_tag(v___x_5008_) == 0 {
                    v_a_5009_ = crate::leanh::lean_ctor_get(v___x_5008_, 0);
                    crate::leanh::lean_inc(v_a_5009_);
                    crate::leanh::lean_dec_ref_known(v___x_5008_, 1);
                    v___x_5010_ = l_Lean_Meta_Simp_neutralConfig;
                    v_maxSteps_5011_ = crate::leanh::lean_ctor_get(v___x_5010_, 0);
                    v_maxDischargeDepth_5012_ = crate::leanh::lean_ctor_get(v___x_5010_, 1);
                    v_contextual_5013_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_5010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v_memoize_5014_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_5010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    );
                    v_singlePass_5015_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_5010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 2) as u32,
                    );
                    v_zeta_5016_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_5010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 3) as u32,
                    );
                    v_beta_5017_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_5010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 4) as u32,
                    );
                    v_eta_5018_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_5010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 5) as u32,
                    );
                    v_etaStruct_5019_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_5010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 6) as u32,
                    );
                    v_iota_5020_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_5010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 7) as u32,
                    );
                    v_proj_5021_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_5010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    v_decide_5022_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_5010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 9) as u32,
                    );
                    v_arith_5023_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_5010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 10) as u32,
                    );
                    v_autoUnfold_5024_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_5010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 11) as u32,
                    );
                    v_failIfUnchanged_5025_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_5010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 13) as u32,
                    );
                    v_ground_5026_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_5010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 14) as u32,
                    );
                    v_unfoldPartialApp_5027_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_5010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 15) as u32,
                    );
                    v_zetaDelta_5028_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_5010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    );
                    v_index_5029_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_5010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 17) as u32,
                    );
                    v_implicitDefEqProofs_5030_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_5010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 18) as u32,
                    );
                    v_zetaUnused_5031_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_5010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 19) as u32,
                    );
                    v_catchRuntime_5032_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_5010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 20) as u32,
                    );
                    v_zetaHave_5033_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_5010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 21) as u32,
                    );
                    v_congrConsts_5034_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_5010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 23) as u32,
                    );
                    v_bitVecOfNat_5035_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_5010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 24) as u32,
                    );
                    v_warnExponents_5036_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_5010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 25) as u32,
                    );
                    v_suggestions_5037_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_5010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 26) as u32,
                    );
                    v_maxSuggestions_5038_ = crate::leanh::lean_ctor_get(v___x_5010_, 2);
                    v_locals_5039_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_5010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 27) as u32,
                    );
                    v_instances_5040_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_5010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 28) as u32,
                    );
                    v___x_5041_ = 0;
                    v___x_5042_ = 1;
                    crate::leanh::lean_inc(v_maxSuggestions_5038_);
                    crate::leanh::lean_inc(v_maxDischargeDepth_5012_);
                    crate::leanh::lean_inc(v_maxSteps_5011_);
                    v___x_5043_ = crate::leanh::lean_alloc_ctor(0, 3, (29) as u32);
                    crate::leanh::lean_ctor_set(v___x_5043_, 0, v_maxSteps_5011_);
                    crate::leanh::lean_ctor_set(v___x_5043_, 1, v_maxDischargeDepth_5012_);
                    crate::leanh::lean_ctor_set(v___x_5043_, 2, v_maxSuggestions_5038_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_contextual_5013_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_memoize_5014_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 2) as u32,
                        v_singlePass_5015_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 3) as u32,
                        v_zeta_5016_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 4) as u32,
                        v_beta_5017_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 5) as u32,
                        v_eta_5018_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 6) as u32,
                        v_etaStruct_5019_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 7) as u32,
                        v_iota_5020_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        v_proj_5021_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 9) as u32,
                        v_decide_5022_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 10) as u32,
                        v_arith_5023_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 11) as u32,
                        v_autoUnfold_5024_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 12) as u32,
                        v___x_5041_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 13) as u32,
                        v_failIfUnchanged_5025_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 14) as u32,
                        v_ground_5026_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 15) as u32,
                        v_unfoldPartialApp_5027_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                        v_zetaDelta_5028_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 17) as u32,
                        v_index_5029_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 18) as u32,
                        v_implicitDefEqProofs_5030_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 19) as u32,
                        v_zetaUnused_5031_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 20) as u32,
                        v_catchRuntime_5032_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 21) as u32,
                        v_zetaHave_5033_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 22) as u32,
                        v___x_5042_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 23) as u32,
                        v_congrConsts_5034_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 24) as u32,
                        v_bitVecOfNat_5035_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 25) as u32,
                        v_warnExponents_5036_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 26) as u32,
                        v_suggestions_5037_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 27) as u32,
                        v_locals_5039_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 28) as u32,
                        v_instances_5040_,
                    );
                    v___x_5044_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg___closed__0;
                    v___x_5045_ = l_Lean_Options_empty;
                    v___x_5046_ = l_Lean_Meta_Simp_mkContext___redArg(
                        v___x_5043_,
                        v___x_5044_,
                        v_a_5009_,
                        v___x_5045_,
                        v_a_5004_,
                        v_a_5005_,
                        v_a_5006_,
                    );
                    return v___x_5046_;
                } else {
                    v_a_5047_ = crate::leanh::lean_ctor_get(v___x_5008_, 0);
                    v_isSharedCheck_5054_ = (!crate::leanh::lean_is_exclusive(v___x_5008_)) as u8;
                    if v_isSharedCheck_5054_ == 0 {
                        v___x_5049_ = v___x_5008_;
                        v_isShared_5050_ = v_isSharedCheck_5054_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5047_);
                        crate::leanh::lean_dec(v___x_5008_);
                        v___x_5049_ = crate::leanh::lean_box(0);
                        v_isShared_5050_ = v_isSharedCheck_5054_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5050_ == 0 {
                    v___x_5052_ = v___x_5049_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5053_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5053_, 0, v_a_5047_);
                    v___x_5052_ = v_reuseFailAlloc_5053_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5052_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg___boxed(
    mut v_a_5055_: *mut crate::leanh::LeanObject,
    mut v_a_5056_: *mut crate::leanh::LeanObject,
    mut v_a_5057_: *mut crate::leanh::LeanObject,
    mut v_a_5058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5059_ =
        l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(
            v_a_5055_, v_a_5056_, v_a_5057_,
        );
    crate::leanh::lean_dec(v_a_5057_);
    crate::leanh::lean_dec_ref(v_a_5056_);
    crate::leanh::lean_dec_ref(v_a_5055_);
    return v_res_5059_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27(
    mut v_a_5060_: *mut crate::leanh::LeanObject,
    mut v_a_5061_: *mut crate::leanh::LeanObject,
    mut v_a_5062_: *mut crate::leanh::LeanObject,
    mut v_a_5063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5065_ =
        l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(
            v_a_5060_, v_a_5062_, v_a_5063_,
        );
    return v___x_5065_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___boxed(
    mut v_a_5066_: *mut crate::leanh::LeanObject,
    mut v_a_5067_: *mut crate::leanh::LeanObject,
    mut v_a_5068_: *mut crate::leanh::LeanObject,
    mut v_a_5069_: *mut crate::leanh::LeanObject,
    mut v_a_5070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5071_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27(
        v_a_5066_, v_a_5067_, v_a_5068_, v_a_5069_,
    );
    crate::leanh::lean_dec(v_a_5069_);
    crate::leanh::lean_dec_ref(v_a_5068_);
    crate::leanh::lean_dec(v_a_5067_);
    crate::leanh::lean_dec_ref(v_a_5066_);
    return v_res_5071_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(
    mut v_e_5072_: *mut crate::leanh::LeanObject,
    mut v___y_5073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5075_: u8 = 0;
    let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5089_: u8 = 0;
    let mut v___x_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5095_: u8 = 0;
    let mut v_unused_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5075_ = l_Lean_Expr_hasMVar(v_e_5072_);
                if v___x_5075_ == 0 {
                    v___x_5076_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5076_, 0, v_e_5072_);
                    return v___x_5076_;
                } else {
                    v___x_5077_ = lean_st_ref_get(v___y_5073_);
                    v_mctx_5078_ = crate::leanh::lean_ctor_get(v___x_5077_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_5078_);
                    crate::leanh::lean_dec(v___x_5077_);
                    v___x_5079_ = l_Lean_instantiateMVarsCore(v_mctx_5078_, v_e_5072_);
                    v_fst_5080_ = crate::leanh::lean_ctor_get(v___x_5079_, 0);
                    crate::leanh::lean_inc(v_fst_5080_);
                    v_snd_5081_ = crate::leanh::lean_ctor_get(v___x_5079_, 1);
                    crate::leanh::lean_inc(v_snd_5081_);
                    crate::leanh::lean_dec_ref(v___x_5079_);
                    v___x_5082_ = lean_st_ref_take(v___y_5073_);
                    v_cache_5083_ = crate::leanh::lean_ctor_get(v___x_5082_, 1);
                    v_zetaDeltaFVarIds_5084_ = crate::leanh::lean_ctor_get(v___x_5082_, 2);
                    v_postponed_5085_ = crate::leanh::lean_ctor_get(v___x_5082_, 3);
                    v_diag_5086_ = crate::leanh::lean_ctor_get(v___x_5082_, 4);
                    v_isSharedCheck_5095_ = (!crate::leanh::lean_is_exclusive(v___x_5082_)) as u8;
                    if v_isSharedCheck_5095_ == 0 {
                        v_unused_5096_ = crate::leanh::lean_ctor_get(v___x_5082_, 0);
                        crate::leanh::lean_dec(v_unused_5096_);
                        v___x_5088_ = v___x_5082_;
                        v_isShared_5089_ = v_isSharedCheck_5095_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_5086_);
                        crate::leanh::lean_inc(v_postponed_5085_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_5084_);
                        crate::leanh::lean_inc(v_cache_5083_);
                        crate::leanh::lean_dec(v___x_5082_);
                        v___x_5088_ = crate::leanh::lean_box(0);
                        v_isShared_5089_ = v_isSharedCheck_5095_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5089_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5088_, 0, v_snd_5081_);
                    v___x_5091_ = v___x_5088_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5094_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5094_, 0, v_snd_5081_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5094_, 1, v_cache_5083_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5094_,
                        2,
                        v_zetaDeltaFVarIds_5084_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5094_, 3, v_postponed_5085_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5094_, 4, v_diag_5086_);
                    v___x_5091_ = v_reuseFailAlloc_5094_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5092_ = lean_st_ref_set(v___y_5073_, v___x_5091_);
                v___x_5093_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5093_, 0, v_fst_5080_);
                return v___x_5093_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg___boxed(
    mut v_e_5097_: *mut crate::leanh::LeanObject,
    mut v___y_5098_: *mut crate::leanh::LeanObject,
    mut v___y_5099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5100_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_e_5097_, v___y_5098_);
    crate::leanh::lean_dec(v___y_5098_);
    return v_res_5100_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0(
    mut v_e_5101_: *mut crate::leanh::LeanObject,
    mut v___y_5102_: *mut crate::leanh::LeanObject,
    mut v___y_5103_: *mut crate::leanh::LeanObject,
    mut v___y_5104_: *mut crate::leanh::LeanObject,
    mut v___y_5105_: *mut crate::leanh::LeanObject,
    mut v___y_5106_: *mut crate::leanh::LeanObject,
    mut v___y_5107_: *mut crate::leanh::LeanObject,
    mut v___y_5108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5110_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_e_5101_, v___y_5106_);
    return v___x_5110_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___boxed(
    mut v_e_5111_: *mut crate::leanh::LeanObject,
    mut v___y_5112_: *mut crate::leanh::LeanObject,
    mut v___y_5113_: *mut crate::leanh::LeanObject,
    mut v___y_5114_: *mut crate::leanh::LeanObject,
    mut v___y_5115_: *mut crate::leanh::LeanObject,
    mut v___y_5116_: *mut crate::leanh::LeanObject,
    mut v___y_5117_: *mut crate::leanh::LeanObject,
    mut v___y_5118_: *mut crate::leanh::LeanObject,
    mut v___y_5119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5120_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0(v_e_5111_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_);
    crate::leanh::lean_dec(v___y_5118_);
    crate::leanh::lean_dec_ref(v___y_5117_);
    crate::leanh::lean_dec(v___y_5116_);
    crate::leanh::lean_dec_ref(v___y_5115_);
    crate::leanh::lean_dec(v___y_5114_);
    crate::leanh::lean_dec_ref(v___y_5113_);
    crate::leanh::lean_dec(v___y_5112_);
    return v_res_5120_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(
    mut v_cls_5121_: *mut crate::leanh::LeanObject,
    mut v_msg_5122_: *mut crate::leanh::LeanObject,
    mut v___y_5123_: *mut crate::leanh::LeanObject,
    mut v___y_5124_: *mut crate::leanh::LeanObject,
    mut v___y_5125_: *mut crate::leanh::LeanObject,
    mut v___y_5126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5133_: u8 = 0;
    let mut v___x_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5146_: u8 = 0;
    let mut v_tid_5147_: u64 = 0;
    let mut v_traces_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5151_: u8 = 0;
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: f64 = 0.0;
    let mut v___x_5154_: u8 = 0;
    let mut v___x_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5172_: u8 = 0;
    let mut v_isSharedCheck_5173_: u8 = 0;
    let mut v_isSharedCheck_5174_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5128_ = crate::leanh::lean_ctor_get(v___y_5125_, 5);
                v___x_5129_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0_spec__0(v_msg_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_);
                v_a_5130_ = crate::leanh::lean_ctor_get(v___x_5129_, 0);
                v_isSharedCheck_5174_ = (!crate::leanh::lean_is_exclusive(v___x_5129_)) as u8;
                if v_isSharedCheck_5174_ == 0 {
                    v___x_5132_ = v___x_5129_;
                    v_isShared_5133_ = v_isSharedCheck_5174_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5130_);
                    crate::leanh::lean_dec(v___x_5129_);
                    v___x_5132_ = crate::leanh::lean_box(0);
                    v_isShared_5133_ = v_isSharedCheck_5174_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5134_ = lean_st_ref_take(v___y_5126_);
                v_traceState_5135_ = crate::leanh::lean_ctor_get(v___x_5134_, 4);
                v_env_5136_ = crate::leanh::lean_ctor_get(v___x_5134_, 0);
                v_nextMacroScope_5137_ = crate::leanh::lean_ctor_get(v___x_5134_, 1);
                v_ngen_5138_ = crate::leanh::lean_ctor_get(v___x_5134_, 2);
                v_auxDeclNGen_5139_ = crate::leanh::lean_ctor_get(v___x_5134_, 3);
                v_cache_5140_ = crate::leanh::lean_ctor_get(v___x_5134_, 5);
                v_messages_5141_ = crate::leanh::lean_ctor_get(v___x_5134_, 6);
                v_infoState_5142_ = crate::leanh::lean_ctor_get(v___x_5134_, 7);
                v_snapshotTasks_5143_ = crate::leanh::lean_ctor_get(v___x_5134_, 8);
                v_isSharedCheck_5173_ = (!crate::leanh::lean_is_exclusive(v___x_5134_)) as u8;
                if v_isSharedCheck_5173_ == 0 {
                    v___x_5145_ = v___x_5134_;
                    v_isShared_5146_ = v_isSharedCheck_5173_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5143_);
                    crate::leanh::lean_inc(v_infoState_5142_);
                    crate::leanh::lean_inc(v_messages_5141_);
                    crate::leanh::lean_inc(v_cache_5140_);
                    crate::leanh::lean_inc(v_traceState_5135_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5139_);
                    crate::leanh::lean_inc(v_ngen_5138_);
                    crate::leanh::lean_inc(v_nextMacroScope_5137_);
                    crate::leanh::lean_inc(v_env_5136_);
                    crate::leanh::lean_dec(v___x_5134_);
                    v___x_5145_ = crate::leanh::lean_box(0);
                    v_isShared_5146_ = v_isSharedCheck_5173_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_5147_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_5135_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_5148_ = crate::leanh::lean_ctor_get(v_traceState_5135_, 0);
                v_isSharedCheck_5172_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_5135_)) as u8;
                if v_isSharedCheck_5172_ == 0 {
                    v___x_5150_ = v_traceState_5135_;
                    v_isShared_5151_ = v_isSharedCheck_5172_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_5148_);
                    crate::leanh::lean_dec(v_traceState_5135_);
                    v___x_5150_ = crate::leanh::lean_box(0);
                    v_isShared_5151_ = v_isSharedCheck_5172_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5152_ = crate::leanh::lean_box(0);
                v___x_5153_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__0);
                v___x_5154_ = 0;
                v___x_5155_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__1;
                v___x_5156_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_5156_, 0, v_cls_5121_);
                crate::leanh::lean_ctor_set(v___x_5156_, 1, v___x_5152_);
                crate::leanh::lean_ctor_set(v___x_5156_, 2, v___x_5155_);
                crate::leanh::lean_ctor_set_float(
                    v___x_5156_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_5153_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_5156_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_5153_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5156_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_5154_,
                );
                v___x_5157_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0___closed__2;
                v___x_5158_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5158_, 0, v___x_5156_);
                crate::leanh::lean_ctor_set(v___x_5158_, 1, v_a_5130_);
                crate::leanh::lean_ctor_set(v___x_5158_, 2, v___x_5157_);
                crate::leanh::lean_inc(v_ref_5128_);
                v___x_5159_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5159_, 0, v_ref_5128_);
                crate::leanh::lean_ctor_set(v___x_5159_, 1, v___x_5158_);
                v___x_5160_ = l_Lean_PersistentArray_push___redArg(v_traces_5148_, v___x_5159_);
                if v_isShared_5151_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5150_, 0, v___x_5160_);
                    v___x_5162_ = v___x_5150_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5171_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5171_, 0, v___x_5160_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_5171_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_5147_,
                    );
                    v___x_5162_ = v_reuseFailAlloc_5171_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5146_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5145_, 4, v___x_5162_);
                    v___x_5164_ = v___x_5145_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5170_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5170_, 0, v_env_5136_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5170_, 1, v_nextMacroScope_5137_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5170_, 2, v_ngen_5138_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5170_, 3, v_auxDeclNGen_5139_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5170_, 4, v___x_5162_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5170_, 5, v_cache_5140_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5170_, 6, v_messages_5141_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5170_, 7, v_infoState_5142_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5170_, 8, v_snapshotTasks_5143_);
                    v___x_5164_ = v_reuseFailAlloc_5170_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5165_ = lean_st_ref_set(v___y_5126_, v___x_5164_);
                v___x_5166_ = crate::leanh::lean_box(0);
                if v_isShared_5133_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5132_, 0, v___x_5166_);
                    v___x_5168_ = v___x_5132_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5169_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5169_, 0, v___x_5166_);
                    v___x_5168_ = v_reuseFailAlloc_5169_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5168_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg___boxed(
    mut v_cls_5175_: *mut crate::leanh::LeanObject,
    mut v_msg_5176_: *mut crate::leanh::LeanObject,
    mut v___y_5177_: *mut crate::leanh::LeanObject,
    mut v___y_5178_: *mut crate::leanh::LeanObject,
    mut v___y_5179_: *mut crate::leanh::LeanObject,
    mut v___y_5180_: *mut crate::leanh::LeanObject,
    mut v___y_5181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5182_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v_cls_5175_, v_msg_5176_, v___y_5177_, v___y_5178_, v___y_5179_, v___y_5180_);
    crate::leanh::lean_dec(v___y_5180_);
    crate::leanh::lean_dec_ref(v___y_5179_);
    crate::leanh::lean_dec(v___y_5178_);
    crate::leanh::lean_dec_ref(v___y_5177_);
    return v_res_5182_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5189_ = crate::leanh::lean_box(0);
    v___x_5190_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__3;
    v___x_5191_ = l_Lean_mkConst(v___x_5190_, v___x_5189_);
    return v___x_5191_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(
    mut v_a_5192_: *mut crate::leanh::LeanObject,
    mut v_numIndices_5193_: *mut crate::leanh::LeanObject,
    mut v_as_5194_: *mut crate::leanh::LeanObject,
    mut v_i_5195_: *mut crate::leanh::LeanObject,
    mut v___y_5196_: *mut crate::leanh::LeanObject,
    mut v___y_5197_: *mut crate::leanh::LeanObject,
    mut v___y_5198_: *mut crate::leanh::LeanObject,
    mut v___y_5199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_5202_: u8 = 0;
    let mut v___x_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5212_: u8 = 0;
    let mut v___y_5214_: u8 = 0;
    let mut v___x_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5220_: u8 = 0;
    let mut v___x_5221_: u8 = 0;
    let mut v___x_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: u8 = 0;
    let mut v___x_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5226_: u8 = 0;
    let mut v___x_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5233_: u8 = 0;
    let mut v___x_5234_: u8 = 0;
    let mut v___x_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5245_: u8 = 0;
    let mut v_a_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5249_: u8 = 0;
    let mut v___x_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5253_: u8 = 0;
    let mut v___x_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5261_: u8 = 0;
    let mut v_a_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5265_: u8 = 0;
    let mut v___x_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5269_: u8 = 0;
    let mut v___x_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: u8 = 0;
    let mut v___x_5273_: u8 = 0;
    let mut v_isSharedCheck_5274_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_5201_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_5202_ = lean_nat_dec_eq(v_i_5195_, v_zero_5201_);
                if v_isZero_5202_ == 1 {
                    crate::leanh::lean_dec(v_i_5195_);
                    crate::leanh::lean_dec_ref(v_a_5192_);
                    v___x_5203_ = crate::leanh::lean_box(0);
                    v___x_5204_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5204_, 0, v___x_5203_);
                    return v___x_5204_;
                } else {
                    v_one_5205_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_5206_ = lean_nat_sub(v_i_5195_, v_one_5205_);
                    crate::leanh::lean_dec(v_i_5195_);
                    v___x_5207_ = lean_array_fget(v_as_5194_, v_n_5206_);
                    if crate::leanh::lean_obj_tag(v___x_5207_) == 0 {
                        v_i_5195_ = v_n_5206_;
                        state = 0;
                        continue;
                    } else {
                        v_val_5209_ = crate::leanh::lean_ctor_get(v___x_5207_, 0);
                        v_isSharedCheck_5274_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5207_)) as u8;
                        if v_isSharedCheck_5274_ == 0 {
                            v___x_5211_ = v___x_5207_;
                            v_isShared_5212_ = v_isSharedCheck_5274_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_5209_);
                            crate::leanh::lean_dec(v___x_5207_);
                            v___x_5211_ = crate::leanh::lean_box(0);
                            v_isShared_5212_ = v_isSharedCheck_5274_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5271_ = l_Lean_LocalDecl_index(v_val_5209_);
                v___x_5272_ = lean_nat_dec_le(v_numIndices_5193_, v___x_5271_);
                crate::leanh::lean_dec(v___x_5271_);
                if v___x_5272_ == 0 {
                    v___x_5273_ = l_Lean_LocalDecl_isAuxDecl(v_val_5209_);
                    v___y_5214_ = v___x_5273_;
                    state = 2;
                    continue;
                } else {
                    v___y_5214_ = v___x_5272_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_5214_ == 0 {
                    v___x_5215_ = l_Lean_LocalDecl_type(v_val_5209_);
                    crate::leanh::lean_inc_ref(v___x_5215_);
                    crate::leanh::lean_inc_ref(v_a_5192_);
                    v___x_5216_ = l_Lean_Meta_isExprDefEq(
                        v_a_5192_,
                        v___x_5215_,
                        v___y_5196_,
                        v___y_5197_,
                        v___y_5198_,
                        v___y_5199_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5216_) == 0 {
                        v_a_5217_ = crate::leanh::lean_ctor_get(v___x_5216_, 0);
                        v_isSharedCheck_5261_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5216_)) as u8;
                        if v_isSharedCheck_5261_ == 0 {
                            v___x_5219_ = v___x_5216_;
                            v_isShared_5220_ = v_isSharedCheck_5261_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5217_);
                            crate::leanh::lean_dec(v___x_5216_);
                            v___x_5219_ = crate::leanh::lean_box(0);
                            v_isShared_5220_ = v_isSharedCheck_5261_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_5215_);
                        crate::leanh::lean_del_object(v___x_5211_);
                        crate::leanh::lean_dec(v_val_5209_);
                        crate::leanh::lean_dec(v_n_5206_);
                        crate::leanh::lean_dec_ref(v_a_5192_);
                        v_a_5262_ = crate::leanh::lean_ctor_get(v___x_5216_, 0);
                        v_isSharedCheck_5269_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5216_)) as u8;
                        if v_isSharedCheck_5269_ == 0 {
                            v___x_5264_ = v___x_5216_;
                            v_isShared_5265_ = v_isSharedCheck_5269_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5262_);
                            crate::leanh::lean_dec(v___x_5216_);
                            v___x_5264_ = crate::leanh::lean_box(0);
                            v_isShared_5265_ = v_isSharedCheck_5269_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5211_);
                    crate::leanh::lean_dec(v_val_5209_);
                    v_i_5195_ = v_n_5206_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                v___x_5221_ = (crate::leanh::lean_unbox(v_a_5217_) as u8);
                crate::leanh::lean_dec(v_a_5217_);
                if v___x_5221_ == 0 {
                    crate::leanh::lean_del_object(v___x_5219_);
                    v___x_5222_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__1;
                    v___x_5223_ = l_Lean_Expr_isAppOfArity(v_a_5192_, v___x_5222_, v_one_5205_);
                    if v___x_5223_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_5215_);
                        crate::leanh::lean_del_object(v___x_5211_);
                        crate::leanh::lean_dec(v_val_5209_);
                        v_i_5195_ = v_n_5206_;
                        state = 0;
                        continue;
                    } else {
                        v___x_5225_ = l_Lean_Expr_appArg_x21(v_a_5192_);
                        v___x_5226_ =
                            l_Lean_Expr_isAppOfArity(v___x_5225_, v___x_5222_, v_one_5205_);
                        if v___x_5226_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_5225_);
                            crate::leanh::lean_dec_ref(v___x_5215_);
                            crate::leanh::lean_del_object(v___x_5211_);
                            crate::leanh::lean_dec(v_val_5209_);
                            v_i_5195_ = v_n_5206_;
                            state = 0;
                            continue;
                        } else {
                            v___x_5228_ = l_Lean_Expr_appArg_x21(v___x_5225_);
                            crate::leanh::lean_dec_ref(v___x_5225_);
                            crate::leanh::lean_inc_ref(v___x_5228_);
                            v___x_5229_ = l_Lean_Meta_isExprDefEq(
                                v___x_5228_,
                                v___x_5215_,
                                v___y_5196_,
                                v___y_5197_,
                                v___y_5198_,
                                v___y_5199_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5229_) == 0 {
                                v_a_5230_ = crate::leanh::lean_ctor_get(v___x_5229_, 0);
                                v_isSharedCheck_5245_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5229_)) as u8;
                                if v_isSharedCheck_5245_ == 0 {
                                    v___x_5232_ = v___x_5229_;
                                    v_isShared_5233_ = v_isSharedCheck_5245_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5230_);
                                    crate::leanh::lean_dec(v___x_5229_);
                                    v___x_5232_ = crate::leanh::lean_box(0);
                                    v_isShared_5233_ = v_isSharedCheck_5245_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_5228_);
                                crate::leanh::lean_del_object(v___x_5211_);
                                crate::leanh::lean_dec(v_val_5209_);
                                crate::leanh::lean_dec(v_n_5206_);
                                crate::leanh::lean_dec_ref(v_a_5192_);
                                v_a_5246_ = crate::leanh::lean_ctor_get(v___x_5229_, 0);
                                v_isSharedCheck_5253_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5229_)) as u8;
                                if v_isSharedCheck_5253_ == 0 {
                                    v___x_5248_ = v___x_5229_;
                                    v_isShared_5249_ = v_isSharedCheck_5253_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5246_);
                                    crate::leanh::lean_dec(v___x_5229_);
                                    v___x_5248_ = crate::leanh::lean_box(0);
                                    v_isShared_5249_ = v_isSharedCheck_5253_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_5215_);
                    crate::leanh::lean_dec(v_n_5206_);
                    crate::leanh::lean_dec_ref(v_a_5192_);
                    v___x_5254_ = l_Lean_LocalDecl_toExpr(v_val_5209_);
                    if v_isShared_5212_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5211_, 0, v___x_5254_);
                        v___x_5256_ = v___x_5211_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_5260_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5260_, 0, v___x_5254_);
                        v___x_5256_ = v_reuseFailAlloc_5260_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                v___x_5234_ = (crate::leanh::lean_unbox(v_a_5230_) as u8);
                crate::leanh::lean_dec(v_a_5230_);
                if v___x_5234_ == 0 {
                    crate::leanh::lean_del_object(v___x_5232_);
                    crate::leanh::lean_dec_ref(v___x_5228_);
                    crate::leanh::lean_del_object(v___x_5211_);
                    crate::leanh::lean_dec(v_val_5209_);
                    v_i_5195_ = v_n_5206_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_n_5206_);
                    crate::leanh::lean_dec_ref(v_a_5192_);
                    v___x_5236_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__4);
                    v___x_5237_ = l_Lean_LocalDecl_toExpr(v_val_5209_);
                    v___x_5238_ = l_Lean_mkAppB(v___x_5236_, v___x_5228_, v___x_5237_);
                    if v_isShared_5212_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5211_, 0, v___x_5238_);
                        v___x_5240_ = v___x_5211_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5244_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5244_, 0, v___x_5238_);
                        v___x_5240_ = v_reuseFailAlloc_5244_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_5233_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5232_, 0, v___x_5240_);
                    v___x_5242_ = v___x_5232_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5243_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5243_, 0, v___x_5240_);
                    v___x_5242_ = v_reuseFailAlloc_5243_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5242_;
            }
            7 => {
                if v_isShared_5249_ == 0 {
                    v___x_5251_ = v___x_5248_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5252_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5252_, 0, v_a_5246_);
                    v___x_5251_ = v_reuseFailAlloc_5252_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5251_;
            }
            9 => {
                if v_isShared_5220_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5219_, 0, v___x_5256_);
                    v___x_5258_ = v___x_5219_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5259_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5259_, 0, v___x_5256_);
                    v___x_5258_ = v_reuseFailAlloc_5259_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5258_;
            }
            11 => {
                if v_isShared_5265_ == 0 {
                    v___x_5267_ = v___x_5264_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5268_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5268_, 0, v_a_5262_);
                    v___x_5267_ = v_reuseFailAlloc_5268_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5267_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_a_5275_: *mut crate::leanh::LeanObject,
    mut v_numIndices_5276_: *mut crate::leanh::LeanObject,
    mut v_as_5277_: *mut crate::leanh::LeanObject,
    mut v_i_5278_: *mut crate::leanh::LeanObject,
    mut v___y_5279_: *mut crate::leanh::LeanObject,
    mut v___y_5280_: *mut crate::leanh::LeanObject,
    mut v___y_5281_: *mut crate::leanh::LeanObject,
    mut v___y_5282_: *mut crate::leanh::LeanObject,
    mut v___y_5283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5284_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_a_5275_, v_numIndices_5276_, v_as_5277_, v_i_5278_, v___y_5279_, v___y_5280_, v___y_5281_, v___y_5282_);
    crate::leanh::lean_dec(v___y_5282_);
    crate::leanh::lean_dec_ref(v___y_5281_);
    crate::leanh::lean_dec(v___y_5280_);
    crate::leanh::lean_dec_ref(v___y_5279_);
    crate::leanh::lean_dec_ref(v_as_5277_);
    crate::leanh::lean_dec(v_numIndices_5276_);
    return v_res_5284_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(
    mut v_a_5285_: *mut crate::leanh::LeanObject,
    mut v_numIndices_5286_: *mut crate::leanh::LeanObject,
    mut v_as_5287_: *mut crate::leanh::LeanObject,
    mut v_i_5288_: *mut crate::leanh::LeanObject,
    mut v___y_5289_: *mut crate::leanh::LeanObject,
    mut v___y_5290_: *mut crate::leanh::LeanObject,
    mut v___y_5291_: *mut crate::leanh::LeanObject,
    mut v___y_5292_: *mut crate::leanh::LeanObject,
    mut v___y_5293_: *mut crate::leanh::LeanObject,
    mut v___y_5294_: *mut crate::leanh::LeanObject,
    mut v___y_5295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_5298_: u8 = 0;
    let mut v___x_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_5297_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_5298_ = lean_nat_dec_eq(v_i_5288_, v_zero_5297_);
                if v_isZero_5298_ == 1 {
                    crate::leanh::lean_dec(v_i_5288_);
                    crate::leanh::lean_dec_ref(v_a_5285_);
                    v___x_5299_ = crate::leanh::lean_box(0);
                    v___x_5300_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5300_, 0, v___x_5299_);
                    return v___x_5300_;
                } else {
                    v_one_5301_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_5302_ = lean_nat_sub(v_i_5288_, v_one_5301_);
                    crate::leanh::lean_dec(v_i_5288_);
                    v___x_5303_ = lean_array_fget_borrowed(v_as_5287_, v_n_5302_);
                    crate::leanh::lean_inc_ref(v_a_5285_);
                    v___x_5304_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_a_5285_, v_numIndices_5286_, v___x_5303_, v___y_5289_, v___y_5290_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_, v___y_5295_);
                    if crate::leanh::lean_obj_tag(v___x_5304_) == 0 {
                        v_a_5305_ = crate::leanh::lean_ctor_get(v___x_5304_, 0);
                        crate::leanh::lean_inc(v_a_5305_);
                        if crate::leanh::lean_obj_tag(v_a_5305_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5304_, 1);
                            v_i_5288_ = v_n_5302_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_a_5305_, 1);
                            crate::leanh::lean_dec(v_n_5302_);
                            crate::leanh::lean_dec_ref(v_a_5285_);
                            return v___x_5304_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_n_5302_);
                        crate::leanh::lean_dec_ref(v_a_5285_);
                        return v___x_5304_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(
    mut v_a_5307_: *mut crate::leanh::LeanObject,
    mut v_numIndices_5308_: *mut crate::leanh::LeanObject,
    mut v_x_5309_: *mut crate::leanh::LeanObject,
    mut v___y_5310_: *mut crate::leanh::LeanObject,
    mut v___y_5311_: *mut crate::leanh::LeanObject,
    mut v___y_5312_: *mut crate::leanh::LeanObject,
    mut v___y_5313_: *mut crate::leanh::LeanObject,
    mut v___y_5314_: *mut crate::leanh::LeanObject,
    mut v___y_5315_: *mut crate::leanh::LeanObject,
    mut v___y_5316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5309_) == 0 {
        let mut v_cs_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_cs_5318_ = crate::leanh::lean_ctor_get(v_x_5309_, 0);
        v___x_5319_ = lean_array_get_size(v_cs_5318_);
        v___x_5320_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_a_5307_, v_numIndices_5308_, v_cs_5318_, v___x_5319_, v___y_5310_, v___y_5311_, v___y_5312_, v___y_5313_, v___y_5314_, v___y_5315_, v___y_5316_);
        return v___x_5320_;
    } else {
        let mut v_vs_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_vs_5321_ = crate::leanh::lean_ctor_get(v_x_5309_, 0);
        v___x_5322_ = lean_array_get_size(v_vs_5321_);
        v___x_5323_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_a_5307_, v_numIndices_5308_, v_vs_5321_, v___x_5322_, v___y_5313_, v___y_5314_, v___y_5315_, v___y_5316_);
        return v___x_5323_;
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3___boxed(
    mut v_a_5324_: *mut crate::leanh::LeanObject,
    mut v_numIndices_5325_: *mut crate::leanh::LeanObject,
    mut v_x_5326_: *mut crate::leanh::LeanObject,
    mut v___y_5327_: *mut crate::leanh::LeanObject,
    mut v___y_5328_: *mut crate::leanh::LeanObject,
    mut v___y_5329_: *mut crate::leanh::LeanObject,
    mut v___y_5330_: *mut crate::leanh::LeanObject,
    mut v___y_5331_: *mut crate::leanh::LeanObject,
    mut v___y_5332_: *mut crate::leanh::LeanObject,
    mut v___y_5333_: *mut crate::leanh::LeanObject,
    mut v___y_5334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5335_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_a_5324_, v_numIndices_5325_, v_x_5326_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_);
    crate::leanh::lean_dec(v___y_5333_);
    crate::leanh::lean_dec_ref(v___y_5332_);
    crate::leanh::lean_dec(v___y_5331_);
    crate::leanh::lean_dec_ref(v___y_5330_);
    crate::leanh::lean_dec(v___y_5329_);
    crate::leanh::lean_dec_ref(v___y_5328_);
    crate::leanh::lean_dec(v___y_5327_);
    crate::leanh::lean_dec_ref(v_x_5326_);
    crate::leanh::lean_dec(v_numIndices_5325_);
    return v_res_5335_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg___boxed(
    mut v_a_5336_: *mut crate::leanh::LeanObject,
    mut v_numIndices_5337_: *mut crate::leanh::LeanObject,
    mut v_as_5338_: *mut crate::leanh::LeanObject,
    mut v_i_5339_: *mut crate::leanh::LeanObject,
    mut v___y_5340_: *mut crate::leanh::LeanObject,
    mut v___y_5341_: *mut crate::leanh::LeanObject,
    mut v___y_5342_: *mut crate::leanh::LeanObject,
    mut v___y_5343_: *mut crate::leanh::LeanObject,
    mut v___y_5344_: *mut crate::leanh::LeanObject,
    mut v___y_5345_: *mut crate::leanh::LeanObject,
    mut v___y_5346_: *mut crate::leanh::LeanObject,
    mut v___y_5347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5348_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_a_5336_, v_numIndices_5337_, v_as_5338_, v_i_5339_, v___y_5340_, v___y_5341_, v___y_5342_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_);
    crate::leanh::lean_dec(v___y_5346_);
    crate::leanh::lean_dec_ref(v___y_5345_);
    crate::leanh::lean_dec(v___y_5344_);
    crate::leanh::lean_dec_ref(v___y_5343_);
    crate::leanh::lean_dec(v___y_5342_);
    crate::leanh::lean_dec_ref(v___y_5341_);
    crate::leanh::lean_dec(v___y_5340_);
    crate::leanh::lean_dec_ref(v_as_5338_);
    crate::leanh::lean_dec(v_numIndices_5337_);
    return v_res_5348_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(
    mut v_a_5349_: *mut crate::leanh::LeanObject,
    mut v_numIndices_5350_: *mut crate::leanh::LeanObject,
    mut v_t_5351_: *mut crate::leanh::LeanObject,
    mut v___y_5352_: *mut crate::leanh::LeanObject,
    mut v___y_5353_: *mut crate::leanh::LeanObject,
    mut v___y_5354_: *mut crate::leanh::LeanObject,
    mut v___y_5355_: *mut crate::leanh::LeanObject,
    mut v___y_5356_: *mut crate::leanh::LeanObject,
    mut v___y_5357_: *mut crate::leanh::LeanObject,
    mut v___y_5358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_root_5360_ = crate::leanh::lean_ctor_get(v_t_5351_, 0);
    v_tail_5361_ = crate::leanh::lean_ctor_get(v_t_5351_, 1);
    v___x_5362_ = lean_array_get_size(v_tail_5361_);
    crate::leanh::lean_inc_ref(v_a_5349_);
    v___x_5363_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_a_5349_, v_numIndices_5350_, v_tail_5361_, v___x_5362_, v___y_5355_, v___y_5356_, v___y_5357_, v___y_5358_);
    if crate::leanh::lean_obj_tag(v___x_5363_) == 0 {
        let mut v_a_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_5364_ = crate::leanh::lean_ctor_get(v___x_5363_, 0);
        crate::leanh::lean_inc(v_a_5364_);
        if crate::leanh::lean_obj_tag(v_a_5364_) == 0 {
            let mut v___x_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_5363_, 1);
            v___x_5365_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3(v_a_5349_, v_numIndices_5350_, v_root_5360_, v___y_5352_, v___y_5353_, v___y_5354_, v___y_5355_, v___y_5356_, v___y_5357_, v___y_5358_);
            return v___x_5365_;
        } else {
            crate::leanh::lean_dec_ref_known(v_a_5364_, 1);
            crate::leanh::lean_dec_ref(v_a_5349_);
            return v___x_5363_;
        }
    } else {
        crate::leanh::lean_dec_ref(v_a_5349_);
        return v___x_5363_;
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1___boxed(
    mut v_a_5366_: *mut crate::leanh::LeanObject,
    mut v_numIndices_5367_: *mut crate::leanh::LeanObject,
    mut v_t_5368_: *mut crate::leanh::LeanObject,
    mut v___y_5369_: *mut crate::leanh::LeanObject,
    mut v___y_5370_: *mut crate::leanh::LeanObject,
    mut v___y_5371_: *mut crate::leanh::LeanObject,
    mut v___y_5372_: *mut crate::leanh::LeanObject,
    mut v___y_5373_: *mut crate::leanh::LeanObject,
    mut v___y_5374_: *mut crate::leanh::LeanObject,
    mut v___y_5375_: *mut crate::leanh::LeanObject,
    mut v___y_5376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5377_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(v_a_5366_, v_numIndices_5367_, v_t_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_);
    crate::leanh::lean_dec(v___y_5375_);
    crate::leanh::lean_dec_ref(v___y_5374_);
    crate::leanh::lean_dec(v___y_5373_);
    crate::leanh::lean_dec_ref(v___y_5372_);
    crate::leanh::lean_dec(v___y_5371_);
    crate::leanh::lean_dec_ref(v___y_5370_);
    crate::leanh::lean_dec(v___y_5369_);
    crate::leanh::lean_dec_ref(v_t_5368_);
    crate::leanh::lean_dec(v_numIndices_5367_);
    return v_res_5377_;
}
pub unsafe fn l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(
    mut v_a_5378_: *mut crate::leanh::LeanObject,
    mut v_numIndices_5379_: *mut crate::leanh::LeanObject,
    mut v_lctx_5380_: *mut crate::leanh::LeanObject,
    mut v___y_5381_: *mut crate::leanh::LeanObject,
    mut v___y_5382_: *mut crate::leanh::LeanObject,
    mut v___y_5383_: *mut crate::leanh::LeanObject,
    mut v___y_5384_: *mut crate::leanh::LeanObject,
    mut v___y_5385_: *mut crate::leanh::LeanObject,
    mut v___y_5386_: *mut crate::leanh::LeanObject,
    mut v___y_5387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decls_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_decls_5389_ = crate::leanh::lean_ctor_get(v_lctx_5380_, 1);
    v___x_5390_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1(v_a_5378_, v_numIndices_5379_, v_decls_5389_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_);
    return v___x_5390_;
}
pub unsafe fn l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1___boxed(
    mut v_a_5391_: *mut crate::leanh::LeanObject,
    mut v_numIndices_5392_: *mut crate::leanh::LeanObject,
    mut v_lctx_5393_: *mut crate::leanh::LeanObject,
    mut v___y_5394_: *mut crate::leanh::LeanObject,
    mut v___y_5395_: *mut crate::leanh::LeanObject,
    mut v___y_5396_: *mut crate::leanh::LeanObject,
    mut v___y_5397_: *mut crate::leanh::LeanObject,
    mut v___y_5398_: *mut crate::leanh::LeanObject,
    mut v___y_5399_: *mut crate::leanh::LeanObject,
    mut v___y_5400_: *mut crate::leanh::LeanObject,
    mut v___y_5401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5402_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(v_a_5391_, v_numIndices_5392_, v_lctx_5393_, v___y_5394_, v___y_5395_, v___y_5396_, v___y_5397_, v___y_5398_, v___y_5399_, v___y_5400_);
    crate::leanh::lean_dec(v___y_5400_);
    crate::leanh::lean_dec_ref(v___y_5399_);
    crate::leanh::lean_dec(v___y_5398_);
    crate::leanh::lean_dec_ref(v___y_5397_);
    crate::leanh::lean_dec(v___y_5396_);
    crate::leanh::lean_dec_ref(v___y_5395_);
    crate::leanh::lean_dec(v___y_5394_);
    crate::leanh::lean_dec_ref(v_lctx_5393_);
    crate::leanh::lean_dec(v_numIndices_5392_);
    return v_res_5402_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5408_ = crate::leanh::lean_box(0);
    v___x_5409_ =
        l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2;
    v___x_5410_ = l_Lean_mkConst(v___x_5409_, v___x_5408_);
    return v___x_5410_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5414_ = crate::leanh::lean_box(0);
    v___x_5415_ =
        l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__5;
    v___x_5416_ = l_Lean_mkConst(v___x_5415_, v___x_5414_);
    return v___x_5416_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7()
-> u64 {
    let mut v___x_5417_: u8 = 0;
    let mut v___x_5418_: u64 = 0;
    v___x_5417_ = 1;
    v___x_5418_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_5417_);
    return v___x_5418_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5425_ =
        l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10;
    v___x_5426_ =
        l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4;
    v___x_5427_ = l_Lean_Name_append(v___x_5426_, v___x_5425_);
    return v___x_5427_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5429_ =
        l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__12;
    v___x_5430_ = l_Lean_stringToMessageData(v___x_5429_);
    return v___x_5430_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5432_ =
        l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__14;
    v___x_5433_ = l_Lean_stringToMessageData(v___x_5432_);
    return v___x_5433_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5437_ =
        l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__17;
    v___x_5438_ = l_Lean_MessageData_ofFormat(v___x_5437_);
    return v___x_5438_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(
    mut v_numIndices_5439_: *mut crate::leanh::LeanObject,
    mut v_useDecide_5440_: u8,
    mut v_prop_5441_: *mut crate::leanh::LeanObject,
    mut v_a_5442_: *mut crate::leanh::LeanObject,
    mut v_a_5443_: *mut crate::leanh::LeanObject,
    mut v_a_5444_: *mut crate::leanh::LeanObject,
    mut v_a_5445_: *mut crate::leanh::LeanObject,
    mut v_a_5446_: *mut crate::leanh::LeanObject,
    mut v_a_5447_: *mut crate::leanh::LeanObject,
    mut v_a_5448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5454_: u8 = 0;
    let mut v___y_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: u8 = 0;
    let mut v___x_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5483_: u8 = 0;
    let mut v___x_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5493_: u8 = 0;
    let mut v_a_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5497_: u8 = 0;
    let mut v___x_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5501_: u8 = 0;
    let mut v___y_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: u8 = 0;
    let mut v___x_5513_: u8 = 0;
    let mut v___x_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_5517_: u8 = 0;
    let mut v_ctxApprox_5518_: u8 = 0;
    let mut v_quasiPatternApprox_5519_: u8 = 0;
    let mut v_constApprox_5520_: u8 = 0;
    let mut v_isDefEqStuckEx_5521_: u8 = 0;
    let mut v_unificationHints_5522_: u8 = 0;
    let mut v_proofIrrelevance_5523_: u8 = 0;
    let mut v_assignSyntheticOpaque_5524_: u8 = 0;
    let mut v_offsetCnstrs_5525_: u8 = 0;
    let mut v_etaStruct_5526_: u8 = 0;
    let mut v_univApprox_5527_: u8 = 0;
    let mut v_iota_5528_: u8 = 0;
    let mut v_beta_5529_: u8 = 0;
    let mut v_proj_5530_: u8 = 0;
    let mut v_zeta_5531_: u8 = 0;
    let mut v_zetaDelta_5532_: u8 = 0;
    let mut v_zetaUnused_5533_: u8 = 0;
    let mut v_zetaHave_5534_: u8 = 0;
    let mut v___x_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5537_: u8 = 0;
    let mut v_trackZetaDelta_5538_: u8 = 0;
    let mut v_zetaDeltaSet_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_5545_: u8 = 0;
    let mut v_inTypeClassResolution_5546_: u8 = 0;
    let mut v_cacheInferType_5547_: u8 = 0;
    let mut v___x_5548_: u8 = 0;
    let mut v_config_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: u64 = 0;
    let mut v___x_5552_: u64 = 0;
    let mut v___x_5553_: u64 = 0;
    let mut v___x_5554_: u64 = 0;
    let mut v___x_5555_: u64 = 0;
    let mut v_key_5556_: u64 = 0;
    let mut v___x_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5565_: u8 = 0;
    let mut v___x_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5569_: u8 = 0;
    let mut v_reuseFailAlloc_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5571_: u8 = 0;
    let mut v_a_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5575_: u8 = 0;
    let mut v___x_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5579_: u8 = 0;
    let mut v_options_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5581_: u8 = 0;
    let mut v_inheritedTraceOptions_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: u8 = 0;
    let mut v___x_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5598_: u8 = 0;
    let mut v___x_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5602_: u8 = 0;
    let mut v___x_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: u8 = 0;
    let mut v___x_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: u8 = 0;
    let mut v___x_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5612_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5450_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_prop_5441_, v_a_5446_);
                v_a_5451_ = crate::leanh::lean_ctor_get(v___x_5450_, 0);
                v_isSharedCheck_5612_ = (!crate::leanh::lean_is_exclusive(v___x_5450_)) as u8;
                if v_isSharedCheck_5612_ == 0 {
                    v___x_5453_ = v___x_5450_;
                    v_isShared_5454_ = v_isSharedCheck_5612_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5451_);
                    crate::leanh::lean_dec(v___x_5450_);
                    v___x_5453_ = crate::leanh::lean_box(0);
                    v_isShared_5454_ = v_isSharedCheck_5612_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_options_5580_ = crate::leanh::lean_ctor_get(v_a_5447_, 2);
                v_hasTrace_5581_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_5580_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_5581_ == 0 {
                    v___y_5503_ = v_a_5442_;
                    v___y_5504_ = v_a_5443_;
                    v___y_5505_ = v_a_5444_;
                    v___y_5506_ = v_a_5445_;
                    v___y_5507_ = v_a_5446_;
                    v___y_5508_ = v_a_5447_;
                    v___y_5509_ = v_a_5448_;
                    state = 9;
                    continue;
                } else {
                    v_inheritedTraceOptions_5582_ = crate::leanh::lean_ctor_get(v_a_5447_, 13);
                    v___x_5583_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10;
                    v___x_5584_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11_once), _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11);
                    v___x_5585_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_5582_,
                        v_options_5580_,
                        v___x_5584_,
                    );
                    if v___x_5585_ == 0 {
                        v___y_5503_ = v_a_5442_;
                        v___y_5504_ = v_a_5443_;
                        v___y_5505_ = v_a_5444_;
                        v___y_5506_ = v_a_5445_;
                        v___y_5507_ = v_a_5446_;
                        v___y_5508_ = v_a_5447_;
                        v___y_5509_ = v_a_5448_;
                        state = 9;
                        continue;
                    } else {
                        v___x_5586_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13_once), _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__13);
                        crate::leanh::lean_inc(v_a_5451_);
                        v___x_5587_ = l_Lean_MessageData_ofExpr(v_a_5451_);
                        v___x_5588_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5588_, 0, v___x_5586_);
                        crate::leanh::lean_ctor_set(v___x_5588_, 1, v___x_5587_);
                        v___x_5589_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__15_once), _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__15);
                        v___x_5590_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5590_, 0, v___x_5588_);
                        crate::leanh::lean_ctor_set(v___x_5590_, 1, v___x_5589_);
                        v___x_5605_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg___closed__1;
                        v___x_5606_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5607_ = l_Lean_Expr_isAppOfArity(v_a_5451_, v___x_5605_, v___x_5606_);
                        if v___x_5607_ == 0 {
                            state = 19;
                            continue;
                        } else {
                            v___x_5608_ = l_Lean_Expr_appArg_x21(v_a_5451_);
                            v___x_5609_ =
                                l_Lean_Expr_isAppOfArity(v___x_5608_, v___x_5605_, v___x_5606_);
                            if v___x_5609_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_5608_);
                                state = 19;
                                continue;
                            } else {
                                v___x_5610_ = l_Lean_Expr_appArg_x21(v___x_5608_);
                                crate::leanh::lean_dec_ref(v___x_5608_);
                                v___x_5611_ = l_Lean_MessageData_ofExpr(v___x_5610_);
                                v___y_5592_ = v___x_5611_;
                                state = 16;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                v_lctx_5463_ = crate::leanh::lean_ctor_get(v___y_5459_, 2);
                v___x_5464_ = l_Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1(v_a_5451_, v_numIndices_5439_, v_lctx_5463_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_);
                return v___x_5464_;
            }
            3 => {
                v___x_5476_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__2;
                v___x_5477_ = l_Lean_Expr_isConstOf(v_a_5475_, v___x_5476_);
                crate::leanh::lean_dec_ref(v_a_5475_);
                if v___x_5477_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_5474_);
                    crate::leanh::lean_dec_ref(v___y_5470_);
                    crate::leanh::lean_del_object(v___x_5453_);
                    v___y_5456_ = v___y_5466_;
                    v___y_5457_ = v___y_5472_;
                    v___y_5458_ = v___y_5469_;
                    v___y_5459_ = v___y_5468_;
                    v___y_5460_ = v___y_5471_;
                    v___y_5461_ = v___y_5467_;
                    v___y_5462_ = v___y_5473_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_5451_);
                    v___x_5478_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3_once), _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__3);
                    v___x_5479_ = l_Lean_Meta_mkEqRefl(
                        v___x_5478_,
                        v___y_5468_,
                        v___y_5471_,
                        v___y_5467_,
                        v___y_5473_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5479_) == 0 {
                        v_a_5480_ = crate::leanh::lean_ctor_get(v___x_5479_, 0);
                        v_isSharedCheck_5493_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5479_)) as u8;
                        if v_isSharedCheck_5493_ == 0 {
                            v___x_5482_ = v___x_5479_;
                            v_isShared_5483_ = v_isSharedCheck_5493_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5480_);
                            crate::leanh::lean_dec(v___x_5479_);
                            v___x_5482_ = crate::leanh::lean_box(0);
                            v_isShared_5483_ = v_isSharedCheck_5493_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_5474_);
                        crate::leanh::lean_dec_ref(v___y_5470_);
                        crate::leanh::lean_del_object(v___x_5453_);
                        v_a_5494_ = crate::leanh::lean_ctor_get(v___x_5479_, 0);
                        v_isSharedCheck_5501_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5479_)) as u8;
                        if v_isSharedCheck_5501_ == 0 {
                            v___x_5496_ = v___x_5479_;
                            v_isShared_5497_ = v_isSharedCheck_5501_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5494_);
                            crate::leanh::lean_dec(v___x_5479_);
                            v___x_5496_ = crate::leanh::lean_box(0);
                            v_isShared_5497_ = v_isSharedCheck_5501_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v___x_5484_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6_once), _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__6);
                v___x_5485_ = l_Lean_Expr_appArg_x21(v___y_5470_);
                crate::leanh::lean_dec_ref(v___y_5470_);
                v___x_5486_ = l_Lean_mkApp3(v___x_5484_, v___y_5474_, v___x_5485_, v_a_5480_);
                if v_isShared_5454_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5453_, 1);
                    crate::leanh::lean_ctor_set(v___x_5453_, 0, v___x_5486_);
                    v___x_5488_ = v___x_5453_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5492_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5492_, 0, v___x_5486_);
                    v___x_5488_ = v_reuseFailAlloc_5492_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_5483_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5482_, 0, v___x_5488_);
                    v___x_5490_ = v___x_5482_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5491_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5491_, 0, v___x_5488_);
                    v___x_5490_ = v_reuseFailAlloc_5491_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5490_;
            }
            7 => {
                if v_isShared_5497_ == 0 {
                    v___x_5499_ = v___x_5496_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5500_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5500_, 0, v_a_5494_);
                    v___x_5499_ = v_reuseFailAlloc_5500_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5499_;
            }
            9 => {
                if v_useDecide_5440_ == 0 {
                    crate::leanh::lean_del_object(v___x_5453_);
                    v___y_5456_ = v___y_5503_;
                    v___y_5457_ = v___y_5504_;
                    v___y_5458_ = v___y_5505_;
                    v___y_5459_ = v___y_5506_;
                    v___y_5460_ = v___y_5507_;
                    v___y_5461_ = v___y_5508_;
                    v___y_5462_ = v___y_5509_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5451_);
                    v___x_5510_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__0___redArg(v_a_5451_, v___y_5507_);
                    v_a_5511_ = crate::leanh::lean_ctor_get(v___x_5510_, 0);
                    crate::leanh::lean_inc(v_a_5511_);
                    crate::leanh::lean_dec_ref(v___x_5510_);
                    v___x_5512_ = l_Lean_Expr_hasFVar(v_a_5511_);
                    if v___x_5512_ == 0 {
                        v___x_5513_ = l_Lean_Expr_hasMVar(v_a_5511_);
                        if v___x_5513_ == 0 {
                            crate::leanh::lean_inc(v_a_5511_);
                            v___x_5514_ = l_Lean_Meta_mkDecide(
                                v_a_5511_,
                                v___y_5506_,
                                v___y_5507_,
                                v___y_5508_,
                                v___y_5509_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5514_) == 0 {
                                v_a_5515_ = crate::leanh::lean_ctor_get(v___x_5514_, 0);
                                crate::leanh::lean_inc(v_a_5515_);
                                crate::leanh::lean_dec_ref_known(v___x_5514_, 1);
                                v___x_5516_ = l_Lean_Meta_Context_config(v___y_5506_);
                                v_foApprox_5517_ =
                                    crate::leanh::lean_ctor_get_uint8(v___x_5516_, 0 as u32);
                                v_ctxApprox_5518_ =
                                    crate::leanh::lean_ctor_get_uint8(v___x_5516_, 1 as u32);
                                v_quasiPatternApprox_5519_ =
                                    crate::leanh::lean_ctor_get_uint8(v___x_5516_, 2 as u32);
                                v_constApprox_5520_ =
                                    crate::leanh::lean_ctor_get_uint8(v___x_5516_, 3 as u32);
                                v_isDefEqStuckEx_5521_ =
                                    crate::leanh::lean_ctor_get_uint8(v___x_5516_, 4 as u32);
                                v_unificationHints_5522_ =
                                    crate::leanh::lean_ctor_get_uint8(v___x_5516_, 5 as u32);
                                v_proofIrrelevance_5523_ =
                                    crate::leanh::lean_ctor_get_uint8(v___x_5516_, 6 as u32);
                                v_assignSyntheticOpaque_5524_ =
                                    crate::leanh::lean_ctor_get_uint8(v___x_5516_, 7 as u32);
                                v_offsetCnstrs_5525_ =
                                    crate::leanh::lean_ctor_get_uint8(v___x_5516_, 8 as u32);
                                v_etaStruct_5526_ =
                                    crate::leanh::lean_ctor_get_uint8(v___x_5516_, 10 as u32);
                                v_univApprox_5527_ =
                                    crate::leanh::lean_ctor_get_uint8(v___x_5516_, 11 as u32);
                                v_iota_5528_ =
                                    crate::leanh::lean_ctor_get_uint8(v___x_5516_, 12 as u32);
                                v_beta_5529_ =
                                    crate::leanh::lean_ctor_get_uint8(v___x_5516_, 13 as u32);
                                v_proj_5530_ =
                                    crate::leanh::lean_ctor_get_uint8(v___x_5516_, 14 as u32);
                                v_zeta_5531_ =
                                    crate::leanh::lean_ctor_get_uint8(v___x_5516_, 15 as u32);
                                v_zetaDelta_5532_ =
                                    crate::leanh::lean_ctor_get_uint8(v___x_5516_, 16 as u32);
                                v_zetaUnused_5533_ =
                                    crate::leanh::lean_ctor_get_uint8(v___x_5516_, 17 as u32);
                                v_zetaHave_5534_ =
                                    crate::leanh::lean_ctor_get_uint8(v___x_5516_, 18 as u32);
                                v_isSharedCheck_5571_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5516_)) as u8;
                                if v_isSharedCheck_5571_ == 0 {
                                    v___x_5536_ = v___x_5516_;
                                    v_isShared_5537_ = v_isSharedCheck_5571_;
                                    state = 10;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_5516_);
                                    v___x_5536_ = crate::leanh::lean_box(0);
                                    v_isShared_5537_ = v_isSharedCheck_5571_;
                                    state = 10;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5511_);
                                crate::leanh::lean_del_object(v___x_5453_);
                                crate::leanh::lean_dec(v_a_5451_);
                                v_a_5572_ = crate::leanh::lean_ctor_get(v___x_5514_, 0);
                                v_isSharedCheck_5579_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5514_)) as u8;
                                if v_isSharedCheck_5579_ == 0 {
                                    v___x_5574_ = v___x_5514_;
                                    v_isShared_5575_ = v_isSharedCheck_5579_;
                                    state = 14;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5572_);
                                    crate::leanh::lean_dec(v___x_5514_);
                                    v___x_5574_ = crate::leanh::lean_box(0);
                                    v_isShared_5575_ = v_isSharedCheck_5579_;
                                    state = 14;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5511_);
                            crate::leanh::lean_del_object(v___x_5453_);
                            v___y_5456_ = v___y_5503_;
                            v___y_5457_ = v___y_5504_;
                            v___y_5458_ = v___y_5505_;
                            v___y_5459_ = v___y_5506_;
                            v___y_5460_ = v___y_5507_;
                            v___y_5461_ = v___y_5508_;
                            v___y_5462_ = v___y_5509_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5511_);
                        crate::leanh::lean_del_object(v___x_5453_);
                        v___y_5456_ = v___y_5503_;
                        v___y_5457_ = v___y_5504_;
                        v___y_5458_ = v___y_5505_;
                        v___y_5459_ = v___y_5506_;
                        v___y_5460_ = v___y_5507_;
                        v___y_5461_ = v___y_5508_;
                        v___y_5462_ = v___y_5509_;
                        state = 2;
                        continue;
                    }
                }
            }
            10 => {
                v_trackZetaDelta_5538_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_5506_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_5539_ = crate::leanh::lean_ctor_get(v___y_5506_, 1);
                v_lctx_5540_ = crate::leanh::lean_ctor_get(v___y_5506_, 2);
                v_localInstances_5541_ = crate::leanh::lean_ctor_get(v___y_5506_, 3);
                v_defEqCtx_x3f_5542_ = crate::leanh::lean_ctor_get(v___y_5506_, 4);
                v_synthPendingDepth_5543_ = crate::leanh::lean_ctor_get(v___y_5506_, 5);
                v_canUnfold_x3f_5544_ = crate::leanh::lean_ctor_get(v___y_5506_, 6);
                v_univApprox_5545_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_5506_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_5546_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_5506_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_5547_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_5506_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_5548_ = 1;
                if v_isShared_5537_ == 0 {
                    v_config_5550_ = v___x_5536_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5570_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5570_,
                        0 as u32,
                        v_foApprox_5517_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5570_,
                        1 as u32,
                        v_ctxApprox_5518_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5570_,
                        2 as u32,
                        v_quasiPatternApprox_5519_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5570_,
                        3 as u32,
                        v_constApprox_5520_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5570_,
                        4 as u32,
                        v_isDefEqStuckEx_5521_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5570_,
                        5 as u32,
                        v_unificationHints_5522_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5570_,
                        6 as u32,
                        v_proofIrrelevance_5523_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5570_,
                        7 as u32,
                        v_assignSyntheticOpaque_5524_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5570_,
                        8 as u32,
                        v_offsetCnstrs_5525_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5570_,
                        10 as u32,
                        v_etaStruct_5526_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5570_,
                        11 as u32,
                        v_univApprox_5527_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5570_,
                        12 as u32,
                        v_iota_5528_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5570_,
                        13 as u32,
                        v_beta_5529_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5570_,
                        14 as u32,
                        v_proj_5530_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5570_,
                        15 as u32,
                        v_zeta_5531_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5570_,
                        16 as u32,
                        v_zetaDelta_5532_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5570_,
                        17 as u32,
                        v_zetaUnused_5533_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5570_,
                        18 as u32,
                        v_zetaHave_5534_,
                    );
                    v_config_5550_ = v_reuseFailAlloc_5570_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                crate::leanh::lean_ctor_set_uint8(v_config_5550_, 9 as u32, v___x_5548_);
                v___x_5551_ = l_Lean_Meta_Context_configKey(v___y_5506_);
                v___x_5552_ = 3u64;
                v___x_5553_ = lean_uint64_shift_right(v___x_5551_, v___x_5552_);
                v___x_5554_ = lean_uint64_shift_left(v___x_5553_, v___x_5552_);
                v___x_5555_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7_once), _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__7);
                v_key_5556_ = lean_uint64_lor(v___x_5554_, v___x_5555_);
                v___x_5557_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_5557_, 0, v_config_5550_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_5557_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_5556_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_5544_);
                crate::leanh::lean_inc(v_synthPendingDepth_5543_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_5542_);
                crate::leanh::lean_inc_ref(v_localInstances_5541_);
                crate::leanh::lean_inc_ref(v_lctx_5540_);
                crate::leanh::lean_inc(v_zetaDeltaSet_5539_);
                v___x_5558_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_5558_, 0, v___x_5557_);
                crate::leanh::lean_ctor_set(v___x_5558_, 1, v_zetaDeltaSet_5539_);
                crate::leanh::lean_ctor_set(v___x_5558_, 2, v_lctx_5540_);
                crate::leanh::lean_ctor_set(v___x_5558_, 3, v_localInstances_5541_);
                crate::leanh::lean_ctor_set(v___x_5558_, 4, v_defEqCtx_x3f_5542_);
                crate::leanh::lean_ctor_set(v___x_5558_, 5, v_synthPendingDepth_5543_);
                crate::leanh::lean_ctor_set(v___x_5558_, 6, v_canUnfold_x3f_5544_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5558_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_5538_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5558_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_5545_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5558_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_5546_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5558_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_5547_,
                );
                crate::leanh::lean_inc(v___y_5509_);
                crate::leanh::lean_inc_ref(v___y_5508_);
                crate::leanh::lean_inc(v___y_5507_);
                crate::leanh::lean_inc(v_a_5515_);
                v___x_5559_ = lean_whnf(
                    v_a_5515_,
                    v___x_5558_,
                    v___y_5507_,
                    v___y_5508_,
                    v___y_5509_,
                );
                if crate::leanh::lean_obj_tag(v___x_5559_) == 0 {
                    v_a_5560_ = crate::leanh::lean_ctor_get(v___x_5559_, 0);
                    crate::leanh::lean_inc(v_a_5560_);
                    crate::leanh::lean_dec_ref_known(v___x_5559_, 1);
                    v___y_5466_ = v___y_5503_;
                    v___y_5467_ = v___y_5508_;
                    v___y_5468_ = v___y_5506_;
                    v___y_5469_ = v___y_5505_;
                    v___y_5470_ = v_a_5515_;
                    v___y_5471_ = v___y_5507_;
                    v___y_5472_ = v___y_5504_;
                    v___y_5473_ = v___y_5509_;
                    v___y_5474_ = v_a_5511_;
                    v_a_5475_ = v_a_5560_;
                    state = 3;
                    continue;
                } else {
                    if crate::leanh::lean_obj_tag(v___x_5559_) == 0 {
                        v_a_5561_ = crate::leanh::lean_ctor_get(v___x_5559_, 0);
                        crate::leanh::lean_inc(v_a_5561_);
                        crate::leanh::lean_dec_ref_known(v___x_5559_, 1);
                        v___y_5466_ = v___y_5503_;
                        v___y_5467_ = v___y_5508_;
                        v___y_5468_ = v___y_5506_;
                        v___y_5469_ = v___y_5505_;
                        v___y_5470_ = v_a_5515_;
                        v___y_5471_ = v___y_5507_;
                        v___y_5472_ = v___y_5504_;
                        v___y_5473_ = v___y_5509_;
                        v___y_5474_ = v_a_5511_;
                        v_a_5475_ = v_a_5561_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_5515_);
                        crate::leanh::lean_dec(v_a_5511_);
                        crate::leanh::lean_del_object(v___x_5453_);
                        crate::leanh::lean_dec(v_a_5451_);
                        v_a_5562_ = crate::leanh::lean_ctor_get(v___x_5559_, 0);
                        v_isSharedCheck_5569_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5559_)) as u8;
                        if v_isSharedCheck_5569_ == 0 {
                            v___x_5564_ = v___x_5559_;
                            v_isShared_5565_ = v_isSharedCheck_5569_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5562_);
                            crate::leanh::lean_dec(v___x_5559_);
                            v___x_5564_ = crate::leanh::lean_box(0);
                            v_isShared_5565_ = v_isSharedCheck_5569_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            12 => {
                if v_isShared_5565_ == 0 {
                    v___x_5567_ = v___x_5564_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5568_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5568_, 0, v_a_5562_);
                    v___x_5567_ = v_reuseFailAlloc_5568_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5567_;
            }
            14 => {
                if v_isShared_5575_ == 0 {
                    v___x_5577_ = v___x_5574_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5578_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5578_, 0, v_a_5572_);
                    v___x_5577_ = v_reuseFailAlloc_5578_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_5577_;
            }
            16 => {
                v___x_5593_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5593_, 0, v___x_5590_);
                crate::leanh::lean_ctor_set(v___x_5593_, 1, v___y_5592_);
                v___x_5594_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v___x_5583_, v___x_5593_, v_a_5445_, v_a_5446_, v_a_5447_, v_a_5448_);
                if crate::leanh::lean_obj_tag(v___x_5594_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5594_, 1);
                    v___y_5503_ = v_a_5442_;
                    v___y_5504_ = v_a_5443_;
                    v___y_5505_ = v_a_5444_;
                    v___y_5506_ = v_a_5445_;
                    v___y_5507_ = v_a_5446_;
                    v___y_5508_ = v_a_5447_;
                    v___y_5509_ = v_a_5448_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_del_object(v___x_5453_);
                    crate::leanh::lean_dec(v_a_5451_);
                    v_a_5595_ = crate::leanh::lean_ctor_get(v___x_5594_, 0);
                    v_isSharedCheck_5602_ = (!crate::leanh::lean_is_exclusive(v___x_5594_)) as u8;
                    if v_isSharedCheck_5602_ == 0 {
                        v___x_5597_ = v___x_5594_;
                        v_isShared_5598_ = v_isSharedCheck_5602_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5595_);
                        crate::leanh::lean_dec(v___x_5594_);
                        v___x_5597_ = crate::leanh::lean_box(0);
                        v_isShared_5598_ = v_isSharedCheck_5602_;
                        state = 17;
                        continue;
                    }
                }
            }
            17 => {
                if v_isShared_5598_ == 0 {
                    v___x_5600_ = v___x_5597_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5601_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5601_, 0, v_a_5595_);
                    v___x_5600_ = v_reuseFailAlloc_5601_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5600_;
            }
            19 => {
                v___x_5604_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__18), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__18_once), _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__18);
                v___y_5592_ = v___x_5604_;
                state = 16;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___boxed(
    mut v_numIndices_5613_: *mut crate::leanh::LeanObject,
    mut v_useDecide_5614_: *mut crate::leanh::LeanObject,
    mut v_prop_5615_: *mut crate::leanh::LeanObject,
    mut v_a_5616_: *mut crate::leanh::LeanObject,
    mut v_a_5617_: *mut crate::leanh::LeanObject,
    mut v_a_5618_: *mut crate::leanh::LeanObject,
    mut v_a_5619_: *mut crate::leanh::LeanObject,
    mut v_a_5620_: *mut crate::leanh::LeanObject,
    mut v_a_5621_: *mut crate::leanh::LeanObject,
    mut v_a_5622_: *mut crate::leanh::LeanObject,
    mut v_a_5623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useDecide_boxed_5624_: u8 = 0;
    let mut v_res_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useDecide_boxed_5624_ = (crate::leanh::lean_unbox(v_useDecide_5614_) as u8);
    v_res_5625_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(
        v_numIndices_5613_,
        v_useDecide_boxed_5624_,
        v_prop_5615_,
        v_a_5616_,
        v_a_5617_,
        v_a_5618_,
        v_a_5619_,
        v_a_5620_,
        v_a_5621_,
        v_a_5622_,
    );
    crate::leanh::lean_dec(v_a_5622_);
    crate::leanh::lean_dec_ref(v_a_5621_);
    crate::leanh::lean_dec(v_a_5620_);
    crate::leanh::lean_dec_ref(v_a_5619_);
    crate::leanh::lean_dec(v_a_5618_);
    crate::leanh::lean_dec_ref(v_a_5617_);
    crate::leanh::lean_dec(v_a_5616_);
    crate::leanh::lean_dec(v_numIndices_5613_);
    return v_res_5625_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2(
    mut v_cls_5626_: *mut crate::leanh::LeanObject,
    mut v_msg_5627_: *mut crate::leanh::LeanObject,
    mut v___y_5628_: *mut crate::leanh::LeanObject,
    mut v___y_5629_: *mut crate::leanh::LeanObject,
    mut v___y_5630_: *mut crate::leanh::LeanObject,
    mut v___y_5631_: *mut crate::leanh::LeanObject,
    mut v___y_5632_: *mut crate::leanh::LeanObject,
    mut v___y_5633_: *mut crate::leanh::LeanObject,
    mut v___y_5634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5636_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___redArg(v_cls_5626_, v_msg_5627_, v___y_5631_, v___y_5632_, v___y_5633_, v___y_5634_);
    return v___x_5636_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2___boxed(
    mut v_cls_5637_: *mut crate::leanh::LeanObject,
    mut v_msg_5638_: *mut crate::leanh::LeanObject,
    mut v___y_5639_: *mut crate::leanh::LeanObject,
    mut v___y_5640_: *mut crate::leanh::LeanObject,
    mut v___y_5641_: *mut crate::leanh::LeanObject,
    mut v___y_5642_: *mut crate::leanh::LeanObject,
    mut v___y_5643_: *mut crate::leanh::LeanObject,
    mut v___y_5644_: *mut crate::leanh::LeanObject,
    mut v___y_5645_: *mut crate::leanh::LeanObject,
    mut v___y_5646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5647_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__2(v_cls_5637_, v_msg_5638_, v___y_5639_, v___y_5640_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_, v___y_5645_);
    crate::leanh::lean_dec(v___y_5645_);
    crate::leanh::lean_dec_ref(v___y_5644_);
    crate::leanh::lean_dec(v___y_5643_);
    crate::leanh::lean_dec_ref(v___y_5642_);
    crate::leanh::lean_dec(v___y_5641_);
    crate::leanh::lean_dec_ref(v___y_5640_);
    crate::leanh::lean_dec(v___y_5639_);
    return v_res_5647_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2(
    mut v_a_5648_: *mut crate::leanh::LeanObject,
    mut v_numIndices_5649_: *mut crate::leanh::LeanObject,
    mut v_as_5650_: *mut crate::leanh::LeanObject,
    mut v_i_5651_: *mut crate::leanh::LeanObject,
    mut v_a_5652_: *mut crate::leanh::LeanObject,
    mut v___y_5653_: *mut crate::leanh::LeanObject,
    mut v___y_5654_: *mut crate::leanh::LeanObject,
    mut v___y_5655_: *mut crate::leanh::LeanObject,
    mut v___y_5656_: *mut crate::leanh::LeanObject,
    mut v___y_5657_: *mut crate::leanh::LeanObject,
    mut v___y_5658_: *mut crate::leanh::LeanObject,
    mut v___y_5659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5661_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___redArg(v_a_5648_, v_numIndices_5649_, v_as_5650_, v_i_5651_, v___y_5656_, v___y_5657_, v___y_5658_, v___y_5659_);
    return v___x_5661_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2___boxed(
    mut v_a_5662_: *mut crate::leanh::LeanObject,
    mut v_numIndices_5663_: *mut crate::leanh::LeanObject,
    mut v_as_5664_: *mut crate::leanh::LeanObject,
    mut v_i_5665_: *mut crate::leanh::LeanObject,
    mut v_a_5666_: *mut crate::leanh::LeanObject,
    mut v___y_5667_: *mut crate::leanh::LeanObject,
    mut v___y_5668_: *mut crate::leanh::LeanObject,
    mut v___y_5669_: *mut crate::leanh::LeanObject,
    mut v___y_5670_: *mut crate::leanh::LeanObject,
    mut v___y_5671_: *mut crate::leanh::LeanObject,
    mut v___y_5672_: *mut crate::leanh::LeanObject,
    mut v___y_5673_: *mut crate::leanh::LeanObject,
    mut v___y_5674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5675_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__2(v_a_5662_, v_numIndices_5663_, v_as_5664_, v_i_5665_, v_a_5666_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_, v___y_5671_, v___y_5672_, v___y_5673_);
    crate::leanh::lean_dec(v___y_5673_);
    crate::leanh::lean_dec_ref(v___y_5672_);
    crate::leanh::lean_dec(v___y_5671_);
    crate::leanh::lean_dec_ref(v___y_5670_);
    crate::leanh::lean_dec(v___y_5669_);
    crate::leanh::lean_dec_ref(v___y_5668_);
    crate::leanh::lean_dec(v___y_5667_);
    crate::leanh::lean_dec_ref(v_as_5664_);
    crate::leanh::lean_dec(v_numIndices_5663_);
    return v_res_5675_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5(
    mut v_a_5676_: *mut crate::leanh::LeanObject,
    mut v_numIndices_5677_: *mut crate::leanh::LeanObject,
    mut v_as_5678_: *mut crate::leanh::LeanObject,
    mut v_i_5679_: *mut crate::leanh::LeanObject,
    mut v_a_5680_: *mut crate::leanh::LeanObject,
    mut v___y_5681_: *mut crate::leanh::LeanObject,
    mut v___y_5682_: *mut crate::leanh::LeanObject,
    mut v___y_5683_: *mut crate::leanh::LeanObject,
    mut v___y_5684_: *mut crate::leanh::LeanObject,
    mut v___y_5685_: *mut crate::leanh::LeanObject,
    mut v___y_5686_: *mut crate::leanh::LeanObject,
    mut v___y_5687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5689_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___redArg(v_a_5676_, v_numIndices_5677_, v_as_5678_, v_i_5679_, v___y_5681_, v___y_5682_, v___y_5683_, v___y_5684_, v___y_5685_, v___y_5686_, v___y_5687_);
    return v___x_5689_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5___boxed(
    mut v_a_5690_: *mut crate::leanh::LeanObject,
    mut v_numIndices_5691_: *mut crate::leanh::LeanObject,
    mut v_as_5692_: *mut crate::leanh::LeanObject,
    mut v_i_5693_: *mut crate::leanh::LeanObject,
    mut v_a_5694_: *mut crate::leanh::LeanObject,
    mut v___y_5695_: *mut crate::leanh::LeanObject,
    mut v___y_5696_: *mut crate::leanh::LeanObject,
    mut v___y_5697_: *mut crate::leanh::LeanObject,
    mut v___y_5698_: *mut crate::leanh::LeanObject,
    mut v___y_5699_: *mut crate::leanh::LeanObject,
    mut v___y_5700_: *mut crate::leanh::LeanObject,
    mut v___y_5701_: *mut crate::leanh::LeanObject,
    mut v___y_5702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5703_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f_spec__1_spec__1_spec__3_spec__5(v_a_5690_, v_numIndices_5691_, v_as_5692_, v_i_5693_, v_a_5694_, v___y_5695_, v___y_5696_, v___y_5697_, v___y_5698_, v___y_5699_, v___y_5700_, v___y_5701_);
    crate::leanh::lean_dec(v___y_5701_);
    crate::leanh::lean_dec_ref(v___y_5700_);
    crate::leanh::lean_dec(v___y_5699_);
    crate::leanh::lean_dec_ref(v___y_5698_);
    crate::leanh::lean_dec(v___y_5697_);
    crate::leanh::lean_dec_ref(v___y_5696_);
    crate::leanh::lean_dec(v___y_5695_);
    crate::leanh::lean_dec_ref(v_as_5692_);
    crate::leanh::lean_dec(v_numIndices_5691_);
    return v_res_5703_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5709_ = crate::leanh::lean_box(0);
    v___x_5710_ =
        l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__2;
    v___x_5711_ = l_Lean_mkConst(v___x_5710_, v___x_5709_);
    return v___x_5711_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27(
    mut v_numIndices_5715_: *mut crate::leanh::LeanObject,
    mut v_useDecideBool_5716_: u8,
    mut v_e_5717_: *mut crate::leanh::LeanObject,
    mut v_a_5718_: *mut crate::leanh::LeanObject,
    mut v_a_5719_: *mut crate::leanh::LeanObject,
    mut v_a_5720_: *mut crate::leanh::LeanObject,
    mut v_a_5721_: *mut crate::leanh::LeanObject,
    mut v_a_5722_: *mut crate::leanh::LeanObject,
    mut v_a_5723_: *mut crate::leanh::LeanObject,
    mut v_a_5724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5730_: u8 = 0;
    let mut v___x_5732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: u8 = 0;
    let mut v_arg_5738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: u8 = 0;
    let mut v_arg_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: u8 = 0;
    let mut v_arg_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: u8 = 0;
    let mut v_arg_5747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: u8 = 0;
    let mut v_arg_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: u8 = 0;
    let mut v___x_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5758_: u8 = 0;
    let mut v___x_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5763_: u8 = 0;
    let mut v___x_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5775_: u8 = 0;
    let mut v___x_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5781_: u8 = 0;
    let mut v_val_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5785_: u8 = 0;
    let mut v___x_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5797_: u8 = 0;
    let mut v___x_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5802_: u8 = 0;
    let mut v_expr_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: u8 = 0;
    let mut v___x_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5812_: u8 = 0;
    let mut v_a_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5816_: u8 = 0;
    let mut v___x_5817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5821_: u8 = 0;
    let mut v___x_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5834_: u8 = 0;
    let mut v_a_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5838_: u8 = 0;
    let mut v___x_5840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5842_: u8 = 0;
    let mut v_isSharedCheck_5843_: u8 = 0;
    let mut v___x_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5846_: u8 = 0;
    let mut v___x_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5854_: u8 = 0;
    let mut v_unused_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5857_: u8 = 0;
    let mut v_a_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5861_: u8 = 0;
    let mut v___x_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5865_: u8 = 0;
    let mut v___x_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5868_: u8 = 0;
    let mut v___x_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5877_: u8 = 0;
    let mut v_unused_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5880_: u8 = 0;
    let mut v_a_5881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5884_: u8 = 0;
    let mut v___x_5886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5888_: u8 = 0;
    let mut v_isSharedCheck_5889_: u8 = 0;
    let mut v_a_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5893_: u8 = 0;
    let mut v___x_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5897_: u8 = 0;
    let mut v_isSharedCheck_5898_: u8 = 0;
    let mut v_a_5899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5902_: u8 = 0;
    let mut v___x_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5906_: u8 = 0;
    let mut v_isSharedCheck_5907_: u8 = 0;
    let mut v_a_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5911_: u8 = 0;
    let mut v___x_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5915_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_5717_);
                v___x_5726_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_5717_, v_a_5722_);
                if crate::leanh::lean_obj_tag(v___x_5726_) == 0 {
                    v_a_5727_ = crate::leanh::lean_ctor_get(v___x_5726_, 0);
                    v_isSharedCheck_5907_ = (!crate::leanh::lean_is_exclusive(v___x_5726_)) as u8;
                    if v_isSharedCheck_5907_ == 0 {
                        v___x_5729_ = v___x_5726_;
                        v_isShared_5730_ = v_isSharedCheck_5907_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5727_);
                        crate::leanh::lean_dec(v___x_5726_);
                        v___x_5729_ = crate::leanh::lean_box(0);
                        v_isShared_5730_ = v_isSharedCheck_5907_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_5717_);
                    v_a_5908_ = crate::leanh::lean_ctor_get(v___x_5726_, 0);
                    v_isSharedCheck_5915_ = (!crate::leanh::lean_is_exclusive(v___x_5726_)) as u8;
                    if v_isSharedCheck_5915_ == 0 {
                        v___x_5910_ = v___x_5726_;
                        v_isShared_5911_ = v_isSharedCheck_5915_;
                        state = 34;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5908_);
                        crate::leanh::lean_dec(v___x_5726_);
                        v___x_5910_ = crate::leanh::lean_box(0);
                        v_isShared_5911_ = v_isSharedCheck_5915_;
                        state = 34;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5736_ = l_Lean_Expr_cleanupAnnotations(v_a_5727_);
                v___x_5737_ = l_Lean_Expr_isApp(v___x_5736_);
                if v___x_5737_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_5736_);
                    crate::leanh::lean_dec_ref(v_e_5717_);
                    state = 2;
                    continue;
                } else {
                    v_arg_5738_ = crate::leanh::lean_ctor_get(v___x_5736_, 1);
                    crate::leanh::lean_inc_ref(v_arg_5738_);
                    v___x_5739_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5736_);
                    v___x_5740_ = l_Lean_Expr_isApp(v___x_5739_);
                    if v___x_5740_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_5739_);
                        crate::leanh::lean_dec_ref(v_arg_5738_);
                        crate::leanh::lean_dec_ref(v_e_5717_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_5741_ = crate::leanh::lean_ctor_get(v___x_5739_, 1);
                        crate::leanh::lean_inc_ref(v_arg_5741_);
                        v___x_5742_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5739_);
                        v___x_5743_ = l_Lean_Expr_isApp(v___x_5742_);
                        if v___x_5743_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_5742_);
                            crate::leanh::lean_dec_ref(v_arg_5741_);
                            crate::leanh::lean_dec_ref(v_arg_5738_);
                            crate::leanh::lean_dec_ref(v_e_5717_);
                            state = 2;
                            continue;
                        } else {
                            v_arg_5744_ = crate::leanh::lean_ctor_get(v___x_5742_, 1);
                            crate::leanh::lean_inc_ref(v_arg_5744_);
                            v___x_5745_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5742_);
                            v___x_5746_ = l_Lean_Expr_isApp(v___x_5745_);
                            if v___x_5746_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_5745_);
                                crate::leanh::lean_dec_ref(v_arg_5744_);
                                crate::leanh::lean_dec_ref(v_arg_5741_);
                                crate::leanh::lean_dec_ref(v_arg_5738_);
                                crate::leanh::lean_dec_ref(v_e_5717_);
                                state = 2;
                                continue;
                            } else {
                                v_arg_5747_ = crate::leanh::lean_ctor_get(v___x_5745_, 1);
                                crate::leanh::lean_inc_ref(v_arg_5747_);
                                v___x_5748_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5745_);
                                v___x_5749_ = l_Lean_Expr_isApp(v___x_5748_);
                                if v___x_5749_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_5748_);
                                    crate::leanh::lean_dec_ref(v_arg_5747_);
                                    crate::leanh::lean_dec_ref(v_arg_5744_);
                                    crate::leanh::lean_dec_ref(v_arg_5741_);
                                    crate::leanh::lean_dec_ref(v_arg_5738_);
                                    crate::leanh::lean_dec_ref(v_e_5717_);
                                    state = 2;
                                    continue;
                                } else {
                                    v_arg_5750_ = crate::leanh::lean_ctor_get(v___x_5748_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_5750_);
                                    v___x_5751_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5748_);
                                    v___x_5752_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__2;
                                    v___x_5753_ = l_Lean_Expr_isConstOf(v___x_5751_, v___x_5752_);
                                    if v___x_5753_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_5751_);
                                        crate::leanh::lean_dec_ref(v_arg_5750_);
                                        crate::leanh::lean_dec_ref(v_arg_5747_);
                                        crate::leanh::lean_dec_ref(v_arg_5744_);
                                        crate::leanh::lean_dec_ref(v_arg_5741_);
                                        crate::leanh::lean_dec_ref(v_arg_5738_);
                                        crate::leanh::lean_dec_ref(v_e_5717_);
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_del_object(v___x_5729_);
                                        crate::leanh::lean_inc_ref(v_arg_5747_);
                                        v___x_5754_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_5715_, v_useDecideBool_5716_, v_arg_5747_, v_a_5718_, v_a_5719_, v_a_5720_, v_a_5721_, v_a_5722_, v_a_5723_, v_a_5724_);
                                        if crate::leanh::lean_obj_tag(v___x_5754_) == 0 {
                                            v_a_5755_ = crate::leanh::lean_ctor_get(v___x_5754_, 0);
                                            v_isSharedCheck_5898_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_5754_))
                                                    as u8;
                                            if v_isSharedCheck_5898_ == 0 {
                                                v___x_5757_ = v___x_5754_;
                                                v_isShared_5758_ = v_isSharedCheck_5898_;
                                                state = 4;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_5755_);
                                                crate::leanh::lean_dec(v___x_5754_);
                                                v___x_5757_ = crate::leanh::lean_box(0);
                                                v_isShared_5758_ = v_isSharedCheck_5898_;
                                                state = 4;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_5751_);
                                            crate::leanh::lean_dec_ref(v_arg_5750_);
                                            crate::leanh::lean_dec_ref(v_arg_5747_);
                                            crate::leanh::lean_dec_ref(v_arg_5744_);
                                            crate::leanh::lean_dec_ref(v_arg_5741_);
                                            crate::leanh::lean_dec_ref(v_arg_5738_);
                                            crate::leanh::lean_dec_ref(v_e_5717_);
                                            v_a_5899_ = crate::leanh::lean_ctor_get(v___x_5754_, 0);
                                            v_isSharedCheck_5906_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_5754_))
                                                    as u8;
                                            if v_isSharedCheck_5906_ == 0 {
                                                v___x_5901_ = v___x_5754_;
                                                v_isShared_5902_ = v_isSharedCheck_5906_;
                                                state = 32;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_5899_);
                                                crate::leanh::lean_dec(v___x_5754_);
                                                v___x_5901_ = crate::leanh::lean_box(0);
                                                v_isShared_5902_ = v_isSharedCheck_5906_;
                                                state = 32;
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
            2 => {
                v___x_5732_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__0;
                if v_isShared_5730_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5729_, 0, v___x_5732_);
                    v___x_5734_ = v___x_5729_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5735_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5735_, 0, v___x_5732_);
                    v___x_5734_ = v_reuseFailAlloc_5735_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5734_;
            }
            4 => {
                v___x_5759_ = l_Lean_Expr_constLevels_x21(v___x_5751_);
                if crate::leanh::lean_obj_tag(v_a_5755_) == 1 {
                    crate::leanh::lean_dec_ref(v___x_5751_);
                    crate::leanh::lean_dec_ref(v_e_5717_);
                    v_val_5760_ = crate::leanh::lean_ctor_get(v_a_5755_, 0);
                    v_isSharedCheck_5775_ = (!crate::leanh::lean_is_exclusive(v_a_5755_)) as u8;
                    if v_isSharedCheck_5775_ == 0 {
                        v___x_5762_ = v_a_5755_;
                        v_isShared_5763_ = v_isSharedCheck_5775_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5760_);
                        crate::leanh::lean_dec(v_a_5755_);
                        v___x_5762_ = crate::leanh::lean_box(0);
                        v_isShared_5763_ = v_isSharedCheck_5775_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5757_);
                    crate::leanh::lean_dec(v_a_5755_);
                    crate::leanh::lean_inc_ref(v_arg_5747_);
                    v___x_5776_ = l_Lean_mkNot(v_arg_5747_);
                    v___x_5777_ =
                        l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(
                            v_numIndices_5715_,
                            v_useDecideBool_5716_,
                            v___x_5776_,
                            v_a_5718_,
                            v_a_5719_,
                            v_a_5720_,
                            v_a_5721_,
                            v_a_5722_,
                            v_a_5723_,
                            v_a_5724_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_5777_) == 0 {
                        v_a_5778_ = crate::leanh::lean_ctor_get(v___x_5777_, 0);
                        v_isSharedCheck_5889_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5777_)) as u8;
                        if v_isSharedCheck_5889_ == 0 {
                            v___x_5780_ = v___x_5777_;
                            v_isShared_5781_ = v_isSharedCheck_5889_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5778_);
                            crate::leanh::lean_dec(v___x_5777_);
                            v___x_5780_ = crate::leanh::lean_box(0);
                            v_isShared_5781_ = v_isSharedCheck_5889_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5759_);
                        crate::leanh::lean_dec_ref(v___x_5751_);
                        crate::leanh::lean_dec_ref(v_arg_5750_);
                        crate::leanh::lean_dec_ref(v_arg_5747_);
                        crate::leanh::lean_dec_ref(v_arg_5744_);
                        crate::leanh::lean_dec_ref(v_arg_5741_);
                        crate::leanh::lean_dec_ref(v_arg_5738_);
                        crate::leanh::lean_dec_ref(v_e_5717_);
                        v_a_5890_ = crate::leanh::lean_ctor_get(v___x_5777_, 0);
                        v_isSharedCheck_5897_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5777_)) as u8;
                        if v_isSharedCheck_5897_ == 0 {
                            v___x_5892_ = v___x_5777_;
                            v_isShared_5893_ = v_isSharedCheck_5897_;
                            state = 30;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5890_);
                            crate::leanh::lean_dec(v___x_5777_);
                            v___x_5892_ = crate::leanh::lean_box(0);
                            v_isShared_5893_ = v_isSharedCheck_5897_;
                            state = 30;
                            continue;
                        }
                    }
                }
            }
            5 => {
                v___x_5764_ = l_Lean_Meta_SplitIf_getSimpContext___closed__7;
                v___x_5765_ = l_Lean_mkConst(v___x_5764_, v___x_5759_);
                crate::leanh::lean_inc_ref(v_arg_5741_);
                v___x_5766_ = l_Lean_mkApp6(
                    v___x_5765_,
                    v_arg_5747_,
                    v_arg_5744_,
                    v_val_5760_,
                    v_arg_5750_,
                    v_arg_5741_,
                    v_arg_5738_,
                );
                if v_isShared_5763_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5762_, 0, v___x_5766_);
                    v___x_5768_ = v___x_5762_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5774_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5774_, 0, v___x_5766_);
                    v___x_5768_ = v_reuseFailAlloc_5774_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5769_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5769_, 0, v_arg_5741_);
                crate::leanh::lean_ctor_set(v___x_5769_, 1, v___x_5768_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5769_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_5753_,
                );
                v___x_5770_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5770_, 0, v___x_5769_);
                if v_isShared_5758_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5757_, 0, v___x_5770_);
                    v___x_5772_ = v___x_5757_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5773_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5773_, 0, v___x_5770_);
                    v___x_5772_ = v_reuseFailAlloc_5773_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5772_;
            }
            8 => {
                if crate::leanh::lean_obj_tag(v_a_5778_) == 1 {
                    crate::leanh::lean_dec_ref(v___x_5751_);
                    crate::leanh::lean_dec_ref(v_e_5717_);
                    v_val_5782_ = crate::leanh::lean_ctor_get(v_a_5778_, 0);
                    v_isSharedCheck_5797_ = (!crate::leanh::lean_is_exclusive(v_a_5778_)) as u8;
                    if v_isSharedCheck_5797_ == 0 {
                        v___x_5784_ = v_a_5778_;
                        v_isShared_5785_ = v_isSharedCheck_5797_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5782_);
                        crate::leanh::lean_dec(v_a_5778_);
                        v___x_5784_ = crate::leanh::lean_box(0);
                        v_isShared_5785_ = v_isSharedCheck_5797_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5780_);
                    crate::leanh::lean_dec(v_a_5778_);
                    crate::leanh::lean_inc(v_a_5724_);
                    crate::leanh::lean_inc_ref(v_a_5723_);
                    crate::leanh::lean_inc(v_a_5722_);
                    crate::leanh::lean_inc_ref(v_a_5721_);
                    crate::leanh::lean_inc(v_a_5720_);
                    crate::leanh::lean_inc_ref(v_a_5719_);
                    crate::leanh::lean_inc(v_a_5718_);
                    crate::leanh::lean_inc_ref(v_arg_5747_);
                    v___x_5798_ = lean_simp(
                        v_arg_5747_,
                        v_a_5718_,
                        v_a_5719_,
                        v_a_5720_,
                        v_a_5721_,
                        v_a_5722_,
                        v_a_5723_,
                        v_a_5724_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5798_) == 0 {
                        v_a_5799_ = crate::leanh::lean_ctor_get(v___x_5798_, 0);
                        v_isSharedCheck_5880_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5798_)) as u8;
                        if v_isSharedCheck_5880_ == 0 {
                            v___x_5801_ = v___x_5798_;
                            v_isShared_5802_ = v_isSharedCheck_5880_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5799_);
                            crate::leanh::lean_dec(v___x_5798_);
                            v___x_5801_ = crate::leanh::lean_box(0);
                            v_isShared_5802_ = v_isSharedCheck_5880_;
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5759_);
                        crate::leanh::lean_dec_ref(v___x_5751_);
                        crate::leanh::lean_dec_ref(v_arg_5750_);
                        crate::leanh::lean_dec_ref(v_arg_5747_);
                        crate::leanh::lean_dec_ref(v_arg_5744_);
                        crate::leanh::lean_dec_ref(v_arg_5741_);
                        crate::leanh::lean_dec_ref(v_arg_5738_);
                        crate::leanh::lean_dec_ref(v_e_5717_);
                        v_a_5881_ = crate::leanh::lean_ctor_get(v___x_5798_, 0);
                        v_isSharedCheck_5888_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5798_)) as u8;
                        if v_isSharedCheck_5888_ == 0 {
                            v___x_5883_ = v___x_5798_;
                            v_isShared_5884_ = v_isSharedCheck_5888_;
                            state = 28;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5881_);
                            crate::leanh::lean_dec(v___x_5798_);
                            v___x_5883_ = crate::leanh::lean_box(0);
                            v_isShared_5884_ = v_isSharedCheck_5888_;
                            state = 28;
                            continue;
                        }
                    }
                }
            }
            9 => {
                v___x_5786_ = l_Lean_Meta_SplitIf_getSimpContext___closed__9;
                v___x_5787_ = l_Lean_mkConst(v___x_5786_, v___x_5759_);
                crate::leanh::lean_inc_ref(v_arg_5738_);
                v___x_5788_ = l_Lean_mkApp6(
                    v___x_5787_,
                    v_arg_5747_,
                    v_arg_5744_,
                    v_val_5782_,
                    v_arg_5750_,
                    v_arg_5741_,
                    v_arg_5738_,
                );
                if v_isShared_5785_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5784_, 0, v___x_5788_);
                    v___x_5790_ = v___x_5784_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5796_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5796_, 0, v___x_5788_);
                    v___x_5790_ = v_reuseFailAlloc_5796_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_5791_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5791_, 0, v_arg_5738_);
                crate::leanh::lean_ctor_set(v___x_5791_, 1, v___x_5790_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5791_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_5753_,
                );
                v___x_5792_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5792_, 0, v___x_5791_);
                if v_isShared_5781_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5780_, 0, v___x_5792_);
                    v___x_5794_ = v___x_5780_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5795_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5795_, 0, v___x_5792_);
                    v___x_5794_ = v_reuseFailAlloc_5795_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5794_;
            }
            12 => {
                v_expr_5803_ = crate::leanh::lean_ctor_get(v_a_5799_, 0);
                v___x_5804_ = lean_expr_eqv(v_expr_5803_, v_arg_5747_);
                if v___x_5804_ == 0 {
                    crate::leanh::lean_del_object(v___x_5801_);
                    v___x_5805_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3_once), _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3);
                    crate::leanh::lean_inc_ref(v_expr_5803_);
                    v___x_5806_ = l_Lean_Expr_app___override(v___x_5805_, v_expr_5803_);
                    v___x_5807_ = crate::leanh::lean_box(0);
                    v___x_5808_ = l_Lean_Meta_trySynthInstance(
                        v___x_5806_,
                        v___x_5807_,
                        v_a_5721_,
                        v_a_5722_,
                        v_a_5723_,
                        v_a_5724_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5808_) == 0 {
                        v_a_5809_ = crate::leanh::lean_ctor_get(v___x_5808_, 0);
                        v_isSharedCheck_5857_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5808_)) as u8;
                        if v_isSharedCheck_5857_ == 0 {
                            v___x_5811_ = v___x_5808_;
                            v_isShared_5812_ = v_isSharedCheck_5857_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5809_);
                            crate::leanh::lean_dec(v___x_5808_);
                            v___x_5811_ = crate::leanh::lean_box(0);
                            v_isShared_5812_ = v_isSharedCheck_5857_;
                            state = 13;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5799_);
                        crate::leanh::lean_dec(v___x_5759_);
                        crate::leanh::lean_dec_ref(v___x_5751_);
                        crate::leanh::lean_dec_ref(v_arg_5750_);
                        crate::leanh::lean_dec_ref(v_arg_5747_);
                        crate::leanh::lean_dec_ref(v_arg_5744_);
                        crate::leanh::lean_dec_ref(v_arg_5741_);
                        crate::leanh::lean_dec_ref(v_arg_5738_);
                        crate::leanh::lean_dec_ref(v_e_5717_);
                        v_a_5858_ = crate::leanh::lean_ctor_get(v___x_5808_, 0);
                        v_isSharedCheck_5865_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5808_)) as u8;
                        if v_isSharedCheck_5865_ == 0 {
                            v___x_5860_ = v___x_5808_;
                            v_isShared_5861_ = v_isSharedCheck_5865_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5858_);
                            crate::leanh::lean_dec(v___x_5808_);
                            v___x_5860_ = crate::leanh::lean_box(0);
                            v_isShared_5861_ = v_isSharedCheck_5865_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5759_);
                    crate::leanh::lean_dec_ref(v___x_5751_);
                    crate::leanh::lean_dec_ref(v_arg_5750_);
                    crate::leanh::lean_dec_ref(v_arg_5747_);
                    crate::leanh::lean_dec_ref(v_arg_5744_);
                    crate::leanh::lean_dec_ref(v_arg_5741_);
                    crate::leanh::lean_dec_ref(v_arg_5738_);
                    v_isSharedCheck_5877_ = (!crate::leanh::lean_is_exclusive(v_a_5799_)) as u8;
                    if v_isSharedCheck_5877_ == 0 {
                        v_unused_5878_ = crate::leanh::lean_ctor_get(v_a_5799_, 1);
                        crate::leanh::lean_dec(v_unused_5878_);
                        v_unused_5879_ = crate::leanh::lean_ctor_get(v_a_5799_, 0);
                        crate::leanh::lean_dec(v_unused_5879_);
                        v___x_5867_ = v_a_5799_;
                        v_isShared_5868_ = v_isSharedCheck_5877_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_5799_);
                        v___x_5867_ = crate::leanh::lean_box(0);
                        v_isShared_5868_ = v_isSharedCheck_5877_;
                        state = 25;
                        continue;
                    }
                }
            }
            13 => {
                if crate::leanh::lean_obj_tag(v_a_5809_) == 1 {
                    crate::leanh::lean_inc_ref(v_expr_5803_);
                    crate::leanh::lean_del_object(v___x_5811_);
                    crate::leanh::lean_dec_ref(v_e_5717_);
                    v_a_5813_ = crate::leanh::lean_ctor_get(v_a_5809_, 0);
                    v_isSharedCheck_5843_ = (!crate::leanh::lean_is_exclusive(v_a_5809_)) as u8;
                    if v_isSharedCheck_5843_ == 0 {
                        v___x_5815_ = v_a_5809_;
                        v_isShared_5816_ = v_isSharedCheck_5843_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5813_);
                        crate::leanh::lean_dec(v_a_5809_);
                        v___x_5815_ = crate::leanh::lean_box(0);
                        v_isShared_5816_ = v_isSharedCheck_5843_;
                        state = 14;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5809_);
                    crate::leanh::lean_dec(v___x_5759_);
                    crate::leanh::lean_dec_ref(v___x_5751_);
                    crate::leanh::lean_dec_ref(v_arg_5750_);
                    crate::leanh::lean_dec_ref(v_arg_5747_);
                    crate::leanh::lean_dec_ref(v_arg_5744_);
                    crate::leanh::lean_dec_ref(v_arg_5741_);
                    crate::leanh::lean_dec_ref(v_arg_5738_);
                    v_isSharedCheck_5854_ = (!crate::leanh::lean_is_exclusive(v_a_5799_)) as u8;
                    if v_isSharedCheck_5854_ == 0 {
                        v_unused_5855_ = crate::leanh::lean_ctor_get(v_a_5799_, 1);
                        crate::leanh::lean_dec(v_unused_5855_);
                        v_unused_5856_ = crate::leanh::lean_ctor_get(v_a_5799_, 0);
                        crate::leanh::lean_dec(v_unused_5856_);
                        v___x_5845_ = v_a_5799_;
                        v_isShared_5846_ = v_isSharedCheck_5854_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_5799_);
                        v___x_5845_ = crate::leanh::lean_box(0);
                        v_isShared_5846_ = v_isSharedCheck_5854_;
                        state = 20;
                        continue;
                    }
                }
            }
            14 => {
                v___x_5817_ = l_Lean_Meta_Simp_Result_getProof(
                    v_a_5799_, v_a_5721_, v_a_5722_, v_a_5723_, v_a_5724_,
                );
                if crate::leanh::lean_obj_tag(v___x_5817_) == 0 {
                    v_a_5818_ = crate::leanh::lean_ctor_get(v___x_5817_, 0);
                    v_isSharedCheck_5834_ = (!crate::leanh::lean_is_exclusive(v___x_5817_)) as u8;
                    if v_isSharedCheck_5834_ == 0 {
                        v___x_5820_ = v___x_5817_;
                        v_isShared_5821_ = v_isSharedCheck_5834_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5818_);
                        crate::leanh::lean_dec(v___x_5817_);
                        v___x_5820_ = crate::leanh::lean_box(0);
                        v_isShared_5821_ = v_isSharedCheck_5834_;
                        state = 15;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5815_);
                    crate::leanh::lean_dec(v_a_5813_);
                    crate::leanh::lean_dec_ref(v_expr_5803_);
                    crate::leanh::lean_dec(v___x_5759_);
                    crate::leanh::lean_dec_ref(v___x_5751_);
                    crate::leanh::lean_dec_ref(v_arg_5750_);
                    crate::leanh::lean_dec_ref(v_arg_5747_);
                    crate::leanh::lean_dec_ref(v_arg_5744_);
                    crate::leanh::lean_dec_ref(v_arg_5741_);
                    crate::leanh::lean_dec_ref(v_arg_5738_);
                    v_a_5835_ = crate::leanh::lean_ctor_get(v___x_5817_, 0);
                    v_isSharedCheck_5842_ = (!crate::leanh::lean_is_exclusive(v___x_5817_)) as u8;
                    if v_isSharedCheck_5842_ == 0 {
                        v___x_5837_ = v___x_5817_;
                        v_isShared_5838_ = v_isSharedCheck_5842_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5835_);
                        crate::leanh::lean_dec(v___x_5817_);
                        v___x_5837_ = crate::leanh::lean_box(0);
                        v_isShared_5838_ = v_isSharedCheck_5842_;
                        state = 18;
                        continue;
                    }
                }
            }
            15 => {
                v___x_5822_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__5;
                v___x_5823_ = l_Lean_mkConst(v___x_5822_, v___x_5759_);
                crate::leanh::lean_inc_ref(v_arg_5738_);
                crate::leanh::lean_inc_ref(v_arg_5741_);
                crate::leanh::lean_inc(v_a_5813_);
                crate::leanh::lean_inc_ref(v_expr_5803_);
                crate::leanh::lean_inc_ref(v_arg_5750_);
                v___x_5824_ = l_Lean_mkApp8(
                    v___x_5823_,
                    v_arg_5750_,
                    v_arg_5747_,
                    v_expr_5803_,
                    v_arg_5744_,
                    v_a_5813_,
                    v_arg_5741_,
                    v_arg_5738_,
                    v_a_5818_,
                );
                v___x_5825_ = l_Lean_mkApp5(
                    v___x_5751_,
                    v_arg_5750_,
                    v_expr_5803_,
                    v_a_5813_,
                    v_arg_5741_,
                    v_arg_5738_,
                );
                if v_isShared_5816_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5815_, 0, v___x_5824_);
                    v___x_5827_ = v___x_5815_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5833_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5833_, 0, v___x_5824_);
                    v___x_5827_ = v_reuseFailAlloc_5833_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_5828_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5828_, 0, v___x_5825_);
                crate::leanh::lean_ctor_set(v___x_5828_, 1, v___x_5827_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5828_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_5753_,
                );
                v___x_5829_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5829_, 0, v___x_5828_);
                if v_isShared_5821_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5820_, 0, v___x_5829_);
                    v___x_5831_ = v___x_5820_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5832_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5832_, 0, v___x_5829_);
                    v___x_5831_ = v_reuseFailAlloc_5832_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_5831_;
            }
            18 => {
                if v_isShared_5838_ == 0 {
                    v___x_5840_ = v___x_5837_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5841_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5841_, 0, v_a_5835_);
                    v___x_5840_ = v_reuseFailAlloc_5841_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_5840_;
            }
            20 => {
                if v_isShared_5846_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5845_, 1, v___x_5807_);
                    crate::leanh::lean_ctor_set(v___x_5845_, 0, v_e_5717_);
                    v___x_5848_ = v___x_5845_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5853_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5853_, 0, v_e_5717_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5853_, 1, v___x_5807_);
                    v___x_5848_ = v_reuseFailAlloc_5853_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5848_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_5753_,
                );
                v___x_5849_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5849_, 0, v___x_5848_);
                if v_isShared_5812_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5811_, 0, v___x_5849_);
                    v___x_5851_ = v___x_5811_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5852_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5852_, 0, v___x_5849_);
                    v___x_5851_ = v_reuseFailAlloc_5852_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5851_;
            }
            23 => {
                if v_isShared_5861_ == 0 {
                    v___x_5863_ = v___x_5860_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5864_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5864_, 0, v_a_5858_);
                    v___x_5863_ = v_reuseFailAlloc_5864_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5863_;
            }
            25 => {
                v___x_5869_ = crate::leanh::lean_box(0);
                if v_isShared_5868_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5867_, 1, v___x_5869_);
                    crate::leanh::lean_ctor_set(v___x_5867_, 0, v_e_5717_);
                    v___x_5871_ = v___x_5867_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5876_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5876_, 0, v_e_5717_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5876_, 1, v___x_5869_);
                    v___x_5871_ = v_reuseFailAlloc_5876_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5871_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_5753_,
                );
                v___x_5872_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5872_, 0, v___x_5871_);
                if v_isShared_5802_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5801_, 0, v___x_5872_);
                    v___x_5874_ = v___x_5801_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_5875_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5875_, 0, v___x_5872_);
                    v___x_5874_ = v_reuseFailAlloc_5875_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_5874_;
            }
            28 => {
                if v_isShared_5884_ == 0 {
                    v___x_5886_ = v___x_5883_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_5887_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5887_, 0, v_a_5881_);
                    v___x_5886_ = v_reuseFailAlloc_5887_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_5886_;
            }
            30 => {
                if v_isShared_5893_ == 0 {
                    v___x_5895_ = v___x_5892_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_5896_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5896_, 0, v_a_5890_);
                    v___x_5895_ = v_reuseFailAlloc_5896_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_5895_;
            }
            32 => {
                if v_isShared_5902_ == 0 {
                    v___x_5904_ = v___x_5901_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_5905_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5905_, 0, v_a_5899_);
                    v___x_5904_ = v_reuseFailAlloc_5905_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_5904_;
            }
            34 => {
                if v_isShared_5911_ == 0 {
                    v___x_5913_ = v___x_5910_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_5914_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5914_, 0, v_a_5908_);
                    v___x_5913_ = v_reuseFailAlloc_5914_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_5913_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___boxed(
    mut v_numIndices_5916_: *mut crate::leanh::LeanObject,
    mut v_useDecideBool_5917_: *mut crate::leanh::LeanObject,
    mut v_e_5918_: *mut crate::leanh::LeanObject,
    mut v_a_5919_: *mut crate::leanh::LeanObject,
    mut v_a_5920_: *mut crate::leanh::LeanObject,
    mut v_a_5921_: *mut crate::leanh::LeanObject,
    mut v_a_5922_: *mut crate::leanh::LeanObject,
    mut v_a_5923_: *mut crate::leanh::LeanObject,
    mut v_a_5924_: *mut crate::leanh::LeanObject,
    mut v_a_5925_: *mut crate::leanh::LeanObject,
    mut v_a_5926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useDecideBool_boxed_5927_: u8 = 0;
    let mut v_res_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useDecideBool_boxed_5927_ = (crate::leanh::lean_unbox(v_useDecideBool_5917_) as u8);
    v_res_5928_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27(
        v_numIndices_5916_,
        v_useDecideBool_boxed_5927_,
        v_e_5918_,
        v_a_5919_,
        v_a_5920_,
        v_a_5921_,
        v_a_5922_,
        v_a_5923_,
        v_a_5924_,
        v_a_5925_,
    );
    crate::leanh::lean_dec(v_a_5925_);
    crate::leanh::lean_dec_ref(v_a_5924_);
    crate::leanh::lean_dec(v_a_5923_);
    crate::leanh::lean_dec_ref(v_a_5922_);
    crate::leanh::lean_dec(v_a_5921_);
    crate::leanh::lean_dec_ref(v_a_5920_);
    crate::leanh::lean_dec(v_a_5919_);
    crate::leanh::lean_dec(v_numIndices_5916_);
    return v_res_5928_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(
    mut v_e_5932_: *mut crate::leanh::LeanObject,
    mut v_a_5933_: *mut crate::leanh::LeanObject,
    mut v_a_5934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_5932_) == 6 {
        let mut v_binderName_5936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_binderName_5936_ = crate::leanh::lean_ctor_get(v_e_5932_, 0);
        crate::leanh::lean_inc(v_binderName_5936_);
        v___x_5937_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5937_, 0, v_binderName_5936_);
        return v___x_5937_;
    } else {
        let mut v___x_5938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5938_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__1;
        v___x_5939_ = l_Lean_Core_mkFreshUserName(v___x_5938_, v_a_5933_, v_a_5934_);
        return v___x_5939_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___boxed(
    mut v_e_5940_: *mut crate::leanh::LeanObject,
    mut v_a_5941_: *mut crate::leanh::LeanObject,
    mut v_a_5942_: *mut crate::leanh::LeanObject,
    mut v_a_5943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5944_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(
        v_e_5940_, v_a_5941_, v_a_5942_,
    );
    crate::leanh::lean_dec(v_a_5942_);
    crate::leanh::lean_dec_ref(v_a_5941_);
    crate::leanh::lean_dec_ref(v_e_5940_);
    return v_res_5944_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName(
    mut v_e_5945_: *mut crate::leanh::LeanObject,
    mut v_a_5946_: *mut crate::leanh::LeanObject,
    mut v_a_5947_: *mut crate::leanh::LeanObject,
    mut v_a_5948_: *mut crate::leanh::LeanObject,
    mut v_a_5949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5951_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(
        v_e_5945_, v_a_5948_, v_a_5949_,
    );
    return v___x_5951_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___boxed(
    mut v_e_5952_: *mut crate::leanh::LeanObject,
    mut v_a_5953_: *mut crate::leanh::LeanObject,
    mut v_a_5954_: *mut crate::leanh::LeanObject,
    mut v_a_5955_: *mut crate::leanh::LeanObject,
    mut v_a_5956_: *mut crate::leanh::LeanObject,
    mut v_a_5957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5958_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName(
        v_e_5952_, v_a_5953_, v_a_5954_, v_a_5955_, v_a_5956_,
    );
    crate::leanh::lean_dec(v_a_5956_);
    crate::leanh::lean_dec_ref(v_a_5955_);
    crate::leanh::lean_dec(v_a_5954_);
    crate::leanh::lean_dec_ref(v_a_5953_);
    crate::leanh::lean_dec_ref(v_e_5952_);
    return v_res_5958_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5964_ = crate::leanh::lean_box(0);
    v___x_5965_ =
        l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__2;
    v___x_5966_ = l_Lean_mkConst(v___x_5965_, v___x_5964_);
    return v___x_5966_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5967_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5968_ = l_Lean_mkBVar(v___x_5967_);
    return v___x_5968_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5973_ = crate::leanh::lean_box(0);
    v___x_5974_ =
        l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__6;
    v___x_5975_ = l_Lean_mkConst(v___x_5974_, v___x_5973_);
    return v___x_5975_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27(
    mut v_numIndices_5979_: *mut crate::leanh::LeanObject,
    mut v_useDecideBool_5980_: u8,
    mut v_e_5981_: *mut crate::leanh::LeanObject,
    mut v_a_5982_: *mut crate::leanh::LeanObject,
    mut v_a_5983_: *mut crate::leanh::LeanObject,
    mut v_a_5984_: *mut crate::leanh::LeanObject,
    mut v_a_5985_: *mut crate::leanh::LeanObject,
    mut v_a_5986_: *mut crate::leanh::LeanObject,
    mut v_a_5987_: *mut crate::leanh::LeanObject,
    mut v_a_5988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5994_: u8 = 0;
    let mut v___x_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: u8 = 0;
    let mut v_arg_6002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: u8 = 0;
    let mut v_arg_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: u8 = 0;
    let mut v_arg_6008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: u8 = 0;
    let mut v_arg_6011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: u8 = 0;
    let mut v_arg_6014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: u8 = 0;
    let mut v___x_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6022_: u8 = 0;
    let mut v___x_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6027_: u8 = 0;
    let mut v___x_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6041_: u8 = 0;
    let mut v___x_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6047_: u8 = 0;
    let mut v_val_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6051_: u8 = 0;
    let mut v___x_6052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6065_: u8 = 0;
    let mut v___x_6066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6070_: u8 = 0;
    let mut v_expr_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: u8 = 0;
    let mut v___x_6073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6082_: u8 = 0;
    let mut v_a_6083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6086_: u8 = 0;
    let mut v___x_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6093_: u8 = 0;
    let mut v___x_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: u8 = 0;
    let mut v___x_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6119_: u8 = 0;
    let mut v_a_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6123_: u8 = 0;
    let mut v___x_6125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6127_: u8 = 0;
    let mut v_a_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6131_: u8 = 0;
    let mut v___x_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6135_: u8 = 0;
    let mut v_isSharedCheck_6136_: u8 = 0;
    let mut v___x_6137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6142_: u8 = 0;
    let mut v_a_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6146_: u8 = 0;
    let mut v___x_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6150_: u8 = 0;
    let mut v_a_6151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6154_: u8 = 0;
    let mut v___x_6156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6158_: u8 = 0;
    let mut v___x_6160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6161_: u8 = 0;
    let mut v___x_6162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6170_: u8 = 0;
    let mut v_unused_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6173_: u8 = 0;
    let mut v_a_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6177_: u8 = 0;
    let mut v___x_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6181_: u8 = 0;
    let mut v_isSharedCheck_6182_: u8 = 0;
    let mut v_a_6183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6186_: u8 = 0;
    let mut v___x_6188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6190_: u8 = 0;
    let mut v_isSharedCheck_6191_: u8 = 0;
    let mut v_a_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6195_: u8 = 0;
    let mut v___x_6197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6199_: u8 = 0;
    let mut v_isSharedCheck_6200_: u8 = 0;
    let mut v_a_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6204_: u8 = 0;
    let mut v___x_6206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6208_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_5981_);
                v___x_5990_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_5981_, v_a_5986_);
                if crate::leanh::lean_obj_tag(v___x_5990_) == 0 {
                    v_a_5991_ = crate::leanh::lean_ctor_get(v___x_5990_, 0);
                    v_isSharedCheck_6200_ = (!crate::leanh::lean_is_exclusive(v___x_5990_)) as u8;
                    if v_isSharedCheck_6200_ == 0 {
                        v___x_5993_ = v___x_5990_;
                        v_isShared_5994_ = v_isSharedCheck_6200_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5991_);
                        crate::leanh::lean_dec(v___x_5990_);
                        v___x_5993_ = crate::leanh::lean_box(0);
                        v_isShared_5994_ = v_isSharedCheck_6200_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_5981_);
                    v_a_6201_ = crate::leanh::lean_ctor_get(v___x_5990_, 0);
                    v_isSharedCheck_6208_ = (!crate::leanh::lean_is_exclusive(v___x_5990_)) as u8;
                    if v_isSharedCheck_6208_ == 0 {
                        v___x_6203_ = v___x_5990_;
                        v_isShared_6204_ = v_isSharedCheck_6208_;
                        state = 36;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6201_);
                        crate::leanh::lean_dec(v___x_5990_);
                        v___x_6203_ = crate::leanh::lean_box(0);
                        v_isShared_6204_ = v_isSharedCheck_6208_;
                        state = 36;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6000_ = l_Lean_Expr_cleanupAnnotations(v_a_5991_);
                v___x_6001_ = l_Lean_Expr_isApp(v___x_6000_);
                if v___x_6001_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_6000_);
                    crate::leanh::lean_dec_ref(v_e_5981_);
                    state = 2;
                    continue;
                } else {
                    v_arg_6002_ = crate::leanh::lean_ctor_get(v___x_6000_, 1);
                    crate::leanh::lean_inc_ref(v_arg_6002_);
                    v___x_6003_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6000_);
                    v___x_6004_ = l_Lean_Expr_isApp(v___x_6003_);
                    if v___x_6004_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_6003_);
                        crate::leanh::lean_dec_ref(v_arg_6002_);
                        crate::leanh::lean_dec_ref(v_e_5981_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_6005_ = crate::leanh::lean_ctor_get(v___x_6003_, 1);
                        crate::leanh::lean_inc_ref(v_arg_6005_);
                        v___x_6006_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6003_);
                        v___x_6007_ = l_Lean_Expr_isApp(v___x_6006_);
                        if v___x_6007_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_6006_);
                            crate::leanh::lean_dec_ref(v_arg_6005_);
                            crate::leanh::lean_dec_ref(v_arg_6002_);
                            crate::leanh::lean_dec_ref(v_e_5981_);
                            state = 2;
                            continue;
                        } else {
                            v_arg_6008_ = crate::leanh::lean_ctor_get(v___x_6006_, 1);
                            crate::leanh::lean_inc_ref(v_arg_6008_);
                            v___x_6009_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6006_);
                            v___x_6010_ = l_Lean_Expr_isApp(v___x_6009_);
                            if v___x_6010_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_6009_);
                                crate::leanh::lean_dec_ref(v_arg_6008_);
                                crate::leanh::lean_dec_ref(v_arg_6005_);
                                crate::leanh::lean_dec_ref(v_arg_6002_);
                                crate::leanh::lean_dec_ref(v_e_5981_);
                                state = 2;
                                continue;
                            } else {
                                v_arg_6011_ = crate::leanh::lean_ctor_get(v___x_6009_, 1);
                                crate::leanh::lean_inc_ref(v_arg_6011_);
                                v___x_6012_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6009_);
                                v___x_6013_ = l_Lean_Expr_isApp(v___x_6012_);
                                if v___x_6013_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_6012_);
                                    crate::leanh::lean_dec_ref(v_arg_6011_);
                                    crate::leanh::lean_dec_ref(v_arg_6008_);
                                    crate::leanh::lean_dec_ref(v_arg_6005_);
                                    crate::leanh::lean_dec_ref(v_arg_6002_);
                                    crate::leanh::lean_dec_ref(v_e_5981_);
                                    state = 2;
                                    continue;
                                } else {
                                    v_arg_6014_ = crate::leanh::lean_ctor_get(v___x_6012_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_6014_);
                                    v___x_6015_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6012_);
                                    v___x_6016_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_FindSplitImpl_isCandidate_x3f___closed__4;
                                    v___x_6017_ = l_Lean_Expr_isConstOf(v___x_6015_, v___x_6016_);
                                    if v___x_6017_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_6015_);
                                        crate::leanh::lean_dec_ref(v_arg_6014_);
                                        crate::leanh::lean_dec_ref(v_arg_6011_);
                                        crate::leanh::lean_dec_ref(v_arg_6008_);
                                        crate::leanh::lean_dec_ref(v_arg_6005_);
                                        crate::leanh::lean_dec_ref(v_arg_6002_);
                                        crate::leanh::lean_dec_ref(v_e_5981_);
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_del_object(v___x_5993_);
                                        crate::leanh::lean_inc_ref(v_arg_6011_);
                                        v___x_6018_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(v_numIndices_5979_, v_useDecideBool_5980_, v_arg_6011_, v_a_5982_, v_a_5983_, v_a_5984_, v_a_5985_, v_a_5986_, v_a_5987_, v_a_5988_);
                                        if crate::leanh::lean_obj_tag(v___x_6018_) == 0 {
                                            v_a_6019_ = crate::leanh::lean_ctor_get(v___x_6018_, 0);
                                            v_isSharedCheck_6191_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_6018_))
                                                    as u8;
                                            if v_isSharedCheck_6191_ == 0 {
                                                v___x_6021_ = v___x_6018_;
                                                v_isShared_6022_ = v_isSharedCheck_6191_;
                                                state = 4;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_6019_);
                                                crate::leanh::lean_dec(v___x_6018_);
                                                v___x_6021_ = crate::leanh::lean_box(0);
                                                v_isShared_6022_ = v_isSharedCheck_6191_;
                                                state = 4;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_6015_);
                                            crate::leanh::lean_dec_ref(v_arg_6014_);
                                            crate::leanh::lean_dec_ref(v_arg_6011_);
                                            crate::leanh::lean_dec_ref(v_arg_6008_);
                                            crate::leanh::lean_dec_ref(v_arg_6005_);
                                            crate::leanh::lean_dec_ref(v_arg_6002_);
                                            crate::leanh::lean_dec_ref(v_e_5981_);
                                            v_a_6192_ = crate::leanh::lean_ctor_get(v___x_6018_, 0);
                                            v_isSharedCheck_6199_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_6018_))
                                                    as u8;
                                            if v_isSharedCheck_6199_ == 0 {
                                                v___x_6194_ = v___x_6018_;
                                                v_isShared_6195_ = v_isSharedCheck_6199_;
                                                state = 34;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_6192_);
                                                crate::leanh::lean_dec(v___x_6018_);
                                                v___x_6194_ = crate::leanh::lean_box(0);
                                                v_isShared_6195_ = v_isSharedCheck_6199_;
                                                state = 34;
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
            2 => {
                v___x_5996_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__0;
                if v_isShared_5994_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5993_, 0, v___x_5996_);
                    v___x_5998_ = v___x_5993_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5999_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5999_, 0, v___x_5996_);
                    v___x_5998_ = v_reuseFailAlloc_5999_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5998_;
            }
            4 => {
                v___x_6023_ = l_Lean_Expr_constLevels_x21(v___x_6015_);
                if crate::leanh::lean_obj_tag(v_a_6019_) == 1 {
                    crate::leanh::lean_dec_ref(v___x_6015_);
                    crate::leanh::lean_dec_ref(v_e_5981_);
                    v_val_6024_ = crate::leanh::lean_ctor_get(v_a_6019_, 0);
                    v_isSharedCheck_6041_ = (!crate::leanh::lean_is_exclusive(v_a_6019_)) as u8;
                    if v_isSharedCheck_6041_ == 0 {
                        v___x_6026_ = v_a_6019_;
                        v_isShared_6027_ = v_isSharedCheck_6041_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_6024_);
                        crate::leanh::lean_dec(v_a_6019_);
                        v___x_6026_ = crate::leanh::lean_box(0);
                        v_isShared_6027_ = v_isSharedCheck_6041_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6021_);
                    crate::leanh::lean_dec(v_a_6019_);
                    crate::leanh::lean_inc_ref(v_arg_6011_);
                    v___x_6042_ = l_Lean_mkNot(v_arg_6011_);
                    v___x_6043_ =
                        l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f(
                            v_numIndices_5979_,
                            v_useDecideBool_5980_,
                            v___x_6042_,
                            v_a_5982_,
                            v_a_5983_,
                            v_a_5984_,
                            v_a_5985_,
                            v_a_5986_,
                            v_a_5987_,
                            v_a_5988_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_6043_) == 0 {
                        v_a_6044_ = crate::leanh::lean_ctor_get(v___x_6043_, 0);
                        v_isSharedCheck_6182_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6043_)) as u8;
                        if v_isSharedCheck_6182_ == 0 {
                            v___x_6046_ = v___x_6043_;
                            v_isShared_6047_ = v_isSharedCheck_6182_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6044_);
                            crate::leanh::lean_dec(v___x_6043_);
                            v___x_6046_ = crate::leanh::lean_box(0);
                            v_isShared_6047_ = v_isSharedCheck_6182_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_6023_);
                        crate::leanh::lean_dec_ref(v___x_6015_);
                        crate::leanh::lean_dec_ref(v_arg_6014_);
                        crate::leanh::lean_dec_ref(v_arg_6011_);
                        crate::leanh::lean_dec_ref(v_arg_6008_);
                        crate::leanh::lean_dec_ref(v_arg_6005_);
                        crate::leanh::lean_dec_ref(v_arg_6002_);
                        crate::leanh::lean_dec_ref(v_e_5981_);
                        v_a_6183_ = crate::leanh::lean_ctor_get(v___x_6043_, 0);
                        v_isSharedCheck_6190_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6043_)) as u8;
                        if v_isSharedCheck_6190_ == 0 {
                            v___x_6185_ = v___x_6043_;
                            v_isShared_6186_ = v_isSharedCheck_6190_;
                            state = 32;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6183_);
                            crate::leanh::lean_dec(v___x_6043_);
                            v___x_6185_ = crate::leanh::lean_box(0);
                            v_isShared_6186_ = v_isSharedCheck_6190_;
                            state = 32;
                            continue;
                        }
                    }
                }
            }
            5 => {
                crate::leanh::lean_inc(v_val_6024_);
                crate::leanh::lean_inc_ref(v_arg_6005_);
                v___x_6028_ = l_Lean_Expr_app___override(v_arg_6005_, v_val_6024_);
                v___x_6029_ = l_Lean_Expr_headBeta(v___x_6028_);
                v___x_6030_ = l_Lean_Meta_SplitIf_getSimpContext___closed__11;
                v___x_6031_ = l_Lean_mkConst(v___x_6030_, v___x_6023_);
                v___x_6032_ = l_Lean_mkApp6(
                    v___x_6031_,
                    v_arg_6011_,
                    v_arg_6008_,
                    v_val_6024_,
                    v_arg_6014_,
                    v_arg_6005_,
                    v_arg_6002_,
                );
                if v_isShared_6027_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6026_, 0, v___x_6032_);
                    v___x_6034_ = v___x_6026_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6040_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6040_, 0, v___x_6032_);
                    v___x_6034_ = v_reuseFailAlloc_6040_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_6035_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_6035_, 0, v___x_6029_);
                crate::leanh::lean_ctor_set(v___x_6035_, 1, v___x_6034_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6035_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_6017_,
                );
                v___x_6036_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6036_, 0, v___x_6035_);
                if v_isShared_6022_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6021_, 0, v___x_6036_);
                    v___x_6038_ = v___x_6021_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6039_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6039_, 0, v___x_6036_);
                    v___x_6038_ = v_reuseFailAlloc_6039_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6038_;
            }
            8 => {
                if crate::leanh::lean_obj_tag(v_a_6044_) == 1 {
                    crate::leanh::lean_dec_ref(v___x_6015_);
                    crate::leanh::lean_dec_ref(v_e_5981_);
                    v_val_6048_ = crate::leanh::lean_ctor_get(v_a_6044_, 0);
                    v_isSharedCheck_6065_ = (!crate::leanh::lean_is_exclusive(v_a_6044_)) as u8;
                    if v_isSharedCheck_6065_ == 0 {
                        v___x_6050_ = v_a_6044_;
                        v_isShared_6051_ = v_isSharedCheck_6065_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_6048_);
                        crate::leanh::lean_dec(v_a_6044_);
                        v___x_6050_ = crate::leanh::lean_box(0);
                        v_isShared_6051_ = v_isSharedCheck_6065_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6046_);
                    crate::leanh::lean_dec(v_a_6044_);
                    crate::leanh::lean_inc(v_a_5988_);
                    crate::leanh::lean_inc_ref(v_a_5987_);
                    crate::leanh::lean_inc(v_a_5986_);
                    crate::leanh::lean_inc_ref(v_a_5985_);
                    crate::leanh::lean_inc(v_a_5984_);
                    crate::leanh::lean_inc_ref(v_a_5983_);
                    crate::leanh::lean_inc(v_a_5982_);
                    crate::leanh::lean_inc_ref(v_arg_6011_);
                    v___x_6066_ = lean_simp(
                        v_arg_6011_,
                        v_a_5982_,
                        v_a_5983_,
                        v_a_5984_,
                        v_a_5985_,
                        v_a_5986_,
                        v_a_5987_,
                        v_a_5988_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6066_) == 0 {
                        v_a_6067_ = crate::leanh::lean_ctor_get(v___x_6066_, 0);
                        v_isSharedCheck_6173_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6066_)) as u8;
                        if v_isSharedCheck_6173_ == 0 {
                            v___x_6069_ = v___x_6066_;
                            v_isShared_6070_ = v_isSharedCheck_6173_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6067_);
                            crate::leanh::lean_dec(v___x_6066_);
                            v___x_6069_ = crate::leanh::lean_box(0);
                            v_isShared_6070_ = v_isSharedCheck_6173_;
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_6023_);
                        crate::leanh::lean_dec_ref(v___x_6015_);
                        crate::leanh::lean_dec_ref(v_arg_6014_);
                        crate::leanh::lean_dec_ref(v_arg_6011_);
                        crate::leanh::lean_dec_ref(v_arg_6008_);
                        crate::leanh::lean_dec_ref(v_arg_6005_);
                        crate::leanh::lean_dec_ref(v_arg_6002_);
                        crate::leanh::lean_dec_ref(v_e_5981_);
                        v_a_6174_ = crate::leanh::lean_ctor_get(v___x_6066_, 0);
                        v_isSharedCheck_6181_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6066_)) as u8;
                        if v_isSharedCheck_6181_ == 0 {
                            v___x_6176_ = v___x_6066_;
                            v_isShared_6177_ = v_isSharedCheck_6181_;
                            state = 30;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6174_);
                            crate::leanh::lean_dec(v___x_6066_);
                            v___x_6176_ = crate::leanh::lean_box(0);
                            v_isShared_6177_ = v_isSharedCheck_6181_;
                            state = 30;
                            continue;
                        }
                    }
                }
            }
            9 => {
                crate::leanh::lean_inc(v_val_6048_);
                crate::leanh::lean_inc_ref(v_arg_6002_);
                v___x_6052_ = l_Lean_Expr_app___override(v_arg_6002_, v_val_6048_);
                v___x_6053_ = l_Lean_Expr_headBeta(v___x_6052_);
                v___x_6054_ = l_Lean_Meta_SplitIf_getSimpContext___closed__13;
                v___x_6055_ = l_Lean_mkConst(v___x_6054_, v___x_6023_);
                v___x_6056_ = l_Lean_mkApp6(
                    v___x_6055_,
                    v_arg_6011_,
                    v_arg_6008_,
                    v_val_6048_,
                    v_arg_6014_,
                    v_arg_6005_,
                    v_arg_6002_,
                );
                if v_isShared_6051_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6050_, 0, v___x_6056_);
                    v___x_6058_ = v___x_6050_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6064_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6064_, 0, v___x_6056_);
                    v___x_6058_ = v_reuseFailAlloc_6064_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_6059_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_6059_, 0, v___x_6053_);
                crate::leanh::lean_ctor_set(v___x_6059_, 1, v___x_6058_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6059_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_6017_,
                );
                v___x_6060_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6060_, 0, v___x_6059_);
                if v_isShared_6047_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6046_, 0, v___x_6060_);
                    v___x_6062_ = v___x_6046_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6063_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6063_, 0, v___x_6060_);
                    v___x_6062_ = v_reuseFailAlloc_6063_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6062_;
            }
            12 => {
                v_expr_6071_ = crate::leanh::lean_ctor_get(v_a_6067_, 0);
                v___x_6072_ = lean_expr_eqv(v_expr_6071_, v_arg_6011_);
                if v___x_6072_ == 0 {
                    crate::leanh::lean_inc_ref(v_expr_6071_);
                    crate::leanh::lean_del_object(v___x_6069_);
                    v___x_6073_ = l_Lean_Meta_Simp_Result_getProof(
                        v_a_6067_, v_a_5985_, v_a_5986_, v_a_5987_, v_a_5988_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6073_) == 0 {
                        v_a_6074_ = crate::leanh::lean_ctor_get(v___x_6073_, 0);
                        crate::leanh::lean_inc(v_a_6074_);
                        crate::leanh::lean_dec_ref_known(v___x_6073_, 1);
                        v___x_6075_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3_once), _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___closed__3);
                        crate::leanh::lean_inc_ref(v_expr_6071_);
                        v___x_6076_ = l_Lean_Expr_app___override(v___x_6075_, v_expr_6071_);
                        v___x_6077_ = crate::leanh::lean_box(0);
                        v___x_6078_ = l_Lean_Meta_trySynthInstance(
                            v___x_6076_,
                            v___x_6077_,
                            v_a_5985_,
                            v_a_5986_,
                            v_a_5987_,
                            v_a_5988_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6078_) == 0 {
                            v_a_6079_ = crate::leanh::lean_ctor_get(v___x_6078_, 0);
                            v_isSharedCheck_6142_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6078_)) as u8;
                            if v_isSharedCheck_6142_ == 0 {
                                v___x_6081_ = v___x_6078_;
                                v_isShared_6082_ = v_isSharedCheck_6142_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6079_);
                                crate::leanh::lean_dec(v___x_6078_);
                                v___x_6081_ = crate::leanh::lean_box(0);
                                v_isShared_6082_ = v_isSharedCheck_6142_;
                                state = 13;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_6074_);
                            crate::leanh::lean_dec_ref(v_expr_6071_);
                            crate::leanh::lean_dec(v___x_6023_);
                            crate::leanh::lean_dec_ref(v___x_6015_);
                            crate::leanh::lean_dec_ref(v_arg_6014_);
                            crate::leanh::lean_dec_ref(v_arg_6011_);
                            crate::leanh::lean_dec_ref(v_arg_6008_);
                            crate::leanh::lean_dec_ref(v_arg_6005_);
                            crate::leanh::lean_dec_ref(v_arg_6002_);
                            crate::leanh::lean_dec_ref(v_e_5981_);
                            v_a_6143_ = crate::leanh::lean_ctor_get(v___x_6078_, 0);
                            v_isSharedCheck_6150_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6078_)) as u8;
                            if v_isSharedCheck_6150_ == 0 {
                                v___x_6145_ = v___x_6078_;
                                v_isShared_6146_ = v_isSharedCheck_6150_;
                                state = 23;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6143_);
                                crate::leanh::lean_dec(v___x_6078_);
                                v___x_6145_ = crate::leanh::lean_box(0);
                                v_isShared_6146_ = v_isSharedCheck_6150_;
                                state = 23;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_expr_6071_);
                        crate::leanh::lean_dec(v___x_6023_);
                        crate::leanh::lean_dec_ref(v___x_6015_);
                        crate::leanh::lean_dec_ref(v_arg_6014_);
                        crate::leanh::lean_dec_ref(v_arg_6011_);
                        crate::leanh::lean_dec_ref(v_arg_6008_);
                        crate::leanh::lean_dec_ref(v_arg_6005_);
                        crate::leanh::lean_dec_ref(v_arg_6002_);
                        crate::leanh::lean_dec_ref(v_e_5981_);
                        v_a_6151_ = crate::leanh::lean_ctor_get(v___x_6073_, 0);
                        v_isSharedCheck_6158_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6073_)) as u8;
                        if v_isSharedCheck_6158_ == 0 {
                            v___x_6153_ = v___x_6073_;
                            v_isShared_6154_ = v_isSharedCheck_6158_;
                            state = 25;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6151_);
                            crate::leanh::lean_dec(v___x_6073_);
                            v___x_6153_ = crate::leanh::lean_box(0);
                            v_isShared_6154_ = v_isSharedCheck_6158_;
                            state = 25;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6023_);
                    crate::leanh::lean_dec_ref(v___x_6015_);
                    crate::leanh::lean_dec_ref(v_arg_6014_);
                    crate::leanh::lean_dec_ref(v_arg_6011_);
                    crate::leanh::lean_dec_ref(v_arg_6008_);
                    crate::leanh::lean_dec_ref(v_arg_6005_);
                    crate::leanh::lean_dec_ref(v_arg_6002_);
                    v_isSharedCheck_6170_ = (!crate::leanh::lean_is_exclusive(v_a_6067_)) as u8;
                    if v_isSharedCheck_6170_ == 0 {
                        v_unused_6171_ = crate::leanh::lean_ctor_get(v_a_6067_, 1);
                        crate::leanh::lean_dec(v_unused_6171_);
                        v_unused_6172_ = crate::leanh::lean_ctor_get(v_a_6067_, 0);
                        crate::leanh::lean_dec(v_unused_6172_);
                        v___x_6160_ = v_a_6067_;
                        v_isShared_6161_ = v_isSharedCheck_6170_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_6067_);
                        v___x_6160_ = crate::leanh::lean_box(0);
                        v_isShared_6161_ = v_isSharedCheck_6170_;
                        state = 27;
                        continue;
                    }
                }
            }
            13 => {
                if crate::leanh::lean_obj_tag(v_a_6079_) == 1 {
                    crate::leanh::lean_del_object(v___x_6081_);
                    crate::leanh::lean_dec_ref(v_e_5981_);
                    v_a_6083_ = crate::leanh::lean_ctor_get(v_a_6079_, 0);
                    v_isSharedCheck_6136_ = (!crate::leanh::lean_is_exclusive(v_a_6079_)) as u8;
                    if v_isSharedCheck_6136_ == 0 {
                        v___x_6085_ = v_a_6079_;
                        v_isShared_6086_ = v_isSharedCheck_6136_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6083_);
                        crate::leanh::lean_dec(v_a_6079_);
                        v___x_6085_ = crate::leanh::lean_box(0);
                        v_isShared_6086_ = v_isSharedCheck_6136_;
                        state = 14;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6079_);
                    crate::leanh::lean_dec(v_a_6074_);
                    crate::leanh::lean_dec_ref(v_expr_6071_);
                    crate::leanh::lean_dec(v___x_6023_);
                    crate::leanh::lean_dec_ref(v___x_6015_);
                    crate::leanh::lean_dec_ref(v_arg_6014_);
                    crate::leanh::lean_dec_ref(v_arg_6011_);
                    crate::leanh::lean_dec_ref(v_arg_6008_);
                    crate::leanh::lean_dec_ref(v_arg_6005_);
                    crate::leanh::lean_dec_ref(v_arg_6002_);
                    v___x_6137_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_6137_, 0, v_e_5981_);
                    crate::leanh::lean_ctor_set(v___x_6137_, 1, v___x_6077_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_6137_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_6017_,
                    );
                    v___x_6138_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6138_, 0, v___x_6137_);
                    if v_isShared_6082_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6081_, 0, v___x_6138_);
                        v___x_6140_ = v___x_6081_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_6141_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6141_, 0, v___x_6138_);
                        v___x_6140_ = v_reuseFailAlloc_6141_;
                        state = 22;
                        continue;
                    }
                }
            }
            14 => {
                v___x_6087_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_arg_6005_, v_a_5987_, v_a_5988_);
                if crate::leanh::lean_obj_tag(v___x_6087_) == 0 {
                    v_a_6088_ = crate::leanh::lean_ctor_get(v___x_6087_, 0);
                    crate::leanh::lean_inc(v_a_6088_);
                    crate::leanh::lean_dec_ref_known(v___x_6087_, 1);
                    v___x_6089_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg(v_arg_6002_, v_a_5987_, v_a_5988_);
                    if crate::leanh::lean_obj_tag(v___x_6089_) == 0 {
                        v_a_6090_ = crate::leanh::lean_ctor_get(v___x_6089_, 0);
                        v_isSharedCheck_6119_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6089_)) as u8;
                        if v_isSharedCheck_6119_ == 0 {
                            v___x_6092_ = v___x_6089_;
                            v_isShared_6093_ = v_isSharedCheck_6119_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6090_);
                            crate::leanh::lean_dec(v___x_6089_);
                            v___x_6092_ = crate::leanh::lean_box(0);
                            v_isShared_6093_ = v_isSharedCheck_6119_;
                            state = 15;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6088_);
                        crate::leanh::lean_del_object(v___x_6085_);
                        crate::leanh::lean_dec(v_a_6083_);
                        crate::leanh::lean_dec(v_a_6074_);
                        crate::leanh::lean_dec_ref(v_expr_6071_);
                        crate::leanh::lean_dec(v___x_6023_);
                        crate::leanh::lean_dec_ref(v___x_6015_);
                        crate::leanh::lean_dec_ref(v_arg_6014_);
                        crate::leanh::lean_dec_ref(v_arg_6011_);
                        crate::leanh::lean_dec_ref(v_arg_6008_);
                        crate::leanh::lean_dec_ref(v_arg_6005_);
                        crate::leanh::lean_dec_ref(v_arg_6002_);
                        v_a_6120_ = crate::leanh::lean_ctor_get(v___x_6089_, 0);
                        v_isSharedCheck_6127_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6089_)) as u8;
                        if v_isSharedCheck_6127_ == 0 {
                            v___x_6122_ = v___x_6089_;
                            v_isShared_6123_ = v_isSharedCheck_6127_;
                            state = 18;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6120_);
                            crate::leanh::lean_dec(v___x_6089_);
                            v___x_6122_ = crate::leanh::lean_box(0);
                            v_isShared_6123_ = v_isSharedCheck_6127_;
                            state = 18;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6085_);
                    crate::leanh::lean_dec(v_a_6083_);
                    crate::leanh::lean_dec(v_a_6074_);
                    crate::leanh::lean_dec_ref(v_expr_6071_);
                    crate::leanh::lean_dec(v___x_6023_);
                    crate::leanh::lean_dec_ref(v___x_6015_);
                    crate::leanh::lean_dec_ref(v_arg_6014_);
                    crate::leanh::lean_dec_ref(v_arg_6011_);
                    crate::leanh::lean_dec_ref(v_arg_6008_);
                    crate::leanh::lean_dec_ref(v_arg_6005_);
                    crate::leanh::lean_dec_ref(v_arg_6002_);
                    v_a_6128_ = crate::leanh::lean_ctor_get(v___x_6087_, 0);
                    v_isSharedCheck_6135_ = (!crate::leanh::lean_is_exclusive(v___x_6087_)) as u8;
                    if v_isSharedCheck_6135_ == 0 {
                        v___x_6130_ = v___x_6087_;
                        v_isShared_6131_ = v_isSharedCheck_6135_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6128_);
                        crate::leanh::lean_dec(v___x_6087_);
                        v___x_6130_ = crate::leanh::lean_box(0);
                        v_isShared_6131_ = v_isSharedCheck_6135_;
                        state = 20;
                        continue;
                    }
                }
            }
            15 => {
                v___x_6094_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3_once), _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__3);
                v___x_6095_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4_once), _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__4);
                crate::leanh::lean_inc_n(v_a_6074_, 2);
                crate::leanh::lean_inc_ref_n(v_expr_6071_, 5);
                crate::leanh::lean_inc_ref_n(v_arg_6011_, 2);
                v___x_6096_ = l_Lean_mkApp4(
                    v___x_6094_,
                    v_arg_6011_,
                    v_expr_6071_,
                    v_a_6074_,
                    v___x_6095_,
                );
                crate::leanh::lean_inc_ref(v_arg_6005_);
                v___x_6097_ = l_Lean_Expr_app___override(v_arg_6005_, v___x_6096_);
                v___x_6098_ = l_Lean_Expr_headBeta(v___x_6097_);
                v___x_6099_ = 0;
                v___x_6100_ = l_Lean_mkLambda(v_a_6088_, v___x_6099_, v_expr_6071_, v___x_6098_);
                v___x_6101_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7_once), _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__7);
                v___x_6102_ = l_Lean_mkApp4(
                    v___x_6101_,
                    v_arg_6011_,
                    v_expr_6071_,
                    v_a_6074_,
                    v___x_6095_,
                );
                crate::leanh::lean_inc_ref(v_arg_6002_);
                v___x_6103_ = l_Lean_Expr_app___override(v_arg_6002_, v___x_6102_);
                v___x_6104_ = l_Lean_Expr_headBeta(v___x_6103_);
                v___x_6105_ = l_Lean_mkNot(v_expr_6071_);
                v___x_6106_ = l_Lean_mkLambda(v_a_6090_, v___x_6099_, v___x_6105_, v___x_6104_);
                crate::leanh::lean_inc(v_a_6083_);
                crate::leanh::lean_inc_ref(v_arg_6014_);
                v___x_6107_ = l_Lean_mkApp5(
                    v___x_6015_,
                    v_arg_6014_,
                    v_expr_6071_,
                    v_a_6083_,
                    v___x_6100_,
                    v___x_6106_,
                );
                v___x_6108_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___closed__9;
                v___x_6109_ = l_Lean_mkConst(v___x_6108_, v___x_6023_);
                v___x_6110_ = l_Lean_mkApp8(
                    v___x_6109_,
                    v_arg_6014_,
                    v_arg_6011_,
                    v_expr_6071_,
                    v_arg_6008_,
                    v_a_6083_,
                    v_arg_6005_,
                    v_arg_6002_,
                    v_a_6074_,
                );
                if v_isShared_6086_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6085_, 0, v___x_6110_);
                    v___x_6112_ = v___x_6085_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6118_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6118_, 0, v___x_6110_);
                    v___x_6112_ = v_reuseFailAlloc_6118_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_6113_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_6113_, 0, v___x_6107_);
                crate::leanh::lean_ctor_set(v___x_6113_, 1, v___x_6112_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6113_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_6017_,
                );
                v___x_6114_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6114_, 0, v___x_6113_);
                if v_isShared_6093_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6092_, 0, v___x_6114_);
                    v___x_6116_ = v___x_6092_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6117_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6117_, 0, v___x_6114_);
                    v___x_6116_ = v_reuseFailAlloc_6117_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6116_;
            }
            18 => {
                if v_isShared_6123_ == 0 {
                    v___x_6125_ = v___x_6122_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_6126_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6126_, 0, v_a_6120_);
                    v___x_6125_ = v_reuseFailAlloc_6126_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_6125_;
            }
            20 => {
                if v_isShared_6131_ == 0 {
                    v___x_6133_ = v___x_6130_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_6134_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6134_, 0, v_a_6128_);
                    v___x_6133_ = v_reuseFailAlloc_6134_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_6133_;
            }
            22 => {
                return v___x_6140_;
            }
            23 => {
                if v_isShared_6146_ == 0 {
                    v___x_6148_ = v___x_6145_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_6149_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6149_, 0, v_a_6143_);
                    v___x_6148_ = v_reuseFailAlloc_6149_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_6148_;
            }
            25 => {
                if v_isShared_6154_ == 0 {
                    v___x_6156_ = v___x_6153_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_6157_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6157_, 0, v_a_6151_);
                    v___x_6156_ = v_reuseFailAlloc_6157_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_6156_;
            }
            27 => {
                v___x_6162_ = crate::leanh::lean_box(0);
                if v_isShared_6161_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6160_, 1, v___x_6162_);
                    crate::leanh::lean_ctor_set(v___x_6160_, 0, v_e_5981_);
                    v___x_6164_ = v___x_6160_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_6169_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6169_, 0, v_e_5981_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6169_, 1, v___x_6162_);
                    v___x_6164_ = v_reuseFailAlloc_6169_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6164_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_6017_,
                );
                v___x_6165_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6165_, 0, v___x_6164_);
                if v_isShared_6070_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6069_, 0, v___x_6165_);
                    v___x_6167_ = v___x_6069_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_6168_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6168_, 0, v___x_6165_);
                    v___x_6167_ = v_reuseFailAlloc_6168_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_6167_;
            }
            30 => {
                if v_isShared_6177_ == 0 {
                    v___x_6179_ = v___x_6176_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_6180_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6180_, 0, v_a_6174_);
                    v___x_6179_ = v_reuseFailAlloc_6180_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_6179_;
            }
            32 => {
                if v_isShared_6186_ == 0 {
                    v___x_6188_ = v___x_6185_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_6189_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6189_, 0, v_a_6183_);
                    v___x_6188_ = v_reuseFailAlloc_6189_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_6188_;
            }
            34 => {
                if v_isShared_6195_ == 0 {
                    v___x_6197_ = v___x_6194_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_6198_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6198_, 0, v_a_6192_);
                    v___x_6197_ = v_reuseFailAlloc_6198_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_6197_;
            }
            36 => {
                if v_isShared_6204_ == 0 {
                    v___x_6206_ = v___x_6203_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_6207_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6207_, 0, v_a_6201_);
                    v___x_6206_ = v_reuseFailAlloc_6207_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_6206_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___boxed(
    mut v_numIndices_6209_: *mut crate::leanh::LeanObject,
    mut v_useDecideBool_6210_: *mut crate::leanh::LeanObject,
    mut v_e_6211_: *mut crate::leanh::LeanObject,
    mut v_a_6212_: *mut crate::leanh::LeanObject,
    mut v_a_6213_: *mut crate::leanh::LeanObject,
    mut v_a_6214_: *mut crate::leanh::LeanObject,
    mut v_a_6215_: *mut crate::leanh::LeanObject,
    mut v_a_6216_: *mut crate::leanh::LeanObject,
    mut v_a_6217_: *mut crate::leanh::LeanObject,
    mut v_a_6218_: *mut crate::leanh::LeanObject,
    mut v_a_6219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useDecideBool_boxed_6220_: u8 = 0;
    let mut v_res_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useDecideBool_boxed_6220_ = (crate::leanh::lean_unbox(v_useDecideBool_6210_) as u8);
    v_res_6221_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27(
        v_numIndices_6209_,
        v_useDecideBool_boxed_6220_,
        v_e_6211_,
        v_a_6212_,
        v_a_6213_,
        v_a_6214_,
        v_a_6215_,
        v_a_6216_,
        v_a_6217_,
        v_a_6218_,
    );
    crate::leanh::lean_dec(v_a_6218_);
    crate::leanh::lean_dec_ref(v_a_6217_);
    crate::leanh::lean_dec(v_a_6216_);
    crate::leanh::lean_dec_ref(v_a_6215_);
    crate::leanh::lean_dec(v_a_6214_);
    crate::leanh::lean_dec_ref(v_a_6213_);
    crate::leanh::lean_dec(v_a_6212_);
    crate::leanh::lean_dec(v_numIndices_6209_);
    return v_res_6221_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6222_ = l_Lean_Meta_DiscrTree_empty(crate::leanh::lean_box(0));
    return v___x_6222_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_6225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6223_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_SplitIf_getSimpContext___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_SplitIf_getSimpContext___closed__2_once),
        _init_l_Lean_Meta_SplitIf_getSimpContext___closed__2,
    );
    v___x_6224_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0_once), _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__0);
    v_s_6225_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v_s_6225_, 0, v___x_6224_);
    crate::leanh::lean_ctor_set(v_s_6225_, 1, v___x_6224_);
    crate::leanh::lean_ctor_set(v_s_6225_, 2, v___x_6223_);
    crate::leanh::lean_ctor_set(v_s_6225_, 3, v___x_6223_);
    return v_s_6225_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(
    mut v_numIndices_6289_: *mut crate::leanh::LeanObject,
    mut v_useDecide_6290_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_6292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: u8 = 0;
    let mut v___x_6296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_6299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_6305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_s_6292_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1_once), _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__1);
    v___x_6293_ =
        l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__3;
    v___x_6294_ =
        l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__16;
    v___x_6295_ = 0;
    v___x_6296_ = crate::leanh::lean_box((v_useDecide_6290_) as usize);
    crate::leanh::lean_inc(v_numIndices_6289_);
    v___x_6297_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceIte_x27___boxed
            as *mut core::ffi::c_void,
        11,
        2,
    );
    crate::leanh::lean_closure_set(v___x_6297_, 0, v_numIndices_6289_);
    crate::leanh::lean_closure_set(v___x_6297_, 1, v___x_6296_);
    v___x_6298_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6298_, 0, v___x_6297_);
    v_s_6299_ = l_Lean_Meta_Simp_Simprocs_addCore(
        v_s_6292_,
        v___x_6293_,
        v___x_6294_,
        v___x_6295_,
        v___x_6298_,
    );
    v___x_6300_ =
        l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__18;
    v___x_6301_ =
        l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___closed__20;
    v___x_6302_ = crate::leanh::lean_box((v_useDecide_6290_) as usize);
    v___x_6303_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_reduceDIte_x27___boxed
            as *mut core::ffi::c_void,
        11,
        2,
    );
    crate::leanh::lean_closure_set(v___x_6303_, 0, v_numIndices_6289_);
    crate::leanh::lean_closure_set(v___x_6303_, 1, v___x_6302_);
    v___x_6304_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6304_, 0, v___x_6303_);
    v_s_6305_ = l_Lean_Meta_Simp_Simprocs_addCore(
        v_s_6299_,
        v___x_6300_,
        v___x_6301_,
        v___x_6295_,
        v___x_6304_,
    );
    v___x_6306_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_6307_ = lean_mk_empty_array_with_capacity(v___x_6306_);
    v___x_6308_ = lean_array_push(v___x_6307_, v_s_6305_);
    v___x_6309_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6309_, 0, v___x_6308_);
    return v___x_6309_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg___boxed(
    mut v_numIndices_6310_: *mut crate::leanh::LeanObject,
    mut v_useDecide_6311_: *mut crate::leanh::LeanObject,
    mut v_a_6312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useDecide_boxed_6313_: u8 = 0;
    let mut v_res_6314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useDecide_boxed_6313_ = (crate::leanh::lean_unbox(v_useDecide_6311_) as u8);
    v_res_6314_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(
        v_numIndices_6310_,
        v_useDecide_boxed_6313_,
    );
    return v_res_6314_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs(
    mut v_numIndices_6315_: *mut crate::leanh::LeanObject,
    mut v_useDecide_6316_: u8,
    mut v_a_6317_: *mut crate::leanh::LeanObject,
    mut v_a_6318_: *mut crate::leanh::LeanObject,
    mut v_a_6319_: *mut crate::leanh::LeanObject,
    mut v_a_6320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6322_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(
        v_numIndices_6315_,
        v_useDecide_6316_,
    );
    return v___x_6322_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___boxed(
    mut v_numIndices_6323_: *mut crate::leanh::LeanObject,
    mut v_useDecide_6324_: *mut crate::leanh::LeanObject,
    mut v_a_6325_: *mut crate::leanh::LeanObject,
    mut v_a_6326_: *mut crate::leanh::LeanObject,
    mut v_a_6327_: *mut crate::leanh::LeanObject,
    mut v_a_6328_: *mut crate::leanh::LeanObject,
    mut v_a_6329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useDecide_boxed_6330_: u8 = 0;
    let mut v_res_6331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useDecide_boxed_6330_ = (crate::leanh::lean_unbox(v_useDecide_6324_) as u8);
    v_res_6331_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs(
        v_numIndices_6323_,
        v_useDecide_boxed_6330_,
        v_a_6325_,
        v_a_6326_,
        v_a_6327_,
        v_a_6328_,
    );
    crate::leanh::lean_dec(v_a_6328_);
    crate::leanh::lean_dec_ref(v_a_6327_);
    crate::leanh::lean_dec(v_a_6326_);
    crate::leanh::lean_dec_ref(v_a_6325_);
    return v_res_6331_;
}
pub unsafe fn l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(
    mut v_useDecide_6332_: u8,
    mut v_a_6333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lctx_6335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lctx_6335_ = crate::leanh::lean_ctor_get(v_a_6333_, 2);
    crate::leanh::lean_inc_ref(v_lctx_6335_);
    v___x_6336_ = lean_local_ctx_num_indices(v_lctx_6335_);
    v___x_6337_ = crate::leanh::lean_box((v_useDecide_6332_) as usize);
    v___x_6338_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___boxed
            as *mut core::ffi::c_void,
        11,
        2,
    );
    crate::leanh::lean_closure_set(v___x_6338_, 0, v___x_6336_);
    crate::leanh::lean_closure_set(v___x_6338_, 1, v___x_6337_);
    v___x_6339_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6339_, 0, v___x_6338_);
    return v___x_6339_;
}
pub unsafe fn l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg___boxed(
    mut v_useDecide_6340_: *mut crate::leanh::LeanObject,
    mut v_a_6341_: *mut crate::leanh::LeanObject,
    mut v_a_6342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useDecide_boxed_6343_: u8 = 0;
    let mut v_res_6344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useDecide_boxed_6343_ = (crate::leanh::lean_unbox(v_useDecide_6340_) as u8);
    v_res_6344_ = l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(v_useDecide_boxed_6343_, v_a_6341_);
    crate::leanh::lean_dec_ref(v_a_6341_);
    return v_res_6344_;
}
pub unsafe fn l_Lean_Meta_SplitIf_mkDischarge_x3f(
    mut v_useDecide_6345_: u8,
    mut v_a_6346_: *mut crate::leanh::LeanObject,
    mut v_a_6347_: *mut crate::leanh::LeanObject,
    mut v_a_6348_: *mut crate::leanh::LeanObject,
    mut v_a_6349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6351_ = l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(v_useDecide_6345_, v_a_6346_);
    return v___x_6351_;
}
pub unsafe fn l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed(
    mut v_useDecide_6352_: *mut crate::leanh::LeanObject,
    mut v_a_6353_: *mut crate::leanh::LeanObject,
    mut v_a_6354_: *mut crate::leanh::LeanObject,
    mut v_a_6355_: *mut crate::leanh::LeanObject,
    mut v_a_6356_: *mut crate::leanh::LeanObject,
    mut v_a_6357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useDecide_boxed_6358_: u8 = 0;
    let mut v_res_6359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useDecide_boxed_6358_ = (crate::leanh::lean_unbox(v_useDecide_6352_) as u8);
    v_res_6359_ = l_Lean_Meta_SplitIf_mkDischarge_x3f(
        v_useDecide_boxed_6358_,
        v_a_6353_,
        v_a_6354_,
        v_a_6355_,
        v_a_6356_,
    );
    crate::leanh::lean_dec(v_a_6356_);
    crate::leanh::lean_dec_ref(v_a_6355_);
    crate::leanh::lean_dec(v_a_6354_);
    crate::leanh::lean_dec_ref(v_a_6353_);
    return v_res_6359_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(
    mut v_mvarId_6360_: *mut crate::leanh::LeanObject,
    mut v_x_6361_: *mut crate::leanh::LeanObject,
    mut v___y_6362_: *mut crate::leanh::LeanObject,
    mut v___y_6363_: *mut crate::leanh::LeanObject,
    mut v___y_6364_: *mut crate::leanh::LeanObject,
    mut v___y_6365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6371_: u8 = 0;
    let mut v___x_6373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6375_: u8 = 0;
    let mut v_a_6376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6379_: u8 = 0;
    let mut v___x_6381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6383_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6367_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_6360_,
                    v_x_6361_,
                    v___y_6362_,
                    v___y_6363_,
                    v___y_6364_,
                    v___y_6365_,
                );
                if crate::leanh::lean_obj_tag(v___x_6367_) == 0 {
                    v_a_6368_ = crate::leanh::lean_ctor_get(v___x_6367_, 0);
                    v_isSharedCheck_6375_ = (!crate::leanh::lean_is_exclusive(v___x_6367_)) as u8;
                    if v_isSharedCheck_6375_ == 0 {
                        v___x_6370_ = v___x_6367_;
                        v_isShared_6371_ = v_isSharedCheck_6375_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6368_);
                        crate::leanh::lean_dec(v___x_6367_);
                        v___x_6370_ = crate::leanh::lean_box(0);
                        v_isShared_6371_ = v_isSharedCheck_6375_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6376_ = crate::leanh::lean_ctor_get(v___x_6367_, 0);
                    v_isSharedCheck_6383_ = (!crate::leanh::lean_is_exclusive(v___x_6367_)) as u8;
                    if v_isSharedCheck_6383_ == 0 {
                        v___x_6378_ = v___x_6367_;
                        v_isShared_6379_ = v_isSharedCheck_6383_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6376_);
                        crate::leanh::lean_dec(v___x_6367_);
                        v___x_6378_ = crate::leanh::lean_box(0);
                        v_isShared_6379_ = v_isSharedCheck_6383_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6371_ == 0 {
                    v___x_6373_ = v___x_6370_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6374_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6374_, 0, v_a_6368_);
                    v___x_6373_ = v_reuseFailAlloc_6374_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6373_;
            }
            3 => {
                if v_isShared_6379_ == 0 {
                    v___x_6381_ = v___x_6378_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6382_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6382_, 0, v_a_6376_);
                    v___x_6381_ = v_reuseFailAlloc_6382_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6381_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg___boxed(
    mut v_mvarId_6384_: *mut crate::leanh::LeanObject,
    mut v_x_6385_: *mut crate::leanh::LeanObject,
    mut v___y_6386_: *mut crate::leanh::LeanObject,
    mut v___y_6387_: *mut crate::leanh::LeanObject,
    mut v___y_6388_: *mut crate::leanh::LeanObject,
    mut v___y_6389_: *mut crate::leanh::LeanObject,
    mut v___y_6390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6391_ =
        l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(
            v_mvarId_6384_,
            v_x_6385_,
            v___y_6386_,
            v___y_6387_,
            v___y_6388_,
            v___y_6389_,
        );
    crate::leanh::lean_dec(v___y_6389_);
    crate::leanh::lean_dec_ref(v___y_6388_);
    crate::leanh::lean_dec(v___y_6387_);
    crate::leanh::lean_dec_ref(v___y_6386_);
    return v_res_6391_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0(
    mut v_00_u03b1_6392_: *mut crate::leanh::LeanObject,
    mut v_mvarId_6393_: *mut crate::leanh::LeanObject,
    mut v_x_6394_: *mut crate::leanh::LeanObject,
    mut v___y_6395_: *mut crate::leanh::LeanObject,
    mut v___y_6396_: *mut crate::leanh::LeanObject,
    mut v___y_6397_: *mut crate::leanh::LeanObject,
    mut v___y_6398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6400_ =
        l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(
            v_mvarId_6393_,
            v_x_6394_,
            v___y_6395_,
            v___y_6396_,
            v___y_6397_,
            v___y_6398_,
        );
    return v___x_6400_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___boxed(
    mut v_00_u03b1_6401_: *mut crate::leanh::LeanObject,
    mut v_mvarId_6402_: *mut crate::leanh::LeanObject,
    mut v_x_6403_: *mut crate::leanh::LeanObject,
    mut v___y_6404_: *mut crate::leanh::LeanObject,
    mut v___y_6405_: *mut crate::leanh::LeanObject,
    mut v___y_6406_: *mut crate::leanh::LeanObject,
    mut v___y_6407_: *mut crate::leanh::LeanObject,
    mut v___y_6408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6409_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0(
        v_00_u03b1_6401_,
        v_mvarId_6402_,
        v_x_6403_,
        v___y_6404_,
        v___y_6405_,
        v___y_6406_,
        v___y_6407_,
    );
    crate::leanh::lean_dec(v___y_6407_);
    crate::leanh::lean_dec_ref(v___y_6406_);
    crate::leanh::lean_dec(v___y_6405_);
    crate::leanh::lean_dec_ref(v___y_6404_);
    return v_res_6409_;
}
pub unsafe fn _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6411_ = l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__0;
    v___x_6412_ = l_Lean_stringToMessageData(v___x_6411_);
    return v___x_6412_;
}
pub unsafe fn _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6414_ = l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__2;
    v___x_6415_ = l_Lean_stringToMessageData(v___x_6414_);
    return v___x_6415_;
}
pub unsafe fn l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0(
    mut v_e_6416_: *mut crate::leanh::LeanObject,
    mut v_mvarId_6417_: *mut crate::leanh::LeanObject,
    mut v_hName_x3f_6418_: *mut crate::leanh::LeanObject,
    mut v___y_6419_: *mut crate::leanh::LeanObject,
    mut v___y_6420_: *mut crate::leanh::LeanObject,
    mut v___y_6421_: *mut crate::leanh::LeanObject,
    mut v___y_6422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6434_: u8 = 0;
    let mut v_fst_6435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6439_: u8 = 0;
    let mut v___y_6441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6450_: u8 = 0;
    let mut v___x_6452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6457_: u8 = 0;
    let mut v_a_6458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6461_: u8 = 0;
    let mut v___x_6463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6465_: u8 = 0;
    let mut v_hName_6467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6473_: u8 = 0;
    let mut v_inheritedTraceOptions_6474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6477_: u8 = 0;
    let mut v___x_6478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6486_: u8 = 0;
    let mut v___x_6488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6490_: u8 = 0;
    let mut v_reuseFailAlloc_6491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6498_: u8 = 0;
    let mut v___x_6500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6502_: u8 = 0;
    let mut v_val_6503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6504_: u8 = 0;
    let mut v_isSharedCheck_6505_: u8 = 0;
    let mut v_options_6506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6507_: u8 = 0;
    let mut v_inheritedTraceOptions_6508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: u8 = 0;
    let mut v___x_6512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6519_: u8 = 0;
    let mut v___x_6521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6523_: u8 = 0;
    let mut v_a_6524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6527_: u8 = 0;
    let mut v___x_6529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6531_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6427_ =
                    l_Lean_instantiateMVars___at___00Lean_Meta_findSplit_x3f_spec__0___redArg(
                        v_e_6416_,
                        v___y_6420_,
                    );
                v_a_6428_ = crate::leanh::lean_ctor_get(v___x_6427_, 0);
                crate::leanh::lean_inc_n(v_a_6428_, 2);
                crate::leanh::lean_dec_ref(v___x_6427_);
                v___x_6429_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findIfToSplit_x3f(
                    v_a_6428_,
                    v___y_6419_,
                    v___y_6420_,
                    v___y_6421_,
                    v___y_6422_,
                );
                if crate::leanh::lean_obj_tag(v___x_6429_) == 0 {
                    v_a_6430_ = crate::leanh::lean_ctor_get(v___x_6429_, 0);
                    crate::leanh::lean_inc(v_a_6430_);
                    crate::leanh::lean_dec_ref_known(v___x_6429_, 1);
                    if crate::leanh::lean_obj_tag(v_a_6430_) == 1 {
                        crate::leanh::lean_dec(v_a_6428_);
                        v_val_6431_ = crate::leanh::lean_ctor_get(v_a_6430_, 0);
                        v_isSharedCheck_6505_ = (!crate::leanh::lean_is_exclusive(v_a_6430_)) as u8;
                        if v_isSharedCheck_6505_ == 0 {
                            v___x_6433_ = v_a_6430_;
                            v_isShared_6434_ = v_isSharedCheck_6505_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_6431_);
                            crate::leanh::lean_dec(v_a_6430_);
                            v___x_6433_ = crate::leanh::lean_box(0);
                            v_isShared_6434_ = v_isSharedCheck_6505_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6430_);
                        crate::leanh::lean_dec(v_hName_x3f_6418_);
                        crate::leanh::lean_dec(v_mvarId_6417_);
                        v_options_6506_ = crate::leanh::lean_ctor_get(v___y_6421_, 2);
                        v_hasTrace_6507_ = crate::leanh::lean_ctor_get_uint8(
                            v_options_6506_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_6507_ == 0 {
                            crate::leanh::lean_dec(v_a_6428_);
                            state = 1;
                            continue;
                        } else {
                            v_inheritedTraceOptions_6508_ =
                                crate::leanh::lean_ctor_get(v___y_6421_, 13);
                            v___x_6509_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10;
                            v___x_6510_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11_once), _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11);
                            v___x_6511_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_6508_,
                                v_options_6506_,
                                v___x_6510_,
                            );
                            if v___x_6511_ == 0 {
                                crate::leanh::lean_dec(v_a_6428_);
                                state = 1;
                                continue;
                            } else {
                                v___x_6512_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3_once
                                    ),
                                    _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__3,
                                );
                                v___x_6513_ = l_Lean_indentExpr(v_a_6428_);
                                v___x_6514_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_6514_, 0, v___x_6512_);
                                crate::leanh::lean_ctor_set(v___x_6514_, 1, v___x_6513_);
                                v___x_6515_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_6509_, v___x_6514_, v___y_6419_, v___y_6420_, v___y_6421_, v___y_6422_);
                                if crate::leanh::lean_obj_tag(v___x_6515_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_6515_, 1);
                                    state = 1;
                                    continue;
                                } else {
                                    v_a_6516_ = crate::leanh::lean_ctor_get(v___x_6515_, 0);
                                    v_isSharedCheck_6523_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6515_)) as u8;
                                    if v_isSharedCheck_6523_ == 0 {
                                        v___x_6518_ = v___x_6515_;
                                        v_isShared_6519_ = v_isSharedCheck_6523_;
                                        state = 16;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6516_);
                                        crate::leanh::lean_dec(v___x_6515_);
                                        v___x_6518_ = crate::leanh::lean_box(0);
                                        v_isShared_6519_ = v_isSharedCheck_6523_;
                                        state = 16;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6428_);
                    crate::leanh::lean_dec(v_hName_x3f_6418_);
                    crate::leanh::lean_dec(v_mvarId_6417_);
                    v_a_6524_ = crate::leanh::lean_ctor_get(v___x_6429_, 0);
                    v_isSharedCheck_6531_ = (!crate::leanh::lean_is_exclusive(v___x_6429_)) as u8;
                    if v_isSharedCheck_6531_ == 0 {
                        v___x_6526_ = v___x_6429_;
                        v_isShared_6527_ = v_isSharedCheck_6531_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6524_);
                        crate::leanh::lean_dec(v___x_6429_);
                        v___x_6526_ = crate::leanh::lean_box(0);
                        v_isShared_6527_ = v_isSharedCheck_6531_;
                        state = 18;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6425_ = crate::leanh::lean_box(0);
                v___x_6426_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6426_, 0, v___x_6425_);
                return v___x_6426_;
            }
            2 => {
                v_fst_6435_ = crate::leanh::lean_ctor_get(v_val_6431_, 0);
                v_snd_6436_ = crate::leanh::lean_ctor_get(v_val_6431_, 1);
                v_isSharedCheck_6504_ = (!crate::leanh::lean_is_exclusive(v_val_6431_)) as u8;
                if v_isSharedCheck_6504_ == 0 {
                    v___x_6438_ = v_val_6431_;
                    v_isShared_6439_ = v_isSharedCheck_6504_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_6436_);
                    crate::leanh::lean_inc(v_fst_6435_);
                    crate::leanh::lean_dec(v_val_6431_);
                    v___x_6438_ = crate::leanh::lean_box(0);
                    v_isShared_6439_ = v_isSharedCheck_6504_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_hName_x3f_6418_) == 0 {
                    v___x_6492_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getBinderName___redArg___closed__1;
                    v___x_6493_ =
                        l_Lean_Core_mkFreshUserName(v___x_6492_, v___y_6421_, v___y_6422_);
                    if crate::leanh::lean_obj_tag(v___x_6493_) == 0 {
                        v_a_6494_ = crate::leanh::lean_ctor_get(v___x_6493_, 0);
                        crate::leanh::lean_inc(v_a_6494_);
                        crate::leanh::lean_dec_ref_known(v___x_6493_, 1);
                        v_hName_6467_ = v_a_6494_;
                        v___y_6468_ = v___y_6419_;
                        v___y_6469_ = v___y_6420_;
                        v___y_6470_ = v___y_6421_;
                        v___y_6471_ = v___y_6422_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_6438_);
                        crate::leanh::lean_dec(v_snd_6436_);
                        crate::leanh::lean_dec(v_fst_6435_);
                        crate::leanh::lean_del_object(v___x_6433_);
                        crate::leanh::lean_dec(v_mvarId_6417_);
                        v_a_6495_ = crate::leanh::lean_ctor_get(v___x_6493_, 0);
                        v_isSharedCheck_6502_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6493_)) as u8;
                        if v_isSharedCheck_6502_ == 0 {
                            v___x_6497_ = v___x_6493_;
                            v_isShared_6498_ = v_isSharedCheck_6502_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6495_);
                            crate::leanh::lean_dec(v___x_6493_);
                            v___x_6497_ = crate::leanh::lean_box(0);
                            v_isShared_6498_ = v_isSharedCheck_6502_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    v_val_6503_ = crate::leanh::lean_ctor_get(v_hName_x3f_6418_, 0);
                    crate::leanh::lean_inc(v_val_6503_);
                    crate::leanh::lean_dec_ref_known(v_hName_x3f_6418_, 1);
                    v_hName_6467_ = v_val_6503_;
                    v___y_6468_ = v___y_6419_;
                    v___y_6469_ = v___y_6420_;
                    v___y_6470_ = v___y_6421_;
                    v___y_6471_ = v___y_6422_;
                    state = 10;
                    continue;
                }
            }
            4 => {
                v___x_6446_ = l_Lean_MVarId_byCasesDec(
                    v_mvarId_6417_,
                    v_fst_6435_,
                    v_snd_6436_,
                    v___y_6441_,
                    v___y_6442_,
                    v___y_6443_,
                    v___y_6444_,
                    v___y_6445_,
                );
                if crate::leanh::lean_obj_tag(v___x_6446_) == 0 {
                    v_a_6447_ = crate::leanh::lean_ctor_get(v___x_6446_, 0);
                    v_isSharedCheck_6457_ = (!crate::leanh::lean_is_exclusive(v___x_6446_)) as u8;
                    if v_isSharedCheck_6457_ == 0 {
                        v___x_6449_ = v___x_6446_;
                        v_isShared_6450_ = v_isSharedCheck_6457_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6447_);
                        crate::leanh::lean_dec(v___x_6446_);
                        v___x_6449_ = crate::leanh::lean_box(0);
                        v_isShared_6450_ = v_isSharedCheck_6457_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6433_);
                    v_a_6458_ = crate::leanh::lean_ctor_get(v___x_6446_, 0);
                    v_isSharedCheck_6465_ = (!crate::leanh::lean_is_exclusive(v___x_6446_)) as u8;
                    if v_isSharedCheck_6465_ == 0 {
                        v___x_6460_ = v___x_6446_;
                        v_isShared_6461_ = v_isSharedCheck_6465_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6458_);
                        crate::leanh::lean_dec(v___x_6446_);
                        v___x_6460_ = crate::leanh::lean_box(0);
                        v_isShared_6461_ = v_isSharedCheck_6465_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_6434_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6433_, 0, v_a_6447_);
                    v___x_6452_ = v___x_6433_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6456_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6456_, 0, v_a_6447_);
                    v___x_6452_ = v_reuseFailAlloc_6456_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_6450_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6449_, 0, v___x_6452_);
                    v___x_6454_ = v___x_6449_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6455_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6455_, 0, v___x_6452_);
                    v___x_6454_ = v_reuseFailAlloc_6455_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6454_;
            }
            8 => {
                if v_isShared_6461_ == 0 {
                    v___x_6463_ = v___x_6460_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6464_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6464_, 0, v_a_6458_);
                    v___x_6463_ = v_reuseFailAlloc_6464_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6463_;
            }
            10 => {
                v_options_6472_ = crate::leanh::lean_ctor_get(v___y_6470_, 2);
                v_hasTrace_6473_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_6472_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_6473_ == 0 {
                    crate::leanh::lean_del_object(v___x_6438_);
                    v___y_6441_ = v_hName_6467_;
                    v___y_6442_ = v___y_6468_;
                    v___y_6443_ = v___y_6469_;
                    v___y_6444_ = v___y_6470_;
                    v___y_6445_ = v___y_6471_;
                    state = 4;
                    continue;
                } else {
                    v_inheritedTraceOptions_6474_ = crate::leanh::lean_ctor_get(v___y_6470_, 13);
                    v___x_6475_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10;
                    v___x_6476_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11_once), _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__11);
                    v___x_6477_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_6474_,
                        v_options_6472_,
                        v___x_6476_,
                    );
                    if v___x_6477_ == 0 {
                        crate::leanh::lean_del_object(v___x_6438_);
                        v___y_6441_ = v_hName_6467_;
                        v___y_6442_ = v___y_6468_;
                        v___y_6443_ = v___y_6469_;
                        v___y_6444_ = v___y_6470_;
                        v___y_6445_ = v___y_6471_;
                        state = 4;
                        continue;
                    } else {
                        v___x_6478_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1_once
                            ),
                            _init_l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___closed__1,
                        );
                        crate::leanh::lean_inc(v_snd_6436_);
                        v___x_6479_ = l_Lean_MessageData_ofExpr(v_snd_6436_);
                        if v_isShared_6439_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_6438_, 7);
                            crate::leanh::lean_ctor_set(v___x_6438_, 1, v___x_6479_);
                            crate::leanh::lean_ctor_set(v___x_6438_, 0, v___x_6478_);
                            v___x_6481_ = v___x_6438_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_6491_ =
                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6491_, 0, v___x_6478_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6491_, 1, v___x_6479_);
                            v___x_6481_ = v_reuseFailAlloc_6491_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            11 => {
                v___x_6482_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_6475_, v___x_6481_, v___y_6468_, v___y_6469_, v___y_6470_, v___y_6471_);
                if crate::leanh::lean_obj_tag(v___x_6482_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6482_, 1);
                    v___y_6441_ = v_hName_6467_;
                    v___y_6442_ = v___y_6468_;
                    v___y_6443_ = v___y_6469_;
                    v___y_6444_ = v___y_6470_;
                    v___y_6445_ = v___y_6471_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_hName_6467_);
                    crate::leanh::lean_dec(v_snd_6436_);
                    crate::leanh::lean_dec(v_fst_6435_);
                    crate::leanh::lean_del_object(v___x_6433_);
                    crate::leanh::lean_dec(v_mvarId_6417_);
                    v_a_6483_ = crate::leanh::lean_ctor_get(v___x_6482_, 0);
                    v_isSharedCheck_6490_ = (!crate::leanh::lean_is_exclusive(v___x_6482_)) as u8;
                    if v_isSharedCheck_6490_ == 0 {
                        v___x_6485_ = v___x_6482_;
                        v_isShared_6486_ = v_isSharedCheck_6490_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6483_);
                        crate::leanh::lean_dec(v___x_6482_);
                        v___x_6485_ = crate::leanh::lean_box(0);
                        v_isShared_6486_ = v_isSharedCheck_6490_;
                        state = 12;
                        continue;
                    }
                }
            }
            12 => {
                if v_isShared_6486_ == 0 {
                    v___x_6488_ = v___x_6485_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6489_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6489_, 0, v_a_6483_);
                    v___x_6488_ = v_reuseFailAlloc_6489_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6488_;
            }
            14 => {
                if v_isShared_6498_ == 0 {
                    v___x_6500_ = v___x_6497_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6501_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6501_, 0, v_a_6495_);
                    v___x_6500_ = v_reuseFailAlloc_6501_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6500_;
            }
            16 => {
                if v_isShared_6519_ == 0 {
                    v___x_6521_ = v___x_6518_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6522_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6522_, 0, v_a_6516_);
                    v___x_6521_ = v_reuseFailAlloc_6522_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6521_;
            }
            18 => {
                if v_isShared_6527_ == 0 {
                    v___x_6529_ = v___x_6526_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_6530_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6530_, 0, v_a_6524_);
                    v___x_6529_ = v_reuseFailAlloc_6530_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_6529_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___boxed(
    mut v_e_6532_: *mut crate::leanh::LeanObject,
    mut v_mvarId_6533_: *mut crate::leanh::LeanObject,
    mut v_hName_x3f_6534_: *mut crate::leanh::LeanObject,
    mut v___y_6535_: *mut crate::leanh::LeanObject,
    mut v___y_6536_: *mut crate::leanh::LeanObject,
    mut v___y_6537_: *mut crate::leanh::LeanObject,
    mut v___y_6538_: *mut crate::leanh::LeanObject,
    mut v___y_6539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6540_ = l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0(
        v_e_6532_,
        v_mvarId_6533_,
        v_hName_x3f_6534_,
        v___y_6535_,
        v___y_6536_,
        v___y_6537_,
        v___y_6538_,
    );
    crate::leanh::lean_dec(v___y_6538_);
    crate::leanh::lean_dec_ref(v___y_6537_);
    crate::leanh::lean_dec(v___y_6536_);
    crate::leanh::lean_dec_ref(v___y_6535_);
    return v_res_6540_;
}
pub unsafe fn l_Lean_Meta_SplitIf_splitIfAt_x3f(
    mut v_mvarId_6541_: *mut crate::leanh::LeanObject,
    mut v_e_6542_: *mut crate::leanh::LeanObject,
    mut v_hName_x3f_6543_: *mut crate::leanh::LeanObject,
    mut v_a_6544_: *mut crate::leanh::LeanObject,
    mut v_a_6545_: *mut crate::leanh::LeanObject,
    mut v_a_6546_: *mut crate::leanh::LeanObject,
    mut v_a_6547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_mvarId_6541_);
    v___f_6549_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_SplitIf_splitIfAt_x3f___lam__0___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___f_6549_, 0, v_e_6542_);
    crate::leanh::lean_closure_set(v___f_6549_, 1, v_mvarId_6541_);
    crate::leanh::lean_closure_set(v___f_6549_, 2, v_hName_x3f_6543_);
    v___x_6550_ =
        l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(
            v_mvarId_6541_,
            v___f_6549_,
            v_a_6544_,
            v_a_6545_,
            v_a_6546_,
            v_a_6547_,
        );
    return v___x_6550_;
}
pub unsafe fn l_Lean_Meta_SplitIf_splitIfAt_x3f___boxed(
    mut v_mvarId_6551_: *mut crate::leanh::LeanObject,
    mut v_e_6552_: *mut crate::leanh::LeanObject,
    mut v_hName_x3f_6553_: *mut crate::leanh::LeanObject,
    mut v_a_6554_: *mut crate::leanh::LeanObject,
    mut v_a_6555_: *mut crate::leanh::LeanObject,
    mut v_a_6556_: *mut crate::leanh::LeanObject,
    mut v_a_6557_: *mut crate::leanh::LeanObject,
    mut v_a_6558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6559_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(
        v_mvarId_6551_,
        v_e_6552_,
        v_hName_x3f_6553_,
        v_a_6554_,
        v_a_6555_,
        v_a_6556_,
        v_a_6557_,
    );
    crate::leanh::lean_dec(v_a_6557_);
    crate::leanh::lean_dec_ref(v_a_6556_);
    crate::leanh::lean_dec(v_a_6555_);
    crate::leanh::lean_dec_ref(v_a_6554_);
    return v_res_6559_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0(
    mut v___y_6560_: *mut crate::leanh::LeanObject,
    mut v___y_6561_: *mut crate::leanh::LeanObject,
    mut v___y_6562_: *mut crate::leanh::LeanObject,
    mut v___y_6563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lctx_6565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lctx_6565_ = crate::leanh::lean_ctor_get(v___y_6560_, 2);
    crate::leanh::lean_inc_ref(v_lctx_6565_);
    crate::leanh::lean_dec_ref(v___y_6560_);
    v___x_6566_ = lean_local_ctx_num_indices(v_lctx_6565_);
    v___x_6567_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6567_, 0, v___x_6566_);
    return v___x_6567_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0___boxed(
    mut v___y_6568_: *mut crate::leanh::LeanObject,
    mut v___y_6569_: *mut crate::leanh::LeanObject,
    mut v___y_6570_: *mut crate::leanh::LeanObject,
    mut v___y_6571_: *mut crate::leanh::LeanObject,
    mut v___y_6572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6573_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___lam__0(
        v___y_6568_,
        v___y_6569_,
        v___y_6570_,
        v___y_6571_,
    );
    crate::leanh::lean_dec(v___y_6571_);
    crate::leanh::lean_dec_ref(v___y_6570_);
    crate::leanh::lean_dec(v___y_6569_);
    return v_res_6573_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(
    mut v_mvarId_6575_: *mut crate::leanh::LeanObject,
    mut v_a_6576_: *mut crate::leanh::LeanObject,
    mut v_a_6577_: *mut crate::leanh::LeanObject,
    mut v_a_6578_: *mut crate::leanh::LeanObject,
    mut v_a_6579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6581_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___closed__0;
    v___x_6582_ =
        l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(
            v_mvarId_6575_,
            v___f_6581_,
            v_a_6576_,
            v_a_6577_,
            v_a_6578_,
            v_a_6579_,
        );
    return v___x_6582_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices___boxed(
    mut v_mvarId_6583_: *mut crate::leanh::LeanObject,
    mut v_a_6584_: *mut crate::leanh::LeanObject,
    mut v_a_6585_: *mut crate::leanh::LeanObject,
    mut v_a_6586_: *mut crate::leanh::LeanObject,
    mut v_a_6587_: *mut crate::leanh::LeanObject,
    mut v_a_6588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6589_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(
        v_mvarId_6583_,
        v_a_6584_,
        v_a_6585_,
        v_a_6586_,
        v_a_6587_,
    );
    crate::leanh::lean_dec(v_a_6587_);
    crate::leanh::lean_dec_ref(v_a_6586_);
    crate::leanh::lean_dec(v_a_6585_);
    crate::leanh::lean_dec_ref(v_a_6584_);
    return v_res_6589_;
}
pub unsafe fn l_panic___at___00Lean_Meta_simpIfTarget_spec__0(
    mut v_msg_6591_: *mut crate::leanh::LeanObject,
    mut v___y_6592_: *mut crate::leanh::LeanObject,
    mut v___y_6593_: *mut crate::leanh::LeanObject,
    mut v___y_6594_: *mut crate::leanh::LeanObject,
    mut v___y_6595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955__overap_6598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6597_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0___closed__0;
    v___x_1955__overap_6598_ = lean_panic_fn_borrowed(v___f_6597_, v_msg_6591_);
    crate::leanh::lean_inc(v___y_6595_);
    crate::leanh::lean_inc_ref(v___y_6594_);
    crate::leanh::lean_inc(v___y_6593_);
    crate::leanh::lean_inc_ref(v___y_6592_);
    v___x_6599_ = crate::leanh::lean_apply_5(
        v___x_1955__overap_6598_,
        v___y_6592_,
        v___y_6593_,
        v___y_6594_,
        v___y_6595_,
        crate::leanh::lean_box(0),
    );
    return v___x_6599_;
}
pub unsafe fn l_panic___at___00Lean_Meta_simpIfTarget_spec__0___boxed(
    mut v_msg_6600_: *mut crate::leanh::LeanObject,
    mut v___y_6601_: *mut crate::leanh::LeanObject,
    mut v___y_6602_: *mut crate::leanh::LeanObject,
    mut v___y_6603_: *mut crate::leanh::LeanObject,
    mut v___y_6604_: *mut crate::leanh::LeanObject,
    mut v___y_6605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6606_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(
        v_msg_6600_,
        v___y_6601_,
        v___y_6602_,
        v___y_6603_,
        v___y_6604_,
    );
    crate::leanh::lean_dec(v___y_6604_);
    crate::leanh::lean_dec_ref(v___y_6603_);
    crate::leanh::lean_dec(v___y_6602_);
    crate::leanh::lean_dec_ref(v___y_6601_);
    return v_res_6606_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(
    mut v_opts_6607_: *mut crate::leanh::LeanObject,
    mut v_opt_6608_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_6609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_6610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_6611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_6609_ = crate::leanh::lean_ctor_get(v_opt_6608_, 0);
    v_defValue_6610_ = crate::leanh::lean_ctor_get(v_opt_6608_, 1);
    v_map_6611_ = crate::leanh::lean_ctor_get(v_opts_6607_, 0);
    v___x_6612_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_6611_,
            v_name_6609_,
        );
    if crate::leanh::lean_obj_tag(v___x_6612_) == 0 {
        let mut v___x_6613_: u8 = 0;
        v___x_6613_ = (crate::leanh::lean_unbox(v_defValue_6610_) as u8);
        return v___x_6613_;
    } else {
        let mut v_val_6614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6614_ = crate::leanh::lean_ctor_get(v___x_6612_, 0);
        crate::leanh::lean_inc(v_val_6614_);
        crate::leanh::lean_dec_ref_known(v___x_6612_, 1);
        if crate::leanh::lean_obj_tag(v_val_6614_) == 1 {
            let mut v_v_6615_: u8 = 0;
            v_v_6615_ = crate::leanh::lean_ctor_get_uint8(v_val_6614_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_6614_, 0);
            return v_v_6615_;
        } else {
            let mut v___x_6616_: u8 = 0;
            crate::leanh::lean_dec(v_val_6614_);
            v___x_6616_ = (crate::leanh::lean_unbox(v_defValue_6610_) as u8);
            return v___x_6616_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1___boxed(
    mut v_opts_6617_: *mut crate::leanh::LeanObject,
    mut v_opt_6618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6619_: u8 = 0;
    let mut v_r_6620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6619_ =
        l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(v_opts_6617_, v_opt_6618_);
    crate::leanh::lean_dec_ref(v_opt_6618_);
    crate::leanh::lean_dec_ref(v_opts_6617_);
    v_r_6620_ = crate::leanh::lean_box((v_res_6619_) as usize);
    return v_r_6620_;
}
pub unsafe fn _init_l_Lean_Meta_simpIfTarget___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_6621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6621_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_6621_;
}
pub unsafe fn _init_l_Lean_Meta_simpIfTarget___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_6622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6622_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_simpIfTarget___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_simpIfTarget___closed__0_once),
        _init_l_Lean_Meta_simpIfTarget___closed__0,
    );
    v___x_6623_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6623_, 0, v___x_6622_);
    return v___x_6623_;
}
pub unsafe fn _init_l_Lean_Meta_simpIfTarget___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_6624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6624_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6625_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_simpIfTarget___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_simpIfTarget___closed__1_once),
        _init_l_Lean_Meta_simpIfTarget___closed__1,
    );
    v___x_6626_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6626_, 0, v___x_6625_);
    crate::leanh::lean_ctor_set(v___x_6626_, 1, v___x_6624_);
    return v___x_6626_;
}
pub unsafe fn _init_l_Lean_Meta_simpIfTarget___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_6627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6627_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_6628_ = lean_mk_empty_array_with_capacity(v___x_6627_);
    v___x_6629_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6629_, 0, v___x_6628_);
    return v___x_6629_;
}
pub unsafe fn _init_l_Lean_Meta_simpIfTarget___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_6630_: usize = 0;
    let mut v___x_6631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6630_ = 5usize;
    v___x_6631_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6632_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_6633_ = lean_mk_empty_array_with_capacity(v___x_6632_);
    v___x_6634_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_simpIfTarget___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_simpIfTarget___closed__3_once),
        _init_l_Lean_Meta_simpIfTarget___closed__3,
    );
    v___x_6635_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_6635_, 0, v___x_6634_);
    crate::leanh::lean_ctor_set(v___x_6635_, 1, v___x_6633_);
    crate::leanh::lean_ctor_set(v___x_6635_, 2, v___x_6631_);
    crate::leanh::lean_ctor_set(v___x_6635_, 3, v___x_6631_);
    crate::leanh::lean_ctor_set_usize(v___x_6635_, 4, v___x_6630_);
    return v___x_6635_;
}
pub unsafe fn _init_l_Lean_Meta_simpIfTarget___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_6636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6636_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_simpIfTarget___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_simpIfTarget___closed__4_once),
        _init_l_Lean_Meta_simpIfTarget___closed__4,
    );
    v___x_6637_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_simpIfTarget___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_simpIfTarget___closed__1_once),
        _init_l_Lean_Meta_simpIfTarget___closed__1,
    );
    v___x_6638_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6638_, 0, v___x_6637_);
    crate::leanh::lean_ctor_set(v___x_6638_, 1, v___x_6637_);
    crate::leanh::lean_ctor_set(v___x_6638_, 2, v___x_6637_);
    crate::leanh::lean_ctor_set(v___x_6638_, 3, v___x_6636_);
    return v___x_6638_;
}
pub unsafe fn _init_l_Lean_Meta_simpIfTarget___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_6639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6639_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_simpIfTarget___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Meta_simpIfTarget___closed__5_once),
        _init_l_Lean_Meta_simpIfTarget___closed__5,
    );
    v___x_6640_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_simpIfTarget___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_simpIfTarget___closed__2_once),
        _init_l_Lean_Meta_simpIfTarget___closed__2,
    );
    v___x_6641_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6641_, 0, v___x_6640_);
    crate::leanh::lean_ctor_set(v___x_6641_, 1, v___x_6639_);
    return v___x_6641_;
}
pub unsafe fn _init_l_Lean_Meta_simpIfTarget___closed__10() -> *mut crate::leanh::LeanObject {
    let mut v___x_6645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6645_ = l_Lean_Meta_simpIfTarget___closed__9;
    v___x_6646_ = crate::leanh::lean_unsigned_to_nat(78);
    v___x_6647_ = crate::leanh::lean_unsigned_to_nat(289);
    v___x_6648_ = l_Lean_Meta_simpIfTarget___closed__8;
    v___x_6649_ = l_Lean_Meta_simpIfTarget___closed__7;
    v___x_6650_ = l_mkPanicMessageWithDecl(
        v___x_6649_,
        v___x_6648_,
        v___x_6647_,
        v___x_6646_,
        v___x_6645_,
    );
    return v___x_6650_;
}
pub unsafe fn _init_l_Lean_Meta_simpIfTarget___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v___x_6653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6653_ = l_Lean_Meta_simpIfTarget___closed__9;
    v___x_6654_ = crate::leanh::lean_unsigned_to_nat(128);
    v___x_6655_ = crate::leanh::lean_unsigned_to_nat(293);
    v___x_6656_ = l_Lean_Meta_simpIfTarget___closed__8;
    v___x_6657_ = l_Lean_Meta_simpIfTarget___closed__7;
    v___x_6658_ = l_mkPanicMessageWithDecl(
        v___x_6657_,
        v___x_6656_,
        v___x_6655_,
        v___x_6654_,
        v___x_6653_,
    );
    return v___x_6658_;
}
pub unsafe fn l_Lean_Meta_simpIfTarget(
    mut v_mvarId_6659_: *mut crate::leanh::LeanObject,
    mut v_useDecide_6660_: u8,
    mut v_useNewSemantics_6661_: u8,
    mut v_a_6662_: *mut crate::leanh::LeanObject,
    mut v_a_6663_: *mut crate::leanh::LeanObject,
    mut v_a_6664_: *mut crate::leanh::LeanObject,
    mut v_a_6665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6675_: u8 = 0;
    let mut v___x_6676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6681_: u8 = 0;
    let mut v_fst_6682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6689_: u8 = 0;
    let mut v_a_6690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6693_: u8 = 0;
    let mut v___x_6695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6697_: u8 = 0;
    let mut v_a_6698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6701_: u8 = 0;
    let mut v___x_6703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6705_: u8 = 0;
    let mut v_a_6706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6709_: u8 = 0;
    let mut v___x_6711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6713_: u8 = 0;
    let mut v_options_6714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6716_: u8 = 0;
    let mut v___x_6717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6730_: u8 = 0;
    let mut v_fst_6731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6738_: u8 = 0;
    let mut v_a_6739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6742_: u8 = 0;
    let mut v___x_6744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6746_: u8 = 0;
    let mut v_a_6747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6750_: u8 = 0;
    let mut v___x_6752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6754_: u8 = 0;
    let mut v_a_6755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6758_: u8 = 0;
    let mut v___x_6760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6762_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_useNewSemantics_6661_ == 0 {
                    v_options_6714_ = crate::leanh::lean_ctor_get(v_a_6664_, 2);
                    v___x_6715_ = l_Lean_Meta_backward_split;
                    v___x_6716_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(
                        v_options_6714_,
                        v___x_6715_,
                    );
                    if v___x_6716_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_6717_ = l_Lean_Meta_SplitIf_getSimpContext(
                            v_a_6662_, v_a_6663_, v_a_6664_, v_a_6665_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6717_) == 0 {
                            v_a_6718_ = crate::leanh::lean_ctor_get(v___x_6717_, 0);
                            crate::leanh::lean_inc(v_a_6718_);
                            crate::leanh::lean_dec_ref_known(v___x_6717_, 1);
                            v___x_6719_ = crate::leanh::lean_box((v_useDecide_6660_) as usize);
                            v___x_6720_ = crate::leanh::lean_alloc_closure(
                                l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed
                                    as *mut core::ffi::c_void,
                                6,
                                1,
                            );
                            crate::leanh::lean_closure_set(v___x_6720_, 0, v___x_6719_);
                            crate::leanh::lean_inc(v_mvarId_6659_);
                            v___x_6721_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_6659_, v___x_6720_, v_a_6662_, v_a_6663_, v_a_6664_, v_a_6665_);
                            if crate::leanh::lean_obj_tag(v___x_6721_) == 0 {
                                v_a_6722_ = crate::leanh::lean_ctor_get(v___x_6721_, 0);
                                crate::leanh::lean_inc(v_a_6722_);
                                crate::leanh::lean_dec_ref_known(v___x_6721_, 1);
                                v___x_6723_ = l_Lean_Meta_simpIfTarget___closed__11;
                                v___x_6724_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_6724_, 0, v_a_6722_);
                                v___x_6725_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(l_Lean_Meta_simpIfTarget___closed__6),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_simpIfTarget___closed__6_once
                                    ),
                                    _init_l_Lean_Meta_simpIfTarget___closed__6,
                                );
                                v___x_6726_ = l_Lean_Meta_simpTarget(
                                    v_mvarId_6659_,
                                    v_a_6718_,
                                    v___x_6723_,
                                    v___x_6724_,
                                    v_useNewSemantics_6661_,
                                    v___x_6725_,
                                    v_a_6662_,
                                    v_a_6663_,
                                    v_a_6664_,
                                    v_a_6665_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_6726_) == 0 {
                                    v_a_6727_ = crate::leanh::lean_ctor_get(v___x_6726_, 0);
                                    v_isSharedCheck_6738_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6726_)) as u8;
                                    if v_isSharedCheck_6738_ == 0 {
                                        v___x_6729_ = v___x_6726_;
                                        v_isShared_6730_ = v_isSharedCheck_6738_;
                                        state = 10;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6727_);
                                        crate::leanh::lean_dec(v___x_6726_);
                                        v___x_6729_ = crate::leanh::lean_box(0);
                                        v_isShared_6730_ = v_isSharedCheck_6738_;
                                        state = 10;
                                        continue;
                                    }
                                } else {
                                    v_a_6739_ = crate::leanh::lean_ctor_get(v___x_6726_, 0);
                                    v_isSharedCheck_6746_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6726_)) as u8;
                                    if v_isSharedCheck_6746_ == 0 {
                                        v___x_6741_ = v___x_6726_;
                                        v_isShared_6742_ = v_isSharedCheck_6746_;
                                        state = 12;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6739_);
                                        crate::leanh::lean_dec(v___x_6726_);
                                        v___x_6741_ = crate::leanh::lean_box(0);
                                        v_isShared_6742_ = v_isSharedCheck_6746_;
                                        state = 12;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_6718_);
                                crate::leanh::lean_dec(v_mvarId_6659_);
                                v_a_6747_ = crate::leanh::lean_ctor_get(v___x_6721_, 0);
                                v_isSharedCheck_6754_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6721_)) as u8;
                                if v_isSharedCheck_6754_ == 0 {
                                    v___x_6749_ = v___x_6721_;
                                    v_isShared_6750_ = v_isSharedCheck_6754_;
                                    state = 14;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6747_);
                                    crate::leanh::lean_dec(v___x_6721_);
                                    v___x_6749_ = crate::leanh::lean_box(0);
                                    v_isShared_6750_ = v_isSharedCheck_6754_;
                                    state = 14;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_mvarId_6659_);
                            v_a_6755_ = crate::leanh::lean_ctor_get(v___x_6717_, 0);
                            v_isSharedCheck_6762_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6717_)) as u8;
                            if v_isSharedCheck_6762_ == 0 {
                                v___x_6757_ = v___x_6717_;
                                v_isShared_6758_ = v_isSharedCheck_6762_;
                                state = 16;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6755_);
                                crate::leanh::lean_dec(v___x_6717_);
                                v___x_6757_ = crate::leanh::lean_box(0);
                                v_isShared_6758_ = v_isSharedCheck_6762_;
                                state = 16;
                                continue;
                            }
                        }
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6668_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_6662_, v_a_6664_, v_a_6665_);
                if crate::leanh::lean_obj_tag(v___x_6668_) == 0 {
                    v_a_6669_ = crate::leanh::lean_ctor_get(v___x_6668_, 0);
                    crate::leanh::lean_inc(v_a_6669_);
                    crate::leanh::lean_dec_ref_known(v___x_6668_, 1);
                    crate::leanh::lean_inc(v_mvarId_6659_);
                    v___x_6670_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(
                        v_mvarId_6659_,
                        v_a_6662_,
                        v_a_6663_,
                        v_a_6664_,
                        v_a_6665_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6670_) == 0 {
                        v_a_6671_ = crate::leanh::lean_ctor_get(v___x_6670_, 0);
                        crate::leanh::lean_inc(v_a_6671_);
                        crate::leanh::lean_dec_ref_known(v___x_6670_, 1);
                        v___x_6672_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_a_6671_, v_useDecide_6660_);
                        v_a_6673_ = crate::leanh::lean_ctor_get(v___x_6672_, 0);
                        crate::leanh::lean_inc(v_a_6673_);
                        crate::leanh::lean_dec_ref(v___x_6672_);
                        v___x_6674_ = crate::leanh::lean_box(0);
                        v___x_6675_ = 0;
                        v___x_6676_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_simpIfTarget___closed__6),
                            core::ptr::addr_of_mut!(l_Lean_Meta_simpIfTarget___closed__6_once),
                            _init_l_Lean_Meta_simpIfTarget___closed__6,
                        );
                        v___x_6677_ = l_Lean_Meta_simpTarget(
                            v_mvarId_6659_,
                            v_a_6669_,
                            v_a_6673_,
                            v___x_6674_,
                            v___x_6675_,
                            v___x_6676_,
                            v_a_6662_,
                            v_a_6663_,
                            v_a_6664_,
                            v_a_6665_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6677_) == 0 {
                            v_a_6678_ = crate::leanh::lean_ctor_get(v___x_6677_, 0);
                            v_isSharedCheck_6689_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6677_)) as u8;
                            if v_isSharedCheck_6689_ == 0 {
                                v___x_6680_ = v___x_6677_;
                                v_isShared_6681_ = v_isSharedCheck_6689_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6678_);
                                crate::leanh::lean_dec(v___x_6677_);
                                v___x_6680_ = crate::leanh::lean_box(0);
                                v_isShared_6681_ = v_isSharedCheck_6689_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_a_6690_ = crate::leanh::lean_ctor_get(v___x_6677_, 0);
                            v_isSharedCheck_6697_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6677_)) as u8;
                            if v_isSharedCheck_6697_ == 0 {
                                v___x_6692_ = v___x_6677_;
                                v_isShared_6693_ = v_isSharedCheck_6697_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6690_);
                                crate::leanh::lean_dec(v___x_6677_);
                                v___x_6692_ = crate::leanh::lean_box(0);
                                v_isShared_6693_ = v_isSharedCheck_6697_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6669_);
                        crate::leanh::lean_dec(v_mvarId_6659_);
                        v_a_6698_ = crate::leanh::lean_ctor_get(v___x_6670_, 0);
                        v_isSharedCheck_6705_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6670_)) as u8;
                        if v_isSharedCheck_6705_ == 0 {
                            v___x_6700_ = v___x_6670_;
                            v_isShared_6701_ = v_isSharedCheck_6705_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6698_);
                            crate::leanh::lean_dec(v___x_6670_);
                            v___x_6700_ = crate::leanh::lean_box(0);
                            v_isShared_6701_ = v_isSharedCheck_6705_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_6659_);
                    v_a_6706_ = crate::leanh::lean_ctor_get(v___x_6668_, 0);
                    v_isSharedCheck_6713_ = (!crate::leanh::lean_is_exclusive(v___x_6668_)) as u8;
                    if v_isSharedCheck_6713_ == 0 {
                        v___x_6708_ = v___x_6668_;
                        v_isShared_6709_ = v_isSharedCheck_6713_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6706_);
                        crate::leanh::lean_dec(v___x_6668_);
                        v___x_6708_ = crate::leanh::lean_box(0);
                        v_isShared_6709_ = v_isSharedCheck_6713_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_6682_ = crate::leanh::lean_ctor_get(v_a_6678_, 0);
                crate::leanh::lean_inc(v_fst_6682_);
                crate::leanh::lean_dec(v_a_6678_);
                if crate::leanh::lean_obj_tag(v_fst_6682_) == 1 {
                    v_val_6683_ = crate::leanh::lean_ctor_get(v_fst_6682_, 0);
                    crate::leanh::lean_inc(v_val_6683_);
                    crate::leanh::lean_dec_ref_known(v_fst_6682_, 1);
                    if v_isShared_6681_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6680_, 0, v_val_6683_);
                        v___x_6685_ = v___x_6680_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6686_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6686_, 0, v_val_6683_);
                        v___x_6685_ = v_reuseFailAlloc_6686_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_6682_);
                    crate::leanh::lean_del_object(v___x_6680_);
                    v___x_6687_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_simpIfTarget___closed__10),
                        core::ptr::addr_of_mut!(l_Lean_Meta_simpIfTarget___closed__10_once),
                        _init_l_Lean_Meta_simpIfTarget___closed__10,
                    );
                    v___x_6688_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(
                        v___x_6687_,
                        v_a_6662_,
                        v_a_6663_,
                        v_a_6664_,
                        v_a_6665_,
                    );
                    return v___x_6688_;
                }
            }
            3 => {
                return v___x_6685_;
            }
            4 => {
                if v_isShared_6693_ == 0 {
                    v___x_6695_ = v___x_6692_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6696_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6696_, 0, v_a_6690_);
                    v___x_6695_ = v_reuseFailAlloc_6696_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6695_;
            }
            6 => {
                if v_isShared_6701_ == 0 {
                    v___x_6703_ = v___x_6700_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6704_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6704_, 0, v_a_6698_);
                    v___x_6703_ = v_reuseFailAlloc_6704_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6703_;
            }
            8 => {
                if v_isShared_6709_ == 0 {
                    v___x_6711_ = v___x_6708_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6712_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6712_, 0, v_a_6706_);
                    v___x_6711_ = v_reuseFailAlloc_6712_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6711_;
            }
            10 => {
                v_fst_6731_ = crate::leanh::lean_ctor_get(v_a_6727_, 0);
                crate::leanh::lean_inc(v_fst_6731_);
                crate::leanh::lean_dec(v_a_6727_);
                if crate::leanh::lean_obj_tag(v_fst_6731_) == 1 {
                    v_val_6732_ = crate::leanh::lean_ctor_get(v_fst_6731_, 0);
                    crate::leanh::lean_inc(v_val_6732_);
                    crate::leanh::lean_dec_ref_known(v_fst_6731_, 1);
                    if v_isShared_6730_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6729_, 0, v_val_6732_);
                        v___x_6734_ = v___x_6729_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_6735_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6735_, 0, v_val_6732_);
                        v___x_6734_ = v_reuseFailAlloc_6735_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_6731_);
                    crate::leanh::lean_del_object(v___x_6729_);
                    v___x_6736_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_simpIfTarget___closed__12),
                        core::ptr::addr_of_mut!(l_Lean_Meta_simpIfTarget___closed__12_once),
                        _init_l_Lean_Meta_simpIfTarget___closed__12,
                    );
                    v___x_6737_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(
                        v___x_6736_,
                        v_a_6662_,
                        v_a_6663_,
                        v_a_6664_,
                        v_a_6665_,
                    );
                    return v___x_6737_;
                }
            }
            11 => {
                return v___x_6734_;
            }
            12 => {
                if v_isShared_6742_ == 0 {
                    v___x_6744_ = v___x_6741_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6745_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6745_, 0, v_a_6739_);
                    v___x_6744_ = v_reuseFailAlloc_6745_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6744_;
            }
            14 => {
                if v_isShared_6750_ == 0 {
                    v___x_6752_ = v___x_6749_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6753_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6753_, 0, v_a_6747_);
                    v___x_6752_ = v_reuseFailAlloc_6753_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6752_;
            }
            16 => {
                if v_isShared_6758_ == 0 {
                    v___x_6760_ = v___x_6757_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6761_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6761_, 0, v_a_6755_);
                    v___x_6760_ = v_reuseFailAlloc_6761_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6760_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_simpIfTarget___boxed(
    mut v_mvarId_6763_: *mut crate::leanh::LeanObject,
    mut v_useDecide_6764_: *mut crate::leanh::LeanObject,
    mut v_useNewSemantics_6765_: *mut crate::leanh::LeanObject,
    mut v_a_6766_: *mut crate::leanh::LeanObject,
    mut v_a_6767_: *mut crate::leanh::LeanObject,
    mut v_a_6768_: *mut crate::leanh::LeanObject,
    mut v_a_6769_: *mut crate::leanh::LeanObject,
    mut v_a_6770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useDecide_boxed_6771_: u8 = 0;
    let mut v_useNewSemantics_boxed_6772_: u8 = 0;
    let mut v_res_6773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useDecide_boxed_6771_ = (crate::leanh::lean_unbox(v_useDecide_6764_) as u8);
    v_useNewSemantics_boxed_6772_ = (crate::leanh::lean_unbox(v_useNewSemantics_6765_) as u8);
    v_res_6773_ = l_Lean_Meta_simpIfTarget(
        v_mvarId_6763_,
        v_useDecide_boxed_6771_,
        v_useNewSemantics_boxed_6772_,
        v_a_6766_,
        v_a_6767_,
        v_a_6768_,
        v_a_6769_,
    );
    crate::leanh::lean_dec(v_a_6769_);
    crate::leanh::lean_dec_ref(v_a_6768_);
    crate::leanh::lean_dec(v_a_6767_);
    crate::leanh::lean_dec_ref(v_a_6766_);
    return v_res_6773_;
}
pub unsafe fn _init_l_Lean_Meta_simpIfLocalDecl___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_6775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6775_ = l_Lean_Meta_simpIfTarget___closed__9;
    v___x_6776_ = crate::leanh::lean_unsigned_to_nat(93);
    v___x_6777_ = crate::leanh::lean_unsigned_to_nat(305);
    v___x_6778_ = l_Lean_Meta_simpIfLocalDecl___closed__0;
    v___x_6779_ = l_Lean_Meta_simpIfTarget___closed__7;
    v___x_6780_ = l_mkPanicMessageWithDecl(
        v___x_6779_,
        v___x_6778_,
        v___x_6777_,
        v___x_6776_,
        v___x_6775_,
    );
    return v___x_6780_;
}
pub unsafe fn _init_l_Lean_Meta_simpIfLocalDecl___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_6781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6781_ = l_Lean_Meta_simpIfTarget___closed__9;
    v___x_6782_ = crate::leanh::lean_unsigned_to_nat(133);
    v___x_6783_ = crate::leanh::lean_unsigned_to_nat(309);
    v___x_6784_ = l_Lean_Meta_simpIfLocalDecl___closed__0;
    v___x_6785_ = l_Lean_Meta_simpIfTarget___closed__7;
    v___x_6786_ = l_mkPanicMessageWithDecl(
        v___x_6785_,
        v___x_6784_,
        v___x_6783_,
        v___x_6782_,
        v___x_6781_,
    );
    return v___x_6786_;
}
pub unsafe fn l_Lean_Meta_simpIfLocalDecl(
    mut v_mvarId_6787_: *mut crate::leanh::LeanObject,
    mut v_fvarId_6788_: *mut crate::leanh::LeanObject,
    mut v_useNewSemantics_6789_: u8,
    mut v_a_6790_: *mut crate::leanh::LeanObject,
    mut v_a_6791_: *mut crate::leanh::LeanObject,
    mut v_a_6792_: *mut crate::leanh::LeanObject,
    mut v_a_6793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6800_: u8 = 0;
    let mut v___x_6801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6809_: u8 = 0;
    let mut v_fst_6810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6818_: u8 = 0;
    let mut v_a_6819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6822_: u8 = 0;
    let mut v___x_6824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6826_: u8 = 0;
    let mut v_a_6827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6830_: u8 = 0;
    let mut v___x_6832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6834_: u8 = 0;
    let mut v_a_6835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6838_: u8 = 0;
    let mut v___x_6840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6842_: u8 = 0;
    let mut v_options_6843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6845_: u8 = 0;
    let mut v___x_6846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6859_: u8 = 0;
    let mut v_fst_6860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6868_: u8 = 0;
    let mut v_a_6869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6872_: u8 = 0;
    let mut v___x_6874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6876_: u8 = 0;
    let mut v_a_6877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6880_: u8 = 0;
    let mut v___x_6882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6884_: u8 = 0;
    let mut v_a_6885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6888_: u8 = 0;
    let mut v___x_6890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6892_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_useNewSemantics_6789_ == 0 {
                    v_options_6843_ = crate::leanh::lean_ctor_get(v_a_6792_, 2);
                    v___x_6844_ = l_Lean_Meta_backward_split;
                    v___x_6845_ = l_Lean_Option_get___at___00Lean_Meta_simpIfTarget_spec__1(
                        v_options_6843_,
                        v___x_6844_,
                    );
                    if v___x_6845_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_6846_ = l_Lean_Meta_SplitIf_getSimpContext(
                            v_a_6790_, v_a_6791_, v_a_6792_, v_a_6793_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6846_) == 0 {
                            v_a_6847_ = crate::leanh::lean_ctor_get(v___x_6846_, 0);
                            crate::leanh::lean_inc(v_a_6847_);
                            crate::leanh::lean_dec_ref_known(v___x_6846_, 1);
                            v___x_6848_ =
                                crate::leanh::lean_box((v_useNewSemantics_6789_) as usize);
                            v___x_6849_ = crate::leanh::lean_alloc_closure(
                                l_Lean_Meta_SplitIf_mkDischarge_x3f___boxed
                                    as *mut core::ffi::c_void,
                                6,
                                1,
                            );
                            crate::leanh::lean_closure_set(v___x_6849_, 0, v___x_6848_);
                            crate::leanh::lean_inc(v_mvarId_6787_);
                            v___x_6850_ = l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___redArg(v_mvarId_6787_, v___x_6849_, v_a_6790_, v_a_6791_, v_a_6792_, v_a_6793_);
                            if crate::leanh::lean_obj_tag(v___x_6850_) == 0 {
                                v_a_6851_ = crate::leanh::lean_ctor_get(v___x_6850_, 0);
                                crate::leanh::lean_inc(v_a_6851_);
                                crate::leanh::lean_dec_ref_known(v___x_6850_, 1);
                                v___x_6852_ = l_Lean_Meta_simpIfTarget___closed__11;
                                v___x_6853_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_6853_, 0, v_a_6851_);
                                v___x_6854_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(l_Lean_Meta_simpIfTarget___closed__6),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_simpIfTarget___closed__6_once
                                    ),
                                    _init_l_Lean_Meta_simpIfTarget___closed__6,
                                );
                                v___x_6855_ = l_Lean_Meta_simpLocalDecl(
                                    v_mvarId_6787_,
                                    v_fvarId_6788_,
                                    v_a_6847_,
                                    v___x_6852_,
                                    v___x_6853_,
                                    v_useNewSemantics_6789_,
                                    v___x_6854_,
                                    v_a_6790_,
                                    v_a_6791_,
                                    v_a_6792_,
                                    v_a_6793_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_6855_) == 0 {
                                    v_a_6856_ = crate::leanh::lean_ctor_get(v___x_6855_, 0);
                                    v_isSharedCheck_6868_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6855_)) as u8;
                                    if v_isSharedCheck_6868_ == 0 {
                                        v___x_6858_ = v___x_6855_;
                                        v_isShared_6859_ = v_isSharedCheck_6868_;
                                        state = 10;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6856_);
                                        crate::leanh::lean_dec(v___x_6855_);
                                        v___x_6858_ = crate::leanh::lean_box(0);
                                        v_isShared_6859_ = v_isSharedCheck_6868_;
                                        state = 10;
                                        continue;
                                    }
                                } else {
                                    v_a_6869_ = crate::leanh::lean_ctor_get(v___x_6855_, 0);
                                    v_isSharedCheck_6876_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6855_)) as u8;
                                    if v_isSharedCheck_6876_ == 0 {
                                        v___x_6871_ = v___x_6855_;
                                        v_isShared_6872_ = v_isSharedCheck_6876_;
                                        state = 12;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6869_);
                                        crate::leanh::lean_dec(v___x_6855_);
                                        v___x_6871_ = crate::leanh::lean_box(0);
                                        v_isShared_6872_ = v_isSharedCheck_6876_;
                                        state = 12;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_6847_);
                                crate::leanh::lean_dec(v_fvarId_6788_);
                                crate::leanh::lean_dec(v_mvarId_6787_);
                                v_a_6877_ = crate::leanh::lean_ctor_get(v___x_6850_, 0);
                                v_isSharedCheck_6884_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6850_)) as u8;
                                if v_isSharedCheck_6884_ == 0 {
                                    v___x_6879_ = v___x_6850_;
                                    v_isShared_6880_ = v_isSharedCheck_6884_;
                                    state = 14;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6877_);
                                    crate::leanh::lean_dec(v___x_6850_);
                                    v___x_6879_ = crate::leanh::lean_box(0);
                                    v_isShared_6880_ = v_isSharedCheck_6884_;
                                    state = 14;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_fvarId_6788_);
                            crate::leanh::lean_dec(v_mvarId_6787_);
                            v_a_6885_ = crate::leanh::lean_ctor_get(v___x_6846_, 0);
                            v_isSharedCheck_6892_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6846_)) as u8;
                            if v_isSharedCheck_6892_ == 0 {
                                v___x_6887_ = v___x_6846_;
                                v_isShared_6888_ = v_isSharedCheck_6892_;
                                state = 16;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6885_);
                                crate::leanh::lean_dec(v___x_6846_);
                                v___x_6887_ = crate::leanh::lean_box(0);
                                v_isShared_6888_ = v_isSharedCheck_6892_;
                                state = 16;
                                continue;
                            }
                        }
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6796_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimpContext_x27___redArg(v_a_6790_, v_a_6792_, v_a_6793_);
                if crate::leanh::lean_obj_tag(v___x_6796_) == 0 {
                    v_a_6797_ = crate::leanh::lean_ctor_get(v___x_6796_, 0);
                    crate::leanh::lean_inc(v_a_6797_);
                    crate::leanh::lean_dec_ref_known(v___x_6796_, 1);
                    crate::leanh::lean_inc(v_mvarId_6787_);
                    v___x_6798_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_getNumIndices(
                        v_mvarId_6787_,
                        v_a_6790_,
                        v_a_6791_,
                        v_a_6792_,
                        v_a_6793_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6798_) == 0 {
                        v_a_6799_ = crate::leanh::lean_ctor_get(v___x_6798_, 0);
                        crate::leanh::lean_inc(v_a_6799_);
                        crate::leanh::lean_dec_ref_known(v___x_6798_, 1);
                        v___x_6800_ = 0;
                        v___x_6801_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_getSimprocs___redArg(v_a_6799_, v___x_6800_);
                        v_a_6802_ = crate::leanh::lean_ctor_get(v___x_6801_, 0);
                        crate::leanh::lean_inc(v_a_6802_);
                        crate::leanh::lean_dec_ref(v___x_6801_);
                        v___x_6803_ = crate::leanh::lean_box(0);
                        v___x_6804_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_simpIfTarget___closed__6),
                            core::ptr::addr_of_mut!(l_Lean_Meta_simpIfTarget___closed__6_once),
                            _init_l_Lean_Meta_simpIfTarget___closed__6,
                        );
                        v___x_6805_ = l_Lean_Meta_simpLocalDecl(
                            v_mvarId_6787_,
                            v_fvarId_6788_,
                            v_a_6797_,
                            v_a_6802_,
                            v___x_6803_,
                            v___x_6800_,
                            v___x_6804_,
                            v_a_6790_,
                            v_a_6791_,
                            v_a_6792_,
                            v_a_6793_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6805_) == 0 {
                            v_a_6806_ = crate::leanh::lean_ctor_get(v___x_6805_, 0);
                            v_isSharedCheck_6818_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6805_)) as u8;
                            if v_isSharedCheck_6818_ == 0 {
                                v___x_6808_ = v___x_6805_;
                                v_isShared_6809_ = v_isSharedCheck_6818_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6806_);
                                crate::leanh::lean_dec(v___x_6805_);
                                v___x_6808_ = crate::leanh::lean_box(0);
                                v_isShared_6809_ = v_isSharedCheck_6818_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_a_6819_ = crate::leanh::lean_ctor_get(v___x_6805_, 0);
                            v_isSharedCheck_6826_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6805_)) as u8;
                            if v_isSharedCheck_6826_ == 0 {
                                v___x_6821_ = v___x_6805_;
                                v_isShared_6822_ = v_isSharedCheck_6826_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6819_);
                                crate::leanh::lean_dec(v___x_6805_);
                                v___x_6821_ = crate::leanh::lean_box(0);
                                v_isShared_6822_ = v_isSharedCheck_6826_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6797_);
                        crate::leanh::lean_dec(v_fvarId_6788_);
                        crate::leanh::lean_dec(v_mvarId_6787_);
                        v_a_6827_ = crate::leanh::lean_ctor_get(v___x_6798_, 0);
                        v_isSharedCheck_6834_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6798_)) as u8;
                        if v_isSharedCheck_6834_ == 0 {
                            v___x_6829_ = v___x_6798_;
                            v_isShared_6830_ = v_isSharedCheck_6834_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6827_);
                            crate::leanh::lean_dec(v___x_6798_);
                            v___x_6829_ = crate::leanh::lean_box(0);
                            v_isShared_6830_ = v_isSharedCheck_6834_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fvarId_6788_);
                    crate::leanh::lean_dec(v_mvarId_6787_);
                    v_a_6835_ = crate::leanh::lean_ctor_get(v___x_6796_, 0);
                    v_isSharedCheck_6842_ = (!crate::leanh::lean_is_exclusive(v___x_6796_)) as u8;
                    if v_isSharedCheck_6842_ == 0 {
                        v___x_6837_ = v___x_6796_;
                        v_isShared_6838_ = v_isSharedCheck_6842_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6835_);
                        crate::leanh::lean_dec(v___x_6796_);
                        v___x_6837_ = crate::leanh::lean_box(0);
                        v_isShared_6838_ = v_isSharedCheck_6842_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_6810_ = crate::leanh::lean_ctor_get(v_a_6806_, 0);
                crate::leanh::lean_inc(v_fst_6810_);
                crate::leanh::lean_dec(v_a_6806_);
                if crate::leanh::lean_obj_tag(v_fst_6810_) == 1 {
                    v_val_6811_ = crate::leanh::lean_ctor_get(v_fst_6810_, 0);
                    crate::leanh::lean_inc(v_val_6811_);
                    crate::leanh::lean_dec_ref_known(v_fst_6810_, 1);
                    v_snd_6812_ = crate::leanh::lean_ctor_get(v_val_6811_, 1);
                    crate::leanh::lean_inc(v_snd_6812_);
                    crate::leanh::lean_dec(v_val_6811_);
                    if v_isShared_6809_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6808_, 0, v_snd_6812_);
                        v___x_6814_ = v___x_6808_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6815_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6815_, 0, v_snd_6812_);
                        v___x_6814_ = v_reuseFailAlloc_6815_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_6810_);
                    crate::leanh::lean_del_object(v___x_6808_);
                    v___x_6816_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_simpIfLocalDecl___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_simpIfLocalDecl___closed__1_once),
                        _init_l_Lean_Meta_simpIfLocalDecl___closed__1,
                    );
                    v___x_6817_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(
                        v___x_6816_,
                        v_a_6790_,
                        v_a_6791_,
                        v_a_6792_,
                        v_a_6793_,
                    );
                    return v___x_6817_;
                }
            }
            3 => {
                return v___x_6814_;
            }
            4 => {
                if v_isShared_6822_ == 0 {
                    v___x_6824_ = v___x_6821_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6825_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6825_, 0, v_a_6819_);
                    v___x_6824_ = v_reuseFailAlloc_6825_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6824_;
            }
            6 => {
                if v_isShared_6830_ == 0 {
                    v___x_6832_ = v___x_6829_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6833_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6833_, 0, v_a_6827_);
                    v___x_6832_ = v_reuseFailAlloc_6833_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6832_;
            }
            8 => {
                if v_isShared_6838_ == 0 {
                    v___x_6840_ = v___x_6837_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6841_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6841_, 0, v_a_6835_);
                    v___x_6840_ = v_reuseFailAlloc_6841_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6840_;
            }
            10 => {
                v_fst_6860_ = crate::leanh::lean_ctor_get(v_a_6856_, 0);
                crate::leanh::lean_inc(v_fst_6860_);
                crate::leanh::lean_dec(v_a_6856_);
                if crate::leanh::lean_obj_tag(v_fst_6860_) == 1 {
                    v_val_6861_ = crate::leanh::lean_ctor_get(v_fst_6860_, 0);
                    crate::leanh::lean_inc(v_val_6861_);
                    crate::leanh::lean_dec_ref_known(v_fst_6860_, 1);
                    v_snd_6862_ = crate::leanh::lean_ctor_get(v_val_6861_, 1);
                    crate::leanh::lean_inc(v_snd_6862_);
                    crate::leanh::lean_dec(v_val_6861_);
                    if v_isShared_6859_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6858_, 0, v_snd_6862_);
                        v___x_6864_ = v___x_6858_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_6865_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6865_, 0, v_snd_6862_);
                        v___x_6864_ = v_reuseFailAlloc_6865_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_6860_);
                    crate::leanh::lean_del_object(v___x_6858_);
                    v___x_6866_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_simpIfLocalDecl___closed__2),
                        core::ptr::addr_of_mut!(l_Lean_Meta_simpIfLocalDecl___closed__2_once),
                        _init_l_Lean_Meta_simpIfLocalDecl___closed__2,
                    );
                    v___x_6867_ = l_panic___at___00Lean_Meta_simpIfTarget_spec__0(
                        v___x_6866_,
                        v_a_6790_,
                        v_a_6791_,
                        v_a_6792_,
                        v_a_6793_,
                    );
                    return v___x_6867_;
                }
            }
            11 => {
                return v___x_6864_;
            }
            12 => {
                if v_isShared_6872_ == 0 {
                    v___x_6874_ = v___x_6871_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6875_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6875_, 0, v_a_6869_);
                    v___x_6874_ = v_reuseFailAlloc_6875_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6874_;
            }
            14 => {
                if v_isShared_6880_ == 0 {
                    v___x_6882_ = v___x_6879_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6883_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6883_, 0, v_a_6877_);
                    v___x_6882_ = v_reuseFailAlloc_6883_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6882_;
            }
            16 => {
                if v_isShared_6888_ == 0 {
                    v___x_6890_ = v___x_6887_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6891_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6891_, 0, v_a_6885_);
                    v___x_6890_ = v_reuseFailAlloc_6891_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6890_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_simpIfLocalDecl___boxed(
    mut v_mvarId_6893_: *mut crate::leanh::LeanObject,
    mut v_fvarId_6894_: *mut crate::leanh::LeanObject,
    mut v_useNewSemantics_6895_: *mut crate::leanh::LeanObject,
    mut v_a_6896_: *mut crate::leanh::LeanObject,
    mut v_a_6897_: *mut crate::leanh::LeanObject,
    mut v_a_6898_: *mut crate::leanh::LeanObject,
    mut v_a_6899_: *mut crate::leanh::LeanObject,
    mut v_a_6900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useNewSemantics_boxed_6901_: u8 = 0;
    let mut v_res_6902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useNewSemantics_boxed_6901_ = (crate::leanh::lean_unbox(v_useNewSemantics_6895_) as u8);
    v_res_6902_ = l_Lean_Meta_simpIfLocalDecl(
        v_mvarId_6893_,
        v_fvarId_6894_,
        v_useNewSemantics_boxed_6901_,
        v_a_6896_,
        v_a_6897_,
        v_a_6898_,
        v_a_6899_,
    );
    crate::leanh::lean_dec(v_a_6899_);
    crate::leanh::lean_dec_ref(v_a_6898_);
    crate::leanh::lean_dec(v_a_6897_);
    crate::leanh::lean_dec_ref(v_a_6896_);
    return v_res_6902_;
}
pub unsafe fn l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(
    mut v_x_x3f_6903_: *mut crate::leanh::LeanObject,
    mut v___y_6904_: *mut crate::leanh::LeanObject,
    mut v___y_6905_: *mut crate::leanh::LeanObject,
    mut v___y_6906_: *mut crate::leanh::LeanObject,
    mut v___y_6907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6913_: u8 = 0;
    let mut v___y_6915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6916_: u8 = 0;
    let mut v___x_6917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6920_: u8 = 0;
    let mut v___x_6922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6924_: u8 = 0;
    let mut v_unused_6925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6929_: u8 = 0;
    let mut v___x_6931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6933_: u8 = 0;
    let mut v___x_6935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6939_: u8 = 0;
    let mut v___x_6940_: u8 = 0;
    let mut v___x_6941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6946_: u8 = 0;
    let mut v___x_6948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6950_: u8 = 0;
    let mut v_unused_6951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6954_: u8 = 0;
    let mut v_a_6955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6958_: u8 = 0;
    let mut v___x_6960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6962_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6909_ = l_Lean_Meta_saveState___redArg(v___y_6905_, v___y_6907_);
                if crate::leanh::lean_obj_tag(v___x_6909_) == 0 {
                    v_a_6910_ = crate::leanh::lean_ctor_get(v___x_6909_, 0);
                    v_isSharedCheck_6954_ = (!crate::leanh::lean_is_exclusive(v___x_6909_)) as u8;
                    if v_isSharedCheck_6954_ == 0 {
                        v___x_6912_ = v___x_6909_;
                        v_isShared_6913_ = v_isSharedCheck_6954_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6910_);
                        crate::leanh::lean_dec(v___x_6909_);
                        v___x_6912_ = crate::leanh::lean_box(0);
                        v_isShared_6913_ = v_isSharedCheck_6954_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_x3f_6903_);
                    v_a_6955_ = crate::leanh::lean_ctor_get(v___x_6909_, 0);
                    v_isSharedCheck_6962_ = (!crate::leanh::lean_is_exclusive(v___x_6909_)) as u8;
                    if v_isSharedCheck_6962_ == 0 {
                        v___x_6957_ = v___x_6909_;
                        v_isShared_6958_ = v_isSharedCheck_6962_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6955_);
                        crate::leanh::lean_dec(v___x_6909_);
                        v___x_6957_ = crate::leanh::lean_box(0);
                        v_isShared_6958_ = v_isSharedCheck_6962_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_6907_);
                crate::leanh::lean_inc_ref(v___y_6906_);
                crate::leanh::lean_inc(v___y_6905_);
                crate::leanh::lean_inc_ref(v___y_6904_);
                v___x_6941_ = crate::leanh::lean_apply_5(
                    v_x_x3f_6903_,
                    v___y_6904_,
                    v___y_6905_,
                    v___y_6906_,
                    v___y_6907_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_6941_) == 0 {
                    v_a_6942_ = crate::leanh::lean_ctor_get(v___x_6941_, 0);
                    crate::leanh::lean_inc(v_a_6942_);
                    if crate::leanh::lean_obj_tag(v_a_6942_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6941_, 1);
                        v___x_6943_ = l_Lean_Meta_SavedState_restore___redArg(
                            v_a_6910_,
                            v___y_6905_,
                            v___y_6907_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6943_) == 0 {
                            crate::leanh::lean_del_object(v___x_6912_);
                            crate::leanh::lean_dec(v_a_6910_);
                            v_isSharedCheck_6950_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6943_)) as u8;
                            if v_isSharedCheck_6950_ == 0 {
                                v_unused_6951_ = crate::leanh::lean_ctor_get(v___x_6943_, 0);
                                crate::leanh::lean_dec(v_unused_6951_);
                                v___x_6945_ = v___x_6943_;
                                v_isShared_6946_ = v_isSharedCheck_6950_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_6943_);
                                v___x_6945_ = crate::leanh::lean_box(0);
                                v_isShared_6946_ = v_isSharedCheck_6950_;
                                state = 9;
                                continue;
                            }
                        } else {
                            v_a_6952_ = crate::leanh::lean_ctor_get(v___x_6943_, 0);
                            crate::leanh::lean_inc(v_a_6952_);
                            crate::leanh::lean_dec_ref_known(v___x_6943_, 1);
                            v_a_6938_ = v_a_6952_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_6942_, 1);
                        crate::leanh::lean_del_object(v___x_6912_);
                        crate::leanh::lean_dec(v_a_6910_);
                        return v___x_6941_;
                    }
                } else {
                    v_a_6953_ = crate::leanh::lean_ctor_get(v___x_6941_, 0);
                    crate::leanh::lean_inc(v_a_6953_);
                    crate::leanh::lean_dec_ref_known(v___x_6941_, 1);
                    v_a_6938_ = v_a_6953_;
                    state = 8;
                    continue;
                }
            }
            2 => {
                if v___y_6916_ == 0 {
                    crate::leanh::lean_del_object(v___x_6912_);
                    v___x_6917_ = l_Lean_Meta_SavedState_restore___redArg(
                        v_a_6910_,
                        v___y_6905_,
                        v___y_6907_,
                    );
                    crate::leanh::lean_dec(v_a_6910_);
                    if crate::leanh::lean_obj_tag(v___x_6917_) == 0 {
                        v_isSharedCheck_6924_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6917_)) as u8;
                        if v_isSharedCheck_6924_ == 0 {
                            v_unused_6925_ = crate::leanh::lean_ctor_get(v___x_6917_, 0);
                            crate::leanh::lean_dec(v_unused_6925_);
                            v___x_6919_ = v___x_6917_;
                            v_isShared_6920_ = v_isSharedCheck_6924_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_6917_);
                            v___x_6919_ = crate::leanh::lean_box(0);
                            v_isShared_6920_ = v_isSharedCheck_6924_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_6915_);
                        v_a_6926_ = crate::leanh::lean_ctor_get(v___x_6917_, 0);
                        v_isSharedCheck_6933_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6917_)) as u8;
                        if v_isSharedCheck_6933_ == 0 {
                            v___x_6928_ = v___x_6917_;
                            v_isShared_6929_ = v_isSharedCheck_6933_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6926_);
                            crate::leanh::lean_dec(v___x_6917_);
                            v___x_6928_ = crate::leanh::lean_box(0);
                            v_isShared_6929_ = v_isSharedCheck_6933_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6910_);
                    if v_isShared_6913_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_6912_, 1);
                        crate::leanh::lean_ctor_set(v___x_6912_, 0, v___y_6915_);
                        v___x_6935_ = v___x_6912_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_6936_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6936_, 0, v___y_6915_);
                        v___x_6935_ = v_reuseFailAlloc_6936_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6920_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6919_, 1);
                    crate::leanh::lean_ctor_set(v___x_6919_, 0, v___y_6915_);
                    v___x_6922_ = v___x_6919_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6923_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6923_, 0, v___y_6915_);
                    v___x_6922_ = v_reuseFailAlloc_6923_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6922_;
            }
            5 => {
                if v_isShared_6929_ == 0 {
                    v___x_6931_ = v___x_6928_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6932_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6932_, 0, v_a_6926_);
                    v___x_6931_ = v_reuseFailAlloc_6932_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6931_;
            }
            7 => {
                return v___x_6935_;
            }
            8 => {
                v___x_6939_ = l_Lean_Exception_isInterrupt(v_a_6938_);
                if v___x_6939_ == 0 {
                    crate::leanh::lean_inc_ref(v_a_6938_);
                    v___x_6940_ = l_Lean_Exception_isRuntime(v_a_6938_);
                    v___y_6915_ = v_a_6938_;
                    v___y_6916_ = v___x_6940_;
                    state = 2;
                    continue;
                } else {
                    v___y_6915_ = v_a_6938_;
                    v___y_6916_ = v___x_6939_;
                    state = 2;
                    continue;
                }
            }
            9 => {
                if v_isShared_6946_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6945_, 0, v_a_6942_);
                    v___x_6948_ = v___x_6945_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6949_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6949_, 0, v_a_6942_);
                    v___x_6948_ = v_reuseFailAlloc_6949_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6948_;
            }
            11 => {
                if v_isShared_6958_ == 0 {
                    v___x_6960_ = v___x_6957_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6961_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6961_, 0, v_a_6955_);
                    v___x_6960_ = v_reuseFailAlloc_6961_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6960_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg___boxed(
    mut v_x_x3f_6963_: *mut crate::leanh::LeanObject,
    mut v___y_6964_: *mut crate::leanh::LeanObject,
    mut v___y_6965_: *mut crate::leanh::LeanObject,
    mut v___y_6966_: *mut crate::leanh::LeanObject,
    mut v___y_6967_: *mut crate::leanh::LeanObject,
    mut v___y_6968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6969_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(
        v_x_x3f_6963_,
        v___y_6964_,
        v___y_6965_,
        v___y_6966_,
        v___y_6967_,
    );
    crate::leanh::lean_dec(v___y_6967_);
    crate::leanh::lean_dec_ref(v___y_6966_);
    crate::leanh::lean_dec(v___y_6965_);
    crate::leanh::lean_dec_ref(v___y_6964_);
    return v_res_6969_;
}
pub unsafe fn l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0(
    mut v_00_u03b1_6970_: *mut crate::leanh::LeanObject,
    mut v_x_x3f_6971_: *mut crate::leanh::LeanObject,
    mut v___y_6972_: *mut crate::leanh::LeanObject,
    mut v___y_6973_: *mut crate::leanh::LeanObject,
    mut v___y_6974_: *mut crate::leanh::LeanObject,
    mut v___y_6975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6977_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(
        v_x_x3f_6971_,
        v___y_6972_,
        v___y_6973_,
        v___y_6974_,
        v___y_6975_,
    );
    return v___x_6977_;
}
pub unsafe fn l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___boxed(
    mut v_00_u03b1_6978_: *mut crate::leanh::LeanObject,
    mut v_x_x3f_6979_: *mut crate::leanh::LeanObject,
    mut v___y_6980_: *mut crate::leanh::LeanObject,
    mut v___y_6981_: *mut crate::leanh::LeanObject,
    mut v___y_6982_: *mut crate::leanh::LeanObject,
    mut v___y_6983_: *mut crate::leanh::LeanObject,
    mut v___y_6984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6985_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0(
        v_00_u03b1_6978_,
        v_x_x3f_6979_,
        v___y_6980_,
        v___y_6981_,
        v___y_6982_,
        v___y_6983_,
    );
    crate::leanh::lean_dec(v___y_6983_);
    crate::leanh::lean_dec_ref(v___y_6982_);
    crate::leanh::lean_dec(v___y_6981_);
    crate::leanh::lean_dec_ref(v___y_6980_);
    return v_res_6985_;
}
pub unsafe fn _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6990_ = l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1;
    v___x_6991_ =
        l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f___closed__4;
    v___x_6992_ = l_Lean_Name_append(v___x_6991_, v___x_6990_);
    return v___x_6992_;
}
pub unsafe fn _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6994_ = l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__3;
    v___x_6995_ = l_Lean_stringToMessageData(v___x_6994_);
    return v___x_6995_;
}
pub unsafe fn _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6997_ = l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__5;
    v___x_6998_ = l_Lean_stringToMessageData(v___x_6997_);
    return v___x_6998_;
}
pub unsafe fn l_Lean_Meta_splitIfTarget_x3f___lam__0(
    mut v_mvarId_6999_: *mut crate::leanh::LeanObject,
    mut v_hName_x3f_7000_: *mut crate::leanh::LeanObject,
    mut v_useNewSemantics_7001_: u8,
    mut v___y_7002_: *mut crate::leanh::LeanObject,
    mut v___y_7003_: *mut crate::leanh::LeanObject,
    mut v___y_7004_: *mut crate::leanh::LeanObject,
    mut v___y_7005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7016_: u8 = 0;
    let mut v_val_7017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7020_: u8 = 0;
    let mut v_fst_7021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7025_: u8 = 0;
    let mut v_mvarId_7026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7030_: u8 = 0;
    let mut v___x_7031_: u8 = 0;
    let mut v___x_7032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_7034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7038_: u8 = 0;
    let mut v___x_7039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7043_: u8 = 0;
    let mut v___x_7046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7060_: u8 = 0;
    let mut v___x_7061_: u8 = 0;
    let mut v_options_7062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_7063_: u8 = 0;
    let mut v_inheritedTraceOptions_7064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7067_: u8 = 0;
    let mut v___x_7068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7079_: u8 = 0;
    let mut v___x_7081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7083_: u8 = 0;
    let mut v_isSharedCheck_7084_: u8 = 0;
    let mut v_a_7085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7088_: u8 = 0;
    let mut v___x_7090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7092_: u8 = 0;
    let mut v_isSharedCheck_7093_: u8 = 0;
    let mut v_a_7094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7097_: u8 = 0;
    let mut v___x_7099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7101_: u8 = 0;
    let mut v_isSharedCheck_7102_: u8 = 0;
    let mut v_isSharedCheck_7103_: u8 = 0;
    let mut v_isSharedCheck_7104_: u8 = 0;
    let mut v___x_7105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7109_: u8 = 0;
    let mut v_a_7110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7113_: u8 = 0;
    let mut v___x_7115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7117_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_6999_);
                v___x_7010_ = l_Lean_MVarId_getType(
                    v_mvarId_6999_,
                    v___y_7002_,
                    v___y_7003_,
                    v___y_7004_,
                    v___y_7005_,
                );
                if crate::leanh::lean_obj_tag(v___x_7010_) == 0 {
                    v_a_7011_ = crate::leanh::lean_ctor_get(v___x_7010_, 0);
                    crate::leanh::lean_inc(v_a_7011_);
                    crate::leanh::lean_dec_ref_known(v___x_7010_, 1);
                    v___x_7012_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(
                        v_mvarId_6999_,
                        v_a_7011_,
                        v_hName_x3f_7000_,
                        v___y_7002_,
                        v___y_7003_,
                        v___y_7004_,
                        v___y_7005_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7012_) == 0 {
                        v_a_7013_ = crate::leanh::lean_ctor_get(v___x_7012_, 0);
                        v_isSharedCheck_7109_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7012_)) as u8;
                        if v_isSharedCheck_7109_ == 0 {
                            v___x_7015_ = v___x_7012_;
                            v_isShared_7016_ = v_isSharedCheck_7109_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7013_);
                            crate::leanh::lean_dec(v___x_7012_);
                            v___x_7015_ = crate::leanh::lean_box(0);
                            v_isShared_7016_ = v_isSharedCheck_7109_;
                            state = 2;
                            continue;
                        }
                    } else {
                        return v___x_7012_;
                    }
                } else {
                    crate::leanh::lean_dec(v_hName_x3f_7000_);
                    crate::leanh::lean_dec(v_mvarId_6999_);
                    v_a_7110_ = crate::leanh::lean_ctor_get(v___x_7010_, 0);
                    v_isSharedCheck_7117_ = (!crate::leanh::lean_is_exclusive(v___x_7010_)) as u8;
                    if v_isSharedCheck_7117_ == 0 {
                        v___x_7112_ = v___x_7010_;
                        v_isShared_7113_ = v_isSharedCheck_7117_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7110_);
                        crate::leanh::lean_dec(v___x_7010_);
                        v___x_7112_ = crate::leanh::lean_box(0);
                        v_isShared_7113_ = v_isSharedCheck_7117_;
                        state = 21;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7008_ = crate::leanh::lean_box(0);
                v___x_7009_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7009_, 0, v___x_7008_);
                return v___x_7009_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_7013_) == 1 {
                    crate::leanh::lean_del_object(v___x_7015_);
                    v_val_7017_ = crate::leanh::lean_ctor_get(v_a_7013_, 0);
                    v_isSharedCheck_7104_ = (!crate::leanh::lean_is_exclusive(v_a_7013_)) as u8;
                    if v_isSharedCheck_7104_ == 0 {
                        v___x_7019_ = v_a_7013_;
                        v_isShared_7020_ = v_isSharedCheck_7104_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_7017_);
                        crate::leanh::lean_dec(v_a_7013_);
                        v___x_7019_ = crate::leanh::lean_box(0);
                        v_isShared_7020_ = v_isSharedCheck_7104_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_7013_);
                    v___x_7105_ = crate::leanh::lean_box(0);
                    if v_isShared_7016_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7015_, 0, v___x_7105_);
                        v___x_7107_ = v___x_7015_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_7108_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7108_, 0, v___x_7105_);
                        v___x_7107_ = v_reuseFailAlloc_7108_;
                        state = 20;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_7021_ = crate::leanh::lean_ctor_get(v_val_7017_, 0);
                v_snd_7022_ = crate::leanh::lean_ctor_get(v_val_7017_, 1);
                v_isSharedCheck_7103_ = (!crate::leanh::lean_is_exclusive(v_val_7017_)) as u8;
                if v_isSharedCheck_7103_ == 0 {
                    v___x_7024_ = v_val_7017_;
                    v_isShared_7025_ = v_isSharedCheck_7103_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_7022_);
                    crate::leanh::lean_inc(v_fst_7021_);
                    crate::leanh::lean_dec(v_val_7017_);
                    v___x_7024_ = crate::leanh::lean_box(0);
                    v_isShared_7025_ = v_isSharedCheck_7103_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_mvarId_7026_ = crate::leanh::lean_ctor_get(v_fst_7021_, 0);
                v_fvarId_7027_ = crate::leanh::lean_ctor_get(v_fst_7021_, 1);
                v_isSharedCheck_7102_ = (!crate::leanh::lean_is_exclusive(v_fst_7021_)) as u8;
                if v_isSharedCheck_7102_ == 0 {
                    v___x_7029_ = v_fst_7021_;
                    v_isShared_7030_ = v_isSharedCheck_7102_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fvarId_7027_);
                    crate::leanh::lean_inc(v_mvarId_7026_);
                    crate::leanh::lean_dec(v_fst_7021_);
                    v___x_7029_ = crate::leanh::lean_box(0);
                    v_isShared_7030_ = v_isSharedCheck_7102_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_7031_ = 0;
                crate::leanh::lean_inc(v_mvarId_7026_);
                v___x_7032_ = l_Lean_Meta_simpIfTarget(
                    v_mvarId_7026_,
                    v___x_7031_,
                    v_useNewSemantics_7001_,
                    v___y_7002_,
                    v___y_7003_,
                    v___y_7004_,
                    v___y_7005_,
                );
                if crate::leanh::lean_obj_tag(v___x_7032_) == 0 {
                    v_a_7033_ = crate::leanh::lean_ctor_get(v___x_7032_, 0);
                    crate::leanh::lean_inc(v_a_7033_);
                    crate::leanh::lean_dec_ref_known(v___x_7032_, 1);
                    v_mvarId_7034_ = crate::leanh::lean_ctor_get(v_snd_7022_, 0);
                    v_fvarId_7035_ = crate::leanh::lean_ctor_get(v_snd_7022_, 1);
                    v_isSharedCheck_7093_ = (!crate::leanh::lean_is_exclusive(v_snd_7022_)) as u8;
                    if v_isSharedCheck_7093_ == 0 {
                        v___x_7037_ = v_snd_7022_;
                        v_isShared_7038_ = v_isSharedCheck_7093_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fvarId_7035_);
                        crate::leanh::lean_inc(v_mvarId_7034_);
                        crate::leanh::lean_dec(v_snd_7022_);
                        v___x_7037_ = crate::leanh::lean_box(0);
                        v_isShared_7038_ = v_isSharedCheck_7093_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7029_);
                    crate::leanh::lean_dec(v_fvarId_7027_);
                    crate::leanh::lean_dec(v_mvarId_7026_);
                    crate::leanh::lean_del_object(v___x_7024_);
                    crate::leanh::lean_dec(v_snd_7022_);
                    crate::leanh::lean_del_object(v___x_7019_);
                    v_a_7094_ = crate::leanh::lean_ctor_get(v___x_7032_, 0);
                    v_isSharedCheck_7101_ = (!crate::leanh::lean_is_exclusive(v___x_7032_)) as u8;
                    if v_isSharedCheck_7101_ == 0 {
                        v___x_7096_ = v___x_7032_;
                        v_isShared_7097_ = v_isSharedCheck_7101_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7094_);
                        crate::leanh::lean_dec(v___x_7032_);
                        v___x_7096_ = crate::leanh::lean_box(0);
                        v_isShared_7097_ = v_isSharedCheck_7101_;
                        state = 18;
                        continue;
                    }
                }
            }
            6 => {
                crate::leanh::lean_inc(v_mvarId_7034_);
                v___x_7039_ = l_Lean_Meta_simpIfTarget(
                    v_mvarId_7034_,
                    v___x_7031_,
                    v_useNewSemantics_7001_,
                    v___y_7002_,
                    v___y_7003_,
                    v___y_7004_,
                    v___y_7005_,
                );
                if crate::leanh::lean_obj_tag(v___x_7039_) == 0 {
                    v_a_7040_ = crate::leanh::lean_ctor_get(v___x_7039_, 0);
                    v_isSharedCheck_7084_ = (!crate::leanh::lean_is_exclusive(v___x_7039_)) as u8;
                    if v_isSharedCheck_7084_ == 0 {
                        v___x_7042_ = v___x_7039_;
                        v_isShared_7043_ = v_isSharedCheck_7084_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7040_);
                        crate::leanh::lean_dec(v___x_7039_);
                        v___x_7042_ = crate::leanh::lean_box(0);
                        v_isShared_7043_ = v_isSharedCheck_7084_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7037_);
                    crate::leanh::lean_dec(v_fvarId_7035_);
                    crate::leanh::lean_dec(v_mvarId_7034_);
                    crate::leanh::lean_dec(v_a_7033_);
                    crate::leanh::lean_del_object(v___x_7029_);
                    crate::leanh::lean_dec(v_fvarId_7027_);
                    crate::leanh::lean_dec(v_mvarId_7026_);
                    crate::leanh::lean_del_object(v___x_7024_);
                    crate::leanh::lean_del_object(v___x_7019_);
                    v_a_7085_ = crate::leanh::lean_ctor_get(v___x_7039_, 0);
                    v_isSharedCheck_7092_ = (!crate::leanh::lean_is_exclusive(v___x_7039_)) as u8;
                    if v_isSharedCheck_7092_ == 0 {
                        v___x_7087_ = v___x_7039_;
                        v_isShared_7088_ = v_isSharedCheck_7092_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7085_);
                        crate::leanh::lean_dec(v___x_7039_);
                        v___x_7087_ = crate::leanh::lean_box(0);
                        v_isShared_7088_ = v_isSharedCheck_7092_;
                        state = 16;
                        continue;
                    }
                }
            }
            7 => {
                v___x_7060_ = l_Lean_instBEqMVarId_beq(v_mvarId_7026_, v_a_7033_);
                crate::leanh::lean_dec(v_mvarId_7026_);
                if v___x_7060_ == 0 {
                    crate::leanh::lean_dec(v_mvarId_7034_);
                    state = 8;
                    continue;
                } else {
                    v___x_7061_ = l_Lean_instBEqMVarId_beq(v_mvarId_7034_, v_a_7040_);
                    crate::leanh::lean_dec(v_mvarId_7034_);
                    if v___x_7061_ == 0 {
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_7042_);
                        crate::leanh::lean_del_object(v___x_7037_);
                        crate::leanh::lean_dec(v_fvarId_7035_);
                        crate::leanh::lean_del_object(v___x_7029_);
                        crate::leanh::lean_dec(v_fvarId_7027_);
                        crate::leanh::lean_del_object(v___x_7024_);
                        crate::leanh::lean_del_object(v___x_7019_);
                        v_options_7062_ = crate::leanh::lean_ctor_get(v___y_7004_, 2);
                        v_hasTrace_7063_ = crate::leanh::lean_ctor_get_uint8(
                            v_options_7062_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_7063_ == 0 {
                            crate::leanh::lean_dec(v_a_7040_);
                            crate::leanh::lean_dec(v_a_7033_);
                            state = 1;
                            continue;
                        } else {
                            v_inheritedTraceOptions_7064_ =
                                crate::leanh::lean_ctor_get(v___y_7004_, 13);
                            v___x_7065_ = l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1;
                            v___x_7066_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2_once
                                ),
                                _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2,
                            );
                            v___x_7067_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_7064_,
                                v_options_7062_,
                                v___x_7066_,
                            );
                            if v___x_7067_ == 0 {
                                crate::leanh::lean_dec(v_a_7040_);
                                crate::leanh::lean_dec(v_a_7033_);
                                state = 1;
                                continue;
                            } else {
                                v___x_7068_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4_once
                                    ),
                                    _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4,
                                );
                                v___x_7069_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_7069_, 0, v_a_7033_);
                                v___x_7070_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_7070_, 0, v___x_7068_);
                                crate::leanh::lean_ctor_set(v___x_7070_, 1, v___x_7069_);
                                v___x_7071_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6_once
                                    ),
                                    _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6,
                                );
                                v___x_7072_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_7072_, 0, v___x_7070_);
                                crate::leanh::lean_ctor_set(v___x_7072_, 1, v___x_7071_);
                                v___x_7073_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_7073_, 0, v_a_7040_);
                                v___x_7074_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_7074_, 0, v___x_7072_);
                                crate::leanh::lean_ctor_set(v___x_7074_, 1, v___x_7073_);
                                v___x_7075_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_7065_, v___x_7074_, v___y_7002_, v___y_7003_, v___y_7004_, v___y_7005_);
                                if crate::leanh::lean_obj_tag(v___x_7075_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_7075_, 1);
                                    state = 1;
                                    continue;
                                } else {
                                    v_a_7076_ = crate::leanh::lean_ctor_get(v___x_7075_, 0);
                                    v_isSharedCheck_7083_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_7075_)) as u8;
                                    if v_isSharedCheck_7083_ == 0 {
                                        v___x_7078_ = v___x_7075_;
                                        v_isShared_7079_ = v_isSharedCheck_7083_;
                                        state = 14;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_7076_);
                                        crate::leanh::lean_dec(v___x_7075_);
                                        v___x_7078_ = crate::leanh::lean_box(0);
                                        v_isShared_7079_ = v_isSharedCheck_7083_;
                                        state = 14;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            8 => {
                if v_isShared_7038_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7037_, 1, v_fvarId_7027_);
                    crate::leanh::lean_ctor_set(v___x_7037_, 0, v_a_7033_);
                    v___x_7046_ = v___x_7037_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7059_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7059_, 0, v_a_7033_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7059_, 1, v_fvarId_7027_);
                    v___x_7046_ = v_reuseFailAlloc_7059_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_7030_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7029_, 1, v_fvarId_7035_);
                    crate::leanh::lean_ctor_set(v___x_7029_, 0, v_a_7040_);
                    v___x_7048_ = v___x_7029_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7058_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7058_, 0, v_a_7040_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7058_, 1, v_fvarId_7035_);
                    v___x_7048_ = v_reuseFailAlloc_7058_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_7025_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7024_, 1, v___x_7048_);
                    crate::leanh::lean_ctor_set(v___x_7024_, 0, v___x_7046_);
                    v___x_7050_ = v___x_7024_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_7057_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7057_, 0, v___x_7046_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7057_, 1, v___x_7048_);
                    v___x_7050_ = v_reuseFailAlloc_7057_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_7020_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7019_, 0, v___x_7050_);
                    v___x_7052_ = v___x_7019_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_7056_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7056_, 0, v___x_7050_);
                    v___x_7052_ = v_reuseFailAlloc_7056_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_7043_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7042_, 0, v___x_7052_);
                    v___x_7054_ = v___x_7042_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_7055_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7055_, 0, v___x_7052_);
                    v___x_7054_ = v_reuseFailAlloc_7055_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_7054_;
            }
            14 => {
                if v_isShared_7079_ == 0 {
                    v___x_7081_ = v___x_7078_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_7082_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7082_, 0, v_a_7076_);
                    v___x_7081_ = v_reuseFailAlloc_7082_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_7081_;
            }
            16 => {
                if v_isShared_7088_ == 0 {
                    v___x_7090_ = v___x_7087_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_7091_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7091_, 0, v_a_7085_);
                    v___x_7090_ = v_reuseFailAlloc_7091_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_7090_;
            }
            18 => {
                if v_isShared_7097_ == 0 {
                    v___x_7099_ = v___x_7096_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_7100_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7100_, 0, v_a_7094_);
                    v___x_7099_ = v_reuseFailAlloc_7100_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_7099_;
            }
            20 => {
                return v___x_7107_;
            }
            21 => {
                if v_isShared_7113_ == 0 {
                    v___x_7115_ = v___x_7112_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_7116_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7116_, 0, v_a_7110_);
                    v___x_7115_ = v_reuseFailAlloc_7116_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_7115_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_splitIfTarget_x3f___lam__0___boxed(
    mut v_mvarId_7118_: *mut crate::leanh::LeanObject,
    mut v_hName_x3f_7119_: *mut crate::leanh::LeanObject,
    mut v_useNewSemantics_7120_: *mut crate::leanh::LeanObject,
    mut v___y_7121_: *mut crate::leanh::LeanObject,
    mut v___y_7122_: *mut crate::leanh::LeanObject,
    mut v___y_7123_: *mut crate::leanh::LeanObject,
    mut v___y_7124_: *mut crate::leanh::LeanObject,
    mut v___y_7125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useNewSemantics_boxed_7126_: u8 = 0;
    let mut v_res_7127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useNewSemantics_boxed_7126_ = (crate::leanh::lean_unbox(v_useNewSemantics_7120_) as u8);
    v_res_7127_ = l_Lean_Meta_splitIfTarget_x3f___lam__0(
        v_mvarId_7118_,
        v_hName_x3f_7119_,
        v_useNewSemantics_boxed_7126_,
        v___y_7121_,
        v___y_7122_,
        v___y_7123_,
        v___y_7124_,
    );
    crate::leanh::lean_dec(v___y_7124_);
    crate::leanh::lean_dec_ref(v___y_7123_);
    crate::leanh::lean_dec(v___y_7122_);
    crate::leanh::lean_dec_ref(v___y_7121_);
    return v_res_7127_;
}
pub unsafe fn l_Lean_Meta_splitIfTarget_x3f(
    mut v_mvarId_7128_: *mut crate::leanh::LeanObject,
    mut v_hName_x3f_7129_: *mut crate::leanh::LeanObject,
    mut v_useNewSemantics_7130_: u8,
    mut v_a_7131_: *mut crate::leanh::LeanObject,
    mut v_a_7132_: *mut crate::leanh::LeanObject,
    mut v_a_7133_: *mut crate::leanh::LeanObject,
    mut v_a_7134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7136_ = crate::leanh::lean_box((v_useNewSemantics_7130_) as usize);
    v___f_7137_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_splitIfTarget_x3f___lam__0___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___f_7137_, 0, v_mvarId_7128_);
    crate::leanh::lean_closure_set(v___f_7137_, 1, v_hName_x3f_7129_);
    crate::leanh::lean_closure_set(v___f_7137_, 2, v___x_7136_);
    v___x_7138_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(
        v___f_7137_,
        v_a_7131_,
        v_a_7132_,
        v_a_7133_,
        v_a_7134_,
    );
    return v___x_7138_;
}
pub unsafe fn l_Lean_Meta_splitIfTarget_x3f___boxed(
    mut v_mvarId_7139_: *mut crate::leanh::LeanObject,
    mut v_hName_x3f_7140_: *mut crate::leanh::LeanObject,
    mut v_useNewSemantics_7141_: *mut crate::leanh::LeanObject,
    mut v_a_7142_: *mut crate::leanh::LeanObject,
    mut v_a_7143_: *mut crate::leanh::LeanObject,
    mut v_a_7144_: *mut crate::leanh::LeanObject,
    mut v_a_7145_: *mut crate::leanh::LeanObject,
    mut v_a_7146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useNewSemantics_boxed_7147_: u8 = 0;
    let mut v_res_7148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useNewSemantics_boxed_7147_ = (crate::leanh::lean_unbox(v_useNewSemantics_7141_) as u8);
    v_res_7148_ = l_Lean_Meta_splitIfTarget_x3f(
        v_mvarId_7139_,
        v_hName_x3f_7140_,
        v_useNewSemantics_boxed_7147_,
        v_a_7142_,
        v_a_7143_,
        v_a_7144_,
        v_a_7145_,
    );
    crate::leanh::lean_dec(v_a_7145_);
    crate::leanh::lean_dec_ref(v_a_7144_);
    crate::leanh::lean_dec(v_a_7143_);
    crate::leanh::lean_dec_ref(v_a_7142_);
    return v_res_7148_;
}
pub unsafe fn l_Lean_Meta_splitIfLocalDecl_x3f___lam__0(
    mut v___x_7149_: *mut crate::leanh::LeanObject,
    mut v_mvarId_7150_: *mut crate::leanh::LeanObject,
    mut v_hName_x3f_7151_: *mut crate::leanh::LeanObject,
    mut v_fvarId_7152_: *mut crate::leanh::LeanObject,
    mut v___y_7153_: *mut crate::leanh::LeanObject,
    mut v___y_7154_: *mut crate::leanh::LeanObject,
    mut v___y_7155_: *mut crate::leanh::LeanObject,
    mut v___y_7156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7167_: u8 = 0;
    let mut v_val_7168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7171_: u8 = 0;
    let mut v_fst_7172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7176_: u8 = 0;
    let mut v_mvarId_7177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7180_: u8 = 0;
    let mut v___x_7181_: u8 = 0;
    let mut v___x_7182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_7184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7187_: u8 = 0;
    let mut v___x_7188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7192_: u8 = 0;
    let mut v___x_7195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7203_: u8 = 0;
    let mut v___x_7204_: u8 = 0;
    let mut v_options_7205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_7206_: u8 = 0;
    let mut v_inheritedTraceOptions_7207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7210_: u8 = 0;
    let mut v___x_7211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7224_: u8 = 0;
    let mut v___x_7226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7228_: u8 = 0;
    let mut v_reuseFailAlloc_7229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7231_: u8 = 0;
    let mut v_a_7232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7235_: u8 = 0;
    let mut v___x_7237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7239_: u8 = 0;
    let mut v_isSharedCheck_7240_: u8 = 0;
    let mut v_unused_7241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7245_: u8 = 0;
    let mut v___x_7247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7249_: u8 = 0;
    let mut v_isSharedCheck_7250_: u8 = 0;
    let mut v_unused_7251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7252_: u8 = 0;
    let mut v_isSharedCheck_7253_: u8 = 0;
    let mut v___x_7254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7258_: u8 = 0;
    let mut v_a_7259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7262_: u8 = 0;
    let mut v___x_7264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7266_: u8 = 0;
    let mut v_a_7267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7270_: u8 = 0;
    let mut v___x_7272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7274_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_7156_);
                crate::leanh::lean_inc_ref(v___y_7155_);
                crate::leanh::lean_inc(v___y_7154_);
                crate::leanh::lean_inc_ref(v___y_7153_);
                v___x_7161_ = lean_infer_type(
                    v___x_7149_,
                    v___y_7153_,
                    v___y_7154_,
                    v___y_7155_,
                    v___y_7156_,
                );
                if crate::leanh::lean_obj_tag(v___x_7161_) == 0 {
                    v_a_7162_ = crate::leanh::lean_ctor_get(v___x_7161_, 0);
                    crate::leanh::lean_inc(v_a_7162_);
                    crate::leanh::lean_dec_ref_known(v___x_7161_, 1);
                    v___x_7163_ = l_Lean_Meta_SplitIf_splitIfAt_x3f(
                        v_mvarId_7150_,
                        v_a_7162_,
                        v_hName_x3f_7151_,
                        v___y_7153_,
                        v___y_7154_,
                        v___y_7155_,
                        v___y_7156_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7163_) == 0 {
                        v_a_7164_ = crate::leanh::lean_ctor_get(v___x_7163_, 0);
                        v_isSharedCheck_7258_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7163_)) as u8;
                        if v_isSharedCheck_7258_ == 0 {
                            v___x_7166_ = v___x_7163_;
                            v_isShared_7167_ = v_isSharedCheck_7258_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7164_);
                            crate::leanh::lean_dec(v___x_7163_);
                            v___x_7166_ = crate::leanh::lean_box(0);
                            v_isShared_7167_ = v_isSharedCheck_7258_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_7156_);
                        crate::leanh::lean_dec_ref(v___y_7155_);
                        crate::leanh::lean_dec(v___y_7154_);
                        crate::leanh::lean_dec_ref(v___y_7153_);
                        crate::leanh::lean_dec(v_fvarId_7152_);
                        v_a_7259_ = crate::leanh::lean_ctor_get(v___x_7163_, 0);
                        v_isSharedCheck_7266_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7163_)) as u8;
                        if v_isSharedCheck_7266_ == 0 {
                            v___x_7261_ = v___x_7163_;
                            v_isShared_7262_ = v_isSharedCheck_7266_;
                            state = 21;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7259_);
                            crate::leanh::lean_dec(v___x_7163_);
                            v___x_7261_ = crate::leanh::lean_box(0);
                            v_isShared_7262_ = v_isSharedCheck_7266_;
                            state = 21;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_7156_);
                    crate::leanh::lean_dec_ref(v___y_7155_);
                    crate::leanh::lean_dec(v___y_7154_);
                    crate::leanh::lean_dec_ref(v___y_7153_);
                    crate::leanh::lean_dec(v_fvarId_7152_);
                    crate::leanh::lean_dec(v_hName_x3f_7151_);
                    crate::leanh::lean_dec(v_mvarId_7150_);
                    v_a_7267_ = crate::leanh::lean_ctor_get(v___x_7161_, 0);
                    v_isSharedCheck_7274_ = (!crate::leanh::lean_is_exclusive(v___x_7161_)) as u8;
                    if v_isSharedCheck_7274_ == 0 {
                        v___x_7269_ = v___x_7161_;
                        v_isShared_7270_ = v_isSharedCheck_7274_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7267_);
                        crate::leanh::lean_dec(v___x_7161_);
                        v___x_7269_ = crate::leanh::lean_box(0);
                        v_isShared_7270_ = v_isSharedCheck_7274_;
                        state = 23;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7159_ = crate::leanh::lean_box(0);
                v___x_7160_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7160_, 0, v___x_7159_);
                return v___x_7160_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_7164_) == 1 {
                    crate::leanh::lean_del_object(v___x_7166_);
                    v_val_7168_ = crate::leanh::lean_ctor_get(v_a_7164_, 0);
                    v_isSharedCheck_7253_ = (!crate::leanh::lean_is_exclusive(v_a_7164_)) as u8;
                    if v_isSharedCheck_7253_ == 0 {
                        v___x_7170_ = v_a_7164_;
                        v_isShared_7171_ = v_isSharedCheck_7253_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_7168_);
                        crate::leanh::lean_dec(v_a_7164_);
                        v___x_7170_ = crate::leanh::lean_box(0);
                        v_isShared_7171_ = v_isSharedCheck_7253_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_7164_);
                    crate::leanh::lean_dec(v___y_7156_);
                    crate::leanh::lean_dec_ref(v___y_7155_);
                    crate::leanh::lean_dec(v___y_7154_);
                    crate::leanh::lean_dec_ref(v___y_7153_);
                    crate::leanh::lean_dec(v_fvarId_7152_);
                    v___x_7254_ = crate::leanh::lean_box(0);
                    if v_isShared_7167_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7166_, 0, v___x_7254_);
                        v___x_7256_ = v___x_7166_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_7257_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7257_, 0, v___x_7254_);
                        v___x_7256_ = v_reuseFailAlloc_7257_;
                        state = 20;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_7172_ = crate::leanh::lean_ctor_get(v_val_7168_, 0);
                v_snd_7173_ = crate::leanh::lean_ctor_get(v_val_7168_, 1);
                v_isSharedCheck_7252_ = (!crate::leanh::lean_is_exclusive(v_val_7168_)) as u8;
                if v_isSharedCheck_7252_ == 0 {
                    v___x_7175_ = v_val_7168_;
                    v_isShared_7176_ = v_isSharedCheck_7252_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_7173_);
                    crate::leanh::lean_inc(v_fst_7172_);
                    crate::leanh::lean_dec(v_val_7168_);
                    v___x_7175_ = crate::leanh::lean_box(0);
                    v_isShared_7176_ = v_isSharedCheck_7252_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_mvarId_7177_ = crate::leanh::lean_ctor_get(v_fst_7172_, 0);
                v_isSharedCheck_7250_ = (!crate::leanh::lean_is_exclusive(v_fst_7172_)) as u8;
                if v_isSharedCheck_7250_ == 0 {
                    v_unused_7251_ = crate::leanh::lean_ctor_get(v_fst_7172_, 1);
                    crate::leanh::lean_dec(v_unused_7251_);
                    v___x_7179_ = v_fst_7172_;
                    v_isShared_7180_ = v_isSharedCheck_7250_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_mvarId_7177_);
                    crate::leanh::lean_dec(v_fst_7172_);
                    v___x_7179_ = crate::leanh::lean_box(0);
                    v_isShared_7180_ = v_isSharedCheck_7250_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_7181_ = 0;
                crate::leanh::lean_inc(v_fvarId_7152_);
                crate::leanh::lean_inc(v_mvarId_7177_);
                v___x_7182_ = l_Lean_Meta_simpIfLocalDecl(
                    v_mvarId_7177_,
                    v_fvarId_7152_,
                    v___x_7181_,
                    v___y_7153_,
                    v___y_7154_,
                    v___y_7155_,
                    v___y_7156_,
                );
                if crate::leanh::lean_obj_tag(v___x_7182_) == 0 {
                    v_a_7183_ = crate::leanh::lean_ctor_get(v___x_7182_, 0);
                    crate::leanh::lean_inc(v_a_7183_);
                    crate::leanh::lean_dec_ref_known(v___x_7182_, 1);
                    v_mvarId_7184_ = crate::leanh::lean_ctor_get(v_snd_7173_, 0);
                    v_isSharedCheck_7240_ = (!crate::leanh::lean_is_exclusive(v_snd_7173_)) as u8;
                    if v_isSharedCheck_7240_ == 0 {
                        v_unused_7241_ = crate::leanh::lean_ctor_get(v_snd_7173_, 1);
                        crate::leanh::lean_dec(v_unused_7241_);
                        v___x_7186_ = v_snd_7173_;
                        v_isShared_7187_ = v_isSharedCheck_7240_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_mvarId_7184_);
                        crate::leanh::lean_dec(v_snd_7173_);
                        v___x_7186_ = crate::leanh::lean_box(0);
                        v_isShared_7187_ = v_isSharedCheck_7240_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7179_);
                    crate::leanh::lean_dec(v_mvarId_7177_);
                    crate::leanh::lean_del_object(v___x_7175_);
                    crate::leanh::lean_dec(v_snd_7173_);
                    crate::leanh::lean_del_object(v___x_7170_);
                    crate::leanh::lean_dec(v___y_7156_);
                    crate::leanh::lean_dec_ref(v___y_7155_);
                    crate::leanh::lean_dec(v___y_7154_);
                    crate::leanh::lean_dec_ref(v___y_7153_);
                    crate::leanh::lean_dec(v_fvarId_7152_);
                    v_a_7242_ = crate::leanh::lean_ctor_get(v___x_7182_, 0);
                    v_isSharedCheck_7249_ = (!crate::leanh::lean_is_exclusive(v___x_7182_)) as u8;
                    if v_isSharedCheck_7249_ == 0 {
                        v___x_7244_ = v___x_7182_;
                        v_isShared_7245_ = v_isSharedCheck_7249_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7242_);
                        crate::leanh::lean_dec(v___x_7182_);
                        v___x_7244_ = crate::leanh::lean_box(0);
                        v_isShared_7245_ = v_isSharedCheck_7249_;
                        state = 18;
                        continue;
                    }
                }
            }
            6 => {
                crate::leanh::lean_inc(v_mvarId_7184_);
                v___x_7188_ = l_Lean_Meta_simpIfLocalDecl(
                    v_mvarId_7184_,
                    v_fvarId_7152_,
                    v___x_7181_,
                    v___y_7153_,
                    v___y_7154_,
                    v___y_7155_,
                    v___y_7156_,
                );
                if crate::leanh::lean_obj_tag(v___x_7188_) == 0 {
                    v_a_7189_ = crate::leanh::lean_ctor_get(v___x_7188_, 0);
                    v_isSharedCheck_7231_ = (!crate::leanh::lean_is_exclusive(v___x_7188_)) as u8;
                    if v_isSharedCheck_7231_ == 0 {
                        v___x_7191_ = v___x_7188_;
                        v_isShared_7192_ = v_isSharedCheck_7231_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7189_);
                        crate::leanh::lean_dec(v___x_7188_);
                        v___x_7191_ = crate::leanh::lean_box(0);
                        v_isShared_7192_ = v_isSharedCheck_7231_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7186_);
                    crate::leanh::lean_dec(v_mvarId_7184_);
                    crate::leanh::lean_dec(v_a_7183_);
                    crate::leanh::lean_del_object(v___x_7179_);
                    crate::leanh::lean_dec(v_mvarId_7177_);
                    crate::leanh::lean_del_object(v___x_7175_);
                    crate::leanh::lean_del_object(v___x_7170_);
                    crate::leanh::lean_dec(v___y_7156_);
                    crate::leanh::lean_dec_ref(v___y_7155_);
                    crate::leanh::lean_dec(v___y_7154_);
                    crate::leanh::lean_dec_ref(v___y_7153_);
                    v_a_7232_ = crate::leanh::lean_ctor_get(v___x_7188_, 0);
                    v_isSharedCheck_7239_ = (!crate::leanh::lean_is_exclusive(v___x_7188_)) as u8;
                    if v_isSharedCheck_7239_ == 0 {
                        v___x_7234_ = v___x_7188_;
                        v_isShared_7235_ = v_isSharedCheck_7239_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7232_);
                        crate::leanh::lean_dec(v___x_7188_);
                        v___x_7234_ = crate::leanh::lean_box(0);
                        v_isShared_7235_ = v_isSharedCheck_7239_;
                        state = 16;
                        continue;
                    }
                }
            }
            7 => {
                v___x_7203_ = l_Lean_instBEqMVarId_beq(v_mvarId_7177_, v_a_7183_);
                crate::leanh::lean_dec(v_mvarId_7177_);
                if v___x_7203_ == 0 {
                    crate::leanh::lean_del_object(v___x_7186_);
                    crate::leanh::lean_dec(v_mvarId_7184_);
                    crate::leanh::lean_del_object(v___x_7179_);
                    crate::leanh::lean_dec(v___y_7156_);
                    crate::leanh::lean_dec_ref(v___y_7155_);
                    crate::leanh::lean_dec(v___y_7154_);
                    crate::leanh::lean_dec_ref(v___y_7153_);
                    state = 8;
                    continue;
                } else {
                    v___x_7204_ = l_Lean_instBEqMVarId_beq(v_mvarId_7184_, v_a_7189_);
                    crate::leanh::lean_dec(v_mvarId_7184_);
                    if v___x_7204_ == 0 {
                        crate::leanh::lean_del_object(v___x_7186_);
                        crate::leanh::lean_del_object(v___x_7179_);
                        crate::leanh::lean_dec(v___y_7156_);
                        crate::leanh::lean_dec_ref(v___y_7155_);
                        crate::leanh::lean_dec(v___y_7154_);
                        crate::leanh::lean_dec_ref(v___y_7153_);
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_7191_);
                        crate::leanh::lean_del_object(v___x_7175_);
                        crate::leanh::lean_del_object(v___x_7170_);
                        v_options_7205_ = crate::leanh::lean_ctor_get(v___y_7155_, 2);
                        v_hasTrace_7206_ = crate::leanh::lean_ctor_get_uint8(
                            v_options_7205_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_7206_ == 0 {
                            crate::leanh::lean_dec(v_a_7189_);
                            crate::leanh::lean_del_object(v___x_7186_);
                            crate::leanh::lean_dec(v_a_7183_);
                            crate::leanh::lean_del_object(v___x_7179_);
                            crate::leanh::lean_dec(v___y_7156_);
                            crate::leanh::lean_dec_ref(v___y_7155_);
                            crate::leanh::lean_dec(v___y_7154_);
                            crate::leanh::lean_dec_ref(v___y_7153_);
                            state = 1;
                            continue;
                        } else {
                            v_inheritedTraceOptions_7207_ =
                                crate::leanh::lean_ctor_get(v___y_7155_, 13);
                            v___x_7208_ = l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__1;
                            v___x_7209_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2_once
                                ),
                                _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__2,
                            );
                            v___x_7210_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_7207_,
                                v_options_7205_,
                                v___x_7209_,
                            );
                            if v___x_7210_ == 0 {
                                crate::leanh::lean_dec(v_a_7189_);
                                crate::leanh::lean_del_object(v___x_7186_);
                                crate::leanh::lean_dec(v_a_7183_);
                                crate::leanh::lean_del_object(v___x_7179_);
                                crate::leanh::lean_dec(v___y_7156_);
                                crate::leanh::lean_dec_ref(v___y_7155_);
                                crate::leanh::lean_dec(v___y_7154_);
                                crate::leanh::lean_dec_ref(v___y_7153_);
                                state = 1;
                                continue;
                            } else {
                                v___x_7211_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4_once
                                    ),
                                    _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__4,
                                );
                                v___x_7212_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_7212_, 0, v_a_7183_);
                                if v_isShared_7187_ == 0 {
                                    crate::leanh::lean_ctor_set_tag(v___x_7186_, 7);
                                    crate::leanh::lean_ctor_set(v___x_7186_, 1, v___x_7212_);
                                    crate::leanh::lean_ctor_set(v___x_7186_, 0, v___x_7211_);
                                    v___x_7214_ = v___x_7186_;
                                    state = 12;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_7230_ =
                                        crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7230_,
                                        0,
                                        v___x_7211_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7230_,
                                        1,
                                        v___x_7212_,
                                    );
                                    v___x_7214_ = v_reuseFailAlloc_7230_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            8 => {
                if v_isShared_7176_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7175_, 1, v_a_7189_);
                    crate::leanh::lean_ctor_set(v___x_7175_, 0, v_a_7183_);
                    v___x_7195_ = v___x_7175_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7202_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7202_, 0, v_a_7183_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7202_, 1, v_a_7189_);
                    v___x_7195_ = v_reuseFailAlloc_7202_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_7171_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7170_, 0, v___x_7195_);
                    v___x_7197_ = v___x_7170_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7201_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7201_, 0, v___x_7195_);
                    v___x_7197_ = v_reuseFailAlloc_7201_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_7192_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7191_, 0, v___x_7197_);
                    v___x_7199_ = v___x_7191_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_7200_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7200_, 0, v___x_7197_);
                    v___x_7199_ = v_reuseFailAlloc_7200_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_7199_;
            }
            12 => {
                v___x_7215_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6_once
                    ),
                    _init_l_Lean_Meta_splitIfTarget_x3f___lam__0___closed__6,
                );
                if v_isShared_7180_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_7179_, 7);
                    crate::leanh::lean_ctor_set(v___x_7179_, 1, v___x_7215_);
                    crate::leanh::lean_ctor_set(v___x_7179_, 0, v___x_7214_);
                    v___x_7217_ = v___x_7179_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_7229_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7229_, 0, v___x_7214_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7229_, 1, v___x_7215_);
                    v___x_7217_ = v_reuseFailAlloc_7229_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_7218_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7218_, 0, v_a_7189_);
                v___x_7219_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7219_, 0, v___x_7217_);
                crate::leanh::lean_ctor_set(v___x_7219_, 1, v___x_7218_);
                v___x_7220_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_findSplit_x3f_find_x3f_spec__0(v___x_7208_, v___x_7219_, v___y_7153_, v___y_7154_, v___y_7155_, v___y_7156_);
                crate::leanh::lean_dec(v___y_7156_);
                crate::leanh::lean_dec_ref(v___y_7155_);
                crate::leanh::lean_dec(v___y_7154_);
                crate::leanh::lean_dec_ref(v___y_7153_);
                if crate::leanh::lean_obj_tag(v___x_7220_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_7220_, 1);
                    state = 1;
                    continue;
                } else {
                    v_a_7221_ = crate::leanh::lean_ctor_get(v___x_7220_, 0);
                    v_isSharedCheck_7228_ = (!crate::leanh::lean_is_exclusive(v___x_7220_)) as u8;
                    if v_isSharedCheck_7228_ == 0 {
                        v___x_7223_ = v___x_7220_;
                        v_isShared_7224_ = v_isSharedCheck_7228_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7221_);
                        crate::leanh::lean_dec(v___x_7220_);
                        v___x_7223_ = crate::leanh::lean_box(0);
                        v_isShared_7224_ = v_isSharedCheck_7228_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_7224_ == 0 {
                    v___x_7226_ = v___x_7223_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_7227_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7227_, 0, v_a_7221_);
                    v___x_7226_ = v_reuseFailAlloc_7227_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_7226_;
            }
            16 => {
                if v_isShared_7235_ == 0 {
                    v___x_7237_ = v___x_7234_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_7238_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7238_, 0, v_a_7232_);
                    v___x_7237_ = v_reuseFailAlloc_7238_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_7237_;
            }
            18 => {
                if v_isShared_7245_ == 0 {
                    v___x_7247_ = v___x_7244_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_7248_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7248_, 0, v_a_7242_);
                    v___x_7247_ = v_reuseFailAlloc_7248_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_7247_;
            }
            20 => {
                return v___x_7256_;
            }
            21 => {
                if v_isShared_7262_ == 0 {
                    v___x_7264_ = v___x_7261_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_7265_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7265_, 0, v_a_7259_);
                    v___x_7264_ = v_reuseFailAlloc_7265_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_7264_;
            }
            23 => {
                if v_isShared_7270_ == 0 {
                    v___x_7272_ = v___x_7269_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_7273_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7273_, 0, v_a_7267_);
                    v___x_7272_ = v_reuseFailAlloc_7273_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_7272_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_splitIfLocalDecl_x3f___lam__0___boxed(
    mut v___x_7275_: *mut crate::leanh::LeanObject,
    mut v_mvarId_7276_: *mut crate::leanh::LeanObject,
    mut v_hName_x3f_7277_: *mut crate::leanh::LeanObject,
    mut v_fvarId_7278_: *mut crate::leanh::LeanObject,
    mut v___y_7279_: *mut crate::leanh::LeanObject,
    mut v___y_7280_: *mut crate::leanh::LeanObject,
    mut v___y_7281_: *mut crate::leanh::LeanObject,
    mut v___y_7282_: *mut crate::leanh::LeanObject,
    mut v___y_7283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7284_ = l_Lean_Meta_splitIfLocalDecl_x3f___lam__0(
        v___x_7275_,
        v_mvarId_7276_,
        v_hName_x3f_7277_,
        v_fvarId_7278_,
        v___y_7279_,
        v___y_7280_,
        v___y_7281_,
        v___y_7282_,
    );
    return v_res_7284_;
}
pub unsafe fn l_Lean_Meta_splitIfLocalDecl_x3f(
    mut v_mvarId_7285_: *mut crate::leanh::LeanObject,
    mut v_fvarId_7286_: *mut crate::leanh::LeanObject,
    mut v_hName_x3f_7287_: *mut crate::leanh::LeanObject,
    mut v_a_7288_: *mut crate::leanh::LeanObject,
    mut v_a_7289_: *mut crate::leanh::LeanObject,
    mut v_a_7290_: *mut crate::leanh::LeanObject,
    mut v_a_7291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_fvarId_7286_);
    v___x_7293_ = l_Lean_mkFVar(v_fvarId_7286_);
    crate::leanh::lean_inc(v_mvarId_7285_);
    v___f_7294_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_splitIfLocalDecl_x3f___lam__0___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___f_7294_, 0, v___x_7293_);
    crate::leanh::lean_closure_set(v___f_7294_, 1, v_mvarId_7285_);
    crate::leanh::lean_closure_set(v___f_7294_, 2, v_hName_x3f_7287_);
    crate::leanh::lean_closure_set(v___f_7294_, 3, v_fvarId_7286_);
    v___x_7295_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_withContext___at___00Lean_Meta_SplitIf_splitIfAt_x3f_spec__0___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_7295_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_7295_, 1, v_mvarId_7285_);
    crate::leanh::lean_closure_set(v___x_7295_, 2, v___f_7294_);
    v___x_7296_ = l_Lean_commitWhenSome_x3f___at___00Lean_Meta_splitIfTarget_x3f_spec__0___redArg(
        v___x_7295_,
        v_a_7288_,
        v_a_7289_,
        v_a_7290_,
        v_a_7291_,
    );
    return v___x_7296_;
}
pub unsafe fn l_Lean_Meta_splitIfLocalDecl_x3f___boxed(
    mut v_mvarId_7297_: *mut crate::leanh::LeanObject,
    mut v_fvarId_7298_: *mut crate::leanh::LeanObject,
    mut v_hName_x3f_7299_: *mut crate::leanh::LeanObject,
    mut v_a_7300_: *mut crate::leanh::LeanObject,
    mut v_a_7301_: *mut crate::leanh::LeanObject,
    mut v_a_7302_: *mut crate::leanh::LeanObject,
    mut v_a_7303_: *mut crate::leanh::LeanObject,
    mut v_a_7304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7305_ = l_Lean_Meta_splitIfLocalDecl_x3f(
        v_mvarId_7297_,
        v_fvarId_7298_,
        v_hName_x3f_7299_,
        v_a_7300_,
        v_a_7301_,
        v_a_7302_,
        v_a_7303_,
    );
    crate::leanh::lean_dec(v_a_7303_);
    crate::leanh::lean_dec_ref(v_a_7302_);
    crate::leanh::lean_dec(v_a_7301_);
    crate::leanh::lean_dec_ref(v_a_7300_);
    return v_res_7305_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7326_ = crate::leanh::lean_unsigned_to_nat(3526097586);
    v___x_7327_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_;
    v___x_7328_ = l_Lean_Name_num___override(v___x_7327_, v___x_7326_);
    return v___x_7328_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7330_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_;
    v___x_7331_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
    v___x_7332_ = l_Lean_Name_str___override(v___x_7331_, v___x_7330_);
    return v___x_7332_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7334_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_;
    v___x_7335_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
    v___x_7336_ = l_Lean_Name_str___override(v___x_7335_, v___x_7334_);
    return v___x_7336_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7337_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_7338_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
    v___x_7339_ = l_Lean_Name_num___override(v___x_7338_, v___x_7337_);
    return v___x_7339_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7342_: u8 = 0;
    let mut v___x_7343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7341_ =
        l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_SplitIf_discharge_x3f___closed__10;
    v___x_7342_ = 0;
    v___x_7343_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_);
    v___x_7344_ = l_Lean_registerTraceClass(v___x_7341_, v___x_7342_, v___x_7343_);
    return v___x_7344_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2____boxed(
    mut v_a_7345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7346_ = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_();
    return v_res_7346_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_SplitIf(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Cases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_4163081528____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_backward_split = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Meta_backward_split);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_SplitIf_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_SplitIf_3526097586____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_SplitIf(
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
pub unsafe fn initialize_Lean_Meta_Tactic_SplitIf(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Cases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_SplitIf(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_SplitIf(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_SplitIf(builtin);
}
