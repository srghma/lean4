// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.Structures
// Imports: Lean.Meta.Tactic.BVDecide.Normalize.TypeAnalysis Lean.Meta.Tactic.BVDecide.Normalize.ApplyControlFlow Lean.Meta.Injective Lean.Meta.Tactic.Cases
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonad___redArg, l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Environment::{
    l_Lean_AsyncConstantInfo_toConstantInfo, l_Lean_Environment_find_x3f,
    l_Lean_Environment_findAsync_x3f,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_constName_x3f, l_Lean_Expr_getAppFn, l_Lean_Expr_hasMVar, l_Lean_mkConst,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_isImplementationDetail, l_Lean_LocalDecl_isLet, l_Lean_LocalDecl_type,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp,
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
};
use crate::r#gen::Lean::Meta::DiscrTree::Basic::l_Lean_Meta_DiscrTree_empty;
use crate::r#gen::Lean::Meta::Injective::{
    initialize_Lean_Meta_Injective, l_Lean_Meta_mkInjectiveEqTheoremNameFor,
    runtime_initialize_Lean_Meta_Injective,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Normalize::ApplyControlFlow::{
    initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow,
    l_Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc___boxed,
    l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___boxed,
    l_Lean_Meta_Tactic_BVDecide_Normalize_mkApplyProjControlDiscrPath,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Normalize::TypeAnalysis::{
    initialize_Lean_Meta_Tactic_BVDecide_Normalize_TypeAnalysis,
    l_Lean_Meta_Tactic_BVDecide_Normalize_addDefaultTypeAnalysisLemmas,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_TypeAnalysis,
};
use crate::r#gen::Lean::Meta::Tactic::Cases::{
    initialize_Lean_Meta_Tactic_Cases, l_Lean_MVarId_casesRec,
    runtime_initialize_Lean_Meta_Tactic_Cases,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Main::l_Lean_Meta_simpGoal;
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpCongrTheorems::l_Lean_Meta_getSimpCongrTheorems___redArg;
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpTheorems::{
    l_Lean_Meta_SimpTheoremsArray_addTheorem, l_Lean_Meta_simpGlobalConfig,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Simproc::l_Lean_Meta_Simp_Simprocs_addCore;
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::l_Lean_Meta_Simp_mkContext___redArg;
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_Meta_getPropHyps;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::MonadEnv::l_Lean_isInductiveCore_x3f;
use crate::r#gen::Lean::Structure::l_Lean_getStructureInfo;
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::ffi::{lean_array_size, lean_array_uget_borrowed};
use crate::ffi::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_panic_fn_borrowed, lean_uint64_of_nat,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__2_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__4_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [76, 101, 97, 110, 46, 77, 111, 110, 97, 100, 69, 110, 118, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__5_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [76, 101, 97, 110, 46, 105, 115, 67, 116, 111, 114, 63, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__6_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__0_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 0]};
static mut l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [105, 116, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject,18356704233129443855 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__4_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__5_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [66, 86, 68, 101, 99, 105, 100, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__6_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [78, 111, 114, 109, 97, 108, 105, 122, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__7_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [97, 112, 112, 108, 121, 73, 116, 101, 83, 105, 109, 112, 114, 111, 99, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__3_value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__4_value) as *mut crate::leanh::LeanObject,15353829308266697735 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__5_value) as *mut crate::leanh::LeanObject,3081681055095066290 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__6_value) as *mut crate::leanh::LeanObject,15669547423808698083 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__7_value) as *mut crate::leanh::LeanObject,12165403030747803476 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__9_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Tactic_BVDecide_Normalize_applyIteSimproc___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__10_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__11_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 110, 100, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__12_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__11_value) as *mut crate::leanh::LeanObject,105488867511536770 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__13_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [97, 112, 112, 108, 121, 67, 111, 110, 100, 83, 105, 109, 112, 114, 111, 99, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__13_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__3_value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__4_value) as *mut crate::leanh::LeanObject,15353829308266697735 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__5_value) as *mut crate::leanh::LeanObject,3081681055095066290 as *mut crate::leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__6_value) as *mut crate::leanh::LeanObject,15669547423808698083 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__13_value) as *mut crate::leanh::LeanObject,11494774513989324767 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__15_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Tactic_BVDecide_Normalize_applyCondSimproc___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__16_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__15_value) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [98, 118, 0]};
static mut l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__3_value) as *mut crate::leanh::LeanObject,142734480563613395 as *mut crate::leanh::LeanObject] };
static l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__4_value) as *mut crate::leanh::LeanObject,15847151208953044930 as *mut crate::leanh::LeanObject] };
pub static l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__0_value) as *mut crate::leanh::LeanObject,10551690841954068875 as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__2_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__2_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__5_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [85, 115, 105, 110, 103, 32, 105, 110, 106, 69, 113, 32, 108, 101, 109, 109, 97, 58, 32, 0]};
static mut l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__3_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1___redArg___closed__0: u64 = 0;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___closed__0_value:
    crate::leanh::LeanStringObject<51> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 51,
    m_capacity: 51,
    m_length: 50,
    m_data: [
        115, 116, 114, 117, 99, 116, 117, 114, 101, 115, 32, 112, 114, 101, 112, 114, 111, 99, 101,
        115, 115, 111, 114, 32, 103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 109, 111, 114, 101,
        32, 116, 104, 97, 110, 32, 49, 32, 103, 111, 97, 108, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__0_value:
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
    m_fun: l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__1_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [115, 116, 114, 117, 99, 116, 117, 114, 101, 115, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__1_value)
            as *mut crate::leanh::LeanObject,
        16786335436788389450 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1138_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_1138_;
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2(
    mut v_msg_1143_: *mut crate::leanh::LeanObject,
    mut v___y_1144_: *mut crate::leanh::LeanObject,
    mut v___y_1145_: *mut crate::leanh::LeanObject,
    mut v___y_1146_: *mut crate::leanh::LeanObject,
    mut v___y_1147_: *mut crate::leanh::LeanObject,
    mut v___y_1148_: *mut crate::leanh::LeanObject,
    mut v___y_1149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1156_: u8 = 0;
    let mut v_toFunctor_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1163_: u8 = 0;
    let mut v___f_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1180_: u8 = 0;
    let mut v_toFunctor_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1187_: u8 = 0;
    let mut v___f_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_19962__overap_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1208_: u8 = 0;
    let mut v_unused_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1210_: u8 = 0;
    let mut v_unused_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1214_: u8 = 0;
    let mut v_unused_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1216_: u8 = 0;
    let mut v_unused_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1151_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__0_once), _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__0);
                v___x_1152_ = l_StateRefT_x27_instMonad___redArg(v___x_1151_);
                v_toApplicative_1153_ = crate::leanh::lean_ctor_get(v___x_1152_, 0);
                v_isSharedCheck_1216_ = (!crate::leanh::lean_is_exclusive(v___x_1152_)) as u8;
                if v_isSharedCheck_1216_ == 0 {
                    v_unused_1217_ = crate::leanh::lean_ctor_get(v___x_1152_, 1);
                    crate::leanh::lean_dec(v_unused_1217_);
                    v___x_1155_ = v___x_1152_;
                    v_isShared_1156_ = v_isSharedCheck_1216_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_1153_);
                    crate::leanh::lean_dec(v___x_1152_);
                    v___x_1155_ = crate::leanh::lean_box(0);
                    v_isShared_1156_ = v_isSharedCheck_1216_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1157_ = crate::leanh::lean_ctor_get(v_toApplicative_1153_, 0);
                v_toSeq_1158_ = crate::leanh::lean_ctor_get(v_toApplicative_1153_, 2);
                v_toSeqLeft_1159_ = crate::leanh::lean_ctor_get(v_toApplicative_1153_, 3);
                v_toSeqRight_1160_ = crate::leanh::lean_ctor_get(v_toApplicative_1153_, 4);
                v_isSharedCheck_1214_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_1153_)) as u8;
                if v_isSharedCheck_1214_ == 0 {
                    v_unused_1215_ = crate::leanh::lean_ctor_get(v_toApplicative_1153_, 1);
                    crate::leanh::lean_dec(v_unused_1215_);
                    v___x_1162_ = v_toApplicative_1153_;
                    v_isShared_1163_ = v_isSharedCheck_1214_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_1160_);
                    crate::leanh::lean_inc(v_toSeqLeft_1159_);
                    crate::leanh::lean_inc(v_toSeq_1158_);
                    crate::leanh::lean_inc(v_toFunctor_1157_);
                    crate::leanh::lean_dec(v_toApplicative_1153_);
                    v___x_1162_ = crate::leanh::lean_box(0);
                    v_isShared_1163_ = v_isSharedCheck_1214_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1164_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__1;
                v___f_1165_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_1157_);
                v___f_1166_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1166_, 0, v_toFunctor_1157_);
                v___f_1167_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1167_, 0, v_toFunctor_1157_);
                v___x_1168_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1168_, 0, v___f_1166_);
                crate::leanh::lean_ctor_set(v___x_1168_, 1, v___f_1167_);
                v___f_1169_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1169_, 0, v_toSeqRight_1160_);
                v___f_1170_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1170_, 0, v_toSeqLeft_1159_);
                v___f_1171_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1171_, 0, v_toSeq_1158_);
                if v_isShared_1163_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1162_, 4, v___f_1169_);
                    crate::leanh::lean_ctor_set(v___x_1162_, 3, v___f_1170_);
                    crate::leanh::lean_ctor_set(v___x_1162_, 2, v___f_1171_);
                    crate::leanh::lean_ctor_set(v___x_1162_, 1, v___f_1164_);
                    crate::leanh::lean_ctor_set(v___x_1162_, 0, v___x_1168_);
                    v___x_1173_ = v___x_1162_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1213_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1168_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1213_, 1, v___f_1164_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1213_, 2, v___f_1171_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1213_, 3, v___f_1170_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1213_, 4, v___f_1169_);
                    v___x_1173_ = v_reuseFailAlloc_1213_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1156_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1155_, 1, v___f_1165_);
                    crate::leanh::lean_ctor_set(v___x_1155_, 0, v___x_1173_);
                    v___x_1175_ = v___x_1155_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1212_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1173_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1212_, 1, v___f_1165_);
                    v___x_1175_ = v_reuseFailAlloc_1212_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1176_ = l_StateRefT_x27_instMonad___redArg(v___x_1175_);
                v_toApplicative_1177_ = crate::leanh::lean_ctor_get(v___x_1176_, 0);
                v_isSharedCheck_1210_ = (!crate::leanh::lean_is_exclusive(v___x_1176_)) as u8;
                if v_isSharedCheck_1210_ == 0 {
                    v_unused_1211_ = crate::leanh::lean_ctor_get(v___x_1176_, 1);
                    crate::leanh::lean_dec(v_unused_1211_);
                    v___x_1179_ = v___x_1176_;
                    v_isShared_1180_ = v_isSharedCheck_1210_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_1177_);
                    crate::leanh::lean_dec(v___x_1176_);
                    v___x_1179_ = crate::leanh::lean_box(0);
                    v_isShared_1180_ = v_isSharedCheck_1210_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_1181_ = crate::leanh::lean_ctor_get(v_toApplicative_1177_, 0);
                v_toSeq_1182_ = crate::leanh::lean_ctor_get(v_toApplicative_1177_, 2);
                v_toSeqLeft_1183_ = crate::leanh::lean_ctor_get(v_toApplicative_1177_, 3);
                v_toSeqRight_1184_ = crate::leanh::lean_ctor_get(v_toApplicative_1177_, 4);
                v_isSharedCheck_1208_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_1177_)) as u8;
                if v_isSharedCheck_1208_ == 0 {
                    v_unused_1209_ = crate::leanh::lean_ctor_get(v_toApplicative_1177_, 1);
                    crate::leanh::lean_dec(v_unused_1209_);
                    v___x_1186_ = v_toApplicative_1177_;
                    v_isShared_1187_ = v_isSharedCheck_1208_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_1184_);
                    crate::leanh::lean_inc(v_toSeqLeft_1183_);
                    crate::leanh::lean_inc(v_toSeq_1182_);
                    crate::leanh::lean_inc(v_toFunctor_1181_);
                    crate::leanh::lean_dec(v_toApplicative_1177_);
                    v___x_1186_ = crate::leanh::lean_box(0);
                    v_isShared_1187_ = v_isSharedCheck_1208_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_1188_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__3;
                v___f_1189_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_1181_);
                v___f_1190_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1190_, 0, v_toFunctor_1181_);
                v___f_1191_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1191_, 0, v_toFunctor_1181_);
                v___x_1192_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1192_, 0, v___f_1190_);
                crate::leanh::lean_ctor_set(v___x_1192_, 1, v___f_1191_);
                v___f_1193_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1193_, 0, v_toSeqRight_1184_);
                v___f_1194_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1194_, 0, v_toSeqLeft_1183_);
                v___f_1195_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1195_, 0, v_toSeq_1182_);
                if v_isShared_1187_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1186_, 4, v___f_1193_);
                    crate::leanh::lean_ctor_set(v___x_1186_, 3, v___f_1194_);
                    crate::leanh::lean_ctor_set(v___x_1186_, 2, v___f_1195_);
                    crate::leanh::lean_ctor_set(v___x_1186_, 1, v___f_1188_);
                    crate::leanh::lean_ctor_set(v___x_1186_, 0, v___x_1192_);
                    v___x_1197_ = v___x_1186_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1207_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1192_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1207_, 1, v___f_1188_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1207_, 2, v___f_1195_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1207_, 3, v___f_1194_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1207_, 4, v___f_1193_);
                    v___x_1197_ = v_reuseFailAlloc_1207_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1180_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1179_, 1, v___f_1189_);
                    crate::leanh::lean_ctor_set(v___x_1179_, 0, v___x_1197_);
                    v___x_1199_ = v___x_1179_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1206_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1197_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1206_, 1, v___f_1189_);
                    v___x_1199_ = v_reuseFailAlloc_1206_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1200_ = l_StateRefT_x27_instMonad___redArg(v___x_1199_);
                v___x_1201_ = l_ReaderT_instMonad___redArg(v___x_1200_);
                v___x_1202_ = crate::leanh::lean_box(0);
                v___x_1203_ = l_instInhabitedOfMonad___redArg(v___x_1201_, v___x_1202_);
                v___x_19962__overap_1204_ = lean_panic_fn_borrowed(v___x_1203_, v_msg_1143_);
                crate::leanh::lean_dec(v___x_1203_);
                crate::leanh::lean_inc(v___y_1149_);
                crate::leanh::lean_inc_ref(v___y_1148_);
                crate::leanh::lean_inc(v___y_1147_);
                crate::leanh::lean_inc_ref(v___y_1146_);
                crate::leanh::lean_inc(v___y_1145_);
                crate::leanh::lean_inc_ref(v___y_1144_);
                v___x_1205_ = crate::leanh::lean_apply_7(
                    v___x_19962__overap_1204_,
                    v___y_1144_,
                    v___y_1145_,
                    v___y_1146_,
                    v___y_1147_,
                    v___y_1148_,
                    v___y_1149_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1205_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2___boxed(
    mut v_msg_1218_: *mut crate::leanh::LeanObject,
    mut v___y_1219_: *mut crate::leanh::LeanObject,
    mut v___y_1220_: *mut crate::leanh::LeanObject,
    mut v___y_1221_: *mut crate::leanh::LeanObject,
    mut v___y_1222_: *mut crate::leanh::LeanObject,
    mut v___y_1223_: *mut crate::leanh::LeanObject,
    mut v___y_1224_: *mut crate::leanh::LeanObject,
    mut v___y_1225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1226_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2(v_msg_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
    crate::leanh::lean_dec(v___y_1224_);
    crate::leanh::lean_dec_ref(v___y_1223_);
    crate::leanh::lean_dec(v___y_1222_);
    crate::leanh::lean_dec_ref(v___y_1221_);
    crate::leanh::lean_dec(v___y_1220_);
    crate::leanh::lean_dec_ref(v___y_1219_);
    return v_res_1226_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3_spec__5(
    mut v_msgData_1227_: *mut crate::leanh::LeanObject,
    mut v___y_1228_: *mut crate::leanh::LeanObject,
    mut v___y_1229_: *mut crate::leanh::LeanObject,
    mut v___y_1230_: *mut crate::leanh::LeanObject,
    mut v___y_1231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1233_ = lean_st_ref_get(v___y_1231_);
    v_env_1234_ = crate::leanh::lean_ctor_get(v___x_1233_, 0);
    crate::leanh::lean_inc_ref(v_env_1234_);
    crate::leanh::lean_dec(v___x_1233_);
    v___x_1235_ = lean_st_ref_get(v___y_1229_);
    v_mctx_1236_ = crate::leanh::lean_ctor_get(v___x_1235_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1236_);
    crate::leanh::lean_dec(v___x_1235_);
    v_lctx_1237_ = crate::leanh::lean_ctor_get(v___y_1228_, 2);
    v_options_1238_ = crate::leanh::lean_ctor_get(v___y_1230_, 2);
    crate::leanh::lean_inc_ref(v_options_1238_);
    crate::leanh::lean_inc_ref(v_lctx_1237_);
    v___x_1239_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1239_, 0, v_env_1234_);
    crate::leanh::lean_ctor_set(v___x_1239_, 1, v_mctx_1236_);
    crate::leanh::lean_ctor_set(v___x_1239_, 2, v_lctx_1237_);
    crate::leanh::lean_ctor_set(v___x_1239_, 3, v_options_1238_);
    v___x_1240_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1240_, 0, v___x_1239_);
    crate::leanh::lean_ctor_set(v___x_1240_, 1, v_msgData_1227_);
    v___x_1241_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1241_, 0, v___x_1240_);
    return v___x_1241_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3_spec__5___boxed(
    mut v_msgData_1242_: *mut crate::leanh::LeanObject,
    mut v___y_1243_: *mut crate::leanh::LeanObject,
    mut v___y_1244_: *mut crate::leanh::LeanObject,
    mut v___y_1245_: *mut crate::leanh::LeanObject,
    mut v___y_1246_: *mut crate::leanh::LeanObject,
    mut v___y_1247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1248_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3_spec__5(v_msgData_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
    crate::leanh::lean_dec(v___y_1246_);
    crate::leanh::lean_dec_ref(v___y_1245_);
    crate::leanh::lean_dec(v___y_1244_);
    crate::leanh::lean_dec_ref(v___y_1243_);
    return v_res_1248_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(
    mut v_msg_1249_: *mut crate::leanh::LeanObject,
    mut v___y_1250_: *mut crate::leanh::LeanObject,
    mut v___y_1251_: *mut crate::leanh::LeanObject,
    mut v___y_1252_: *mut crate::leanh::LeanObject,
    mut v___y_1253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1260_: u8 = 0;
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1265_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1255_ = crate::leanh::lean_ctor_get(v___y_1252_, 5);
                v___x_1256_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3_spec__5(v_msg_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
                v_a_1257_ = crate::leanh::lean_ctor_get(v___x_1256_, 0);
                v_isSharedCheck_1265_ = (!crate::leanh::lean_is_exclusive(v___x_1256_)) as u8;
                if v_isSharedCheck_1265_ == 0 {
                    v___x_1259_ = v___x_1256_;
                    v_isShared_1260_ = v_isSharedCheck_1265_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1257_);
                    crate::leanh::lean_dec(v___x_1256_);
                    v___x_1259_ = crate::leanh::lean_box(0);
                    v_isShared_1260_ = v_isSharedCheck_1265_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1255_);
                v___x_1261_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1261_, 0, v_ref_1255_);
                crate::leanh::lean_ctor_set(v___x_1261_, 1, v_a_1257_);
                if v_isShared_1260_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1259_, 1);
                    crate::leanh::lean_ctor_set(v___x_1259_, 0, v___x_1261_);
                    v___x_1263_ = v___x_1259_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1264_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1261_);
                    v___x_1263_ = v_reuseFailAlloc_1264_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1263_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg___boxed(
    mut v_msg_1266_: *mut crate::leanh::LeanObject,
    mut v___y_1267_: *mut crate::leanh::LeanObject,
    mut v___y_1268_: *mut crate::leanh::LeanObject,
    mut v___y_1269_: *mut crate::leanh::LeanObject,
    mut v___y_1270_: *mut crate::leanh::LeanObject,
    mut v___y_1271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1272_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(v_msg_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
    crate::leanh::lean_dec(v___y_1270_);
    crate::leanh::lean_dec_ref(v___y_1269_);
    crate::leanh::lean_dec(v___y_1268_);
    crate::leanh::lean_dec_ref(v___y_1267_);
    return v_res_1272_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1274_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__0;
    v___x_1275_ = l_Lean_stringToMessageData(v___x_1274_);
    return v___x_1275_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1277_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__2;
    v___x_1278_ = l_Lean_stringToMessageData(v___x_1277_);
    return v___x_1278_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1282_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__6;
    v___x_1283_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_1284_ = crate::leanh::lean_unsigned_to_nat(122);
    v___x_1285_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__5;
    v___x_1286_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__4;
    v___x_1287_ = l_mkPanicMessageWithDecl(
        v___x_1286_,
        v___x_1285_,
        v___x_1284_,
        v___x_1283_,
        v___x_1282_,
    );
    return v___x_1287_;
}
pub unsafe fn l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1(
    mut v_constName_1288_: *mut crate::leanh::LeanObject,
    mut v___y_1289_: *mut crate::leanh::LeanObject,
    mut v___y_1290_: *mut crate::leanh::LeanObject,
    mut v___y_1291_: *mut crate::leanh::LeanObject,
    mut v___y_1292_: *mut crate::leanh::LeanObject,
    mut v___y_1293_: *mut crate::leanh::LeanObject,
    mut v___y_1294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: u8 = 0;
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: u8 = 0;
    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1309_: u8 = 0;
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1314_: u8 = 0;
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1318_: u8 = 0;
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1324_: u8 = 0;
    let mut v_val_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1329_: u8 = 0;
    let mut v_a_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1333_: u8 = 0;
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1337_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1304_ = lean_st_ref_get(v___y_1294_);
                v_env_1305_ = crate::leanh::lean_ctor_get(v___x_1304_, 0);
                crate::leanh::lean_inc_ref(v_env_1305_);
                crate::leanh::lean_dec(v___x_1304_);
                v___x_1306_ = 0;
                crate::leanh::lean_inc(v_constName_1288_);
                v___x_1307_ =
                    l_Lean_Environment_findAsync_x3f(v_env_1305_, v_constName_1288_, v___x_1306_);
                if crate::leanh::lean_obj_tag(v___x_1307_) == 1 {
                    v_val_1308_ = crate::leanh::lean_ctor_get(v___x_1307_, 0);
                    crate::leanh::lean_inc(v_val_1308_);
                    crate::leanh::lean_dec_ref_known(v___x_1307_, 1);
                    v_kind_1309_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_1308_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    if v_kind_1309_ == 6 {
                        v___x_1310_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1308_);
                        if crate::leanh::lean_obj_tag(v___x_1310_) == 6 {
                            crate::leanh::lean_dec(v_constName_1288_);
                            v_val_1311_ = crate::leanh::lean_ctor_get(v___x_1310_, 0);
                            v_isSharedCheck_1318_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1310_)) as u8;
                            if v_isSharedCheck_1318_ == 0 {
                                v___x_1313_ = v___x_1310_;
                                v_isShared_1314_ = v_isSharedCheck_1318_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_1311_);
                                crate::leanh::lean_dec(v___x_1310_);
                                v___x_1313_ = crate::leanh::lean_box(0);
                                v_isShared_1314_ = v_isSharedCheck_1318_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_1310_);
                            v___x_1319_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__7), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__7_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__7);
                            v___x_1320_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1_spec__2(v___x_1319_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
                            if crate::leanh::lean_obj_tag(v___x_1320_) == 0 {
                                v_a_1321_ = crate::leanh::lean_ctor_get(v___x_1320_, 0);
                                v_isSharedCheck_1329_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1320_)) as u8;
                                if v_isSharedCheck_1329_ == 0 {
                                    v___x_1323_ = v___x_1320_;
                                    v_isShared_1324_ = v_isSharedCheck_1329_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1321_);
                                    crate::leanh::lean_dec(v___x_1320_);
                                    v___x_1323_ = crate::leanh::lean_box(0);
                                    v_isShared_1324_ = v_isSharedCheck_1329_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_constName_1288_);
                                v_a_1330_ = crate::leanh::lean_ctor_get(v___x_1320_, 0);
                                v_isSharedCheck_1337_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1320_)) as u8;
                                if v_isSharedCheck_1337_ == 0 {
                                    v___x_1332_ = v___x_1320_;
                                    v_isShared_1333_ = v_isSharedCheck_1337_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1330_);
                                    crate::leanh::lean_dec(v___x_1320_);
                                    v___x_1332_ = crate::leanh::lean_box(0);
                                    v_isShared_1333_ = v_isSharedCheck_1337_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_1308_);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1307_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1297_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__1_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__1);
                v___x_1298_ = 0;
                v___x_1299_ = l_Lean_MessageData_ofConstName(v_constName_1288_, v___x_1298_);
                v___x_1300_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1300_, 0, v___x_1297_);
                crate::leanh::lean_ctor_set(v___x_1300_, 1, v___x_1299_);
                v___x_1301_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__3_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__3);
                v___x_1302_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1302_, 0, v___x_1300_);
                crate::leanh::lean_ctor_set(v___x_1302_, 1, v___x_1301_);
                v___x_1303_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(v___x_1302_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
                return v___x_1303_;
            }
            2 => {
                if v_isShared_1314_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1313_, 0);
                    v___x_1316_ = v___x_1313_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1317_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_val_1311_);
                    v___x_1316_ = v_reuseFailAlloc_1317_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1316_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_1321_) == 0 {
                    crate::leanh::lean_del_object(v___x_1323_);
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_constName_1288_);
                    v_val_1325_ = crate::leanh::lean_ctor_get(v_a_1321_, 0);
                    crate::leanh::lean_inc(v_val_1325_);
                    crate::leanh::lean_dec_ref_known(v_a_1321_, 1);
                    if v_isShared_1324_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1323_, 0, v_val_1325_);
                        v___x_1327_ = v___x_1323_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1328_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_val_1325_);
                        v___x_1327_ = v_reuseFailAlloc_1328_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_1327_;
            }
            6 => {
                if v_isShared_1333_ == 0 {
                    v___x_1335_ = v___x_1332_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1336_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
                    v___x_1335_ = v_reuseFailAlloc_1336_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1335_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___boxed(
    mut v_constName_1338_: *mut crate::leanh::LeanObject,
    mut v___y_1339_: *mut crate::leanh::LeanObject,
    mut v___y_1340_: *mut crate::leanh::LeanObject,
    mut v___y_1341_: *mut crate::leanh::LeanObject,
    mut v___y_1342_: *mut crate::leanh::LeanObject,
    mut v___y_1343_: *mut crate::leanh::LeanObject,
    mut v___y_1344_: *mut crate::leanh::LeanObject,
    mut v___y_1345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1346_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1(v_constName_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
    crate::leanh::lean_dec(v___y_1344_);
    crate::leanh::lean_dec_ref(v___y_1343_);
    crate::leanh::lean_dec(v___y_1342_);
    crate::leanh::lean_dec_ref(v___y_1341_);
    crate::leanh::lean_dec(v___y_1340_);
    crate::leanh::lean_dec_ref(v___y_1339_);
    return v_res_1346_;
}
pub unsafe fn _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1348_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__0;
    v___x_1349_ = l_Lean_stringToMessageData(v___x_1348_);
    return v___x_1349_;
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0(
    mut v_constName_1350_: *mut crate::leanh::LeanObject,
    mut v___y_1351_: *mut crate::leanh::LeanObject,
    mut v___y_1352_: *mut crate::leanh::LeanObject,
    mut v___y_1353_: *mut crate::leanh::LeanObject,
    mut v___y_1354_: *mut crate::leanh::LeanObject,
    mut v___y_1355_: *mut crate::leanh::LeanObject,
    mut v___y_1356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: u8 = 0;
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1371_: u8 = 0;
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1375_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1358_ = lean_st_ref_get(v___y_1356_);
                v_env_1359_ = crate::leanh::lean_ctor_get(v___x_1358_, 0);
                crate::leanh::lean_inc_ref(v_env_1359_);
                crate::leanh::lean_dec(v___x_1358_);
                crate::leanh::lean_inc(v_constName_1350_);
                v___x_1360_ = l_Lean_isInductiveCore_x3f(v_env_1359_, v_constName_1350_);
                if crate::leanh::lean_obj_tag(v___x_1360_) == 0 {
                    v___x_1361_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__1_once), _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1___closed__1);
                    v___x_1362_ = 0;
                    v___x_1363_ = l_Lean_MessageData_ofConstName(v_constName_1350_, v___x_1362_);
                    v___x_1364_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1364_, 0, v___x_1361_);
                    crate::leanh::lean_ctor_set(v___x_1364_, 1, v___x_1363_);
                    v___x_1365_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__1_once), _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___closed__1);
                    v___x_1366_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1366_, 0, v___x_1364_);
                    crate::leanh::lean_ctor_set(v___x_1366_, 1, v___x_1365_);
                    v___x_1367_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(v___x_1366_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
                    return v___x_1367_;
                } else {
                    crate::leanh::lean_dec(v_constName_1350_);
                    v_val_1368_ = crate::leanh::lean_ctor_get(v___x_1360_, 0);
                    v_isSharedCheck_1375_ = (!crate::leanh::lean_is_exclusive(v___x_1360_)) as u8;
                    if v_isSharedCheck_1375_ == 0 {
                        v___x_1370_ = v___x_1360_;
                        v_isShared_1371_ = v_isSharedCheck_1375_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1368_);
                        crate::leanh::lean_dec(v___x_1360_);
                        v___x_1370_ = crate::leanh::lean_box(0);
                        v_isShared_1371_ = v_isSharedCheck_1375_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1371_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1370_, 0);
                    v___x_1373_ = v___x_1370_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1374_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_val_1368_);
                    v___x_1373_ = v_reuseFailAlloc_1374_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1373_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0___boxed(
    mut v_constName_1376_: *mut crate::leanh::LeanObject,
    mut v___y_1377_: *mut crate::leanh::LeanObject,
    mut v___y_1378_: *mut crate::leanh::LeanObject,
    mut v___y_1379_: *mut crate::leanh::LeanObject,
    mut v___y_1380_: *mut crate::leanh::LeanObject,
    mut v___y_1381_: *mut crate::leanh::LeanObject,
    mut v___y_1382_: *mut crate::leanh::LeanObject,
    mut v___y_1383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1384_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0(v_constName_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
    crate::leanh::lean_dec(v___y_1382_);
    crate::leanh::lean_dec_ref(v___y_1381_);
    crate::leanh::lean_dec(v___y_1380_);
    crate::leanh::lean_dec_ref(v___y_1379_);
    crate::leanh::lean_dec(v___y_1378_);
    crate::leanh::lean_dec_ref(v___y_1377_);
    return v_res_1384_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__0()
-> f64 {
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: f64 = 0.0;
    v___x_1385_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1386_ = lean_float_of_nat(v___x_1385_);
    return v___x_1386_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg(
    mut v_cls_1390_: *mut crate::leanh::LeanObject,
    mut v_msg_1391_: *mut crate::leanh::LeanObject,
    mut v___y_1392_: *mut crate::leanh::LeanObject,
    mut v___y_1393_: *mut crate::leanh::LeanObject,
    mut v___y_1394_: *mut crate::leanh::LeanObject,
    mut v___y_1395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1402_: u8 = 0;
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1415_: u8 = 0;
    let mut v_tid_1416_: u64 = 0;
    let mut v_traces_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1420_: u8 = 0;
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: f64 = 0.0;
    let mut v___x_1423_: u8 = 0;
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1441_: u8 = 0;
    let mut v_isSharedCheck_1442_: u8 = 0;
    let mut v_isSharedCheck_1443_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1397_ = crate::leanh::lean_ctor_get(v___y_1394_, 5);
                v___x_1398_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3_spec__5(v_msg_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
                v_a_1399_ = crate::leanh::lean_ctor_get(v___x_1398_, 0);
                v_isSharedCheck_1443_ = (!crate::leanh::lean_is_exclusive(v___x_1398_)) as u8;
                if v_isSharedCheck_1443_ == 0 {
                    v___x_1401_ = v___x_1398_;
                    v_isShared_1402_ = v_isSharedCheck_1443_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1399_);
                    crate::leanh::lean_dec(v___x_1398_);
                    v___x_1401_ = crate::leanh::lean_box(0);
                    v_isShared_1402_ = v_isSharedCheck_1443_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1403_ = lean_st_ref_take(v___y_1395_);
                v_traceState_1404_ = crate::leanh::lean_ctor_get(v___x_1403_, 4);
                v_env_1405_ = crate::leanh::lean_ctor_get(v___x_1403_, 0);
                v_nextMacroScope_1406_ = crate::leanh::lean_ctor_get(v___x_1403_, 1);
                v_ngen_1407_ = crate::leanh::lean_ctor_get(v___x_1403_, 2);
                v_auxDeclNGen_1408_ = crate::leanh::lean_ctor_get(v___x_1403_, 3);
                v_cache_1409_ = crate::leanh::lean_ctor_get(v___x_1403_, 5);
                v_messages_1410_ = crate::leanh::lean_ctor_get(v___x_1403_, 6);
                v_infoState_1411_ = crate::leanh::lean_ctor_get(v___x_1403_, 7);
                v_snapshotTasks_1412_ = crate::leanh::lean_ctor_get(v___x_1403_, 8);
                v_isSharedCheck_1442_ = (!crate::leanh::lean_is_exclusive(v___x_1403_)) as u8;
                if v_isSharedCheck_1442_ == 0 {
                    v___x_1414_ = v___x_1403_;
                    v_isShared_1415_ = v_isSharedCheck_1442_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1412_);
                    crate::leanh::lean_inc(v_infoState_1411_);
                    crate::leanh::lean_inc(v_messages_1410_);
                    crate::leanh::lean_inc(v_cache_1409_);
                    crate::leanh::lean_inc(v_traceState_1404_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1408_);
                    crate::leanh::lean_inc(v_ngen_1407_);
                    crate::leanh::lean_inc(v_nextMacroScope_1406_);
                    crate::leanh::lean_inc(v_env_1405_);
                    crate::leanh::lean_dec(v___x_1403_);
                    v___x_1414_ = crate::leanh::lean_box(0);
                    v_isShared_1415_ = v_isSharedCheck_1442_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_1416_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_1404_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_1417_ = crate::leanh::lean_ctor_get(v_traceState_1404_, 0);
                v_isSharedCheck_1441_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_1404_)) as u8;
                if v_isSharedCheck_1441_ == 0 {
                    v___x_1419_ = v_traceState_1404_;
                    v_isShared_1420_ = v_isSharedCheck_1441_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_1417_);
                    crate::leanh::lean_dec(v_traceState_1404_);
                    v___x_1419_ = crate::leanh::lean_box(0);
                    v_isShared_1420_ = v_isSharedCheck_1441_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1421_ = crate::leanh::lean_box(0);
                v___x_1422_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__0);
                v___x_1423_ = 0;
                v___x_1424_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__1;
                v___x_1425_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_1425_, 0, v_cls_1390_);
                crate::leanh::lean_ctor_set(v___x_1425_, 1, v___x_1421_);
                crate::leanh::lean_ctor_set(v___x_1425_, 2, v___x_1424_);
                crate::leanh::lean_ctor_set_float(
                    v___x_1425_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_1422_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_1425_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_1422_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1425_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_1423_,
                );
                v___x_1426_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___closed__2;
                v___x_1427_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1427_, 0, v___x_1425_);
                crate::leanh::lean_ctor_set(v___x_1427_, 1, v_a_1399_);
                crate::leanh::lean_ctor_set(v___x_1427_, 2, v___x_1426_);
                crate::leanh::lean_inc(v_ref_1397_);
                v___x_1428_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1428_, 0, v_ref_1397_);
                crate::leanh::lean_ctor_set(v___x_1428_, 1, v___x_1427_);
                v___x_1429_ = l_Lean_PersistentArray_push___redArg(v_traces_1417_, v___x_1428_);
                if v_isShared_1420_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1419_, 0, v___x_1429_);
                    v___x_1431_ = v___x_1419_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1440_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1429_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_1440_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_1416_,
                    );
                    v___x_1431_ = v_reuseFailAlloc_1440_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1415_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1414_, 4, v___x_1431_);
                    v___x_1433_ = v___x_1414_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1439_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_env_1405_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_nextMacroScope_1406_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1439_, 2, v_ngen_1407_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1439_, 3, v_auxDeclNGen_1408_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1439_, 4, v___x_1431_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1439_, 5, v_cache_1409_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1439_, 6, v_messages_1410_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1439_, 7, v_infoState_1411_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1439_, 8, v_snapshotTasks_1412_);
                    v___x_1433_ = v_reuseFailAlloc_1439_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1434_ = lean_st_ref_set(v___y_1395_, v___x_1433_);
                v___x_1435_ = crate::leanh::lean_box(0);
                if v_isShared_1402_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1401_, 0, v___x_1435_);
                    v___x_1437_ = v___x_1401_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1438_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
                    v___x_1437_ = v_reuseFailAlloc_1438_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1437_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg___boxed(
    mut v_cls_1444_: *mut crate::leanh::LeanObject,
    mut v_msg_1445_: *mut crate::leanh::LeanObject,
    mut v___y_1446_: *mut crate::leanh::LeanObject,
    mut v___y_1447_: *mut crate::leanh::LeanObject,
    mut v___y_1448_: *mut crate::leanh::LeanObject,
    mut v___y_1449_: *mut crate::leanh::LeanObject,
    mut v___y_1450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1451_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg(v_cls_1444_, v_msg_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
    crate::leanh::lean_dec(v___y_1449_);
    crate::leanh::lean_dec_ref(v___y_1448_);
    crate::leanh::lean_dec(v___y_1447_);
    crate::leanh::lean_dec_ref(v___y_1446_);
    return v_res_1451_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg(
    mut v_upperBound_1485_: *mut crate::leanh::LeanObject,
    mut v_a_1486_: *mut crate::leanh::LeanObject,
    mut v___x_1487_: *mut crate::leanh::LeanObject,
    mut v_a_1488_: *mut crate::leanh::LeanObject,
    mut v_b_1489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1491_: u8 = 0;
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: u8 = 0;
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1491_ = lean_nat_dec_lt(v_a_1488_, v_upperBound_1485_);
                if v___x_1491_ == 0 {
                    crate::leanh::lean_dec(v_a_1488_);
                    crate::leanh::lean_dec(v___x_1487_);
                    crate::leanh::lean_dec(v_a_1486_);
                    v___x_1492_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1492_, 0, v_b_1489_);
                    return v___x_1492_;
                } else {
                    v___x_1493_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__1;
                    v___x_1494_ = crate::leanh::lean_unsigned_to_nat(5);
                    crate::leanh::lean_inc_n(v_a_1488_, 2);
                    crate::leanh::lean_inc_n(v___x_1487_, 2);
                    crate::leanh::lean_inc_n(v_a_1486_, 2);
                    v___x_1495_ = l_Lean_Meta_Tactic_BVDecide_Normalize_mkApplyProjControlDiscrPath(
                        v_a_1486_,
                        v___x_1487_,
                        v_a_1488_,
                        v___x_1493_,
                        v___x_1494_,
                    );
                    v___x_1496_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__8;
                    v___x_1497_ = 0;
                    v___x_1498_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__10;
                    v___x_1499_ = l_Lean_Meta_Simp_Simprocs_addCore(
                        v_b_1489_,
                        v___x_1495_,
                        v___x_1496_,
                        v___x_1497_,
                        v___x_1498_,
                    );
                    v___x_1500_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__12;
                    v___x_1501_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1502_ = l_Lean_Meta_Tactic_BVDecide_Normalize_mkApplyProjControlDiscrPath(
                        v_a_1486_,
                        v___x_1487_,
                        v_a_1488_,
                        v___x_1500_,
                        v___x_1501_,
                    );
                    v___x_1503_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__14;
                    v___x_1504_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___closed__16;
                    v___x_1505_ = l_Lean_Meta_Simp_Simprocs_addCore(
                        v___x_1499_,
                        v___x_1502_,
                        v___x_1503_,
                        v___x_1497_,
                        v___x_1504_,
                    );
                    v___x_1506_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1507_ = lean_nat_add(v_a_1488_, v___x_1506_);
                    crate::leanh::lean_dec(v_a_1488_);
                    v_a_1488_ = v___x_1507_;
                    v_b_1489_ = v___x_1505_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg___boxed(
    mut v_upperBound_1509_: *mut crate::leanh::LeanObject,
    mut v_a_1510_: *mut crate::leanh::LeanObject,
    mut v___x_1511_: *mut crate::leanh::LeanObject,
    mut v_a_1512_: *mut crate::leanh::LeanObject,
    mut v_b_1513_: *mut crate::leanh::LeanObject,
    mut v___y_1514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1515_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg(v_upperBound_1509_, v_a_1510_, v___x_1511_, v_a_1512_, v_b_1513_);
    crate::leanh::lean_dec(v_upperBound_1509_);
    return v_res_1515_;
}
pub unsafe fn _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1524_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__1;
    v___x_1525_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__3;
    v___x_1526_ = l_Lean_Name_append(v___x_1525_, v___x_1524_);
    return v___x_1526_;
}
pub unsafe fn _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1528_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__5;
    v___x_1529_ = l_Lean_stringToMessageData(v___x_1528_);
    return v___x_1529_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4(
    mut v___x_1530_: *mut crate::leanh::LeanObject,
    mut v_a_1531_: *mut crate::leanh::LeanObject,
    mut v_a_1532_: *mut crate::leanh::LeanObject,
    mut v___y_1533_: *mut crate::leanh::LeanObject,
    mut v___y_1534_: *mut crate::leanh::LeanObject,
    mut v___y_1535_: *mut crate::leanh::LeanObject,
    mut v___y_1536_: *mut crate::leanh::LeanObject,
    mut v___y_1537_: *mut crate::leanh::LeanObject,
    mut v___y_1538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1557_: u8 = 0;
    let mut v_lemmas_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldNames_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1579_: u8 = 0;
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1583_: u8 = 0;
    let mut v_toConstantVal_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: u8 = 0;
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1592_: u8 = 0;
    let mut v___x_1593_: u8 = 0;
    let mut v___y_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1610_: u8 = 0;
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1614_: u8 = 0;
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: u8 = 0;
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1625_: u8 = 0;
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1629_: u8 = 0;
    let mut v_isSharedCheck_1630_: u8 = 0;
    let mut v_a_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1634_: u8 = 0;
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1638_: u8 = 0;
    let mut v_a_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1642_: u8 = 0;
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1646_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1531_) == 0 {
                    crate::leanh::lean_dec_ref(v___x_1530_);
                    v___x_1540_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1540_, 0, v_a_1532_);
                    v___x_1541_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1541_, 0, v___x_1540_);
                    return v___x_1541_;
                } else {
                    v_key_1542_ = crate::leanh::lean_ctor_get(v_a_1531_, 0);
                    crate::leanh::lean_inc_n(v_key_1542_, 2);
                    v_tail_1543_ = crate::leanh::lean_ctor_get(v_a_1531_, 2);
                    crate::leanh::lean_inc(v_tail_1543_);
                    crate::leanh::lean_dec_ref_known(v_a_1531_, 3);
                    v___x_1544_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0(v_key_1542_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
                    if crate::leanh::lean_obj_tag(v___x_1544_) == 0 {
                        v_a_1545_ = crate::leanh::lean_ctor_get(v___x_1544_, 0);
                        crate::leanh::lean_inc(v_a_1545_);
                        crate::leanh::lean_dec_ref_known(v___x_1544_, 1);
                        v_numParams_1546_ = crate::leanh::lean_ctor_get(v_a_1545_, 1);
                        crate::leanh::lean_inc(v_numParams_1546_);
                        v_ctors_1547_ = crate::leanh::lean_ctor_get(v_a_1545_, 4);
                        crate::leanh::lean_inc(v_ctors_1547_);
                        crate::leanh::lean_dec(v_a_1545_);
                        v___x_1548_ = crate::leanh::lean_box(0);
                        v___x_1549_ = l_List_head_x21___redArg(v___x_1548_, v_ctors_1547_);
                        crate::leanh::lean_dec(v_ctors_1547_);
                        v___x_1550_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__1(v___x_1549_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
                        if crate::leanh::lean_obj_tag(v___x_1550_) == 0 {
                            v_a_1551_ = crate::leanh::lean_ctor_get(v___x_1550_, 0);
                            crate::leanh::lean_inc(v_a_1551_);
                            crate::leanh::lean_dec_ref_known(v___x_1550_, 1);
                            v___x_1552_ = lean_st_ref_get(v___y_1538_);
                            v_fst_1553_ = crate::leanh::lean_ctor_get(v_a_1532_, 0);
                            v_snd_1554_ = crate::leanh::lean_ctor_get(v_a_1532_, 1);
                            v_isSharedCheck_1630_ =
                                (!crate::leanh::lean_is_exclusive(v_a_1532_)) as u8;
                            if v_isSharedCheck_1630_ == 0 {
                                v___x_1556_ = v_a_1532_;
                                v_isShared_1557_ = v_isSharedCheck_1630_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_1554_);
                                crate::leanh::lean_inc(v_fst_1553_);
                                crate::leanh::lean_dec(v_a_1532_);
                                v___x_1556_ = crate::leanh::lean_box(0);
                                v_isShared_1557_ = v_isSharedCheck_1630_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_numParams_1546_);
                            crate::leanh::lean_dec(v_tail_1543_);
                            crate::leanh::lean_dec(v_key_1542_);
                            crate::leanh::lean_dec_ref(v_a_1532_);
                            crate::leanh::lean_dec_ref(v___x_1530_);
                            v_a_1631_ = crate::leanh::lean_ctor_get(v___x_1550_, 0);
                            v_isSharedCheck_1638_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1550_)) as u8;
                            if v_isSharedCheck_1638_ == 0 {
                                v___x_1633_ = v___x_1550_;
                                v_isShared_1634_ = v_isSharedCheck_1638_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1631_);
                                crate::leanh::lean_dec(v___x_1550_);
                                v___x_1633_ = crate::leanh::lean_box(0);
                                v_isShared_1634_ = v_isSharedCheck_1638_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_tail_1543_);
                        crate::leanh::lean_dec(v_key_1542_);
                        crate::leanh::lean_dec_ref(v_a_1532_);
                        crate::leanh::lean_dec_ref(v___x_1530_);
                        v_a_1639_ = crate::leanh::lean_ctor_get(v___x_1544_, 0);
                        v_isSharedCheck_1646_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1544_)) as u8;
                        if v_isSharedCheck_1646_ == 0 {
                            v___x_1641_ = v___x_1544_;
                            v_isShared_1642_ = v_isSharedCheck_1646_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1639_);
                            crate::leanh::lean_dec(v___x_1544_);
                            v___x_1641_ = crate::leanh::lean_box(0);
                            v_isShared_1642_ = v_isSharedCheck_1646_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_toConstantVal_1584_ = crate::leanh::lean_ctor_get(v_a_1551_, 0);
                crate::leanh::lean_inc_ref(v_toConstantVal_1584_);
                crate::leanh::lean_dec(v_a_1551_);
                v_name_1585_ = crate::leanh::lean_ctor_get(v_toConstantVal_1584_, 0);
                crate::leanh::lean_inc(v_name_1585_);
                crate::leanh::lean_dec_ref(v_toConstantVal_1584_);
                v_env_1586_ = crate::leanh::lean_ctor_get(v___x_1552_, 0);
                crate::leanh::lean_inc_ref(v_env_1586_);
                crate::leanh::lean_dec(v___x_1552_);
                v___x_1587_ = l_Lean_Meta_mkInjectiveEqTheoremNameFor(v_name_1585_);
                v___x_1588_ = 0;
                crate::leanh::lean_inc(v___x_1587_);
                v___x_1589_ = l_Lean_Environment_find_x3f(v_env_1586_, v___x_1587_, v___x_1588_);
                if crate::leanh::lean_obj_tag(v___x_1589_) == 0 {
                    crate::leanh::lean_dec(v___x_1587_);
                    v_lemmas_1559_ = v_snd_1554_;
                    v___y_1560_ = v___y_1533_;
                    v___y_1561_ = v___y_1534_;
                    v___y_1562_ = v___y_1535_;
                    v___y_1563_ = v___y_1536_;
                    v___y_1564_ = v___y_1537_;
                    v___y_1565_ = v___y_1538_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_1589_, 1);
                    v_options_1590_ = crate::leanh::lean_ctor_get(v___y_1537_, 2);
                    v_inheritedTraceOptions_1591_ = crate::leanh::lean_ctor_get(v___y_1537_, 13);
                    v_hasTrace_1592_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_1590_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v___x_1593_ = 1;
                    if v_hasTrace_1592_ == 0 {
                        v___y_1595_ = v___y_1533_;
                        v___y_1596_ = v___y_1534_;
                        v___y_1597_ = v___y_1535_;
                        v___y_1598_ = v___y_1536_;
                        v___y_1599_ = v___y_1537_;
                        v___y_1600_ = v___y_1538_;
                        state = 6;
                        continue;
                    } else {
                        v___x_1615_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__1;
                        v___x_1616_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__4), core::ptr::addr_of_mut!(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__4_once), _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__4);
                        v___x_1617_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_1591_,
                            v_options_1590_,
                            v___x_1616_,
                        );
                        if v___x_1617_ == 0 {
                            v___y_1595_ = v___y_1533_;
                            v___y_1596_ = v___y_1534_;
                            v___y_1597_ = v___y_1535_;
                            v___y_1598_ = v___y_1536_;
                            v___y_1599_ = v___y_1537_;
                            v___y_1600_ = v___y_1538_;
                            state = 6;
                            continue;
                        } else {
                            v___x_1618_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__6), core::ptr::addr_of_mut!(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__6_once), _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___closed__6);
                            crate::leanh::lean_inc(v___x_1587_);
                            v___x_1619_ = l_Lean_MessageData_ofName(v___x_1587_);
                            v___x_1620_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1620_, 0, v___x_1618_);
                            crate::leanh::lean_ctor_set(v___x_1620_, 1, v___x_1619_);
                            v___x_1621_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg(v___x_1615_, v___x_1620_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
                            if crate::leanh::lean_obj_tag(v___x_1621_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_1621_, 1);
                                v___y_1595_ = v___y_1533_;
                                v___y_1596_ = v___y_1534_;
                                v___y_1597_ = v___y_1535_;
                                v___y_1598_ = v___y_1536_;
                                v___y_1599_ = v___y_1537_;
                                v___y_1600_ = v___y_1538_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1587_);
                                crate::leanh::lean_del_object(v___x_1556_);
                                crate::leanh::lean_dec(v_snd_1554_);
                                crate::leanh::lean_dec(v_fst_1553_);
                                crate::leanh::lean_dec(v_numParams_1546_);
                                crate::leanh::lean_dec(v_tail_1543_);
                                crate::leanh::lean_dec(v_key_1542_);
                                crate::leanh::lean_dec_ref(v___x_1530_);
                                v_a_1622_ = crate::leanh::lean_ctor_get(v___x_1621_, 0);
                                v_isSharedCheck_1629_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1621_)) as u8;
                                if v_isSharedCheck_1629_ == 0 {
                                    v___x_1624_ = v___x_1621_;
                                    v_isShared_1625_ = v_isSharedCheck_1629_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1622_);
                                    crate::leanh::lean_dec(v___x_1621_);
                                    v___x_1624_ = crate::leanh::lean_box(0);
                                    v_isShared_1625_ = v_isSharedCheck_1629_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                crate::leanh::lean_inc(v_key_1542_);
                crate::leanh::lean_inc_ref(v___x_1530_);
                v___x_1566_ = l_Lean_getStructureInfo(v___x_1530_, v_key_1542_);
                v_fieldNames_1567_ = crate::leanh::lean_ctor_get(v___x_1566_, 1);
                crate::leanh::lean_inc_ref(v_fieldNames_1567_);
                crate::leanh::lean_dec_ref(v___x_1566_);
                v___x_1568_ = lean_array_get_size(v_fieldNames_1567_);
                crate::leanh::lean_dec_ref(v_fieldNames_1567_);
                v___x_1569_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1570_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg(v___x_1568_, v_key_1542_, v_numParams_1546_, v___x_1569_, v_fst_1553_);
                if crate::leanh::lean_obj_tag(v___x_1570_) == 0 {
                    v_a_1571_ = crate::leanh::lean_ctor_get(v___x_1570_, 0);
                    crate::leanh::lean_inc(v_a_1571_);
                    crate::leanh::lean_dec_ref_known(v___x_1570_, 1);
                    if v_isShared_1557_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1556_, 1, v_lemmas_1559_);
                        crate::leanh::lean_ctor_set(v___x_1556_, 0, v_a_1571_);
                        v___x_1573_ = v___x_1556_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1575_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1571_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_lemmas_1559_);
                        v___x_1573_ = v_reuseFailAlloc_1575_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_lemmas_1559_);
                    crate::leanh::lean_del_object(v___x_1556_);
                    crate::leanh::lean_dec(v_tail_1543_);
                    crate::leanh::lean_dec_ref(v___x_1530_);
                    v_a_1576_ = crate::leanh::lean_ctor_get(v___x_1570_, 0);
                    v_isSharedCheck_1583_ = (!crate::leanh::lean_is_exclusive(v___x_1570_)) as u8;
                    if v_isSharedCheck_1583_ == 0 {
                        v___x_1578_ = v___x_1570_;
                        v_isShared_1579_ = v_isSharedCheck_1583_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1576_);
                        crate::leanh::lean_dec(v___x_1570_);
                        v___x_1578_ = crate::leanh::lean_box(0);
                        v_isShared_1579_ = v_isSharedCheck_1583_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v_a_1531_ = v_tail_1543_;
                v_a_1532_ = v___x_1573_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_1579_ == 0 {
                    v___x_1581_ = v___x_1578_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1582_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
                    v___x_1581_ = v_reuseFailAlloc_1582_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1581_;
            }
            6 => {
                crate::leanh::lean_inc(v___x_1587_);
                v___x_1601_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_1601_, 0, v___x_1587_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1601_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1593_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1601_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    v___x_1588_,
                );
                v___x_1602_ = crate::leanh::lean_box(0);
                v___x_1603_ = l_Lean_mkConst(v___x_1587_, v___x_1602_);
                v___x_1604_ = l_Lean_Meta_simpGlobalConfig;
                v___x_1605_ = l_Lean_Meta_SimpTheoremsArray_addTheorem(
                    v_snd_1554_,
                    v___x_1601_,
                    v___x_1603_,
                    v___x_1604_,
                    v___y_1597_,
                    v___y_1598_,
                    v___y_1599_,
                    v___y_1600_,
                );
                if crate::leanh::lean_obj_tag(v___x_1605_) == 0 {
                    v_a_1606_ = crate::leanh::lean_ctor_get(v___x_1605_, 0);
                    crate::leanh::lean_inc(v_a_1606_);
                    crate::leanh::lean_dec_ref_known(v___x_1605_, 1);
                    v_lemmas_1559_ = v_a_1606_;
                    v___y_1560_ = v___y_1595_;
                    v___y_1561_ = v___y_1596_;
                    v___y_1562_ = v___y_1597_;
                    v___y_1563_ = v___y_1598_;
                    v___y_1564_ = v___y_1599_;
                    v___y_1565_ = v___y_1600_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_del_object(v___x_1556_);
                    crate::leanh::lean_dec(v_fst_1553_);
                    crate::leanh::lean_dec(v_numParams_1546_);
                    crate::leanh::lean_dec(v_tail_1543_);
                    crate::leanh::lean_dec(v_key_1542_);
                    crate::leanh::lean_dec_ref(v___x_1530_);
                    v_a_1607_ = crate::leanh::lean_ctor_get(v___x_1605_, 0);
                    v_isSharedCheck_1614_ = (!crate::leanh::lean_is_exclusive(v___x_1605_)) as u8;
                    if v_isSharedCheck_1614_ == 0 {
                        v___x_1609_ = v___x_1605_;
                        v_isShared_1610_ = v_isSharedCheck_1614_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1607_);
                        crate::leanh::lean_dec(v___x_1605_);
                        v___x_1609_ = crate::leanh::lean_box(0);
                        v_isShared_1610_ = v_isSharedCheck_1614_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_1610_ == 0 {
                    v___x_1612_ = v___x_1609_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1613_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
                    v___x_1612_ = v_reuseFailAlloc_1613_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1612_;
            }
            9 => {
                if v_isShared_1625_ == 0 {
                    v___x_1627_ = v___x_1624_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1628_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
                    v___x_1627_ = v_reuseFailAlloc_1628_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1627_;
            }
            11 => {
                if v_isShared_1634_ == 0 {
                    v___x_1636_ = v___x_1633_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1637_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
                    v___x_1636_ = v_reuseFailAlloc_1637_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1636_;
            }
            13 => {
                if v_isShared_1642_ == 0 {
                    v___x_1644_ = v___x_1641_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1645_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
                    v___x_1644_ = v_reuseFailAlloc_1645_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1644_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4___boxed(
    mut v___x_1647_: *mut crate::leanh::LeanObject,
    mut v_a_1648_: *mut crate::leanh::LeanObject,
    mut v_a_1649_: *mut crate::leanh::LeanObject,
    mut v___y_1650_: *mut crate::leanh::LeanObject,
    mut v___y_1651_: *mut crate::leanh::LeanObject,
    mut v___y_1652_: *mut crate::leanh::LeanObject,
    mut v___y_1653_: *mut crate::leanh::LeanObject,
    mut v___y_1654_: *mut crate::leanh::LeanObject,
    mut v___y_1655_: *mut crate::leanh::LeanObject,
    mut v___y_1656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1657_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4(v___x_1647_, v_a_1648_, v_a_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
    crate::leanh::lean_dec(v___y_1655_);
    crate::leanh::lean_dec_ref(v___y_1654_);
    crate::leanh::lean_dec(v___y_1653_);
    crate::leanh::lean_dec_ref(v___y_1652_);
    crate::leanh::lean_dec(v___y_1651_);
    crate::leanh::lean_dec_ref(v___y_1650_);
    return v_res_1657_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__5(
    mut v___x_1658_: *mut crate::leanh::LeanObject,
    mut v_as_1659_: *mut crate::leanh::LeanObject,
    mut v_sz_1660_: usize,
    mut v_i_1661_: usize,
    mut v_b_1662_: *mut crate::leanh::LeanObject,
    mut v___y_1663_: *mut crate::leanh::LeanObject,
    mut v___y_1664_: *mut crate::leanh::LeanObject,
    mut v___y_1665_: *mut crate::leanh::LeanObject,
    mut v___y_1666_: *mut crate::leanh::LeanObject,
    mut v___y_1667_: *mut crate::leanh::LeanObject,
    mut v___y_1668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1670_: u8 = 0;
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1677_: u8 = 0;
    let mut v_a_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: usize = 0;
    let mut v___x_1684_: usize = 0;
    let mut v_isSharedCheck_1686_: u8 = 0;
    let mut v_a_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1690_: u8 = 0;
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1694_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1670_ = lean_usize_dec_lt(v_i_1661_, v_sz_1660_);
                if v___x_1670_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1658_);
                    v___x_1671_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1671_, 0, v_b_1662_);
                    return v___x_1671_;
                } else {
                    v_a_1672_ = lean_array_uget_borrowed(v_as_1659_, v_i_1661_);
                    crate::leanh::lean_inc(v_a_1672_);
                    crate::leanh::lean_inc_ref(v___x_1658_);
                    v___x_1673_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__4(v___x_1658_, v_a_1672_, v_b_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
                    if crate::leanh::lean_obj_tag(v___x_1673_) == 0 {
                        v_a_1674_ = crate::leanh::lean_ctor_get(v___x_1673_, 0);
                        v_isSharedCheck_1686_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1673_)) as u8;
                        if v_isSharedCheck_1686_ == 0 {
                            v___x_1676_ = v___x_1673_;
                            v_isShared_1677_ = v_isSharedCheck_1686_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1674_);
                            crate::leanh::lean_dec(v___x_1673_);
                            v___x_1676_ = crate::leanh::lean_box(0);
                            v_isShared_1677_ = v_isSharedCheck_1686_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1658_);
                        v_a_1687_ = crate::leanh::lean_ctor_get(v___x_1673_, 0);
                        v_isSharedCheck_1694_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1673_)) as u8;
                        if v_isSharedCheck_1694_ == 0 {
                            v___x_1689_ = v___x_1673_;
                            v_isShared_1690_ = v_isSharedCheck_1694_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1687_);
                            crate::leanh::lean_dec(v___x_1673_);
                            v___x_1689_ = crate::leanh::lean_box(0);
                            v_isShared_1690_ = v_isSharedCheck_1694_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1674_) == 0 {
                    crate::leanh::lean_dec_ref(v___x_1658_);
                    v_a_1678_ = crate::leanh::lean_ctor_get(v_a_1674_, 0);
                    crate::leanh::lean_inc(v_a_1678_);
                    crate::leanh::lean_dec_ref_known(v_a_1674_, 1);
                    if v_isShared_1677_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1676_, 0, v_a_1678_);
                        v___x_1680_ = v___x_1676_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1681_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_a_1678_);
                        v___x_1680_ = v_reuseFailAlloc_1681_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1676_);
                    v_a_1682_ = crate::leanh::lean_ctor_get(v_a_1674_, 0);
                    crate::leanh::lean_inc(v_a_1682_);
                    crate::leanh::lean_dec_ref_known(v_a_1674_, 1);
                    v___x_1683_ = 1usize;
                    v___x_1684_ = lean_usize_add(v_i_1661_, v___x_1683_);
                    v_i_1661_ = v___x_1684_;
                    v_b_1662_ = v_a_1682_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                return v___x_1680_;
            }
            3 => {
                if v_isShared_1690_ == 0 {
                    v___x_1692_ = v___x_1689_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1693_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
                    v___x_1692_ = v_reuseFailAlloc_1693_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1692_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__5___boxed(
    mut v___x_1695_: *mut crate::leanh::LeanObject,
    mut v_as_1696_: *mut crate::leanh::LeanObject,
    mut v_sz_1697_: *mut crate::leanh::LeanObject,
    mut v_i_1698_: *mut crate::leanh::LeanObject,
    mut v_b_1699_: *mut crate::leanh::LeanObject,
    mut v___y_1700_: *mut crate::leanh::LeanObject,
    mut v___y_1701_: *mut crate::leanh::LeanObject,
    mut v___y_1702_: *mut crate::leanh::LeanObject,
    mut v___y_1703_: *mut crate::leanh::LeanObject,
    mut v___y_1704_: *mut crate::leanh::LeanObject,
    mut v___y_1705_: *mut crate::leanh::LeanObject,
    mut v___y_1706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1707_: usize = 0;
    let mut v_i_boxed_1708_: usize = 0;
    let mut v_res_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1707_ = crate::leanh::lean_unbox_usize(v_sz_1697_);
    crate::leanh::lean_dec(v_sz_1697_);
    v_i_boxed_1708_ = crate::leanh::lean_unbox_usize(v_i_1698_);
    crate::leanh::lean_dec(v_i_1698_);
    v_res_1709_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__5(v___x_1695_, v_as_1696_, v_sz_boxed_1707_, v_i_boxed_1708_, v_b_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
    crate::leanh::lean_dec(v___y_1705_);
    crate::leanh::lean_dec_ref(v___y_1704_);
    crate::leanh::lean_dec(v___y_1703_);
    crate::leanh::lean_dec_ref(v___y_1702_);
    crate::leanh::lean_dec(v___y_1701_);
    crate::leanh::lean_dec_ref(v___y_1700_);
    crate::leanh::lean_dec_ref(v_as_1696_);
    return v_res_1709_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas(
    mut v_simprocs_1710_: *mut crate::leanh::LeanObject,
    mut v_lemmas_1711_: *mut crate::leanh::LeanObject,
    mut v_a_1712_: *mut crate::leanh::LeanObject,
    mut v_a_1713_: *mut crate::leanh::LeanObject,
    mut v_a_1714_: *mut crate::leanh::LeanObject,
    mut v_a_1715_: *mut crate::leanh::LeanObject,
    mut v_a_1716_: *mut crate::leanh::LeanObject,
    mut v_a_1717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingStructures_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1727_: u8 = 0;
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1730_: usize = 0;
    let mut v___x_1731_: usize = 0;
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1736_: u8 = 0;
    let mut v_fst_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1741_: u8 = 0;
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1748_: u8 = 0;
    let mut v_isSharedCheck_1749_: u8 = 0;
    let mut v_reuseFailAlloc_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1751_: u8 = 0;
    let mut v_unused_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1719_ = lean_st_ref_get(v_a_1713_);
                v___x_1720_ = lean_st_ref_get(v_a_1717_);
                v_typeAnalysis_1721_ = crate::leanh::lean_ctor_get(v___x_1719_, 2);
                crate::leanh::lean_inc_ref(v_typeAnalysis_1721_);
                crate::leanh::lean_dec(v___x_1719_);
                v_interestingStructures_1722_ =
                    crate::leanh::lean_ctor_get(v_typeAnalysis_1721_, 0);
                crate::leanh::lean_inc_ref(v_interestingStructures_1722_);
                crate::leanh::lean_dec_ref(v_typeAnalysis_1721_);
                v_env_1723_ = crate::leanh::lean_ctor_get(v___x_1720_, 0);
                crate::leanh::lean_inc_ref(v_env_1723_);
                crate::leanh::lean_dec(v___x_1720_);
                v_buckets_1724_ = crate::leanh::lean_ctor_get(v_interestingStructures_1722_, 1);
                v_isSharedCheck_1751_ =
                    (!crate::leanh::lean_is_exclusive(v_interestingStructures_1722_)) as u8;
                if v_isSharedCheck_1751_ == 0 {
                    v_unused_1752_ = crate::leanh::lean_ctor_get(v_interestingStructures_1722_, 0);
                    crate::leanh::lean_dec(v_unused_1752_);
                    v___x_1726_ = v_interestingStructures_1722_;
                    v_isShared_1727_ = v_isSharedCheck_1751_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_1724_);
                    crate::leanh::lean_dec(v_interestingStructures_1722_);
                    v___x_1726_ = crate::leanh::lean_box(0);
                    v_isShared_1727_ = v_isSharedCheck_1751_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1727_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1726_, 1, v_lemmas_1711_);
                    crate::leanh::lean_ctor_set(v___x_1726_, 0, v_simprocs_1710_);
                    v___x_1729_ = v___x_1726_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1750_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_simprocs_1710_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_lemmas_1711_);
                    v___x_1729_ = v_reuseFailAlloc_1750_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_sz_1730_ = lean_array_size(v_buckets_1724_);
                v___x_1731_ = 0usize;
                v___x_1732_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__5(v_env_1723_, v_buckets_1724_, v_sz_1730_, v___x_1731_, v___x_1729_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_);
                crate::leanh::lean_dec_ref(v_buckets_1724_);
                if crate::leanh::lean_obj_tag(v___x_1732_) == 0 {
                    v_a_1733_ = crate::leanh::lean_ctor_get(v___x_1732_, 0);
                    v_isSharedCheck_1749_ = (!crate::leanh::lean_is_exclusive(v___x_1732_)) as u8;
                    if v_isSharedCheck_1749_ == 0 {
                        v___x_1735_ = v___x_1732_;
                        v_isShared_1736_ = v_isSharedCheck_1749_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1733_);
                        crate::leanh::lean_dec(v___x_1732_);
                        v___x_1735_ = crate::leanh::lean_box(0);
                        v_isShared_1736_ = v_isSharedCheck_1749_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_1732_;
                }
            }
            3 => {
                v_fst_1737_ = crate::leanh::lean_ctor_get(v_a_1733_, 0);
                v_snd_1738_ = crate::leanh::lean_ctor_get(v_a_1733_, 1);
                v_isSharedCheck_1748_ = (!crate::leanh::lean_is_exclusive(v_a_1733_)) as u8;
                if v_isSharedCheck_1748_ == 0 {
                    v___x_1740_ = v_a_1733_;
                    v_isShared_1741_ = v_isSharedCheck_1748_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1738_);
                    crate::leanh::lean_inc(v_fst_1737_);
                    crate::leanh::lean_dec(v_a_1733_);
                    v___x_1740_ = crate::leanh::lean_box(0);
                    v_isShared_1741_ = v_isSharedCheck_1748_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1741_ == 0 {
                    v___x_1743_ = v___x_1740_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1747_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_fst_1737_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1747_, 1, v_snd_1738_);
                    v___x_1743_ = v_reuseFailAlloc_1747_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1736_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1735_, 0, v___x_1743_);
                    v___x_1745_ = v___x_1735_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1746_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1743_);
                    v___x_1745_ = v_reuseFailAlloc_1746_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1745_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas___boxed(
    mut v_simprocs_1753_: *mut crate::leanh::LeanObject,
    mut v_lemmas_1754_: *mut crate::leanh::LeanObject,
    mut v_a_1755_: *mut crate::leanh::LeanObject,
    mut v_a_1756_: *mut crate::leanh::LeanObject,
    mut v_a_1757_: *mut crate::leanh::LeanObject,
    mut v_a_1758_: *mut crate::leanh::LeanObject,
    mut v_a_1759_: *mut crate::leanh::LeanObject,
    mut v_a_1760_: *mut crate::leanh::LeanObject,
    mut v_a_1761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1762_ = l_Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas(
        v_simprocs_1753_,
        v_lemmas_1754_,
        v_a_1755_,
        v_a_1756_,
        v_a_1757_,
        v_a_1758_,
        v_a_1759_,
        v_a_1760_,
    );
    crate::leanh::lean_dec(v_a_1760_);
    crate::leanh::lean_dec_ref(v_a_1759_);
    crate::leanh::lean_dec(v_a_1758_);
    crate::leanh::lean_dec_ref(v_a_1757_);
    crate::leanh::lean_dec(v_a_1756_);
    crate::leanh::lean_dec_ref(v_a_1755_);
    return v_res_1762_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2(
    mut v_upperBound_1763_: *mut crate::leanh::LeanObject,
    mut v_a_1764_: *mut crate::leanh::LeanObject,
    mut v___x_1765_: *mut crate::leanh::LeanObject,
    mut v_inst_1766_: *mut crate::leanh::LeanObject,
    mut v_R_1767_: *mut crate::leanh::LeanObject,
    mut v_a_1768_: *mut crate::leanh::LeanObject,
    mut v_b_1769_: *mut crate::leanh::LeanObject,
    mut v_c_1770_: *mut crate::leanh::LeanObject,
    mut v___y_1771_: *mut crate::leanh::LeanObject,
    mut v___y_1772_: *mut crate::leanh::LeanObject,
    mut v___y_1773_: *mut crate::leanh::LeanObject,
    mut v___y_1774_: *mut crate::leanh::LeanObject,
    mut v___y_1775_: *mut crate::leanh::LeanObject,
    mut v___y_1776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1778_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___redArg(v_upperBound_1763_, v_a_1764_, v___x_1765_, v_a_1768_, v_b_1769_);
    return v___x_1778_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2___boxed(
    mut v_upperBound_1779_: *mut crate::leanh::LeanObject,
    mut v_a_1780_: *mut crate::leanh::LeanObject,
    mut v___x_1781_: *mut crate::leanh::LeanObject,
    mut v_inst_1782_: *mut crate::leanh::LeanObject,
    mut v_R_1783_: *mut crate::leanh::LeanObject,
    mut v_a_1784_: *mut crate::leanh::LeanObject,
    mut v_b_1785_: *mut crate::leanh::LeanObject,
    mut v_c_1786_: *mut crate::leanh::LeanObject,
    mut v___y_1787_: *mut crate::leanh::LeanObject,
    mut v___y_1788_: *mut crate::leanh::LeanObject,
    mut v___y_1789_: *mut crate::leanh::LeanObject,
    mut v___y_1790_: *mut crate::leanh::LeanObject,
    mut v___y_1791_: *mut crate::leanh::LeanObject,
    mut v___y_1792_: *mut crate::leanh::LeanObject,
    mut v___y_1793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1794_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__2(v_upperBound_1779_, v_a_1780_, v___x_1781_, v_inst_1782_, v_R_1783_, v_a_1784_, v_b_1785_, v_c_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
    crate::leanh::lean_dec(v___y_1792_);
    crate::leanh::lean_dec_ref(v___y_1791_);
    crate::leanh::lean_dec(v___y_1790_);
    crate::leanh::lean_dec_ref(v___y_1789_);
    crate::leanh::lean_dec(v___y_1788_);
    crate::leanh::lean_dec_ref(v___y_1787_);
    crate::leanh::lean_dec(v_upperBound_1779_);
    return v_res_1794_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3(
    mut v_cls_1795_: *mut crate::leanh::LeanObject,
    mut v_msg_1796_: *mut crate::leanh::LeanObject,
    mut v___y_1797_: *mut crate::leanh::LeanObject,
    mut v___y_1798_: *mut crate::leanh::LeanObject,
    mut v___y_1799_: *mut crate::leanh::LeanObject,
    mut v___y_1800_: *mut crate::leanh::LeanObject,
    mut v___y_1801_: *mut crate::leanh::LeanObject,
    mut v___y_1802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1804_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___redArg(v_cls_1795_, v_msg_1796_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
    return v___x_1804_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3___boxed(
    mut v_cls_1805_: *mut crate::leanh::LeanObject,
    mut v_msg_1806_: *mut crate::leanh::LeanObject,
    mut v___y_1807_: *mut crate::leanh::LeanObject,
    mut v___y_1808_: *mut crate::leanh::LeanObject,
    mut v___y_1809_: *mut crate::leanh::LeanObject,
    mut v___y_1810_: *mut crate::leanh::LeanObject,
    mut v___y_1811_: *mut crate::leanh::LeanObject,
    mut v___y_1812_: *mut crate::leanh::LeanObject,
    mut v___y_1813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1814_ =
        l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__3(
            v_cls_1805_,
            v_msg_1806_,
            v___y_1807_,
            v___y_1808_,
            v___y_1809_,
            v___y_1810_,
            v___y_1811_,
            v___y_1812_,
        );
    crate::leanh::lean_dec(v___y_1812_);
    crate::leanh::lean_dec_ref(v___y_1811_);
    crate::leanh::lean_dec(v___y_1810_);
    crate::leanh::lean_dec_ref(v___y_1809_);
    crate::leanh::lean_dec(v___y_1808_);
    crate::leanh::lean_dec_ref(v___y_1807_);
    return v_res_1814_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0(
    mut v_00_u03b1_1815_: *mut crate::leanh::LeanObject,
    mut v_msg_1816_: *mut crate::leanh::LeanObject,
    mut v___y_1817_: *mut crate::leanh::LeanObject,
    mut v___y_1818_: *mut crate::leanh::LeanObject,
    mut v___y_1819_: *mut crate::leanh::LeanObject,
    mut v___y_1820_: *mut crate::leanh::LeanObject,
    mut v___y_1821_: *mut crate::leanh::LeanObject,
    mut v___y_1822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1824_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(v_msg_1816_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
    return v___x_1824_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0___boxed(
    mut v_00_u03b1_1825_: *mut crate::leanh::LeanObject,
    mut v_msg_1826_: *mut crate::leanh::LeanObject,
    mut v___y_1827_: *mut crate::leanh::LeanObject,
    mut v___y_1828_: *mut crate::leanh::LeanObject,
    mut v___y_1829_: *mut crate::leanh::LeanObject,
    mut v___y_1830_: *mut crate::leanh::LeanObject,
    mut v___y_1831_: *mut crate::leanh::LeanObject,
    mut v___y_1832_: *mut crate::leanh::LeanObject,
    mut v___y_1833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1834_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0(v_00_u03b1_1825_, v_msg_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
    crate::leanh::lean_dec(v___y_1832_);
    crate::leanh::lean_dec_ref(v___y_1831_);
    crate::leanh::lean_dec(v___y_1830_);
    crate::leanh::lean_dec_ref(v___y_1829_);
    crate::leanh::lean_dec(v___y_1828_);
    crate::leanh::lean_dec_ref(v___y_1827_);
    return v_res_1834_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1835_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1835_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1836_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__0);
    v___x_1837_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1837_, 0, v___x_1836_);
    return v___x_1837_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0(
    mut v_00_u03b2_1838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1839_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0___closed__1);
    return v___x_1839_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg___lam__0(
    mut v_x_1840_: *mut crate::leanh::LeanObject,
    mut v___y_1841_: *mut crate::leanh::LeanObject,
    mut v___y_1842_: *mut crate::leanh::LeanObject,
    mut v___y_1843_: *mut crate::leanh::LeanObject,
    mut v___y_1844_: *mut crate::leanh::LeanObject,
    mut v___y_1845_: *mut crate::leanh::LeanObject,
    mut v___y_1846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1842_);
    crate::leanh::lean_inc_ref(v___y_1841_);
    v___x_1848_ = crate::leanh::lean_apply_7(
        v_x_1840_,
        v___y_1841_,
        v___y_1842_,
        v___y_1843_,
        v___y_1844_,
        v___y_1845_,
        v___y_1846_,
        crate::leanh::lean_box(0),
    );
    return v___x_1848_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg___lam__0___boxed(
    mut v_x_1849_: *mut crate::leanh::LeanObject,
    mut v___y_1850_: *mut crate::leanh::LeanObject,
    mut v___y_1851_: *mut crate::leanh::LeanObject,
    mut v___y_1852_: *mut crate::leanh::LeanObject,
    mut v___y_1853_: *mut crate::leanh::LeanObject,
    mut v___y_1854_: *mut crate::leanh::LeanObject,
    mut v___y_1855_: *mut crate::leanh::LeanObject,
    mut v___y_1856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1857_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg___lam__0(v_x_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
    crate::leanh::lean_dec(v___y_1851_);
    crate::leanh::lean_dec_ref(v___y_1850_);
    return v_res_1857_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg(
    mut v_mvarId_1858_: *mut crate::leanh::LeanObject,
    mut v_x_1859_: *mut crate::leanh::LeanObject,
    mut v___y_1860_: *mut crate::leanh::LeanObject,
    mut v___y_1861_: *mut crate::leanh::LeanObject,
    mut v___y_1862_: *mut crate::leanh::LeanObject,
    mut v___y_1863_: *mut crate::leanh::LeanObject,
    mut v___y_1864_: *mut crate::leanh::LeanObject,
    mut v___y_1865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1872_: u8 = 0;
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1876_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_1861_);
                crate::leanh::lean_inc_ref(v___y_1860_);
                v___f_1867_ = crate::leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 3);
                crate::leanh::lean_closure_set(v___f_1867_, 0, v_x_1859_);
                crate::leanh::lean_closure_set(v___f_1867_, 1, v___y_1860_);
                crate::leanh::lean_closure_set(v___f_1867_, 2, v___y_1861_);
                v___x_1868_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_1858_,
                    v___f_1867_,
                    v___y_1862_,
                    v___y_1863_,
                    v___y_1864_,
                    v___y_1865_,
                );
                if crate::leanh::lean_obj_tag(v___x_1868_) == 0 {
                    return v___x_1868_;
                } else {
                    v_a_1869_ = crate::leanh::lean_ctor_get(v___x_1868_, 0);
                    v_isSharedCheck_1876_ = (!crate::leanh::lean_is_exclusive(v___x_1868_)) as u8;
                    if v_isSharedCheck_1876_ == 0 {
                        v___x_1871_ = v___x_1868_;
                        v_isShared_1872_ = v_isSharedCheck_1876_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1869_);
                        crate::leanh::lean_dec(v___x_1868_);
                        v___x_1871_ = crate::leanh::lean_box(0);
                        v_isShared_1872_ = v_isSharedCheck_1876_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1872_ == 0 {
                    v___x_1874_ = v___x_1871_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1875_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
                    v___x_1874_ = v_reuseFailAlloc_1875_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1874_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg___boxed(
    mut v_mvarId_1877_: *mut crate::leanh::LeanObject,
    mut v_x_1878_: *mut crate::leanh::LeanObject,
    mut v___y_1879_: *mut crate::leanh::LeanObject,
    mut v___y_1880_: *mut crate::leanh::LeanObject,
    mut v___y_1881_: *mut crate::leanh::LeanObject,
    mut v___y_1882_: *mut crate::leanh::LeanObject,
    mut v___y_1883_: *mut crate::leanh::LeanObject,
    mut v___y_1884_: *mut crate::leanh::LeanObject,
    mut v___y_1885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1886_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg(v_mvarId_1877_, v_x_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
    crate::leanh::lean_dec(v___y_1884_);
    crate::leanh::lean_dec_ref(v___y_1883_);
    crate::leanh::lean_dec(v___y_1882_);
    crate::leanh::lean_dec_ref(v___y_1881_);
    crate::leanh::lean_dec(v___y_1880_);
    crate::leanh::lean_dec_ref(v___y_1879_);
    return v_res_1886_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1(
    mut v_00_u03b1_1887_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1888_: *mut crate::leanh::LeanObject,
    mut v_x_1889_: *mut crate::leanh::LeanObject,
    mut v___y_1890_: *mut crate::leanh::LeanObject,
    mut v___y_1891_: *mut crate::leanh::LeanObject,
    mut v___y_1892_: *mut crate::leanh::LeanObject,
    mut v___y_1893_: *mut crate::leanh::LeanObject,
    mut v___y_1894_: *mut crate::leanh::LeanObject,
    mut v___y_1895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1897_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg(v_mvarId_1888_, v_x_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
    return v___x_1897_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___boxed(
    mut v_00_u03b1_1898_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1899_: *mut crate::leanh::LeanObject,
    mut v_x_1900_: *mut crate::leanh::LeanObject,
    mut v___y_1901_: *mut crate::leanh::LeanObject,
    mut v___y_1902_: *mut crate::leanh::LeanObject,
    mut v___y_1903_: *mut crate::leanh::LeanObject,
    mut v___y_1904_: *mut crate::leanh::LeanObject,
    mut v___y_1905_: *mut crate::leanh::LeanObject,
    mut v___y_1906_: *mut crate::leanh::LeanObject,
    mut v___y_1907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1908_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1(v_00_u03b1_1898_, v_mvarId_1899_, v_x_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
    crate::leanh::lean_dec(v___y_1906_);
    crate::leanh::lean_dec_ref(v___y_1905_);
    crate::leanh::lean_dec(v___y_1904_);
    crate::leanh::lean_dec_ref(v___y_1903_);
    crate::leanh::lean_dec(v___y_1902_);
    crate::leanh::lean_dec_ref(v___y_1901_);
    return v_res_1908_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1909_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1909_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1910_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__0_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__0);
    v___x_1911_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1911_, 0, v___x_1910_);
    return v___x_1911_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1912_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1913_ = lean_mk_empty_array_with_capacity(v___x_1912_);
    v___x_1914_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1914_, 0, v___x_1913_);
    return v___x_1914_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0(
    mut v_simprocs_1915_: *mut crate::leanh::LeanObject,
    mut v_relevantLemmas_1916_: *mut crate::leanh::LeanObject,
    mut v___x_1917_: *mut crate::leanh::LeanObject,
    mut v_goal_1918_: *mut crate::leanh::LeanObject,
    mut v___y_1919_: *mut crate::leanh::LeanObject,
    mut v___y_1920_: *mut crate::leanh::LeanObject,
    mut v___y_1921_: *mut crate::leanh::LeanObject,
    mut v___y_1922_: *mut crate::leanh::LeanObject,
    mut v___y_1923_: *mut crate::leanh::LeanObject,
    mut v___y_1924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1932_: u8 = 0;
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxSteps_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: u8 = 0;
    let mut v___x_1940_: u8 = 0;
    let mut v___x_1941_: u8 = 0;
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: usize = 0;
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1966_: u8 = 0;
    let mut v_fst_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1971_: u8 = 0;
    let mut v_snd_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1979_: u8 = 0;
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1983_: u8 = 0;
    let mut v_a_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1987_: u8 = 0;
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1991_: u8 = 0;
    let mut v_reuseFailAlloc_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1996_: u8 = 0;
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2000_: u8 = 0;
    let mut v_a_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2004_: u8 = 0;
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2008_: u8 = 0;
    let mut v_a_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2012_: u8 = 0;
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2016_: u8 = 0;
    let mut v_a_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2020_: u8 = 0;
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2024_: u8 = 0;
    let mut v_isSharedCheck_2025_: u8 = 0;
    let mut v_a_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2029_: u8 = 0;
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2033_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1926_ = l_Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas(
                    v_simprocs_1915_,
                    v_relevantLemmas_1916_,
                    v___y_1919_,
                    v___y_1920_,
                    v___y_1921_,
                    v___y_1922_,
                    v___y_1923_,
                    v___y_1924_,
                );
                if crate::leanh::lean_obj_tag(v___x_1926_) == 0 {
                    v_a_1927_ = crate::leanh::lean_ctor_get(v___x_1926_, 0);
                    crate::leanh::lean_inc(v_a_1927_);
                    crate::leanh::lean_dec_ref_known(v___x_1926_, 1);
                    v_fst_1928_ = crate::leanh::lean_ctor_get(v_a_1927_, 0);
                    v_snd_1929_ = crate::leanh::lean_ctor_get(v_a_1927_, 1);
                    v_isSharedCheck_2025_ = (!crate::leanh::lean_is_exclusive(v_a_1927_)) as u8;
                    if v_isSharedCheck_2025_ == 0 {
                        v___x_1931_ = v_a_1927_;
                        v_isShared_1932_ = v_isSharedCheck_2025_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1929_);
                        crate::leanh::lean_inc(v_fst_1928_);
                        crate::leanh::lean_dec(v_a_1927_);
                        v___x_1931_ = crate::leanh::lean_box(0);
                        v_isShared_1932_ = v_isSharedCheck_2025_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_goal_1918_);
                    crate::leanh::lean_dec(v___x_1917_);
                    v_a_2026_ = crate::leanh::lean_ctor_get(v___x_1926_, 0);
                    v_isSharedCheck_2033_ = (!crate::leanh::lean_is_exclusive(v___x_1926_)) as u8;
                    if v_isSharedCheck_2033_ == 0 {
                        v___x_2028_ = v___x_1926_;
                        v_isShared_2029_ = v_isSharedCheck_2033_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2026_);
                        crate::leanh::lean_dec(v___x_1926_);
                        v___x_2028_ = crate::leanh::lean_box(0);
                        v_isShared_2029_ = v_isSharedCheck_2033_;
                        state = 18;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1933_ = l_Lean_Meta_Tactic_BVDecide_Normalize_addDefaultTypeAnalysisLemmas(
                    v_snd_1929_,
                    v___y_1919_,
                    v___y_1920_,
                    v___y_1921_,
                    v___y_1922_,
                    v___y_1923_,
                    v___y_1924_,
                );
                if crate::leanh::lean_obj_tag(v___x_1933_) == 0 {
                    v_a_1934_ = crate::leanh::lean_ctor_get(v___x_1933_, 0);
                    crate::leanh::lean_inc(v_a_1934_);
                    crate::leanh::lean_dec_ref_known(v___x_1933_, 1);
                    v___x_1935_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_1924_);
                    if crate::leanh::lean_obj_tag(v___x_1935_) == 0 {
                        v_a_1936_ = crate::leanh::lean_ctor_get(v___x_1935_, 0);
                        crate::leanh::lean_inc(v_a_1936_);
                        crate::leanh::lean_dec_ref_known(v___x_1935_, 1);
                        v_maxSteps_1937_ = crate::leanh::lean_ctor_get(v___y_1919_, 1);
                        v___x_1938_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_1939_ = 0;
                        v___x_1940_ = 1;
                        v___x_1941_ = 0;
                        v___x_1942_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc(v_maxSteps_1937_);
                        v___x_1943_ = crate::leanh::lean_alloc_ctor(0, 3, (29) as u32);
                        crate::leanh::lean_ctor_set(v___x_1943_, 0, v_maxSteps_1937_);
                        crate::leanh::lean_ctor_set(v___x_1943_, 1, v___x_1938_);
                        crate::leanh::lean_ctor_set(v___x_1943_, 2, v___x_1942_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1943_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                            v___x_1939_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1943_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                            v___x_1940_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1943_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 2) as u32,
                            v___x_1939_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1943_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 3) as u32,
                            v___x_1940_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1943_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 4) as u32,
                            v___x_1940_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1943_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 5) as u32,
                            v___x_1940_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1943_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 6) as u32,
                            v___x_1941_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1943_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 7) as u32,
                            v___x_1940_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1943_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                            v___x_1940_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1943_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 9) as u32,
                            v___x_1939_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1943_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 10) as u32,
                            v___x_1939_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1943_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 11) as u32,
                            v___x_1939_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1943_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 12) as u32,
                            v___x_1940_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1943_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 13) as u32,
                            v___x_1939_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1943_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 14) as u32,
                            v___x_1939_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1943_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 15) as u32,
                            v___x_1939_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1943_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                            v___x_1939_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1943_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 17) as u32,
                            v___x_1940_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1943_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 18) as u32,
                            v___x_1939_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1943_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 19) as u32,
                            v___x_1940_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1943_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 20) as u32,
                            v___x_1940_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1943_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 21) as u32,
                            v___x_1940_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1943_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 22) as u32,
                            v___x_1940_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1943_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 23) as u32,
                            v___x_1940_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1943_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 24) as u32,
                            v___x_1940_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1943_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 25) as u32,
                            v___x_1940_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1943_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 26) as u32,
                            v___x_1939_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1943_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 27) as u32,
                            v___x_1939_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1943_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 28) as u32,
                            v___x_1939_,
                        );
                        v___x_1944_ = l_Lean_Options_empty;
                        v___x_1945_ = l_Lean_Meta_Simp_mkContext___redArg(
                            v___x_1943_,
                            v_a_1934_,
                            v_a_1936_,
                            v___x_1944_,
                            v___y_1921_,
                            v___y_1923_,
                            v___y_1924_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1945_) == 0 {
                            v_a_1946_ = crate::leanh::lean_ctor_get(v___x_1945_, 0);
                            crate::leanh::lean_inc(v_a_1946_);
                            crate::leanh::lean_dec_ref_known(v___x_1945_, 1);
                            v___x_1947_ = l_Lean_Meta_getPropHyps(
                                v___y_1921_,
                                v___y_1922_,
                                v___y_1923_,
                                v___y_1924_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1947_) == 0 {
                                v_a_1948_ = crate::leanh::lean_ctor_get(v___x_1947_, 0);
                                crate::leanh::lean_inc(v_a_1948_);
                                crate::leanh::lean_dec_ref_known(v___x_1947_, 1);
                                v___x_1949_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_1950_ = lean_mk_empty_array_with_capacity(v___x_1949_);
                                v___x_1951_ = lean_array_push(v___x_1950_, v_fst_1928_);
                                v___x_1952_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__1_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__1);
                                crate::leanh::lean_inc(v___x_1917_);
                                if v_isShared_1932_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1931_, 1, v___x_1917_);
                                    crate::leanh::lean_ctor_set(v___x_1931_, 0, v___x_1952_);
                                    v___x_1954_ = v___x_1931_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1992_ =
                                        crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1992_,
                                        0,
                                        v___x_1952_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1992_,
                                        1,
                                        v___x_1917_,
                                    );
                                    v___x_1954_ = v_reuseFailAlloc_1992_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_1946_);
                                crate::leanh::lean_del_object(v___x_1931_);
                                crate::leanh::lean_dec(v_fst_1928_);
                                crate::leanh::lean_dec(v_goal_1918_);
                                crate::leanh::lean_dec(v___x_1917_);
                                v_a_1993_ = crate::leanh::lean_ctor_get(v___x_1947_, 0);
                                v_isSharedCheck_2000_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1947_)) as u8;
                                if v_isSharedCheck_2000_ == 0 {
                                    v___x_1995_ = v___x_1947_;
                                    v_isShared_1996_ = v_isSharedCheck_2000_;
                                    state = 10;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1993_);
                                    crate::leanh::lean_dec(v___x_1947_);
                                    v___x_1995_ = crate::leanh::lean_box(0);
                                    v_isShared_1996_ = v_isSharedCheck_2000_;
                                    state = 10;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1931_);
                            crate::leanh::lean_dec(v_fst_1928_);
                            crate::leanh::lean_dec(v_goal_1918_);
                            crate::leanh::lean_dec(v___x_1917_);
                            v_a_2001_ = crate::leanh::lean_ctor_get(v___x_1945_, 0);
                            v_isSharedCheck_2008_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1945_)) as u8;
                            if v_isSharedCheck_2008_ == 0 {
                                v___x_2003_ = v___x_1945_;
                                v_isShared_2004_ = v_isSharedCheck_2008_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2001_);
                                crate::leanh::lean_dec(v___x_1945_);
                                v___x_2003_ = crate::leanh::lean_box(0);
                                v_isShared_2004_ = v_isSharedCheck_2008_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1934_);
                        crate::leanh::lean_del_object(v___x_1931_);
                        crate::leanh::lean_dec(v_fst_1928_);
                        crate::leanh::lean_dec(v_goal_1918_);
                        crate::leanh::lean_dec(v___x_1917_);
                        v_a_2009_ = crate::leanh::lean_ctor_get(v___x_1935_, 0);
                        v_isSharedCheck_2016_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1935_)) as u8;
                        if v_isSharedCheck_2016_ == 0 {
                            v___x_2011_ = v___x_1935_;
                            v_isShared_2012_ = v_isSharedCheck_2016_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2009_);
                            crate::leanh::lean_dec(v___x_1935_);
                            v___x_2011_ = crate::leanh::lean_box(0);
                            v_isShared_2012_ = v_isSharedCheck_2016_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1931_);
                    crate::leanh::lean_dec(v_fst_1928_);
                    crate::leanh::lean_dec(v_goal_1918_);
                    crate::leanh::lean_dec(v___x_1917_);
                    v_a_2017_ = crate::leanh::lean_ctor_get(v___x_1933_, 0);
                    v_isSharedCheck_2024_ = (!crate::leanh::lean_is_exclusive(v___x_1933_)) as u8;
                    if v_isSharedCheck_2024_ == 0 {
                        v___x_2019_ = v___x_1933_;
                        v_isShared_2020_ = v_isSharedCheck_2024_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2017_);
                        crate::leanh::lean_dec(v___x_1933_);
                        v___x_2019_ = crate::leanh::lean_box(0);
                        v_isShared_2020_ = v_isSharedCheck_2024_;
                        state = 16;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1955_ = crate::leanh::lean_unsigned_to_nat(32);
                v___x_1956_ = lean_mk_empty_array_with_capacity(v___x_1955_);
                v___x_1957_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__2_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___closed__2);
                v___x_1958_ = 5usize;
                crate::leanh::lean_inc(v___x_1917_);
                v___x_1959_ =
                    crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                crate::leanh::lean_ctor_set(v___x_1959_, 0, v___x_1957_);
                crate::leanh::lean_ctor_set(v___x_1959_, 1, v___x_1956_);
                crate::leanh::lean_ctor_set(v___x_1959_, 2, v___x_1917_);
                crate::leanh::lean_ctor_set(v___x_1959_, 3, v___x_1917_);
                crate::leanh::lean_ctor_set_usize(v___x_1959_, 4, v___x_1958_);
                v___x_1960_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1960_, 0, v___x_1952_);
                crate::leanh::lean_ctor_set(v___x_1960_, 1, v___x_1952_);
                crate::leanh::lean_ctor_set(v___x_1960_, 2, v___x_1952_);
                crate::leanh::lean_ctor_set(v___x_1960_, 3, v___x_1959_);
                v___x_1961_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1961_, 0, v___x_1954_);
                crate::leanh::lean_ctor_set(v___x_1961_, 1, v___x_1960_);
                v___x_1962_ = l_Lean_Meta_simpGoal(
                    v_goal_1918_,
                    v_a_1946_,
                    v___x_1951_,
                    v___x_1942_,
                    v___x_1940_,
                    v_a_1948_,
                    v___x_1961_,
                    v___y_1921_,
                    v___y_1922_,
                    v___y_1923_,
                    v___y_1924_,
                );
                if crate::leanh::lean_obj_tag(v___x_1962_) == 0 {
                    v_a_1963_ = crate::leanh::lean_ctor_get(v___x_1962_, 0);
                    v_isSharedCheck_1983_ = (!crate::leanh::lean_is_exclusive(v___x_1962_)) as u8;
                    if v_isSharedCheck_1983_ == 0 {
                        v___x_1965_ = v___x_1962_;
                        v_isShared_1966_ = v_isSharedCheck_1983_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1963_);
                        crate::leanh::lean_dec(v___x_1962_);
                        v___x_1965_ = crate::leanh::lean_box(0);
                        v_isShared_1966_ = v_isSharedCheck_1983_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_1984_ = crate::leanh::lean_ctor_get(v___x_1962_, 0);
                    v_isSharedCheck_1991_ = (!crate::leanh::lean_is_exclusive(v___x_1962_)) as u8;
                    if v_isSharedCheck_1991_ == 0 {
                        v___x_1986_ = v___x_1962_;
                        v_isShared_1987_ = v_isSharedCheck_1991_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1984_);
                        crate::leanh::lean_dec(v___x_1962_);
                        v___x_1986_ = crate::leanh::lean_box(0);
                        v_isShared_1987_ = v_isSharedCheck_1991_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_1967_ = crate::leanh::lean_ctor_get(v_a_1963_, 0);
                crate::leanh::lean_inc(v_fst_1967_);
                crate::leanh::lean_dec(v_a_1963_);
                if crate::leanh::lean_obj_tag(v_fst_1967_) == 1 {
                    v_val_1968_ = crate::leanh::lean_ctor_get(v_fst_1967_, 0);
                    v_isSharedCheck_1979_ = (!crate::leanh::lean_is_exclusive(v_fst_1967_)) as u8;
                    if v_isSharedCheck_1979_ == 0 {
                        v___x_1970_ = v_fst_1967_;
                        v_isShared_1971_ = v_isSharedCheck_1979_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1968_);
                        crate::leanh::lean_dec(v_fst_1967_);
                        v___x_1970_ = crate::leanh::lean_box(0);
                        v_isShared_1971_ = v_isSharedCheck_1979_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_1967_);
                    if v_isShared_1966_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1965_, 0, v___x_1942_);
                        v___x_1981_ = v___x_1965_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1982_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1942_);
                        v___x_1981_ = v_reuseFailAlloc_1982_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                v_snd_1972_ = crate::leanh::lean_ctor_get(v_val_1968_, 1);
                crate::leanh::lean_inc(v_snd_1972_);
                crate::leanh::lean_dec(v_val_1968_);
                if v_isShared_1971_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1970_, 0, v_snd_1972_);
                    v___x_1974_ = v___x_1970_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1978_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_snd_1972_);
                    v___x_1974_ = v_reuseFailAlloc_1978_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1966_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1965_, 0, v___x_1974_);
                    v___x_1976_ = v___x_1965_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1977_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1974_);
                    v___x_1976_ = v_reuseFailAlloc_1977_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1976_;
            }
            7 => {
                return v___x_1981_;
            }
            8 => {
                if v_isShared_1987_ == 0 {
                    v___x_1989_ = v___x_1986_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1990_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
                    v___x_1989_ = v_reuseFailAlloc_1990_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1989_;
            }
            10 => {
                if v_isShared_1996_ == 0 {
                    v___x_1998_ = v___x_1995_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1999_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
                    v___x_1998_ = v_reuseFailAlloc_1999_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1998_;
            }
            12 => {
                if v_isShared_2004_ == 0 {
                    v___x_2006_ = v___x_2003_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2007_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
                    v___x_2006_ = v_reuseFailAlloc_2007_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2006_;
            }
            14 => {
                if v_isShared_2012_ == 0 {
                    v___x_2014_ = v___x_2011_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2015_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2009_);
                    v___x_2014_ = v_reuseFailAlloc_2015_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2014_;
            }
            16 => {
                if v_isShared_2020_ == 0 {
                    v___x_2022_ = v___x_2019_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2023_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
                    v___x_2022_ = v_reuseFailAlloc_2023_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2022_;
            }
            18 => {
                if v_isShared_2029_ == 0 {
                    v___x_2031_ = v___x_2028_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2032_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
                    v___x_2031_ = v_reuseFailAlloc_2032_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2031_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___boxed(
    mut v_simprocs_2034_: *mut crate::leanh::LeanObject,
    mut v_relevantLemmas_2035_: *mut crate::leanh::LeanObject,
    mut v___x_2036_: *mut crate::leanh::LeanObject,
    mut v_goal_2037_: *mut crate::leanh::LeanObject,
    mut v___y_2038_: *mut crate::leanh::LeanObject,
    mut v___y_2039_: *mut crate::leanh::LeanObject,
    mut v___y_2040_: *mut crate::leanh::LeanObject,
    mut v___y_2041_: *mut crate::leanh::LeanObject,
    mut v___y_2042_: *mut crate::leanh::LeanObject,
    mut v___y_2043_: *mut crate::leanh::LeanObject,
    mut v___y_2044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2045_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0(v_simprocs_2034_, v_relevantLemmas_2035_, v___x_2036_, v_goal_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
    crate::leanh::lean_dec(v___y_2043_);
    crate::leanh::lean_dec_ref(v___y_2042_);
    crate::leanh::lean_dec(v___y_2041_);
    crate::leanh::lean_dec_ref(v___y_2040_);
    crate::leanh::lean_dec(v___y_2039_);
    crate::leanh::lean_dec_ref(v___y_2038_);
    return v_res_2045_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2046_ = l_Lean_Meta_DiscrTree_empty(crate::leanh::lean_box(0));
    return v___x_2046_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2047_ = l_Lean_PersistentHashMap_empty___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__0(crate::leanh::lean_box(0));
    return v___x_2047_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simprocs_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2048_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__1_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__1);
    v___x_2049_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__0_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__0);
    v_simprocs_2050_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v_simprocs_2050_, 0, v___x_2049_);
    crate::leanh::lean_ctor_set(v_simprocs_2050_, 1, v___x_2049_);
    crate::leanh::lean_ctor_set(v_simprocs_2050_, 2, v___x_2048_);
    crate::leanh::lean_ctor_set(v_simprocs_2050_, 3, v___x_2048_);
    return v_simprocs_2050_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess(
    mut v_goal_2053_: *mut crate::leanh::LeanObject,
    mut v_a_2054_: *mut crate::leanh::LeanObject,
    mut v_a_2055_: *mut crate::leanh::LeanObject,
    mut v_a_2056_: *mut crate::leanh::LeanObject,
    mut v_a_2057_: *mut crate::leanh::LeanObject,
    mut v_a_2058_: *mut crate::leanh::LeanObject,
    mut v_a_2059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_simprocs_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relevantLemmas_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_simprocs_2061_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__2_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__2);
    v___x_2062_ = crate::leanh::lean_unsigned_to_nat(0);
    v_relevantLemmas_2063_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___closed__3;
    crate::leanh::lean_inc(v_goal_2053_);
    v___f_2064_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___lam__0___boxed as *mut core::ffi::c_void, 11, 4);
    crate::leanh::lean_closure_set(v___f_2064_, 0, v_simprocs_2061_);
    crate::leanh::lean_closure_set(v___f_2064_, 1, v_relevantLemmas_2063_);
    crate::leanh::lean_closure_set(v___f_2064_, 2, v___x_2062_);
    crate::leanh::lean_closure_set(v___f_2064_, 3, v_goal_2053_);
    v___x_2065_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess_spec__1___redArg(v_goal_2053_, v___f_2064_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_);
    return v___x_2065_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess___boxed(
    mut v_goal_2066_: *mut crate::leanh::LeanObject,
    mut v_a_2067_: *mut crate::leanh::LeanObject,
    mut v_a_2068_: *mut crate::leanh::LeanObject,
    mut v_a_2069_: *mut crate::leanh::LeanObject,
    mut v_a_2070_: *mut crate::leanh::LeanObject,
    mut v_a_2071_: *mut crate::leanh::LeanObject,
    mut v_a_2072_: *mut crate::leanh::LeanObject,
    mut v_a_2073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2074_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess(v_goal_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
    crate::leanh::lean_dec(v_a_2072_);
    crate::leanh::lean_dec_ref(v_a_2071_);
    crate::leanh::lean_dec(v_a_2070_);
    crate::leanh::lean_dec_ref(v_a_2069_);
    crate::leanh::lean_dec(v_a_2068_);
    crate::leanh::lean_dec_ref(v_a_2067_);
    return v_res_2074_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0___redArg(
    mut v_e_2075_: *mut crate::leanh::LeanObject,
    mut v___y_2076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2078_: u8 = 0;
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2092_: u8 = 0;
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2098_: u8 = 0;
    let mut v_unused_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2078_ = l_Lean_Expr_hasMVar(v_e_2075_);
                if v___x_2078_ == 0 {
                    v___x_2079_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2079_, 0, v_e_2075_);
                    return v___x_2079_;
                } else {
                    v___x_2080_ = lean_st_ref_get(v___y_2076_);
                    v_mctx_2081_ = crate::leanh::lean_ctor_get(v___x_2080_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_2081_);
                    crate::leanh::lean_dec(v___x_2080_);
                    v___x_2082_ = l_Lean_instantiateMVarsCore(v_mctx_2081_, v_e_2075_);
                    v_fst_2083_ = crate::leanh::lean_ctor_get(v___x_2082_, 0);
                    crate::leanh::lean_inc(v_fst_2083_);
                    v_snd_2084_ = crate::leanh::lean_ctor_get(v___x_2082_, 1);
                    crate::leanh::lean_inc(v_snd_2084_);
                    crate::leanh::lean_dec_ref(v___x_2082_);
                    v___x_2085_ = lean_st_ref_take(v___y_2076_);
                    v_cache_2086_ = crate::leanh::lean_ctor_get(v___x_2085_, 1);
                    v_zetaDeltaFVarIds_2087_ = crate::leanh::lean_ctor_get(v___x_2085_, 2);
                    v_postponed_2088_ = crate::leanh::lean_ctor_get(v___x_2085_, 3);
                    v_diag_2089_ = crate::leanh::lean_ctor_get(v___x_2085_, 4);
                    v_isSharedCheck_2098_ = (!crate::leanh::lean_is_exclusive(v___x_2085_)) as u8;
                    if v_isSharedCheck_2098_ == 0 {
                        v_unused_2099_ = crate::leanh::lean_ctor_get(v___x_2085_, 0);
                        crate::leanh::lean_dec(v_unused_2099_);
                        v___x_2091_ = v___x_2085_;
                        v_isShared_2092_ = v_isSharedCheck_2098_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_2089_);
                        crate::leanh::lean_inc(v_postponed_2088_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_2087_);
                        crate::leanh::lean_inc(v_cache_2086_);
                        crate::leanh::lean_dec(v___x_2085_);
                        v___x_2091_ = crate::leanh::lean_box(0);
                        v_isShared_2092_ = v_isSharedCheck_2098_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2092_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2091_, 0, v_snd_2084_);
                    v___x_2094_ = v___x_2091_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2097_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_snd_2084_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_cache_2086_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2097_,
                        2,
                        v_zetaDeltaFVarIds_2087_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2097_, 3, v_postponed_2088_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2097_, 4, v_diag_2089_);
                    v___x_2094_ = v_reuseFailAlloc_2097_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2095_ = lean_st_ref_set(v___y_2076_, v___x_2094_);
                v___x_2096_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2096_, 0, v_fst_2083_);
                return v___x_2096_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0___redArg___boxed(
    mut v_e_2100_: *mut crate::leanh::LeanObject,
    mut v___y_2101_: *mut crate::leanh::LeanObject,
    mut v___y_2102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2103_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0___redArg(v_e_2100_, v___y_2101_);
    crate::leanh::lean_dec(v___y_2101_);
    return v_res_2103_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0(
    mut v_e_2104_: *mut crate::leanh::LeanObject,
    mut v___y_2105_: *mut crate::leanh::LeanObject,
    mut v___y_2106_: *mut crate::leanh::LeanObject,
    mut v___y_2107_: *mut crate::leanh::LeanObject,
    mut v___y_2108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2110_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0___redArg(v_e_2104_, v___y_2106_);
    return v___x_2110_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0___boxed(
    mut v_e_2111_: *mut crate::leanh::LeanObject,
    mut v___y_2112_: *mut crate::leanh::LeanObject,
    mut v___y_2113_: *mut crate::leanh::LeanObject,
    mut v___y_2114_: *mut crate::leanh::LeanObject,
    mut v___y_2115_: *mut crate::leanh::LeanObject,
    mut v___y_2116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2117_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0(
            v_e_2111_,
            v___y_2112_,
            v___y_2113_,
            v___y_2114_,
            v___y_2115_,
        );
    crate::leanh::lean_dec(v___y_2115_);
    crate::leanh::lean_dec_ref(v___y_2114_);
    crate::leanh::lean_dec(v___y_2113_);
    crate::leanh::lean_dec_ref(v___y_2112_);
    return v_res_2117_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__1___redArg(
    mut v_a_2118_: *mut crate::leanh::LeanObject,
    mut v_x_2119_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2120_: u8 = 0;
    let mut v_key_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2119_) == 0 {
                    v___x_2120_ = 0;
                    return v___x_2120_;
                } else {
                    v_key_2121_ = crate::leanh::lean_ctor_get(v_x_2119_, 0);
                    v_tail_2122_ = crate::leanh::lean_ctor_get(v_x_2119_, 2);
                    v___x_2123_ = lean_name_eq(v_key_2121_, v_a_2118_);
                    if v___x_2123_ == 0 {
                        v_x_2119_ = v_tail_2122_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2123_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__1___redArg___boxed(
    mut v_a_2125_: *mut crate::leanh::LeanObject,
    mut v_x_2126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2127_: u8 = 0;
    let mut v_r_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2127_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__1___redArg(v_a_2125_, v_x_2126_);
    crate::leanh::lean_dec(v_x_2126_);
    crate::leanh::lean_dec(v_a_2125_);
    v_r_2128_ = crate::leanh::lean_box((v_res_2127_) as usize);
    return v_r_2128_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1___redArg___closed__0()
-> u64 {
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: u64 = 0;
    v___x_2129_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_2130_ = lean_uint64_of_nat(v___x_2129_);
    return v___x_2130_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1___redArg(
    mut v_m_2131_: *mut crate::leanh::LeanObject,
    mut v_a_2132_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2136_: u64 = 0;
    let mut v___x_2137_: u64 = 0;
    let mut v___x_2138_: u64 = 0;
    let mut v_fold_2139_: u64 = 0;
    let mut v___x_2140_: u64 = 0;
    let mut v___x_2141_: u64 = 0;
    let mut v___x_2142_: u64 = 0;
    let mut v___x_2143_: usize = 0;
    let mut v___x_2144_: usize = 0;
    let mut v___x_2145_: usize = 0;
    let mut v___x_2146_: usize = 0;
    let mut v___x_2147_: usize = 0;
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: u8 = 0;
    let mut v___x_2150_: u64 = 0;
    let mut v_hash_2151_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2133_ = crate::leanh::lean_ctor_get(v_m_2131_, 1);
                v___x_2134_ = lean_array_get_size(v_buckets_2133_);
                if crate::leanh::lean_obj_tag(v_a_2132_) == 0 {
                    v___x_2150_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1___redArg___closed__0);
                    v___y_2136_ = v___x_2150_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2151_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_2132_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2136_ = v_hash_2151_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2137_ = 32u64;
                v___x_2138_ = lean_uint64_shift_right(v___y_2136_, v___x_2137_);
                v_fold_2139_ = lean_uint64_xor(v___y_2136_, v___x_2138_);
                v___x_2140_ = 16u64;
                v___x_2141_ = lean_uint64_shift_right(v_fold_2139_, v___x_2140_);
                v___x_2142_ = lean_uint64_xor(v_fold_2139_, v___x_2141_);
                v___x_2143_ = lean_uint64_to_usize(v___x_2142_);
                v___x_2144_ = lean_usize_of_nat(v___x_2134_);
                v___x_2145_ = 1usize;
                v___x_2146_ = lean_usize_sub(v___x_2144_, v___x_2145_);
                v___x_2147_ = lean_usize_land(v___x_2143_, v___x_2146_);
                v___x_2148_ = lean_array_uget_borrowed(v_buckets_2133_, v___x_2147_);
                v___x_2149_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__1___redArg(v_a_2132_, v___x_2148_);
                return v___x_2149_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1___redArg___boxed(
    mut v_m_2152_: *mut crate::leanh::LeanObject,
    mut v_a_2153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2154_: u8 = 0;
    let mut v_r_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2154_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1___redArg(v_m_2152_, v_a_2153_);
    crate::leanh::lean_dec(v_a_2153_);
    crate::leanh::lean_dec_ref(v_m_2152_);
    v_r_2155_ = crate::leanh::lean_box((v_res_2154_) as usize);
    return v_r_2155_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__0(
    mut v___x_2156_: u8,
    mut v_interestingStructures_2157_: *mut crate::leanh::LeanObject,
    mut v_decl_2158_: *mut crate::leanh::LeanObject,
    mut v___y_2159_: *mut crate::leanh::LeanObject,
    mut v___y_2160_: *mut crate::leanh::LeanObject,
    mut v___y_2161_: *mut crate::leanh::LeanObject,
    mut v___y_2162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2164_: u8 = 0;
    let mut v___x_2165_: u8 = 0;
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2171_: u8 = 0;
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: u8 = 0;
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2184_: u8 = 0;
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2164_ = l_Lean_LocalDecl_isLet(v_decl_2158_, v___x_2156_);
                if v___x_2164_ == 0 {
                    v___x_2165_ = l_Lean_LocalDecl_isImplementationDetail(v_decl_2158_);
                    if v___x_2165_ == 0 {
                        v___x_2166_ = l_Lean_LocalDecl_type(v_decl_2158_);
                        v___x_2167_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__0___redArg(v___x_2166_, v___y_2160_);
                        v_a_2168_ = crate::leanh::lean_ctor_get(v___x_2167_, 0);
                        v_isSharedCheck_2184_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2167_)) as u8;
                        if v_isSharedCheck_2184_ == 0 {
                            v___x_2170_ = v___x_2167_;
                            v_isShared_2171_ = v_isSharedCheck_2184_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2168_);
                            crate::leanh::lean_dec(v___x_2167_);
                            v___x_2170_ = crate::leanh::lean_box(0);
                            v_isShared_2171_ = v_isSharedCheck_2184_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_2185_ = crate::leanh::lean_box((v___x_2156_) as usize);
                        v___x_2186_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2186_, 0, v___x_2185_);
                        return v___x_2186_;
                    }
                } else {
                    v___x_2187_ = crate::leanh::lean_box((v___x_2156_) as usize);
                    v___x_2188_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2188_, 0, v___x_2187_);
                    return v___x_2188_;
                }
            }
            1 => {
                v___x_2172_ = l_Lean_Expr_getAppFn(v_a_2168_);
                crate::leanh::lean_dec(v_a_2168_);
                v___x_2173_ = l_Lean_Expr_constName_x3f(v___x_2172_);
                crate::leanh::lean_dec_ref(v___x_2172_);
                if crate::leanh::lean_obj_tag(v___x_2173_) == 1 {
                    v_val_2174_ = crate::leanh::lean_ctor_get(v___x_2173_, 0);
                    crate::leanh::lean_inc(v_val_2174_);
                    crate::leanh::lean_dec_ref_known(v___x_2173_, 1);
                    v___x_2175_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1___redArg(v_interestingStructures_2157_, v_val_2174_);
                    crate::leanh::lean_dec(v_val_2174_);
                    v___x_2176_ = crate::leanh::lean_box((v___x_2175_) as usize);
                    if v_isShared_2171_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2170_, 0, v___x_2176_);
                        v___x_2178_ = v___x_2170_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2179_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2176_);
                        v___x_2178_ = v_reuseFailAlloc_2179_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2173_);
                    v___x_2180_ = crate::leanh::lean_box((v___x_2156_) as usize);
                    if v_isShared_2171_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2170_, 0, v___x_2180_);
                        v___x_2182_ = v___x_2170_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2183_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2183_, 0, v___x_2180_);
                        v___x_2182_ = v_reuseFailAlloc_2183_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2178_;
            }
            3 => {
                return v___x_2182_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__0___boxed(
    mut v___x_2189_: *mut crate::leanh::LeanObject,
    mut v_interestingStructures_2190_: *mut crate::leanh::LeanObject,
    mut v_decl_2191_: *mut crate::leanh::LeanObject,
    mut v___y_2192_: *mut crate::leanh::LeanObject,
    mut v___y_2193_: *mut crate::leanh::LeanObject,
    mut v___y_2194_: *mut crate::leanh::LeanObject,
    mut v___y_2195_: *mut crate::leanh::LeanObject,
    mut v___y_2196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3219__boxed_2197_: u8 = 0;
    let mut v_res_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3219__boxed_2197_ = (crate::leanh::lean_unbox(v___x_2189_) as u8);
    v_res_2198_ = l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__0(
        v___x_3219__boxed_2197_,
        v_interestingStructures_2190_,
        v_decl_2191_,
        v___y_2192_,
        v___y_2193_,
        v___y_2194_,
        v___y_2195_,
    );
    crate::leanh::lean_dec(v___y_2195_);
    crate::leanh::lean_dec_ref(v___y_2194_);
    crate::leanh::lean_dec(v___y_2193_);
    crate::leanh::lean_dec_ref(v___y_2192_);
    crate::leanh::lean_dec_ref(v_decl_2191_);
    crate::leanh::lean_dec_ref(v_interestingStructures_2190_);
    return v_res_2198_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2200_ = l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___closed__0;
    v___x_2201_ = l_Lean_stringToMessageData(v___x_2200_);
    return v___x_2201_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1(
    mut v_goal_2202_: *mut crate::leanh::LeanObject,
    mut v___y_2203_: *mut crate::leanh::LeanObject,
    mut v___y_2204_: *mut crate::leanh::LeanObject,
    mut v___y_2205_: *mut crate::leanh::LeanObject,
    mut v___y_2206_: *mut crate::leanh::LeanObject,
    mut v___y_2207_: *mut crate::leanh::LeanObject,
    mut v___y_2208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingStructures_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: u8 = 0;
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2233_: u8 = 0;
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2237_: u8 = 0;
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2210_ = lean_st_ref_get(v___y_2204_);
                v_typeAnalysis_2211_ = crate::leanh::lean_ctor_get(v___x_2210_, 2);
                crate::leanh::lean_inc_ref(v_typeAnalysis_2211_);
                crate::leanh::lean_dec(v___x_2210_);
                v_interestingStructures_2212_ =
                    crate::leanh::lean_ctor_get(v_typeAnalysis_2211_, 0);
                crate::leanh::lean_inc_ref(v_interestingStructures_2212_);
                crate::leanh::lean_dec_ref(v_typeAnalysis_2211_);
                v_size_2213_ = crate::leanh::lean_ctor_get(v_interestingStructures_2212_, 0);
                v___x_2214_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2215_ = lean_nat_dec_eq(v_size_2213_, v___x_2214_);
                if v___x_2215_ == 0 {
                    v___x_2216_ = crate::leanh::lean_box((v___x_2215_) as usize);
                    v___f_2217_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__0___boxed
                            as *mut core::ffi::c_void,
                        8,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_2217_, 0, v___x_2216_);
                    crate::leanh::lean_closure_set(v___f_2217_, 1, v_interestingStructures_2212_);
                    v___x_2218_ = l_Lean_MVarId_casesRec(
                        v_goal_2202_,
                        v___f_2217_,
                        v___y_2205_,
                        v___y_2206_,
                        v___y_2207_,
                        v___y_2208_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2218_) == 0 {
                        v_a_2219_ = crate::leanh::lean_ctor_get(v___x_2218_, 0);
                        crate::leanh::lean_inc(v_a_2219_);
                        crate::leanh::lean_dec_ref_known(v___x_2218_, 1);
                        if crate::leanh::lean_obj_tag(v_a_2219_) == 1 {
                            v_tail_2227_ = crate::leanh::lean_ctor_get(v_a_2219_, 1);
                            if crate::leanh::lean_obj_tag(v_tail_2227_) == 0 {
                                v_head_2228_ = crate::leanh::lean_ctor_get(v_a_2219_, 0);
                                crate::leanh::lean_inc(v_head_2228_);
                                crate::leanh::lean_dec_ref_known(v_a_2219_, 2);
                                v___x_2229_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Structures_0__Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_postprocess(v_head_2228_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
                                return v___x_2229_;
                            } else {
                                crate::leanh::lean_dec_ref_known(v_a_2219_, 2);
                                v___y_2221_ = v___y_2205_;
                                v___y_2222_ = v___y_2206_;
                                v___y_2223_ = v___y_2207_;
                                v___y_2224_ = v___y_2208_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2219_);
                            v___y_2221_ = v___y_2205_;
                            v___y_2222_ = v___y_2206_;
                            v___y_2223_ = v___y_2207_;
                            v___y_2224_ = v___y_2208_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2230_ = crate::leanh::lean_ctor_get(v___x_2218_, 0);
                        v_isSharedCheck_2237_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2218_)) as u8;
                        if v_isSharedCheck_2237_ == 0 {
                            v___x_2232_ = v___x_2218_;
                            v_isShared_2233_ = v_isSharedCheck_2237_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2230_);
                            crate::leanh::lean_dec(v___x_2218_);
                            v___x_2232_ = crate::leanh::lean_box(0);
                            v_isShared_2233_ = v_isSharedCheck_2237_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_interestingStructures_2212_);
                    v___x_2238_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2238_, 0, v_goal_2202_);
                    v___x_2239_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2239_, 0, v___x_2238_);
                    return v___x_2239_;
                }
            }
            1 => {
                v___x_2225_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___closed__1_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___closed__1);
                v___x_2226_ = l_Lean_throwError___at___00Lean_getConstInfoInduct___at___00Lean_Meta_Tactic_BVDecide_Normalize_addStructureSimpLemmas_spec__0_spec__0___redArg(v___x_2225_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
                return v___x_2226_;
            }
            2 => {
                if v_isShared_2233_ == 0 {
                    v___x_2235_ = v___x_2232_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2236_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
                    v___x_2235_ = v_reuseFailAlloc_2236_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2235_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1___boxed(
    mut v_goal_2240_: *mut crate::leanh::LeanObject,
    mut v___y_2241_: *mut crate::leanh::LeanObject,
    mut v___y_2242_: *mut crate::leanh::LeanObject,
    mut v___y_2243_: *mut crate::leanh::LeanObject,
    mut v___y_2244_: *mut crate::leanh::LeanObject,
    mut v___y_2245_: *mut crate::leanh::LeanObject,
    mut v___y_2246_: *mut crate::leanh::LeanObject,
    mut v___y_2247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2248_ = l_Lean_Meta_Tactic_BVDecide_Normalize_structuresPass___lam__1(
        v_goal_2240_,
        v___y_2241_,
        v___y_2242_,
        v___y_2243_,
        v___y_2244_,
        v___y_2245_,
        v___y_2246_,
    );
    crate::leanh::lean_dec(v___y_2246_);
    crate::leanh::lean_dec_ref(v___y_2245_);
    crate::leanh::lean_dec(v___y_2244_);
    crate::leanh::lean_dec_ref(v___y_2243_);
    crate::leanh::lean_dec(v___y_2242_);
    crate::leanh::lean_dec_ref(v___y_2241_);
    return v_res_2248_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1(
    mut v_00_u03b2_2257_: *mut crate::leanh::LeanObject,
    mut v_m_2258_: *mut crate::leanh::LeanObject,
    mut v_a_2259_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2260_: u8 = 0;
    v___x_2260_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1___redArg(v_m_2258_, v_a_2259_);
    return v___x_2260_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1___boxed(
    mut v_00_u03b2_2261_: *mut crate::leanh::LeanObject,
    mut v_m_2262_: *mut crate::leanh::LeanObject,
    mut v_a_2263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2264_: u8 = 0;
    let mut v_r_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2264_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1(v_00_u03b2_2261_, v_m_2262_, v_a_2263_);
    crate::leanh::lean_dec(v_a_2263_);
    crate::leanh::lean_dec_ref(v_m_2262_);
    v_r_2265_ = crate::leanh::lean_box((v_res_2264_) as usize);
    return v_r_2265_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__1(
    mut v_00_u03b2_2266_: *mut crate::leanh::LeanObject,
    mut v_a_2267_: *mut crate::leanh::LeanObject,
    mut v_x_2268_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2269_: u8 = 0;
    v___x_2269_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__1___redArg(v_a_2267_, v_x_2268_);
    return v___x_2269_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__1___boxed(
    mut v_00_u03b2_2270_: *mut crate::leanh::LeanObject,
    mut v_a_2271_: *mut crate::leanh::LeanObject,
    mut v_x_2272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2273_: u8 = 0;
    let mut v_r_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2273_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_Normalize_structuresPass_spec__1_spec__1(v_00_u03b2_2270_, v_a_2271_, v_x_2272_);
    crate::leanh::lean_dec(v_x_2272_);
    crate::leanh::lean_dec(v_a_2271_);
    v_r_2274_ = crate::leanh::lean_box((v_res_2273_) as usize);
    return v_r_2274_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_TypeAnalysis(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Injective(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(
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
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_TypeAnalysis(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_ApplyControlFlow(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Injective(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Cases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_Normalize_Structures(builtin);
}
