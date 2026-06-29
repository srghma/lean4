// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.Basic
// Imports: Lean.Meta.Tactic.BVDecide.Attr Std.Tactic.BVDecide.Syntax
use crate::r#gen::Init::Control::Basic::l_instMonadControlTOfPure___redArg;
use crate::r#gen::Init::Control::StateRef::{
    l_StateRefT_x27_instMonad___redArg, l_StateRefT_x27_instMonadFunctor___aux__1___boxed,
    l_StateRefT_x27_lift___boxed,
};
use crate::r#gen::Init::Data::Nat::Power2::Basic::l_Nat_nextPowerOfTwo;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed,
    l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg, l_Lean_replaceRef,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonad___redArg, l_ReaderT_instMonadFunctor___lam__0,
    l_ReaderT_instMonadLift___lam__0___boxed, l_ReaderT_pure___boxed,
};
use crate::r#gen::Init::System::IO::{l_instMonadEIO, l_instMonadExceptOfEIO};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_checkSystem, l_Lean_Core_instMonadCoreM___lam__0___boxed,
    l_Lean_Core_instMonadCoreM___lam__1___boxed, l_Lean_Core_instMonadQuotationCoreM,
    l_Lean_Core_instMonadTraceCoreM,
};
use crate::r#gen::Lean::Data::KVMap::l_Lean_KVMap_instValueBool;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::l_Lean_Option_get___redArg;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_append___redArg, l_Lean_PersistentArray_push___redArg,
    l_Lean_PersistentArray_toArray___redArg,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_instBEqFVarId_beq___boxed, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableFVarId_hash___boxed,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofName, l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_MVarId_withContext___redArg, l_Lean_Meta_instAddMessageContextMetaM,
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Attr::{
    initialize_Lean_Meta_Tactic_BVDecide_Attr, runtime_initialize_Lean_Meta_Tactic_BVDecide_Attr,
};
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_Meta_getPropHyps___boxed;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go,
    l___private_Lean_Util_Trace_0__Lean_getResetTraces,
    l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback, l_Lean_TraceResult_toEmoji,
    l_Lean_instExceptToTraceResultOption___lam__0___boxed,
    l_Lean_instMonadAlwaysExceptReaderT___redArg,
    l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg, l_Lean_instMonadTraceOfMonadLift___redArg,
    l_Lean_trace_profiler, l_Lean_trace_profiler_threshold, l_Lean_trace_profiler_useHeartbeats,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_contains___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insert___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg,
};
use crate::r#gen::Std::Tactic::BVDecide::Syntax::{
    initialize_Std_Tactic_BVDecide_Syntax, runtime_initialize_Std_Tactic_BVDecide_Syntax,
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
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqFVarId_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableFVarId_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__4_value:
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
    m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__5_value:
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
    m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__6_value:
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
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        82, 117, 110, 110, 105, 110, 103, 32, 112, 97, 115, 115, 58, 32, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__2_value:
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
    m_data: [32, 111, 110, 10, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0_value:
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
    m_fun: l_ReaderT_instMonadLift___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateRefT_x27_lift___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6_value:
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
    m_fun: l_ReaderT_instMonadFunctor___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7_value:
    crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateRefT_x27_instMonadFunctor___aux__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__21_value:
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
    m_fun: l_Lean_instExceptToTraceResultOption___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__21:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__22_value:
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
    m_data: [77, 101, 116, 97, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__22:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__23_value:
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
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__23:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__24_value:
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
    m_data: [98, 118, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__24:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__24_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__22_value)
            as *mut crate::leanh::LeanObject,
        142734480563613395 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__23_value)
            as *mut crate::leanh::LeanObject,
        15847151208953044930 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__24_value)
            as *mut crate::leanh::LeanObject,
        10551690841954068875 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__26_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__26:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__27_value:
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
    m_data: [116, 114, 97, 99, 101, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__27:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__28_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__27_value)
            as *mut crate::leanh::LeanObject,
        14231257465488249300 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__28:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__28_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30: f64 = 0.0;
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__2: f64 = 0.0;
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__3_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [60, 101, 120, 99, 101, 112, 116, 105, 111, 110, 32, 116, 104, 114, 111, 119, 110, 32, 119, 104, 105, 108, 101, 32, 112, 114, 111, 100, 117, 99, 105, 110, 103, 32, 116, 114, 97, 99, 101, 32, 110, 111, 100, 101, 32, 109, 101, 115, 115, 97, 103, 101, 62, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__5: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__1_value: crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [70, 105, 120, 112, 111, 105, 110, 116, 32, 105, 116, 101, 114, 97, 116, 105, 111, 110, 32, 115, 111, 108, 118, 101, 100, 32, 116, 104, 101, 32, 103, 111, 97, 108, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__0_value:
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
    m_data: [98, 118, 95, 100, 101, 99, 105, 100, 101, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__1_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        82, 101, 114, 117, 110, 110, 105, 110, 103, 32, 112, 105, 112, 101, 108, 105, 110, 101, 32,
        111, 110, 58, 10, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__3_value:
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
        80, 105, 112, 101, 108, 105, 110, 101, 32, 114, 101, 97, 99, 104, 101, 100, 32, 97, 32,
        102, 105, 120, 112, 111, 105, 110, 116, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx(
    mut v_x_2069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2069_) == 0 {
        let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2070_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_2070_;
    } else {
        let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2071_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_2071_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx___boxed(
    mut v_x_2072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2073_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx(v_x_2072_);
    crate::leanh::lean_dec_ref(v_x_2072_);
    return v_res_2073_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(
    mut v_t_2074_: *mut crate::leanh::LeanObject,
    mut v_k_2075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_info_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_info_2076_ = crate::leanh::lean_ctor_get(v_t_2074_, 0);
    crate::leanh::lean_inc_ref(v_info_2076_);
    v_ctors_2077_ = crate::leanh::lean_ctor_get(v_t_2074_, 1);
    crate::leanh::lean_inc_ref(v_ctors_2077_);
    crate::leanh::lean_dec_ref(v_t_2074_);
    v___x_2078_ = crate::leanh::lean_apply_2(v_k_2075_, v_info_2076_, v_ctors_2077_);
    return v___x_2078_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim(
    mut v_motive_2079_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2080_: *mut crate::leanh::LeanObject,
    mut v_t_2081_: *mut crate::leanh::LeanObject,
    mut v_h_2082_: *mut crate::leanh::LeanObject,
    mut v_k_2083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2084_ =
        l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_2081_, v_k_2083_);
    return v___x_2084_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___boxed(
    mut v_motive_2085_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2086_: *mut crate::leanh::LeanObject,
    mut v_t_2087_: *mut crate::leanh::LeanObject,
    mut v_h_2088_: *mut crate::leanh::LeanObject,
    mut v_k_2089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2090_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim(
        v_motive_2085_,
        v_ctorIdx_2086_,
        v_t_2087_,
        v_h_2088_,
        v_k_2089_,
    );
    crate::leanh::lean_dec(v_ctorIdx_2086_);
    return v_res_2090_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_simpleEnum_elim___redArg(
    mut v_t_2091_: *mut crate::leanh::LeanObject,
    mut v_simpleEnum_2092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2093_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(
        v_t_2091_,
        v_simpleEnum_2092_,
    );
    return v___x_2093_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_simpleEnum_elim(
    mut v_motive_2094_: *mut crate::leanh::LeanObject,
    mut v_t_2095_: *mut crate::leanh::LeanObject,
    mut v_h_2096_: *mut crate::leanh::LeanObject,
    mut v_simpleEnum_2097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2098_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(
        v_t_2095_,
        v_simpleEnum_2097_,
    );
    return v___x_2098_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_enumWithDefault_elim___redArg(
    mut v_t_2099_: *mut crate::leanh::LeanObject,
    mut v_enumWithDefault_2100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2101_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(
        v_t_2099_,
        v_enumWithDefault_2100_,
    );
    return v___x_2101_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_enumWithDefault_elim(
    mut v_motive_2102_: *mut crate::leanh::LeanObject,
    mut v_t_2103_: *mut crate::leanh::LeanObject,
    mut v_h_2104_: *mut crate::leanh::LeanObject,
    mut v_enumWithDefault_2105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2106_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(
        v_t_2103_,
        v_enumWithDefault_2105_,
    );
    return v___x_2106_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg(
    mut v_a_2107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_a_2107_);
    v___x_2109_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2109_, 0, v_a_2107_);
    return v___x_2109_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg___boxed(
    mut v_a_2110_: *mut crate::leanh::LeanObject,
    mut v_a_2111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2112_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg(v_a_2110_);
    crate::leanh::lean_dec_ref(v_a_2110_);
    return v_res_2112_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig(
    mut v_a_2113_: *mut crate::leanh::LeanObject,
    mut v_a_2114_: *mut crate::leanh::LeanObject,
    mut v_a_2115_: *mut crate::leanh::LeanObject,
    mut v_a_2116_: *mut crate::leanh::LeanObject,
    mut v_a_2117_: *mut crate::leanh::LeanObject,
    mut v_a_2118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_a_2113_);
    v___x_2120_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2120_, 0, v_a_2113_);
    return v___x_2120_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___boxed(
    mut v_a_2121_: *mut crate::leanh::LeanObject,
    mut v_a_2122_: *mut crate::leanh::LeanObject,
    mut v_a_2123_: *mut crate::leanh::LeanObject,
    mut v_a_2124_: *mut crate::leanh::LeanObject,
    mut v_a_2125_: *mut crate::leanh::LeanObject,
    mut v_a_2126_: *mut crate::leanh::LeanObject,
    mut v_a_2127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2128_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig(
        v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_,
    );
    crate::leanh::lean_dec(v_a_2126_);
    crate::leanh::lean_dec_ref(v_a_2125_);
    crate::leanh::lean_dec(v_a_2124_);
    crate::leanh::lean_dec_ref(v_a_2123_);
    crate::leanh::lean_dec(v_a_2122_);
    crate::leanh::lean_dec_ref(v_a_2121_);
    return v_res_2128_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg(
    mut v_fvar_2131_: *mut crate::leanh::LeanObject,
    mut v_a_2132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: u8 = 0;
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2134_ = lean_st_ref_get(v_a_2132_);
    v_rewriteCache_2135_ = crate::leanh::lean_ctor_get(v___x_2134_, 0);
    crate::leanh::lean_inc_ref(v_rewriteCache_2135_);
    crate::leanh::lean_dec(v___x_2134_);
    v___x_2136_ =
        l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__0;
    v___x_2137_ =
        l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__1;
    v___x_2138_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v___x_2136_,
        v___x_2137_,
        v_rewriteCache_2135_,
        v_fvar_2131_,
    );
    crate::leanh::lean_dec_ref(v_rewriteCache_2135_);
    v___x_2139_ = crate::leanh::lean_box((v___x_2138_) as usize);
    v___x_2140_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2140_, 0, v___x_2139_);
    return v___x_2140_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___boxed(
    mut v_fvar_2141_: *mut crate::leanh::LeanObject,
    mut v_a_2142_: *mut crate::leanh::LeanObject,
    mut v_a_2143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2144_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg(
        v_fvar_2141_,
        v_a_2142_,
    );
    crate::leanh::lean_dec(v_a_2142_);
    return v_res_2144_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten(
    mut v_fvar_2145_: *mut crate::leanh::LeanObject,
    mut v_a_2146_: *mut crate::leanh::LeanObject,
    mut v_a_2147_: *mut crate::leanh::LeanObject,
    mut v_a_2148_: *mut crate::leanh::LeanObject,
    mut v_a_2149_: *mut crate::leanh::LeanObject,
    mut v_a_2150_: *mut crate::leanh::LeanObject,
    mut v_a_2151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: u8 = 0;
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2153_ = lean_st_ref_get(v_a_2147_);
    v_rewriteCache_2154_ = crate::leanh::lean_ctor_get(v___x_2153_, 0);
    crate::leanh::lean_inc_ref(v_rewriteCache_2154_);
    crate::leanh::lean_dec(v___x_2153_);
    v___x_2155_ =
        l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__0;
    v___x_2156_ =
        l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__1;
    v___x_2157_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v___x_2155_,
        v___x_2156_,
        v_rewriteCache_2154_,
        v_fvar_2145_,
    );
    crate::leanh::lean_dec_ref(v_rewriteCache_2154_);
    v___x_2158_ = crate::leanh::lean_box((v___x_2157_) as usize);
    v___x_2159_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2159_, 0, v___x_2158_);
    return v___x_2159_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___boxed(
    mut v_fvar_2160_: *mut crate::leanh::LeanObject,
    mut v_a_2161_: *mut crate::leanh::LeanObject,
    mut v_a_2162_: *mut crate::leanh::LeanObject,
    mut v_a_2163_: *mut crate::leanh::LeanObject,
    mut v_a_2164_: *mut crate::leanh::LeanObject,
    mut v_a_2165_: *mut crate::leanh::LeanObject,
    mut v_a_2166_: *mut crate::leanh::LeanObject,
    mut v_a_2167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2168_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten(
        v_fvar_2160_,
        v_a_2161_,
        v_a_2162_,
        v_a_2163_,
        v_a_2164_,
        v_a_2165_,
        v_a_2166_,
    );
    crate::leanh::lean_dec(v_a_2166_);
    crate::leanh::lean_dec_ref(v_a_2165_);
    crate::leanh::lean_dec(v_a_2164_);
    crate::leanh::lean_dec_ref(v_a_2163_);
    crate::leanh::lean_dec(v_a_2162_);
    crate::leanh::lean_dec_ref(v_a_2161_);
    return v_res_2168_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkAcNf___redArg(
    mut v_fvar_2169_: *mut crate::leanh::LeanObject,
    mut v_a_2170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: u8 = 0;
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2172_ = lean_st_ref_get(v_a_2170_);
    v_acNfCache_2173_ = crate::leanh::lean_ctor_get(v___x_2172_, 1);
    crate::leanh::lean_inc_ref(v_acNfCache_2173_);
    crate::leanh::lean_dec(v___x_2172_);
    v___x_2174_ =
        l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__0;
    v___x_2175_ =
        l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__1;
    v___x_2176_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v___x_2174_,
        v___x_2175_,
        v_acNfCache_2173_,
        v_fvar_2169_,
    );
    crate::leanh::lean_dec_ref(v_acNfCache_2173_);
    v___x_2177_ = crate::leanh::lean_box((v___x_2176_) as usize);
    v___x_2178_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2178_, 0, v___x_2177_);
    return v___x_2178_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkAcNf___redArg___boxed(
    mut v_fvar_2179_: *mut crate::leanh::LeanObject,
    mut v_a_2180_: *mut crate::leanh::LeanObject,
    mut v_a_2181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2182_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkAcNf___redArg(
        v_fvar_2179_,
        v_a_2180_,
    );
    crate::leanh::lean_dec(v_a_2180_);
    return v_res_2182_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkAcNf(
    mut v_fvar_2183_: *mut crate::leanh::LeanObject,
    mut v_a_2184_: *mut crate::leanh::LeanObject,
    mut v_a_2185_: *mut crate::leanh::LeanObject,
    mut v_a_2186_: *mut crate::leanh::LeanObject,
    mut v_a_2187_: *mut crate::leanh::LeanObject,
    mut v_a_2188_: *mut crate::leanh::LeanObject,
    mut v_a_2189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: u8 = 0;
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2191_ = lean_st_ref_get(v_a_2185_);
    v_acNfCache_2192_ = crate::leanh::lean_ctor_get(v___x_2191_, 1);
    crate::leanh::lean_inc_ref(v_acNfCache_2192_);
    crate::leanh::lean_dec(v___x_2191_);
    v___x_2193_ =
        l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__0;
    v___x_2194_ =
        l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__1;
    v___x_2195_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v___x_2193_,
        v___x_2194_,
        v_acNfCache_2192_,
        v_fvar_2183_,
    );
    crate::leanh::lean_dec_ref(v_acNfCache_2192_);
    v___x_2196_ = crate::leanh::lean_box((v___x_2195_) as usize);
    v___x_2197_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2197_, 0, v___x_2196_);
    return v___x_2197_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkAcNf___boxed(
    mut v_fvar_2198_: *mut crate::leanh::LeanObject,
    mut v_a_2199_: *mut crate::leanh::LeanObject,
    mut v_a_2200_: *mut crate::leanh::LeanObject,
    mut v_a_2201_: *mut crate::leanh::LeanObject,
    mut v_a_2202_: *mut crate::leanh::LeanObject,
    mut v_a_2203_: *mut crate::leanh::LeanObject,
    mut v_a_2204_: *mut crate::leanh::LeanObject,
    mut v_a_2205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2206_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkAcNf(
        v_fvar_2198_,
        v_a_2199_,
        v_a_2200_,
        v_a_2201_,
        v_a_2202_,
        v_a_2203_,
        v_a_2204_,
    );
    crate::leanh::lean_dec(v_a_2204_);
    crate::leanh::lean_dec_ref(v_a_2203_);
    crate::leanh::lean_dec(v_a_2202_);
    crate::leanh::lean_dec_ref(v_a_2201_);
    crate::leanh::lean_dec(v_a_2200_);
    crate::leanh::lean_dec_ref(v_a_2199_);
    return v_res_2206_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_rewriteFinished___redArg(
    mut v_fvar_2207_: *mut crate::leanh::LeanObject,
    mut v_a_2208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2216_: u8 = 0;
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2226_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2210_ = lean_st_ref_take(v_a_2208_);
                v_rewriteCache_2211_ = crate::leanh::lean_ctor_get(v___x_2210_, 0);
                v_acNfCache_2212_ = crate::leanh::lean_ctor_get(v___x_2210_, 1);
                v_typeAnalysis_2213_ = crate::leanh::lean_ctor_get(v___x_2210_, 2);
                v_isSharedCheck_2226_ = (!crate::leanh::lean_is_exclusive(v___x_2210_)) as u8;
                if v_isSharedCheck_2226_ == 0 {
                    v___x_2215_ = v___x_2210_;
                    v_isShared_2216_ = v_isSharedCheck_2226_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_typeAnalysis_2213_);
                    crate::leanh::lean_inc(v_acNfCache_2212_);
                    crate::leanh::lean_inc(v_rewriteCache_2211_);
                    crate::leanh::lean_dec(v___x_2210_);
                    v___x_2215_ = crate::leanh::lean_box(0);
                    v_isShared_2216_ = v_isSharedCheck_2226_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2217_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__0;
                v___x_2218_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__1;
                v___x_2219_ = crate::leanh::lean_box(0);
                v___x_2220_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_2217_,
                    v___x_2218_,
                    v_rewriteCache_2211_,
                    v_fvar_2207_,
                    v___x_2219_,
                );
                if v_isShared_2216_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2215_, 0, v___x_2220_);
                    v___x_2222_ = v___x_2215_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2225_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2220_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2225_, 1, v_acNfCache_2212_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2225_, 2, v_typeAnalysis_2213_);
                    v___x_2222_ = v_reuseFailAlloc_2225_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2223_ = lean_st_ref_set(v_a_2208_, v___x_2222_);
                v___x_2224_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2224_, 0, v___x_2219_);
                return v___x_2224_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_rewriteFinished___redArg___boxed(
    mut v_fvar_2227_: *mut crate::leanh::LeanObject,
    mut v_a_2228_: *mut crate::leanh::LeanObject,
    mut v_a_2229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2230_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_rewriteFinished___redArg(
        v_fvar_2227_,
        v_a_2228_,
    );
    crate::leanh::lean_dec(v_a_2228_);
    return v_res_2230_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_rewriteFinished(
    mut v_fvar_2231_: *mut crate::leanh::LeanObject,
    mut v_a_2232_: *mut crate::leanh::LeanObject,
    mut v_a_2233_: *mut crate::leanh::LeanObject,
    mut v_a_2234_: *mut crate::leanh::LeanObject,
    mut v_a_2235_: *mut crate::leanh::LeanObject,
    mut v_a_2236_: *mut crate::leanh::LeanObject,
    mut v_a_2237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2245_: u8 = 0;
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2255_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2239_ = lean_st_ref_take(v_a_2233_);
                v_rewriteCache_2240_ = crate::leanh::lean_ctor_get(v___x_2239_, 0);
                v_acNfCache_2241_ = crate::leanh::lean_ctor_get(v___x_2239_, 1);
                v_typeAnalysis_2242_ = crate::leanh::lean_ctor_get(v___x_2239_, 2);
                v_isSharedCheck_2255_ = (!crate::leanh::lean_is_exclusive(v___x_2239_)) as u8;
                if v_isSharedCheck_2255_ == 0 {
                    v___x_2244_ = v___x_2239_;
                    v_isShared_2245_ = v_isSharedCheck_2255_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_typeAnalysis_2242_);
                    crate::leanh::lean_inc(v_acNfCache_2241_);
                    crate::leanh::lean_inc(v_rewriteCache_2240_);
                    crate::leanh::lean_dec(v___x_2239_);
                    v___x_2244_ = crate::leanh::lean_box(0);
                    v_isShared_2245_ = v_isSharedCheck_2255_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2246_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__0;
                v___x_2247_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__1;
                v___x_2248_ = crate::leanh::lean_box(0);
                v___x_2249_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_2246_,
                    v___x_2247_,
                    v_rewriteCache_2240_,
                    v_fvar_2231_,
                    v___x_2248_,
                );
                if v_isShared_2245_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2244_, 0, v___x_2249_);
                    v___x_2251_ = v___x_2244_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2254_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2254_, 0, v___x_2249_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2254_, 1, v_acNfCache_2241_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2254_, 2, v_typeAnalysis_2242_);
                    v___x_2251_ = v_reuseFailAlloc_2254_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2252_ = lean_st_ref_set(v_a_2233_, v___x_2251_);
                v___x_2253_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2253_, 0, v___x_2248_);
                return v___x_2253_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_rewriteFinished___boxed(
    mut v_fvar_2256_: *mut crate::leanh::LeanObject,
    mut v_a_2257_: *mut crate::leanh::LeanObject,
    mut v_a_2258_: *mut crate::leanh::LeanObject,
    mut v_a_2259_: *mut crate::leanh::LeanObject,
    mut v_a_2260_: *mut crate::leanh::LeanObject,
    mut v_a_2261_: *mut crate::leanh::LeanObject,
    mut v_a_2262_: *mut crate::leanh::LeanObject,
    mut v_a_2263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2264_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_rewriteFinished(
        v_fvar_2256_,
        v_a_2257_,
        v_a_2258_,
        v_a_2259_,
        v_a_2260_,
        v_a_2261_,
        v_a_2262_,
    );
    crate::leanh::lean_dec(v_a_2262_);
    crate::leanh::lean_dec_ref(v_a_2261_);
    crate::leanh::lean_dec(v_a_2260_);
    crate::leanh::lean_dec_ref(v_a_2259_);
    crate::leanh::lean_dec(v_a_2258_);
    crate::leanh::lean_dec_ref(v_a_2257_);
    return v_res_2264_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_acNfFinished___redArg(
    mut v_fvar_2265_: *mut crate::leanh::LeanObject,
    mut v_a_2266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2274_: u8 = 0;
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2284_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2268_ = lean_st_ref_take(v_a_2266_);
                v_rewriteCache_2269_ = crate::leanh::lean_ctor_get(v___x_2268_, 0);
                v_acNfCache_2270_ = crate::leanh::lean_ctor_get(v___x_2268_, 1);
                v_typeAnalysis_2271_ = crate::leanh::lean_ctor_get(v___x_2268_, 2);
                v_isSharedCheck_2284_ = (!crate::leanh::lean_is_exclusive(v___x_2268_)) as u8;
                if v_isSharedCheck_2284_ == 0 {
                    v___x_2273_ = v___x_2268_;
                    v_isShared_2274_ = v_isSharedCheck_2284_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_typeAnalysis_2271_);
                    crate::leanh::lean_inc(v_acNfCache_2270_);
                    crate::leanh::lean_inc(v_rewriteCache_2269_);
                    crate::leanh::lean_dec(v___x_2268_);
                    v___x_2273_ = crate::leanh::lean_box(0);
                    v_isShared_2274_ = v_isSharedCheck_2284_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2275_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__0;
                v___x_2276_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__1;
                v___x_2277_ = crate::leanh::lean_box(0);
                v___x_2278_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_2275_,
                    v___x_2276_,
                    v_acNfCache_2270_,
                    v_fvar_2265_,
                    v___x_2277_,
                );
                if v_isShared_2274_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2273_, 1, v___x_2278_);
                    v___x_2280_ = v___x_2273_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2283_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_rewriteCache_2269_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2283_, 1, v___x_2278_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2283_, 2, v_typeAnalysis_2271_);
                    v___x_2280_ = v_reuseFailAlloc_2283_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2281_ = lean_st_ref_set(v_a_2266_, v___x_2280_);
                v___x_2282_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2282_, 0, v___x_2277_);
                return v___x_2282_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_acNfFinished___redArg___boxed(
    mut v_fvar_2285_: *mut crate::leanh::LeanObject,
    mut v_a_2286_: *mut crate::leanh::LeanObject,
    mut v_a_2287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2288_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_acNfFinished___redArg(
        v_fvar_2285_,
        v_a_2286_,
    );
    crate::leanh::lean_dec(v_a_2286_);
    return v_res_2288_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_acNfFinished(
    mut v_fvar_2289_: *mut crate::leanh::LeanObject,
    mut v_a_2290_: *mut crate::leanh::LeanObject,
    mut v_a_2291_: *mut crate::leanh::LeanObject,
    mut v_a_2292_: *mut crate::leanh::LeanObject,
    mut v_a_2293_: *mut crate::leanh::LeanObject,
    mut v_a_2294_: *mut crate::leanh::LeanObject,
    mut v_a_2295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2303_: u8 = 0;
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2313_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2297_ = lean_st_ref_take(v_a_2291_);
                v_rewriteCache_2298_ = crate::leanh::lean_ctor_get(v___x_2297_, 0);
                v_acNfCache_2299_ = crate::leanh::lean_ctor_get(v___x_2297_, 1);
                v_typeAnalysis_2300_ = crate::leanh::lean_ctor_get(v___x_2297_, 2);
                v_isSharedCheck_2313_ = (!crate::leanh::lean_is_exclusive(v___x_2297_)) as u8;
                if v_isSharedCheck_2313_ == 0 {
                    v___x_2302_ = v___x_2297_;
                    v_isShared_2303_ = v_isSharedCheck_2313_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_typeAnalysis_2300_);
                    crate::leanh::lean_inc(v_acNfCache_2299_);
                    crate::leanh::lean_inc(v_rewriteCache_2298_);
                    crate::leanh::lean_dec(v___x_2297_);
                    v___x_2302_ = crate::leanh::lean_box(0);
                    v_isShared_2303_ = v_isSharedCheck_2313_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2304_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__0;
                v___x_2305_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__1;
                v___x_2306_ = crate::leanh::lean_box(0);
                v___x_2307_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_2304_,
                    v___x_2305_,
                    v_acNfCache_2299_,
                    v_fvar_2289_,
                    v___x_2306_,
                );
                if v_isShared_2303_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2302_, 1, v___x_2307_);
                    v___x_2309_ = v___x_2302_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2312_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_rewriteCache_2298_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2312_, 1, v___x_2307_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2312_, 2, v_typeAnalysis_2300_);
                    v___x_2309_ = v_reuseFailAlloc_2312_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2310_ = lean_st_ref_set(v_a_2291_, v___x_2309_);
                v___x_2311_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2311_, 0, v___x_2306_);
                return v___x_2311_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_acNfFinished___boxed(
    mut v_fvar_2314_: *mut crate::leanh::LeanObject,
    mut v_a_2315_: *mut crate::leanh::LeanObject,
    mut v_a_2316_: *mut crate::leanh::LeanObject,
    mut v_a_2317_: *mut crate::leanh::LeanObject,
    mut v_a_2318_: *mut crate::leanh::LeanObject,
    mut v_a_2319_: *mut crate::leanh::LeanObject,
    mut v_a_2320_: *mut crate::leanh::LeanObject,
    mut v_a_2321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2322_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_acNfFinished(
        v_fvar_2314_,
        v_a_2315_,
        v_a_2316_,
        v_a_2317_,
        v_a_2318_,
        v_a_2319_,
        v_a_2320_,
    );
    crate::leanh::lean_dec(v_a_2320_);
    crate::leanh::lean_dec_ref(v_a_2319_);
    crate::leanh::lean_dec(v_a_2318_);
    crate::leanh::lean_dec_ref(v_a_2317_);
    crate::leanh::lean_dec(v_a_2316_);
    crate::leanh::lean_dec_ref(v_a_2315_);
    return v_res_2322_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg(
    mut v_a_2323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2325_ = lean_st_ref_get(v_a_2323_);
    v_typeAnalysis_2326_ = crate::leanh::lean_ctor_get(v___x_2325_, 2);
    crate::leanh::lean_inc_ref(v_typeAnalysis_2326_);
    crate::leanh::lean_dec(v___x_2325_);
    v___x_2327_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2327_, 0, v_typeAnalysis_2326_);
    return v___x_2327_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg___boxed(
    mut v_a_2328_: *mut crate::leanh::LeanObject,
    mut v_a_2329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2330_ =
        l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg(v_a_2328_);
    crate::leanh::lean_dec(v_a_2328_);
    return v_res_2330_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis(
    mut v_a_2331_: *mut crate::leanh::LeanObject,
    mut v_a_2332_: *mut crate::leanh::LeanObject,
    mut v_a_2333_: *mut crate::leanh::LeanObject,
    mut v_a_2334_: *mut crate::leanh::LeanObject,
    mut v_a_2335_: *mut crate::leanh::LeanObject,
    mut v_a_2336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2338_ = lean_st_ref_get(v_a_2332_);
    v_typeAnalysis_2339_ = crate::leanh::lean_ctor_get(v___x_2338_, 2);
    crate::leanh::lean_inc_ref(v_typeAnalysis_2339_);
    crate::leanh::lean_dec(v___x_2338_);
    v___x_2340_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2340_, 0, v_typeAnalysis_2339_);
    return v___x_2340_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___boxed(
    mut v_a_2341_: *mut crate::leanh::LeanObject,
    mut v_a_2342_: *mut crate::leanh::LeanObject,
    mut v_a_2343_: *mut crate::leanh::LeanObject,
    mut v_a_2344_: *mut crate::leanh::LeanObject,
    mut v_a_2345_: *mut crate::leanh::LeanObject,
    mut v_a_2346_: *mut crate::leanh::LeanObject,
    mut v_a_2347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2348_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis(
        v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_,
    );
    crate::leanh::lean_dec(v_a_2346_);
    crate::leanh::lean_dec_ref(v_a_2345_);
    crate::leanh::lean_dec(v_a_2344_);
    crate::leanh::lean_dec_ref(v_a_2343_);
    crate::leanh::lean_dec(v_a_2342_);
    crate::leanh::lean_dec_ref(v_a_2341_);
    return v_res_2348_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg(
    mut v_n_2354_: *mut crate::leanh::LeanObject,
    mut v_a_2355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingStructures_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninteresting_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: u8 = 0;
    v___x_2357_ = lean_st_ref_get(v_a_2355_);
    v_typeAnalysis_2358_ = crate::leanh::lean_ctor_get(v___x_2357_, 2);
    crate::leanh::lean_inc_ref(v_typeAnalysis_2358_);
    crate::leanh::lean_dec(v___x_2357_);
    v_interestingStructures_2359_ = crate::leanh::lean_ctor_get(v_typeAnalysis_2358_, 0);
    crate::leanh::lean_inc_ref(v_interestingStructures_2359_);
    v_uninteresting_2360_ = crate::leanh::lean_ctor_get(v_typeAnalysis_2358_, 3);
    crate::leanh::lean_inc_ref(v_uninteresting_2360_);
    crate::leanh::lean_dec_ref(v_typeAnalysis_2358_);
    v___x_2361_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0;
    v___x_2362_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1;
    crate::leanh::lean_inc(v_n_2354_);
    v___x_2363_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v___x_2361_,
        v___x_2362_,
        v_uninteresting_2360_,
        v_n_2354_,
    );
    crate::leanh::lean_dec_ref(v_uninteresting_2360_);
    if v___x_2363_ == 0 {
        let mut v___x_2364_: u8 = 0;
        v___x_2364_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
            v___x_2361_,
            v___x_2362_,
            v_interestingStructures_2359_,
            v_n_2354_,
        );
        crate::leanh::lean_dec_ref(v_interestingStructures_2359_);
        if v___x_2364_ == 0 {
            let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2365_ = crate::leanh::lean_box(0);
            v___x_2366_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2366_, 0, v___x_2365_);
            return v___x_2366_;
        } else {
            let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2367_ = crate::leanh::lean_box((v___x_2364_) as usize);
            v___x_2368_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2368_, 0, v___x_2367_);
            v___x_2369_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2369_, 0, v___x_2368_);
            return v___x_2369_;
        }
    } else {
        let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_interestingStructures_2359_);
        crate::leanh::lean_dec(v_n_2354_);
        v___x_2370_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2;
        v___x_2371_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2371_, 0, v___x_2370_);
        return v___x_2371_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___boxed(
    mut v_n_2372_: *mut crate::leanh::LeanObject,
    mut v_a_2373_: *mut crate::leanh::LeanObject,
    mut v_a_2374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2375_ =
        l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg(
            v_n_2372_, v_a_2373_,
        );
    crate::leanh::lean_dec(v_a_2373_);
    return v_res_2375_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure(
    mut v_n_2376_: *mut crate::leanh::LeanObject,
    mut v_a_2377_: *mut crate::leanh::LeanObject,
    mut v_a_2378_: *mut crate::leanh::LeanObject,
    mut v_a_2379_: *mut crate::leanh::LeanObject,
    mut v_a_2380_: *mut crate::leanh::LeanObject,
    mut v_a_2381_: *mut crate::leanh::LeanObject,
    mut v_a_2382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingStructures_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninteresting_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: u8 = 0;
    v___x_2384_ = lean_st_ref_get(v_a_2378_);
    v_typeAnalysis_2385_ = crate::leanh::lean_ctor_get(v___x_2384_, 2);
    crate::leanh::lean_inc_ref(v_typeAnalysis_2385_);
    crate::leanh::lean_dec(v___x_2384_);
    v_interestingStructures_2386_ = crate::leanh::lean_ctor_get(v_typeAnalysis_2385_, 0);
    crate::leanh::lean_inc_ref(v_interestingStructures_2386_);
    v_uninteresting_2387_ = crate::leanh::lean_ctor_get(v_typeAnalysis_2385_, 3);
    crate::leanh::lean_inc_ref(v_uninteresting_2387_);
    crate::leanh::lean_dec_ref(v_typeAnalysis_2385_);
    v___x_2388_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0;
    v___x_2389_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1;
    crate::leanh::lean_inc(v_n_2376_);
    v___x_2390_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v___x_2388_,
        v___x_2389_,
        v_uninteresting_2387_,
        v_n_2376_,
    );
    crate::leanh::lean_dec_ref(v_uninteresting_2387_);
    if v___x_2390_ == 0 {
        let mut v___x_2391_: u8 = 0;
        v___x_2391_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
            v___x_2388_,
            v___x_2389_,
            v_interestingStructures_2386_,
            v_n_2376_,
        );
        crate::leanh::lean_dec_ref(v_interestingStructures_2386_);
        if v___x_2391_ == 0 {
            let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2392_ = crate::leanh::lean_box(0);
            v___x_2393_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2393_, 0, v___x_2392_);
            return v___x_2393_;
        } else {
            let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2394_ = crate::leanh::lean_box((v___x_2391_) as usize);
            v___x_2395_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2395_, 0, v___x_2394_);
            v___x_2396_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2396_, 0, v___x_2395_);
            return v___x_2396_;
        }
    } else {
        let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_interestingStructures_2386_);
        crate::leanh::lean_dec(v_n_2376_);
        v___x_2397_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2;
        v___x_2398_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2398_, 0, v___x_2397_);
        return v___x_2398_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___boxed(
    mut v_n_2399_: *mut crate::leanh::LeanObject,
    mut v_a_2400_: *mut crate::leanh::LeanObject,
    mut v_a_2401_: *mut crate::leanh::LeanObject,
    mut v_a_2402_: *mut crate::leanh::LeanObject,
    mut v_a_2403_: *mut crate::leanh::LeanObject,
    mut v_a_2404_: *mut crate::leanh::LeanObject,
    mut v_a_2405_: *mut crate::leanh::LeanObject,
    mut v_a_2406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2407_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure(
        v_n_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_,
    );
    crate::leanh::lean_dec(v_a_2405_);
    crate::leanh::lean_dec_ref(v_a_2404_);
    crate::leanh::lean_dec(v_a_2403_);
    crate::leanh::lean_dec_ref(v_a_2402_);
    crate::leanh::lean_dec(v_a_2401_);
    crate::leanh::lean_dec_ref(v_a_2400_);
    return v_res_2407_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg(
    mut v_f_2408_: *mut crate::leanh::LeanObject,
    mut v_a_2409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2417_: u8 = 0;
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2425_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2411_ = lean_st_ref_take(v_a_2409_);
                v_rewriteCache_2412_ = crate::leanh::lean_ctor_get(v___x_2411_, 0);
                v_acNfCache_2413_ = crate::leanh::lean_ctor_get(v___x_2411_, 1);
                v_typeAnalysis_2414_ = crate::leanh::lean_ctor_get(v___x_2411_, 2);
                v_isSharedCheck_2425_ = (!crate::leanh::lean_is_exclusive(v___x_2411_)) as u8;
                if v_isSharedCheck_2425_ == 0 {
                    v___x_2416_ = v___x_2411_;
                    v_isShared_2417_ = v_isSharedCheck_2425_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_typeAnalysis_2414_);
                    crate::leanh::lean_inc(v_acNfCache_2413_);
                    crate::leanh::lean_inc(v_rewriteCache_2412_);
                    crate::leanh::lean_dec(v___x_2411_);
                    v___x_2416_ = crate::leanh::lean_box(0);
                    v_isShared_2417_ = v_isSharedCheck_2425_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2418_ = crate::leanh::lean_apply_1(v_f_2408_, v_typeAnalysis_2414_);
                if v_isShared_2417_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2416_, 2, v___x_2418_);
                    v___x_2420_ = v___x_2416_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2424_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_rewriteCache_2412_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2424_, 1, v_acNfCache_2413_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2424_, 2, v___x_2418_);
                    v___x_2420_ = v_reuseFailAlloc_2424_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2421_ = lean_st_ref_set(v_a_2409_, v___x_2420_);
                v___x_2422_ = crate::leanh::lean_box(0);
                v___x_2423_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2423_, 0, v___x_2422_);
                return v___x_2423_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg___boxed(
    mut v_f_2426_: *mut crate::leanh::LeanObject,
    mut v_a_2427_: *mut crate::leanh::LeanObject,
    mut v_a_2428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2429_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg(
        v_f_2426_, v_a_2427_,
    );
    crate::leanh::lean_dec(v_a_2427_);
    return v_res_2429_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis(
    mut v_f_2430_: *mut crate::leanh::LeanObject,
    mut v_a_2431_: *mut crate::leanh::LeanObject,
    mut v_a_2432_: *mut crate::leanh::LeanObject,
    mut v_a_2433_: *mut crate::leanh::LeanObject,
    mut v_a_2434_: *mut crate::leanh::LeanObject,
    mut v_a_2435_: *mut crate::leanh::LeanObject,
    mut v_a_2436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2444_: u8 = 0;
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2452_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2438_ = lean_st_ref_take(v_a_2432_);
                v_rewriteCache_2439_ = crate::leanh::lean_ctor_get(v___x_2438_, 0);
                v_acNfCache_2440_ = crate::leanh::lean_ctor_get(v___x_2438_, 1);
                v_typeAnalysis_2441_ = crate::leanh::lean_ctor_get(v___x_2438_, 2);
                v_isSharedCheck_2452_ = (!crate::leanh::lean_is_exclusive(v___x_2438_)) as u8;
                if v_isSharedCheck_2452_ == 0 {
                    v___x_2443_ = v___x_2438_;
                    v_isShared_2444_ = v_isSharedCheck_2452_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_typeAnalysis_2441_);
                    crate::leanh::lean_inc(v_acNfCache_2440_);
                    crate::leanh::lean_inc(v_rewriteCache_2439_);
                    crate::leanh::lean_dec(v___x_2438_);
                    v___x_2443_ = crate::leanh::lean_box(0);
                    v_isShared_2444_ = v_isSharedCheck_2452_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2445_ = crate::leanh::lean_apply_1(v_f_2430_, v_typeAnalysis_2441_);
                if v_isShared_2444_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2443_, 2, v___x_2445_);
                    v___x_2447_ = v___x_2443_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2451_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_rewriteCache_2439_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2451_, 1, v_acNfCache_2440_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2451_, 2, v___x_2445_);
                    v___x_2447_ = v_reuseFailAlloc_2451_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2448_ = lean_st_ref_set(v_a_2432_, v___x_2447_);
                v___x_2449_ = crate::leanh::lean_box(0);
                v___x_2450_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2450_, 0, v___x_2449_);
                return v___x_2450_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___boxed(
    mut v_f_2453_: *mut crate::leanh::LeanObject,
    mut v_a_2454_: *mut crate::leanh::LeanObject,
    mut v_a_2455_: *mut crate::leanh::LeanObject,
    mut v_a_2456_: *mut crate::leanh::LeanObject,
    mut v_a_2457_: *mut crate::leanh::LeanObject,
    mut v_a_2458_: *mut crate::leanh::LeanObject,
    mut v_a_2459_: *mut crate::leanh::LeanObject,
    mut v_a_2460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2461_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis(
        v_f_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_,
    );
    crate::leanh::lean_dec(v_a_2459_);
    crate::leanh::lean_dec_ref(v_a_2458_);
    crate::leanh::lean_dec(v_a_2457_);
    crate::leanh::lean_dec_ref(v_a_2456_);
    crate::leanh::lean_dec(v_a_2455_);
    crate::leanh::lean_dec_ref(v_a_2454_);
    return v_res_2461_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg(
    mut v_n_2462_: *mut crate::leanh::LeanObject,
    mut v_a_2463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2471_: u8 = 0;
    let mut v_interestingStructures_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingEnums_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingMatchers_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninteresting_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2478_: u8 = 0;
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2491_: u8 = 0;
    let mut v_isSharedCheck_2492_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2465_ = lean_st_ref_take(v_a_2463_);
                v_typeAnalysis_2466_ = crate::leanh::lean_ctor_get(v___x_2465_, 2);
                v_rewriteCache_2467_ = crate::leanh::lean_ctor_get(v___x_2465_, 0);
                v_acNfCache_2468_ = crate::leanh::lean_ctor_get(v___x_2465_, 1);
                v_isSharedCheck_2492_ = (!crate::leanh::lean_is_exclusive(v___x_2465_)) as u8;
                if v_isSharedCheck_2492_ == 0 {
                    v___x_2470_ = v___x_2465_;
                    v_isShared_2471_ = v_isSharedCheck_2492_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_typeAnalysis_2466_);
                    crate::leanh::lean_inc(v_acNfCache_2468_);
                    crate::leanh::lean_inc(v_rewriteCache_2467_);
                    crate::leanh::lean_dec(v___x_2465_);
                    v___x_2470_ = crate::leanh::lean_box(0);
                    v_isShared_2471_ = v_isSharedCheck_2492_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_interestingStructures_2472_ =
                    crate::leanh::lean_ctor_get(v_typeAnalysis_2466_, 0);
                v_interestingEnums_2473_ = crate::leanh::lean_ctor_get(v_typeAnalysis_2466_, 1);
                v_interestingMatchers_2474_ = crate::leanh::lean_ctor_get(v_typeAnalysis_2466_, 2);
                v_uninteresting_2475_ = crate::leanh::lean_ctor_get(v_typeAnalysis_2466_, 3);
                v_isSharedCheck_2491_ =
                    (!crate::leanh::lean_is_exclusive(v_typeAnalysis_2466_)) as u8;
                if v_isSharedCheck_2491_ == 0 {
                    v___x_2477_ = v_typeAnalysis_2466_;
                    v_isShared_2478_ = v_isSharedCheck_2491_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_uninteresting_2475_);
                    crate::leanh::lean_inc(v_interestingMatchers_2474_);
                    crate::leanh::lean_inc(v_interestingEnums_2473_);
                    crate::leanh::lean_inc(v_interestingStructures_2472_);
                    crate::leanh::lean_dec(v_typeAnalysis_2466_);
                    v___x_2477_ = crate::leanh::lean_box(0);
                    v_isShared_2478_ = v_isSharedCheck_2491_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2479_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0;
                v___x_2480_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1;
                v___x_2481_ = crate::leanh::lean_box(0);
                v___x_2482_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_2479_,
                    v___x_2480_,
                    v_interestingStructures_2472_,
                    v_n_2462_,
                    v___x_2481_,
                );
                if v_isShared_2478_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2477_, 0, v___x_2482_);
                    v___x_2484_ = v___x_2477_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2490_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2482_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2490_,
                        1,
                        v_interestingEnums_2473_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2490_,
                        2,
                        v_interestingMatchers_2474_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2490_, 3, v_uninteresting_2475_);
                    v___x_2484_ = v_reuseFailAlloc_2490_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2471_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2470_, 2, v___x_2484_);
                    v___x_2486_ = v___x_2470_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2489_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_rewriteCache_2467_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2489_, 1, v_acNfCache_2468_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2489_, 2, v___x_2484_);
                    v___x_2486_ = v_reuseFailAlloc_2489_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2487_ = lean_st_ref_set(v_a_2463_, v___x_2486_);
                v___x_2488_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2488_, 0, v___x_2481_);
                return v___x_2488_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg___boxed(
    mut v_n_2493_: *mut crate::leanh::LeanObject,
    mut v_a_2494_: *mut crate::leanh::LeanObject,
    mut v_a_2495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2496_ =
        l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg(
            v_n_2493_, v_a_2494_,
        );
    crate::leanh::lean_dec(v_a_2494_);
    return v_res_2496_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(
    mut v_n_2497_: *mut crate::leanh::LeanObject,
    mut v_a_2498_: *mut crate::leanh::LeanObject,
    mut v_a_2499_: *mut crate::leanh::LeanObject,
    mut v_a_2500_: *mut crate::leanh::LeanObject,
    mut v_a_2501_: *mut crate::leanh::LeanObject,
    mut v_a_2502_: *mut crate::leanh::LeanObject,
    mut v_a_2503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2511_: u8 = 0;
    let mut v_interestingStructures_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingEnums_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingMatchers_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninteresting_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2518_: u8 = 0;
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2531_: u8 = 0;
    let mut v_isSharedCheck_2532_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2505_ = lean_st_ref_take(v_a_2499_);
                v_typeAnalysis_2506_ = crate::leanh::lean_ctor_get(v___x_2505_, 2);
                v_rewriteCache_2507_ = crate::leanh::lean_ctor_get(v___x_2505_, 0);
                v_acNfCache_2508_ = crate::leanh::lean_ctor_get(v___x_2505_, 1);
                v_isSharedCheck_2532_ = (!crate::leanh::lean_is_exclusive(v___x_2505_)) as u8;
                if v_isSharedCheck_2532_ == 0 {
                    v___x_2510_ = v___x_2505_;
                    v_isShared_2511_ = v_isSharedCheck_2532_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_typeAnalysis_2506_);
                    crate::leanh::lean_inc(v_acNfCache_2508_);
                    crate::leanh::lean_inc(v_rewriteCache_2507_);
                    crate::leanh::lean_dec(v___x_2505_);
                    v___x_2510_ = crate::leanh::lean_box(0);
                    v_isShared_2511_ = v_isSharedCheck_2532_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_interestingStructures_2512_ =
                    crate::leanh::lean_ctor_get(v_typeAnalysis_2506_, 0);
                v_interestingEnums_2513_ = crate::leanh::lean_ctor_get(v_typeAnalysis_2506_, 1);
                v_interestingMatchers_2514_ = crate::leanh::lean_ctor_get(v_typeAnalysis_2506_, 2);
                v_uninteresting_2515_ = crate::leanh::lean_ctor_get(v_typeAnalysis_2506_, 3);
                v_isSharedCheck_2531_ =
                    (!crate::leanh::lean_is_exclusive(v_typeAnalysis_2506_)) as u8;
                if v_isSharedCheck_2531_ == 0 {
                    v___x_2517_ = v_typeAnalysis_2506_;
                    v_isShared_2518_ = v_isSharedCheck_2531_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_uninteresting_2515_);
                    crate::leanh::lean_inc(v_interestingMatchers_2514_);
                    crate::leanh::lean_inc(v_interestingEnums_2513_);
                    crate::leanh::lean_inc(v_interestingStructures_2512_);
                    crate::leanh::lean_dec(v_typeAnalysis_2506_);
                    v___x_2517_ = crate::leanh::lean_box(0);
                    v_isShared_2518_ = v_isSharedCheck_2531_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2519_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0;
                v___x_2520_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1;
                v___x_2521_ = crate::leanh::lean_box(0);
                v___x_2522_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_2519_,
                    v___x_2520_,
                    v_interestingStructures_2512_,
                    v_n_2497_,
                    v___x_2521_,
                );
                if v_isShared_2518_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2517_, 0, v___x_2522_);
                    v___x_2524_ = v___x_2517_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2530_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2522_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2530_,
                        1,
                        v_interestingEnums_2513_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2530_,
                        2,
                        v_interestingMatchers_2514_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2530_, 3, v_uninteresting_2515_);
                    v___x_2524_ = v_reuseFailAlloc_2530_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2511_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2510_, 2, v___x_2524_);
                    v___x_2526_ = v___x_2510_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2529_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_rewriteCache_2507_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2529_, 1, v_acNfCache_2508_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2529_, 2, v___x_2524_);
                    v___x_2526_ = v_reuseFailAlloc_2529_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2527_ = lean_st_ref_set(v_a_2499_, v___x_2526_);
                v___x_2528_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2528_, 0, v___x_2521_);
                return v___x_2528_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___boxed(
    mut v_n_2533_: *mut crate::leanh::LeanObject,
    mut v_a_2534_: *mut crate::leanh::LeanObject,
    mut v_a_2535_: *mut crate::leanh::LeanObject,
    mut v_a_2536_: *mut crate::leanh::LeanObject,
    mut v_a_2537_: *mut crate::leanh::LeanObject,
    mut v_a_2538_: *mut crate::leanh::LeanObject,
    mut v_a_2539_: *mut crate::leanh::LeanObject,
    mut v_a_2540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2541_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(
        v_n_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_,
    );
    crate::leanh::lean_dec(v_a_2539_);
    crate::leanh::lean_dec_ref(v_a_2538_);
    crate::leanh::lean_dec(v_a_2537_);
    crate::leanh::lean_dec_ref(v_a_2536_);
    crate::leanh::lean_dec(v_a_2535_);
    crate::leanh::lean_dec_ref(v_a_2534_);
    return v_res_2541_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(
    mut v_n_2542_: *mut crate::leanh::LeanObject,
    mut v_a_2543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2551_: u8 = 0;
    let mut v_interestingStructures_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingEnums_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingMatchers_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninteresting_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2558_: u8 = 0;
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2571_: u8 = 0;
    let mut v_isSharedCheck_2572_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2545_ = lean_st_ref_take(v_a_2543_);
                v_typeAnalysis_2546_ = crate::leanh::lean_ctor_get(v___x_2545_, 2);
                v_rewriteCache_2547_ = crate::leanh::lean_ctor_get(v___x_2545_, 0);
                v_acNfCache_2548_ = crate::leanh::lean_ctor_get(v___x_2545_, 1);
                v_isSharedCheck_2572_ = (!crate::leanh::lean_is_exclusive(v___x_2545_)) as u8;
                if v_isSharedCheck_2572_ == 0 {
                    v___x_2550_ = v___x_2545_;
                    v_isShared_2551_ = v_isSharedCheck_2572_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_typeAnalysis_2546_);
                    crate::leanh::lean_inc(v_acNfCache_2548_);
                    crate::leanh::lean_inc(v_rewriteCache_2547_);
                    crate::leanh::lean_dec(v___x_2545_);
                    v___x_2550_ = crate::leanh::lean_box(0);
                    v_isShared_2551_ = v_isSharedCheck_2572_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_interestingStructures_2552_ =
                    crate::leanh::lean_ctor_get(v_typeAnalysis_2546_, 0);
                v_interestingEnums_2553_ = crate::leanh::lean_ctor_get(v_typeAnalysis_2546_, 1);
                v_interestingMatchers_2554_ = crate::leanh::lean_ctor_get(v_typeAnalysis_2546_, 2);
                v_uninteresting_2555_ = crate::leanh::lean_ctor_get(v_typeAnalysis_2546_, 3);
                v_isSharedCheck_2571_ =
                    (!crate::leanh::lean_is_exclusive(v_typeAnalysis_2546_)) as u8;
                if v_isSharedCheck_2571_ == 0 {
                    v___x_2557_ = v_typeAnalysis_2546_;
                    v_isShared_2558_ = v_isSharedCheck_2571_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_uninteresting_2555_);
                    crate::leanh::lean_inc(v_interestingMatchers_2554_);
                    crate::leanh::lean_inc(v_interestingEnums_2553_);
                    crate::leanh::lean_inc(v_interestingStructures_2552_);
                    crate::leanh::lean_dec(v_typeAnalysis_2546_);
                    v___x_2557_ = crate::leanh::lean_box(0);
                    v_isShared_2558_ = v_isSharedCheck_2571_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2559_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0;
                v___x_2560_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1;
                v___x_2561_ = crate::leanh::lean_box(0);
                v___x_2562_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_2559_,
                    v___x_2560_,
                    v_interestingEnums_2553_,
                    v_n_2542_,
                    v___x_2561_,
                );
                if v_isShared_2558_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2557_, 1, v___x_2562_);
                    v___x_2564_ = v___x_2557_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2570_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2570_,
                        0,
                        v_interestingStructures_2552_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2570_, 1, v___x_2562_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2570_,
                        2,
                        v_interestingMatchers_2554_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2570_, 3, v_uninteresting_2555_);
                    v___x_2564_ = v_reuseFailAlloc_2570_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2551_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2550_, 2, v___x_2564_);
                    v___x_2566_ = v___x_2550_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2569_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_rewriteCache_2547_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2569_, 1, v_acNfCache_2548_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2569_, 2, v___x_2564_);
                    v___x_2566_ = v_reuseFailAlloc_2569_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2567_ = lean_st_ref_set(v_a_2543_, v___x_2566_);
                v___x_2568_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2568_, 0, v___x_2561_);
                return v___x_2568_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg___boxed(
    mut v_n_2573_: *mut crate::leanh::LeanObject,
    mut v_a_2574_: *mut crate::leanh::LeanObject,
    mut v_a_2575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2576_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(
        v_n_2573_, v_a_2574_,
    );
    crate::leanh::lean_dec(v_a_2574_);
    return v_res_2576_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(
    mut v_n_2577_: *mut crate::leanh::LeanObject,
    mut v_a_2578_: *mut crate::leanh::LeanObject,
    mut v_a_2579_: *mut crate::leanh::LeanObject,
    mut v_a_2580_: *mut crate::leanh::LeanObject,
    mut v_a_2581_: *mut crate::leanh::LeanObject,
    mut v_a_2582_: *mut crate::leanh::LeanObject,
    mut v_a_2583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2591_: u8 = 0;
    let mut v_interestingStructures_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingEnums_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingMatchers_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninteresting_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2598_: u8 = 0;
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2611_: u8 = 0;
    let mut v_isSharedCheck_2612_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2585_ = lean_st_ref_take(v_a_2579_);
                v_typeAnalysis_2586_ = crate::leanh::lean_ctor_get(v___x_2585_, 2);
                v_rewriteCache_2587_ = crate::leanh::lean_ctor_get(v___x_2585_, 0);
                v_acNfCache_2588_ = crate::leanh::lean_ctor_get(v___x_2585_, 1);
                v_isSharedCheck_2612_ = (!crate::leanh::lean_is_exclusive(v___x_2585_)) as u8;
                if v_isSharedCheck_2612_ == 0 {
                    v___x_2590_ = v___x_2585_;
                    v_isShared_2591_ = v_isSharedCheck_2612_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_typeAnalysis_2586_);
                    crate::leanh::lean_inc(v_acNfCache_2588_);
                    crate::leanh::lean_inc(v_rewriteCache_2587_);
                    crate::leanh::lean_dec(v___x_2585_);
                    v___x_2590_ = crate::leanh::lean_box(0);
                    v_isShared_2591_ = v_isSharedCheck_2612_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_interestingStructures_2592_ =
                    crate::leanh::lean_ctor_get(v_typeAnalysis_2586_, 0);
                v_interestingEnums_2593_ = crate::leanh::lean_ctor_get(v_typeAnalysis_2586_, 1);
                v_interestingMatchers_2594_ = crate::leanh::lean_ctor_get(v_typeAnalysis_2586_, 2);
                v_uninteresting_2595_ = crate::leanh::lean_ctor_get(v_typeAnalysis_2586_, 3);
                v_isSharedCheck_2611_ =
                    (!crate::leanh::lean_is_exclusive(v_typeAnalysis_2586_)) as u8;
                if v_isSharedCheck_2611_ == 0 {
                    v___x_2597_ = v_typeAnalysis_2586_;
                    v_isShared_2598_ = v_isSharedCheck_2611_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_uninteresting_2595_);
                    crate::leanh::lean_inc(v_interestingMatchers_2594_);
                    crate::leanh::lean_inc(v_interestingEnums_2593_);
                    crate::leanh::lean_inc(v_interestingStructures_2592_);
                    crate::leanh::lean_dec(v_typeAnalysis_2586_);
                    v___x_2597_ = crate::leanh::lean_box(0);
                    v_isShared_2598_ = v_isSharedCheck_2611_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2599_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0;
                v___x_2600_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1;
                v___x_2601_ = crate::leanh::lean_box(0);
                v___x_2602_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_2599_,
                    v___x_2600_,
                    v_interestingEnums_2593_,
                    v_n_2577_,
                    v___x_2601_,
                );
                if v_isShared_2598_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2597_, 1, v___x_2602_);
                    v___x_2604_ = v___x_2597_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2610_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2610_,
                        0,
                        v_interestingStructures_2592_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2610_, 1, v___x_2602_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2610_,
                        2,
                        v_interestingMatchers_2594_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2610_, 3, v_uninteresting_2595_);
                    v___x_2604_ = v_reuseFailAlloc_2610_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2591_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2590_, 2, v___x_2604_);
                    v___x_2606_ = v___x_2590_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2609_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_rewriteCache_2587_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2609_, 1, v_acNfCache_2588_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2609_, 2, v___x_2604_);
                    v___x_2606_ = v_reuseFailAlloc_2609_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2607_ = lean_st_ref_set(v_a_2579_, v___x_2606_);
                v___x_2608_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2608_, 0, v___x_2601_);
                return v___x_2608_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___boxed(
    mut v_n_2613_: *mut crate::leanh::LeanObject,
    mut v_a_2614_: *mut crate::leanh::LeanObject,
    mut v_a_2615_: *mut crate::leanh::LeanObject,
    mut v_a_2616_: *mut crate::leanh::LeanObject,
    mut v_a_2617_: *mut crate::leanh::LeanObject,
    mut v_a_2618_: *mut crate::leanh::LeanObject,
    mut v_a_2619_: *mut crate::leanh::LeanObject,
    mut v_a_2620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2621_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(
        v_n_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_,
    );
    crate::leanh::lean_dec(v_a_2619_);
    crate::leanh::lean_dec_ref(v_a_2618_);
    crate::leanh::lean_dec(v_a_2617_);
    crate::leanh::lean_dec_ref(v_a_2616_);
    crate::leanh::lean_dec(v_a_2615_);
    crate::leanh::lean_dec_ref(v_a_2614_);
    return v_res_2621_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(
    mut v_n_2622_: *mut crate::leanh::LeanObject,
    mut v_k_2623_: *mut crate::leanh::LeanObject,
    mut v_a_2624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2632_: u8 = 0;
    let mut v_interestingStructures_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingEnums_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingMatchers_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninteresting_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2639_: u8 = 0;
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2652_: u8 = 0;
    let mut v_isSharedCheck_2653_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2626_ = lean_st_ref_take(v_a_2624_);
                v_typeAnalysis_2627_ = crate::leanh::lean_ctor_get(v___x_2626_, 2);
                v_rewriteCache_2628_ = crate::leanh::lean_ctor_get(v___x_2626_, 0);
                v_acNfCache_2629_ = crate::leanh::lean_ctor_get(v___x_2626_, 1);
                v_isSharedCheck_2653_ = (!crate::leanh::lean_is_exclusive(v___x_2626_)) as u8;
                if v_isSharedCheck_2653_ == 0 {
                    v___x_2631_ = v___x_2626_;
                    v_isShared_2632_ = v_isSharedCheck_2653_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_typeAnalysis_2627_);
                    crate::leanh::lean_inc(v_acNfCache_2629_);
                    crate::leanh::lean_inc(v_rewriteCache_2628_);
                    crate::leanh::lean_dec(v___x_2626_);
                    v___x_2631_ = crate::leanh::lean_box(0);
                    v_isShared_2632_ = v_isSharedCheck_2653_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_interestingStructures_2633_ =
                    crate::leanh::lean_ctor_get(v_typeAnalysis_2627_, 0);
                v_interestingEnums_2634_ = crate::leanh::lean_ctor_get(v_typeAnalysis_2627_, 1);
                v_interestingMatchers_2635_ = crate::leanh::lean_ctor_get(v_typeAnalysis_2627_, 2);
                v_uninteresting_2636_ = crate::leanh::lean_ctor_get(v_typeAnalysis_2627_, 3);
                v_isSharedCheck_2652_ =
                    (!crate::leanh::lean_is_exclusive(v_typeAnalysis_2627_)) as u8;
                if v_isSharedCheck_2652_ == 0 {
                    v___x_2638_ = v_typeAnalysis_2627_;
                    v_isShared_2639_ = v_isSharedCheck_2652_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_uninteresting_2636_);
                    crate::leanh::lean_inc(v_interestingMatchers_2635_);
                    crate::leanh::lean_inc(v_interestingEnums_2634_);
                    crate::leanh::lean_inc(v_interestingStructures_2633_);
                    crate::leanh::lean_dec(v_typeAnalysis_2627_);
                    v___x_2638_ = crate::leanh::lean_box(0);
                    v_isShared_2639_ = v_isSharedCheck_2652_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2640_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0;
                v___x_2641_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1;
                v___x_2642_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                    v___x_2640_,
                    v___x_2641_,
                    v_interestingMatchers_2635_,
                    v_n_2622_,
                    v_k_2623_,
                );
                if v_isShared_2639_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2638_, 2, v___x_2642_);
                    v___x_2644_ = v___x_2638_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2651_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2651_,
                        0,
                        v_interestingStructures_2633_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2651_,
                        1,
                        v_interestingEnums_2634_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2651_, 2, v___x_2642_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2651_, 3, v_uninteresting_2636_);
                    v___x_2644_ = v_reuseFailAlloc_2651_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2632_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2631_, 2, v___x_2644_);
                    v___x_2646_ = v___x_2631_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2650_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_rewriteCache_2628_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2650_, 1, v_acNfCache_2629_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2650_, 2, v___x_2644_);
                    v___x_2646_ = v_reuseFailAlloc_2650_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2647_ = lean_st_ref_set(v_a_2624_, v___x_2646_);
                v___x_2648_ = crate::leanh::lean_box(0);
                v___x_2649_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2649_, 0, v___x_2648_);
                return v___x_2649_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg___boxed(
    mut v_n_2654_: *mut crate::leanh::LeanObject,
    mut v_k_2655_: *mut crate::leanh::LeanObject,
    mut v_a_2656_: *mut crate::leanh::LeanObject,
    mut v_a_2657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2658_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(
        v_n_2654_, v_k_2655_, v_a_2656_,
    );
    crate::leanh::lean_dec(v_a_2656_);
    return v_res_2658_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(
    mut v_n_2659_: *mut crate::leanh::LeanObject,
    mut v_k_2660_: *mut crate::leanh::LeanObject,
    mut v_a_2661_: *mut crate::leanh::LeanObject,
    mut v_a_2662_: *mut crate::leanh::LeanObject,
    mut v_a_2663_: *mut crate::leanh::LeanObject,
    mut v_a_2664_: *mut crate::leanh::LeanObject,
    mut v_a_2665_: *mut crate::leanh::LeanObject,
    mut v_a_2666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2674_: u8 = 0;
    let mut v_interestingStructures_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingEnums_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingMatchers_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninteresting_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2681_: u8 = 0;
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2694_: u8 = 0;
    let mut v_isSharedCheck_2695_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2668_ = lean_st_ref_take(v_a_2662_);
                v_typeAnalysis_2669_ = crate::leanh::lean_ctor_get(v___x_2668_, 2);
                v_rewriteCache_2670_ = crate::leanh::lean_ctor_get(v___x_2668_, 0);
                v_acNfCache_2671_ = crate::leanh::lean_ctor_get(v___x_2668_, 1);
                v_isSharedCheck_2695_ = (!crate::leanh::lean_is_exclusive(v___x_2668_)) as u8;
                if v_isSharedCheck_2695_ == 0 {
                    v___x_2673_ = v___x_2668_;
                    v_isShared_2674_ = v_isSharedCheck_2695_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_typeAnalysis_2669_);
                    crate::leanh::lean_inc(v_acNfCache_2671_);
                    crate::leanh::lean_inc(v_rewriteCache_2670_);
                    crate::leanh::lean_dec(v___x_2668_);
                    v___x_2673_ = crate::leanh::lean_box(0);
                    v_isShared_2674_ = v_isSharedCheck_2695_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_interestingStructures_2675_ =
                    crate::leanh::lean_ctor_get(v_typeAnalysis_2669_, 0);
                v_interestingEnums_2676_ = crate::leanh::lean_ctor_get(v_typeAnalysis_2669_, 1);
                v_interestingMatchers_2677_ = crate::leanh::lean_ctor_get(v_typeAnalysis_2669_, 2);
                v_uninteresting_2678_ = crate::leanh::lean_ctor_get(v_typeAnalysis_2669_, 3);
                v_isSharedCheck_2694_ =
                    (!crate::leanh::lean_is_exclusive(v_typeAnalysis_2669_)) as u8;
                if v_isSharedCheck_2694_ == 0 {
                    v___x_2680_ = v_typeAnalysis_2669_;
                    v_isShared_2681_ = v_isSharedCheck_2694_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_uninteresting_2678_);
                    crate::leanh::lean_inc(v_interestingMatchers_2677_);
                    crate::leanh::lean_inc(v_interestingEnums_2676_);
                    crate::leanh::lean_inc(v_interestingStructures_2675_);
                    crate::leanh::lean_dec(v_typeAnalysis_2669_);
                    v___x_2680_ = crate::leanh::lean_box(0);
                    v_isShared_2681_ = v_isSharedCheck_2694_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2682_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0;
                v___x_2683_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1;
                v___x_2684_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                    v___x_2682_,
                    v___x_2683_,
                    v_interestingMatchers_2677_,
                    v_n_2659_,
                    v_k_2660_,
                );
                if v_isShared_2681_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2680_, 2, v___x_2684_);
                    v___x_2686_ = v___x_2680_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2693_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2693_,
                        0,
                        v_interestingStructures_2675_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2693_,
                        1,
                        v_interestingEnums_2676_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2693_, 2, v___x_2684_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2693_, 3, v_uninteresting_2678_);
                    v___x_2686_ = v_reuseFailAlloc_2693_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2674_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2673_, 2, v___x_2686_);
                    v___x_2688_ = v___x_2673_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2692_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_rewriteCache_2670_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 1, v_acNfCache_2671_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 2, v___x_2686_);
                    v___x_2688_ = v_reuseFailAlloc_2692_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2689_ = lean_st_ref_set(v_a_2662_, v___x_2688_);
                v___x_2690_ = crate::leanh::lean_box(0);
                v___x_2691_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2691_, 0, v___x_2690_);
                return v___x_2691_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___boxed(
    mut v_n_2696_: *mut crate::leanh::LeanObject,
    mut v_k_2697_: *mut crate::leanh::LeanObject,
    mut v_a_2698_: *mut crate::leanh::LeanObject,
    mut v_a_2699_: *mut crate::leanh::LeanObject,
    mut v_a_2700_: *mut crate::leanh::LeanObject,
    mut v_a_2701_: *mut crate::leanh::LeanObject,
    mut v_a_2702_: *mut crate::leanh::LeanObject,
    mut v_a_2703_: *mut crate::leanh::LeanObject,
    mut v_a_2704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2705_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(
        v_n_2696_, v_k_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_,
    );
    crate::leanh::lean_dec(v_a_2703_);
    crate::leanh::lean_dec_ref(v_a_2702_);
    crate::leanh::lean_dec(v_a_2701_);
    crate::leanh::lean_dec_ref(v_a_2700_);
    crate::leanh::lean_dec(v_a_2699_);
    crate::leanh::lean_dec_ref(v_a_2698_);
    return v_res_2705_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(
    mut v_n_2706_: *mut crate::leanh::LeanObject,
    mut v_a_2707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2715_: u8 = 0;
    let mut v_interestingStructures_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingEnums_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingMatchers_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninteresting_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2722_: u8 = 0;
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2735_: u8 = 0;
    let mut v_isSharedCheck_2736_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2709_ = lean_st_ref_take(v_a_2707_);
                v_typeAnalysis_2710_ = crate::leanh::lean_ctor_get(v___x_2709_, 2);
                v_rewriteCache_2711_ = crate::leanh::lean_ctor_get(v___x_2709_, 0);
                v_acNfCache_2712_ = crate::leanh::lean_ctor_get(v___x_2709_, 1);
                v_isSharedCheck_2736_ = (!crate::leanh::lean_is_exclusive(v___x_2709_)) as u8;
                if v_isSharedCheck_2736_ == 0 {
                    v___x_2714_ = v___x_2709_;
                    v_isShared_2715_ = v_isSharedCheck_2736_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_typeAnalysis_2710_);
                    crate::leanh::lean_inc(v_acNfCache_2712_);
                    crate::leanh::lean_inc(v_rewriteCache_2711_);
                    crate::leanh::lean_dec(v___x_2709_);
                    v___x_2714_ = crate::leanh::lean_box(0);
                    v_isShared_2715_ = v_isSharedCheck_2736_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_interestingStructures_2716_ =
                    crate::leanh::lean_ctor_get(v_typeAnalysis_2710_, 0);
                v_interestingEnums_2717_ = crate::leanh::lean_ctor_get(v_typeAnalysis_2710_, 1);
                v_interestingMatchers_2718_ = crate::leanh::lean_ctor_get(v_typeAnalysis_2710_, 2);
                v_uninteresting_2719_ = crate::leanh::lean_ctor_get(v_typeAnalysis_2710_, 3);
                v_isSharedCheck_2735_ =
                    (!crate::leanh::lean_is_exclusive(v_typeAnalysis_2710_)) as u8;
                if v_isSharedCheck_2735_ == 0 {
                    v___x_2721_ = v_typeAnalysis_2710_;
                    v_isShared_2722_ = v_isSharedCheck_2735_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_uninteresting_2719_);
                    crate::leanh::lean_inc(v_interestingMatchers_2718_);
                    crate::leanh::lean_inc(v_interestingEnums_2717_);
                    crate::leanh::lean_inc(v_interestingStructures_2716_);
                    crate::leanh::lean_dec(v_typeAnalysis_2710_);
                    v___x_2721_ = crate::leanh::lean_box(0);
                    v_isShared_2722_ = v_isSharedCheck_2735_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2723_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0;
                v___x_2724_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1;
                v___x_2725_ = crate::leanh::lean_box(0);
                v___x_2726_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_2723_,
                    v___x_2724_,
                    v_uninteresting_2719_,
                    v_n_2706_,
                    v___x_2725_,
                );
                if v_isShared_2722_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2721_, 3, v___x_2726_);
                    v___x_2728_ = v___x_2721_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2734_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2734_,
                        0,
                        v_interestingStructures_2716_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2734_,
                        1,
                        v_interestingEnums_2717_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2734_,
                        2,
                        v_interestingMatchers_2718_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2734_, 3, v___x_2726_);
                    v___x_2728_ = v_reuseFailAlloc_2734_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2715_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2714_, 2, v___x_2728_);
                    v___x_2730_ = v___x_2714_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2733_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_rewriteCache_2711_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2733_, 1, v_acNfCache_2712_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2733_, 2, v___x_2728_);
                    v___x_2730_ = v_reuseFailAlloc_2733_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2731_ = lean_st_ref_set(v_a_2707_, v___x_2730_);
                v___x_2732_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2732_, 0, v___x_2725_);
                return v___x_2732_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg___boxed(
    mut v_n_2737_: *mut crate::leanh::LeanObject,
    mut v_a_2738_: *mut crate::leanh::LeanObject,
    mut v_a_2739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2740_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(
        v_n_2737_, v_a_2738_,
    );
    crate::leanh::lean_dec(v_a_2738_);
    return v_res_2740_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(
    mut v_n_2741_: *mut crate::leanh::LeanObject,
    mut v_a_2742_: *mut crate::leanh::LeanObject,
    mut v_a_2743_: *mut crate::leanh::LeanObject,
    mut v_a_2744_: *mut crate::leanh::LeanObject,
    mut v_a_2745_: *mut crate::leanh::LeanObject,
    mut v_a_2746_: *mut crate::leanh::LeanObject,
    mut v_a_2747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2755_: u8 = 0;
    let mut v_interestingStructures_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingEnums_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingMatchers_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninteresting_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2762_: u8 = 0;
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2775_: u8 = 0;
    let mut v_isSharedCheck_2776_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2749_ = lean_st_ref_take(v_a_2743_);
                v_typeAnalysis_2750_ = crate::leanh::lean_ctor_get(v___x_2749_, 2);
                v_rewriteCache_2751_ = crate::leanh::lean_ctor_get(v___x_2749_, 0);
                v_acNfCache_2752_ = crate::leanh::lean_ctor_get(v___x_2749_, 1);
                v_isSharedCheck_2776_ = (!crate::leanh::lean_is_exclusive(v___x_2749_)) as u8;
                if v_isSharedCheck_2776_ == 0 {
                    v___x_2754_ = v___x_2749_;
                    v_isShared_2755_ = v_isSharedCheck_2776_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_typeAnalysis_2750_);
                    crate::leanh::lean_inc(v_acNfCache_2752_);
                    crate::leanh::lean_inc(v_rewriteCache_2751_);
                    crate::leanh::lean_dec(v___x_2749_);
                    v___x_2754_ = crate::leanh::lean_box(0);
                    v_isShared_2755_ = v_isSharedCheck_2776_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_interestingStructures_2756_ =
                    crate::leanh::lean_ctor_get(v_typeAnalysis_2750_, 0);
                v_interestingEnums_2757_ = crate::leanh::lean_ctor_get(v_typeAnalysis_2750_, 1);
                v_interestingMatchers_2758_ = crate::leanh::lean_ctor_get(v_typeAnalysis_2750_, 2);
                v_uninteresting_2759_ = crate::leanh::lean_ctor_get(v_typeAnalysis_2750_, 3);
                v_isSharedCheck_2775_ =
                    (!crate::leanh::lean_is_exclusive(v_typeAnalysis_2750_)) as u8;
                if v_isSharedCheck_2775_ == 0 {
                    v___x_2761_ = v_typeAnalysis_2750_;
                    v_isShared_2762_ = v_isSharedCheck_2775_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_uninteresting_2759_);
                    crate::leanh::lean_inc(v_interestingMatchers_2758_);
                    crate::leanh::lean_inc(v_interestingEnums_2757_);
                    crate::leanh::lean_inc(v_interestingStructures_2756_);
                    crate::leanh::lean_dec(v_typeAnalysis_2750_);
                    v___x_2761_ = crate::leanh::lean_box(0);
                    v_isShared_2762_ = v_isSharedCheck_2775_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2763_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0;
                v___x_2764_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1;
                v___x_2765_ = crate::leanh::lean_box(0);
                v___x_2766_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_2763_,
                    v___x_2764_,
                    v_uninteresting_2759_,
                    v_n_2741_,
                    v___x_2765_,
                );
                if v_isShared_2762_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2761_, 3, v___x_2766_);
                    v___x_2768_ = v___x_2761_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2774_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2774_,
                        0,
                        v_interestingStructures_2756_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2774_,
                        1,
                        v_interestingEnums_2757_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2774_,
                        2,
                        v_interestingMatchers_2758_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2774_, 3, v___x_2766_);
                    v___x_2768_ = v_reuseFailAlloc_2774_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2755_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2754_, 2, v___x_2768_);
                    v___x_2770_ = v___x_2754_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2773_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_rewriteCache_2751_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2773_, 1, v_acNfCache_2752_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2773_, 2, v___x_2768_);
                    v___x_2770_ = v_reuseFailAlloc_2773_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2771_ = lean_st_ref_set(v_a_2743_, v___x_2770_);
                v___x_2772_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2772_, 0, v___x_2765_);
                return v___x_2772_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___boxed(
    mut v_n_2777_: *mut crate::leanh::LeanObject,
    mut v_a_2778_: *mut crate::leanh::LeanObject,
    mut v_a_2779_: *mut crate::leanh::LeanObject,
    mut v_a_2780_: *mut crate::leanh::LeanObject,
    mut v_a_2781_: *mut crate::leanh::LeanObject,
    mut v_a_2782_: *mut crate::leanh::LeanObject,
    mut v_a_2783_: *mut crate::leanh::LeanObject,
    mut v_a_2784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2785_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(
        v_n_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_,
    );
    crate::leanh::lean_dec(v_a_2783_);
    crate::leanh::lean_dec_ref(v_a_2782_);
    crate::leanh::lean_dec(v_a_2781_);
    crate::leanh::lean_dec_ref(v_a_2780_);
    crate::leanh::lean_dec(v_a_2779_);
    crate::leanh::lean_dec_ref(v_a_2778_);
    return v_res_2785_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2786_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_2786_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2787_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0,
    );
    v___x_2788_ = l_StateRefT_x27_instMonad___redArg(v___x_2787_);
    return v___x_2788_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2794_ = crate::leanh::lean_box(0);
    v___x_2795_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2796_ = lean_mk_array(v___x_2795_, v___x_2794_);
    return v___x_2796_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2797_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__7_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__7,
    );
    v___x_2798_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2799_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2799_, 0, v___x_2798_);
    crate::leanh::lean_ctor_set(v___x_2799_, 1, v___x_2797_);
    return v___x_2799_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2800_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__8_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__8,
    );
    v___x_2801_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2801_, 0, v___x_2800_);
    crate::leanh::lean_ctor_set(v___x_2801_, 1, v___x_2800_);
    crate::leanh::lean_ctor_set(v___x_2801_, 2, v___x_2800_);
    crate::leanh::lean_ctor_set(v___x_2801_, 3, v___x_2800_);
    return v___x_2801_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(
    mut v_cfg_2802_: *mut crate::leanh::LeanObject,
    mut v_goal_2803_: *mut crate::leanh::LeanObject,
    mut v_x_2804_: *mut crate::leanh::LeanObject,
    mut v_a_2805_: *mut crate::leanh::LeanObject,
    mut v_a_2806_: *mut crate::leanh::LeanObject,
    mut v_a_2807_: *mut crate::leanh::LeanObject,
    mut v_a_2808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2830_: u8 = 0;
    let mut v_toFunctor_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2837_: u8 = 0;
    let mut v___f_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664__overap_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2887_: u8 = 0;
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2892_: u8 = 0;
    let mut v_a_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2896_: u8 = 0;
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2900_: u8 = 0;
    let mut v_reuseFailAlloc_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2903_: u8 = 0;
    let mut v_unused_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2905_: u8 = 0;
    let mut v_unused_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2810_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1);
                v_toApplicative_2811_ = crate::leanh::lean_ctor_get(v___x_2810_, 0);
                v_toFunctor_2812_ = crate::leanh::lean_ctor_get(v_toApplicative_2811_, 0);
                v_toSeq_2813_ = crate::leanh::lean_ctor_get(v_toApplicative_2811_, 2);
                v_toSeqLeft_2814_ = crate::leanh::lean_ctor_get(v_toApplicative_2811_, 3);
                v_toSeqRight_2815_ = crate::leanh::lean_ctor_get(v_toApplicative_2811_, 4);
                v___f_2816_ =
                    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2;
                v___f_2817_ =
                    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_2812_, 2);
                v___f_2818_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2818_, 0, v_toFunctor_2812_);
                v___f_2819_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2819_, 0, v_toFunctor_2812_);
                v___x_2820_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2820_, 0, v___f_2818_);
                crate::leanh::lean_ctor_set(v___x_2820_, 1, v___f_2819_);
                crate::leanh::lean_inc(v_toSeqRight_2815_);
                v___f_2821_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2821_, 0, v_toSeqRight_2815_);
                crate::leanh::lean_inc(v_toSeqLeft_2814_);
                v___f_2822_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2822_, 0, v_toSeqLeft_2814_);
                crate::leanh::lean_inc(v_toSeq_2813_);
                v___f_2823_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2823_, 0, v_toSeq_2813_);
                v___x_2824_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2824_, 0, v___x_2820_);
                crate::leanh::lean_ctor_set(v___x_2824_, 1, v___f_2816_);
                crate::leanh::lean_ctor_set(v___x_2824_, 2, v___f_2823_);
                crate::leanh::lean_ctor_set(v___x_2824_, 3, v___f_2822_);
                crate::leanh::lean_ctor_set(v___x_2824_, 4, v___f_2821_);
                v___x_2825_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2825_, 0, v___x_2824_);
                crate::leanh::lean_ctor_set(v___x_2825_, 1, v___f_2817_);
                v___x_2826_ = l_StateRefT_x27_instMonad___redArg(v___x_2825_);
                v_toApplicative_2827_ = crate::leanh::lean_ctor_get(v___x_2826_, 0);
                v_isSharedCheck_2905_ = (!crate::leanh::lean_is_exclusive(v___x_2826_)) as u8;
                if v_isSharedCheck_2905_ == 0 {
                    v_unused_2906_ = crate::leanh::lean_ctor_get(v___x_2826_, 1);
                    crate::leanh::lean_dec(v_unused_2906_);
                    v___x_2829_ = v___x_2826_;
                    v_isShared_2830_ = v_isSharedCheck_2905_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_2827_);
                    crate::leanh::lean_dec(v___x_2826_);
                    v___x_2829_ = crate::leanh::lean_box(0);
                    v_isShared_2830_ = v_isSharedCheck_2905_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2831_ = crate::leanh::lean_ctor_get(v_toApplicative_2827_, 0);
                v_toSeq_2832_ = crate::leanh::lean_ctor_get(v_toApplicative_2827_, 2);
                v_toSeqLeft_2833_ = crate::leanh::lean_ctor_get(v_toApplicative_2827_, 3);
                v_toSeqRight_2834_ = crate::leanh::lean_ctor_get(v_toApplicative_2827_, 4);
                v_isSharedCheck_2903_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2827_)) as u8;
                if v_isSharedCheck_2903_ == 0 {
                    v_unused_2904_ = crate::leanh::lean_ctor_get(v_toApplicative_2827_, 1);
                    crate::leanh::lean_dec(v_unused_2904_);
                    v___x_2836_ = v_toApplicative_2827_;
                    v_isShared_2837_ = v_isSharedCheck_2903_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_2834_);
                    crate::leanh::lean_inc(v_toSeqLeft_2833_);
                    crate::leanh::lean_inc(v_toSeq_2832_);
                    crate::leanh::lean_inc(v_toFunctor_2831_);
                    crate::leanh::lean_dec(v_toApplicative_2827_);
                    v___x_2836_ = crate::leanh::lean_box(0);
                    v_isShared_2837_ = v_isSharedCheck_2903_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2838_ =
                    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__4;
                v___f_2839_ =
                    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__5;
                crate::leanh::lean_inc_ref(v_toFunctor_2831_);
                v___f_2840_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2840_, 0, v_toFunctor_2831_);
                v___f_2841_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2841_, 0, v_toFunctor_2831_);
                v___x_2842_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2842_, 0, v___f_2840_);
                crate::leanh::lean_ctor_set(v___x_2842_, 1, v___f_2841_);
                v___f_2843_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2843_, 0, v_toSeqRight_2834_);
                v___f_2844_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2844_, 0, v_toSeqLeft_2833_);
                v___f_2845_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2845_, 0, v_toSeq_2832_);
                if v_isShared_2837_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2836_, 4, v___f_2843_);
                    crate::leanh::lean_ctor_set(v___x_2836_, 3, v___f_2844_);
                    crate::leanh::lean_ctor_set(v___x_2836_, 2, v___f_2845_);
                    crate::leanh::lean_ctor_set(v___x_2836_, 1, v___f_2838_);
                    crate::leanh::lean_ctor_set(v___x_2836_, 0, v___x_2842_);
                    v___x_2847_ = v___x_2836_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2902_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2842_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2902_, 1, v___f_2838_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2902_, 2, v___f_2845_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2902_, 3, v___f_2844_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2902_, 4, v___f_2843_);
                    v___x_2847_ = v_reuseFailAlloc_2902_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2830_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2829_, 1, v___f_2839_);
                    crate::leanh::lean_ctor_set(v___x_2829_, 0, v___x_2847_);
                    v___x_2849_ = v___x_2829_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2901_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2901_, 0, v___x_2847_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2901_, 1, v___f_2839_);
                    v___x_2849_ = v_reuseFailAlloc_2901_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_toApplicative_2850_ = crate::leanh::lean_ctor_get(v___x_2810_, 0);
                v_toFunctor_2851_ = crate::leanh::lean_ctor_get(v_toApplicative_2850_, 0);
                v_toSeq_2852_ = crate::leanh::lean_ctor_get(v_toApplicative_2850_, 2);
                v_toSeqLeft_2853_ = crate::leanh::lean_ctor_get(v_toApplicative_2850_, 3);
                v_toSeqRight_2854_ = crate::leanh::lean_ctor_get(v_toApplicative_2850_, 4);
                crate::leanh::lean_inc_ref_n(v_toFunctor_2851_, 2);
                v___f_2855_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2855_, 0, v_toFunctor_2851_);
                v___f_2856_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2856_, 0, v_toFunctor_2851_);
                v___x_2857_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2857_, 0, v___f_2855_);
                crate::leanh::lean_ctor_set(v___x_2857_, 1, v___f_2856_);
                crate::leanh::lean_inc(v_toSeqRight_2854_);
                v___f_2858_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2858_, 0, v_toSeqRight_2854_);
                crate::leanh::lean_inc(v_toSeqLeft_2853_);
                v___f_2859_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2859_, 0, v_toSeqLeft_2853_);
                crate::leanh::lean_inc(v_toSeq_2852_);
                v___f_2860_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2860_, 0, v_toSeq_2852_);
                v___x_2861_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2861_, 0, v___x_2857_);
                crate::leanh::lean_ctor_set(v___x_2861_, 1, v___f_2816_);
                crate::leanh::lean_ctor_set(v___x_2861_, 2, v___f_2860_);
                crate::leanh::lean_ctor_set(v___x_2861_, 3, v___f_2859_);
                crate::leanh::lean_ctor_set(v___x_2861_, 4, v___f_2858_);
                v___x_2862_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2862_, 0, v___x_2861_);
                crate::leanh::lean_ctor_set(v___x_2862_, 1, v___f_2817_);
                v___x_2863_ = l_StateRefT_x27_instMonad___redArg(v___x_2862_);
                v___x_2864_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_pure___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_2864_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_2864_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_2864_, 2, v___x_2863_);
                v___x_2865_ = l_instMonadControlTOfPure___redArg(v___x_2864_);
                v___x_2866_ =
                    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__6;
                v___x_664__overap_2867_ = l_Lean_MVarId_withContext___redArg(
                    v___x_2865_,
                    v___x_2849_,
                    v_goal_2803_,
                    v___x_2866_,
                );
                crate::leanh::lean_inc(v_a_2808_);
                crate::leanh::lean_inc_ref(v_a_2807_);
                crate::leanh::lean_inc(v_a_2806_);
                crate::leanh::lean_inc_ref(v_a_2805_);
                v___x_2868_ = crate::leanh::lean_apply_5(
                    v___x_664__overap_2867_,
                    v_a_2805_,
                    v_a_2806_,
                    v_a_2807_,
                    v_a_2808_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_2868_) == 0 {
                    v_a_2869_ = crate::leanh::lean_ctor_get(v___x_2868_, 0);
                    crate::leanh::lean_inc(v_a_2869_);
                    crate::leanh::lean_dec_ref_known(v___x_2868_, 1);
                    v___x_2870_ = lean_array_get_size(v_a_2869_);
                    crate::leanh::lean_dec(v_a_2869_);
                    v___x_2871_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2872_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2873_ = lean_nat_mul(v___x_2870_, v___x_2872_);
                    v___x_2874_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2875_ = lean_nat_div(v___x_2873_, v___x_2874_);
                    crate::leanh::lean_dec(v___x_2873_);
                    v___x_2876_ = l_Nat_nextPowerOfTwo(v___x_2875_);
                    crate::leanh::lean_dec(v___x_2875_);
                    v___x_2877_ = crate::leanh::lean_box(0);
                    v___x_2878_ = lean_mk_array(v___x_2876_, v___x_2877_);
                    v___x_2879_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2879_, 0, v___x_2871_);
                    crate::leanh::lean_ctor_set(v___x_2879_, 1, v___x_2878_);
                    v___x_2880_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__9_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__9);
                    crate::leanh::lean_inc_ref(v___x_2879_);
                    v___x_2881_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2881_, 0, v___x_2879_);
                    crate::leanh::lean_ctor_set(v___x_2881_, 1, v___x_2879_);
                    crate::leanh::lean_ctor_set(v___x_2881_, 2, v___x_2880_);
                    v___x_2882_ = lean_st_mk_ref(v___x_2881_);
                    crate::leanh::lean_inc(v_a_2808_);
                    crate::leanh::lean_inc_ref(v_a_2807_);
                    crate::leanh::lean_inc(v_a_2806_);
                    crate::leanh::lean_inc_ref(v_a_2805_);
                    crate::leanh::lean_inc(v___x_2882_);
                    v___x_2883_ = crate::leanh::lean_apply_7(
                        v_x_2804_,
                        v_cfg_2802_,
                        v___x_2882_,
                        v_a_2805_,
                        v_a_2806_,
                        v_a_2807_,
                        v_a_2808_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_2883_) == 0 {
                        v_a_2884_ = crate::leanh::lean_ctor_get(v___x_2883_, 0);
                        v_isSharedCheck_2892_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2883_)) as u8;
                        if v_isSharedCheck_2892_ == 0 {
                            v___x_2886_ = v___x_2883_;
                            v_isShared_2887_ = v_isSharedCheck_2892_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2884_);
                            crate::leanh::lean_dec(v___x_2883_);
                            v___x_2886_ = crate::leanh::lean_box(0);
                            v_isShared_2887_ = v_isSharedCheck_2892_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2882_);
                        return v___x_2883_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_2804_);
                    crate::leanh::lean_dec_ref(v_cfg_2802_);
                    v_a_2893_ = crate::leanh::lean_ctor_get(v___x_2868_, 0);
                    v_isSharedCheck_2900_ = (!crate::leanh::lean_is_exclusive(v___x_2868_)) as u8;
                    if v_isSharedCheck_2900_ == 0 {
                        v___x_2895_ = v___x_2868_;
                        v_isShared_2896_ = v_isSharedCheck_2900_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2893_);
                        crate::leanh::lean_dec(v___x_2868_);
                        v___x_2895_ = crate::leanh::lean_box(0);
                        v_isShared_2896_ = v_isSharedCheck_2900_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v___x_2888_ = lean_st_ref_get(v___x_2882_);
                crate::leanh::lean_dec(v___x_2882_);
                crate::leanh::lean_dec(v___x_2888_);
                if v_isShared_2887_ == 0 {
                    v___x_2890_ = v___x_2886_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2891_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2884_);
                    v___x_2890_ = v_reuseFailAlloc_2891_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2890_;
            }
            7 => {
                if v_isShared_2896_ == 0 {
                    v___x_2898_ = v___x_2895_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2899_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2893_);
                    v___x_2898_ = v_reuseFailAlloc_2899_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2898_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___boxed(
    mut v_cfg_2907_: *mut crate::leanh::LeanObject,
    mut v_goal_2908_: *mut crate::leanh::LeanObject,
    mut v_x_2909_: *mut crate::leanh::LeanObject,
    mut v_a_2910_: *mut crate::leanh::LeanObject,
    mut v_a_2911_: *mut crate::leanh::LeanObject,
    mut v_a_2912_: *mut crate::leanh::LeanObject,
    mut v_a_2913_: *mut crate::leanh::LeanObject,
    mut v_a_2914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2915_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(
        v_cfg_2907_,
        v_goal_2908_,
        v_x_2909_,
        v_a_2910_,
        v_a_2911_,
        v_a_2912_,
        v_a_2913_,
    );
    crate::leanh::lean_dec(v_a_2913_);
    crate::leanh::lean_dec_ref(v_a_2912_);
    crate::leanh::lean_dec(v_a_2911_);
    crate::leanh::lean_dec_ref(v_a_2910_);
    return v_res_2915_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(
    mut v_00_u03b1_2916_: *mut crate::leanh::LeanObject,
    mut v_cfg_2917_: *mut crate::leanh::LeanObject,
    mut v_goal_2918_: *mut crate::leanh::LeanObject,
    mut v_x_2919_: *mut crate::leanh::LeanObject,
    mut v_a_2920_: *mut crate::leanh::LeanObject,
    mut v_a_2921_: *mut crate::leanh::LeanObject,
    mut v_a_2922_: *mut crate::leanh::LeanObject,
    mut v_a_2923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2945_: u8 = 0;
    let mut v_toFunctor_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2952_: u8 = 0;
    let mut v___f_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887__overap_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3002_: u8 = 0;
    let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3007_: u8 = 0;
    let mut v_a_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3011_: u8 = 0;
    let mut v___x_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3015_: u8 = 0;
    let mut v_reuseFailAlloc_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3018_: u8 = 0;
    let mut v_unused_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3020_: u8 = 0;
    let mut v_unused_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2925_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1);
                v_toApplicative_2926_ = crate::leanh::lean_ctor_get(v___x_2925_, 0);
                v_toFunctor_2927_ = crate::leanh::lean_ctor_get(v_toApplicative_2926_, 0);
                v_toSeq_2928_ = crate::leanh::lean_ctor_get(v_toApplicative_2926_, 2);
                v_toSeqLeft_2929_ = crate::leanh::lean_ctor_get(v_toApplicative_2926_, 3);
                v_toSeqRight_2930_ = crate::leanh::lean_ctor_get(v_toApplicative_2926_, 4);
                v___f_2931_ =
                    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2;
                v___f_2932_ =
                    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_2927_, 2);
                v___f_2933_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2933_, 0, v_toFunctor_2927_);
                v___f_2934_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2934_, 0, v_toFunctor_2927_);
                v___x_2935_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2935_, 0, v___f_2933_);
                crate::leanh::lean_ctor_set(v___x_2935_, 1, v___f_2934_);
                crate::leanh::lean_inc(v_toSeqRight_2930_);
                v___f_2936_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2936_, 0, v_toSeqRight_2930_);
                crate::leanh::lean_inc(v_toSeqLeft_2929_);
                v___f_2937_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2937_, 0, v_toSeqLeft_2929_);
                crate::leanh::lean_inc(v_toSeq_2928_);
                v___f_2938_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2938_, 0, v_toSeq_2928_);
                v___x_2939_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2939_, 0, v___x_2935_);
                crate::leanh::lean_ctor_set(v___x_2939_, 1, v___f_2931_);
                crate::leanh::lean_ctor_set(v___x_2939_, 2, v___f_2938_);
                crate::leanh::lean_ctor_set(v___x_2939_, 3, v___f_2937_);
                crate::leanh::lean_ctor_set(v___x_2939_, 4, v___f_2936_);
                v___x_2940_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2940_, 0, v___x_2939_);
                crate::leanh::lean_ctor_set(v___x_2940_, 1, v___f_2932_);
                v___x_2941_ = l_StateRefT_x27_instMonad___redArg(v___x_2940_);
                v_toApplicative_2942_ = crate::leanh::lean_ctor_get(v___x_2941_, 0);
                v_isSharedCheck_3020_ = (!crate::leanh::lean_is_exclusive(v___x_2941_)) as u8;
                if v_isSharedCheck_3020_ == 0 {
                    v_unused_3021_ = crate::leanh::lean_ctor_get(v___x_2941_, 1);
                    crate::leanh::lean_dec(v_unused_3021_);
                    v___x_2944_ = v___x_2941_;
                    v_isShared_2945_ = v_isSharedCheck_3020_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_2942_);
                    crate::leanh::lean_dec(v___x_2941_);
                    v___x_2944_ = crate::leanh::lean_box(0);
                    v_isShared_2945_ = v_isSharedCheck_3020_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2946_ = crate::leanh::lean_ctor_get(v_toApplicative_2942_, 0);
                v_toSeq_2947_ = crate::leanh::lean_ctor_get(v_toApplicative_2942_, 2);
                v_toSeqLeft_2948_ = crate::leanh::lean_ctor_get(v_toApplicative_2942_, 3);
                v_toSeqRight_2949_ = crate::leanh::lean_ctor_get(v_toApplicative_2942_, 4);
                v_isSharedCheck_3018_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2942_)) as u8;
                if v_isSharedCheck_3018_ == 0 {
                    v_unused_3019_ = crate::leanh::lean_ctor_get(v_toApplicative_2942_, 1);
                    crate::leanh::lean_dec(v_unused_3019_);
                    v___x_2951_ = v_toApplicative_2942_;
                    v_isShared_2952_ = v_isSharedCheck_3018_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_2949_);
                    crate::leanh::lean_inc(v_toSeqLeft_2948_);
                    crate::leanh::lean_inc(v_toSeq_2947_);
                    crate::leanh::lean_inc(v_toFunctor_2946_);
                    crate::leanh::lean_dec(v_toApplicative_2942_);
                    v___x_2951_ = crate::leanh::lean_box(0);
                    v_isShared_2952_ = v_isSharedCheck_3018_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2953_ =
                    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__4;
                v___f_2954_ =
                    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__5;
                crate::leanh::lean_inc_ref(v_toFunctor_2946_);
                v___f_2955_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2955_, 0, v_toFunctor_2946_);
                v___f_2956_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2956_, 0, v_toFunctor_2946_);
                v___x_2957_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2957_, 0, v___f_2955_);
                crate::leanh::lean_ctor_set(v___x_2957_, 1, v___f_2956_);
                v___f_2958_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2958_, 0, v_toSeqRight_2949_);
                v___f_2959_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2959_, 0, v_toSeqLeft_2948_);
                v___f_2960_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2960_, 0, v_toSeq_2947_);
                if v_isShared_2952_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2951_, 4, v___f_2958_);
                    crate::leanh::lean_ctor_set(v___x_2951_, 3, v___f_2959_);
                    crate::leanh::lean_ctor_set(v___x_2951_, 2, v___f_2960_);
                    crate::leanh::lean_ctor_set(v___x_2951_, 1, v___f_2953_);
                    crate::leanh::lean_ctor_set(v___x_2951_, 0, v___x_2957_);
                    v___x_2962_ = v___x_2951_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3017_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3017_, 0, v___x_2957_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3017_, 1, v___f_2953_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3017_, 2, v___f_2960_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3017_, 3, v___f_2959_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3017_, 4, v___f_2958_);
                    v___x_2962_ = v_reuseFailAlloc_3017_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2945_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2944_, 1, v___f_2954_);
                    crate::leanh::lean_ctor_set(v___x_2944_, 0, v___x_2962_);
                    v___x_2964_ = v___x_2944_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3016_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_2962_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3016_, 1, v___f_2954_);
                    v___x_2964_ = v_reuseFailAlloc_3016_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_toApplicative_2965_ = crate::leanh::lean_ctor_get(v___x_2925_, 0);
                v_toFunctor_2966_ = crate::leanh::lean_ctor_get(v_toApplicative_2965_, 0);
                v_toSeq_2967_ = crate::leanh::lean_ctor_get(v_toApplicative_2965_, 2);
                v_toSeqLeft_2968_ = crate::leanh::lean_ctor_get(v_toApplicative_2965_, 3);
                v_toSeqRight_2969_ = crate::leanh::lean_ctor_get(v_toApplicative_2965_, 4);
                crate::leanh::lean_inc_ref_n(v_toFunctor_2966_, 2);
                v___f_2970_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2970_, 0, v_toFunctor_2966_);
                v___f_2971_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2971_, 0, v_toFunctor_2966_);
                v___x_2972_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2972_, 0, v___f_2970_);
                crate::leanh::lean_ctor_set(v___x_2972_, 1, v___f_2971_);
                crate::leanh::lean_inc(v_toSeqRight_2969_);
                v___f_2973_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2973_, 0, v_toSeqRight_2969_);
                crate::leanh::lean_inc(v_toSeqLeft_2968_);
                v___f_2974_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2974_, 0, v_toSeqLeft_2968_);
                crate::leanh::lean_inc(v_toSeq_2967_);
                v___f_2975_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2975_, 0, v_toSeq_2967_);
                v___x_2976_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2976_, 0, v___x_2972_);
                crate::leanh::lean_ctor_set(v___x_2976_, 1, v___f_2931_);
                crate::leanh::lean_ctor_set(v___x_2976_, 2, v___f_2975_);
                crate::leanh::lean_ctor_set(v___x_2976_, 3, v___f_2974_);
                crate::leanh::lean_ctor_set(v___x_2976_, 4, v___f_2973_);
                v___x_2977_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2977_, 0, v___x_2976_);
                crate::leanh::lean_ctor_set(v___x_2977_, 1, v___f_2932_);
                v___x_2978_ = l_StateRefT_x27_instMonad___redArg(v___x_2977_);
                v___x_2979_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_pure___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_2979_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_2979_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_2979_, 2, v___x_2978_);
                v___x_2980_ = l_instMonadControlTOfPure___redArg(v___x_2979_);
                v___x_2981_ =
                    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__6;
                v___x_887__overap_2982_ = l_Lean_MVarId_withContext___redArg(
                    v___x_2980_,
                    v___x_2964_,
                    v_goal_2918_,
                    v___x_2981_,
                );
                crate::leanh::lean_inc(v_a_2923_);
                crate::leanh::lean_inc_ref(v_a_2922_);
                crate::leanh::lean_inc(v_a_2921_);
                crate::leanh::lean_inc_ref(v_a_2920_);
                v___x_2983_ = crate::leanh::lean_apply_5(
                    v___x_887__overap_2982_,
                    v_a_2920_,
                    v_a_2921_,
                    v_a_2922_,
                    v_a_2923_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_2983_) == 0 {
                    v_a_2984_ = crate::leanh::lean_ctor_get(v___x_2983_, 0);
                    crate::leanh::lean_inc(v_a_2984_);
                    crate::leanh::lean_dec_ref_known(v___x_2983_, 1);
                    v___x_2985_ = lean_array_get_size(v_a_2984_);
                    crate::leanh::lean_dec(v_a_2984_);
                    v___x_2986_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2987_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2988_ = lean_nat_mul(v___x_2985_, v___x_2987_);
                    v___x_2989_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2990_ = lean_nat_div(v___x_2988_, v___x_2989_);
                    crate::leanh::lean_dec(v___x_2988_);
                    v___x_2991_ = l_Nat_nextPowerOfTwo(v___x_2990_);
                    crate::leanh::lean_dec(v___x_2990_);
                    v___x_2992_ = crate::leanh::lean_box(0);
                    v___x_2993_ = lean_mk_array(v___x_2991_, v___x_2992_);
                    v___x_2994_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2994_, 0, v___x_2986_);
                    crate::leanh::lean_ctor_set(v___x_2994_, 1, v___x_2993_);
                    v___x_2995_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__9_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__9);
                    crate::leanh::lean_inc_ref(v___x_2994_);
                    v___x_2996_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2996_, 0, v___x_2994_);
                    crate::leanh::lean_ctor_set(v___x_2996_, 1, v___x_2994_);
                    crate::leanh::lean_ctor_set(v___x_2996_, 2, v___x_2995_);
                    v___x_2997_ = lean_st_mk_ref(v___x_2996_);
                    crate::leanh::lean_inc(v_a_2923_);
                    crate::leanh::lean_inc_ref(v_a_2922_);
                    crate::leanh::lean_inc(v_a_2921_);
                    crate::leanh::lean_inc_ref(v_a_2920_);
                    crate::leanh::lean_inc(v___x_2997_);
                    v___x_2998_ = crate::leanh::lean_apply_7(
                        v_x_2919_,
                        v_cfg_2917_,
                        v___x_2997_,
                        v_a_2920_,
                        v_a_2921_,
                        v_a_2922_,
                        v_a_2923_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_2998_) == 0 {
                        v_a_2999_ = crate::leanh::lean_ctor_get(v___x_2998_, 0);
                        v_isSharedCheck_3007_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2998_)) as u8;
                        if v_isSharedCheck_3007_ == 0 {
                            v___x_3001_ = v___x_2998_;
                            v_isShared_3002_ = v_isSharedCheck_3007_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2999_);
                            crate::leanh::lean_dec(v___x_2998_);
                            v___x_3001_ = crate::leanh::lean_box(0);
                            v_isShared_3002_ = v_isSharedCheck_3007_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2997_);
                        return v___x_2998_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_2919_);
                    crate::leanh::lean_dec_ref(v_cfg_2917_);
                    v_a_3008_ = crate::leanh::lean_ctor_get(v___x_2983_, 0);
                    v_isSharedCheck_3015_ = (!crate::leanh::lean_is_exclusive(v___x_2983_)) as u8;
                    if v_isSharedCheck_3015_ == 0 {
                        v___x_3010_ = v___x_2983_;
                        v_isShared_3011_ = v_isSharedCheck_3015_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3008_);
                        crate::leanh::lean_dec(v___x_2983_);
                        v___x_3010_ = crate::leanh::lean_box(0);
                        v_isShared_3011_ = v_isSharedCheck_3015_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v___x_3003_ = lean_st_ref_get(v___x_2997_);
                crate::leanh::lean_dec(v___x_2997_);
                crate::leanh::lean_dec(v___x_3003_);
                if v_isShared_3002_ == 0 {
                    v___x_3005_ = v___x_3001_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3006_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_a_2999_);
                    v___x_3005_ = v_reuseFailAlloc_3006_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3005_;
            }
            7 => {
                if v_isShared_3011_ == 0 {
                    v___x_3013_ = v___x_3010_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3014_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_a_3008_);
                    v___x_3013_ = v_reuseFailAlloc_3014_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3013_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___boxed(
    mut v_00_u03b1_3022_: *mut crate::leanh::LeanObject,
    mut v_cfg_3023_: *mut crate::leanh::LeanObject,
    mut v_goal_3024_: *mut crate::leanh::LeanObject,
    mut v_x_3025_: *mut crate::leanh::LeanObject,
    mut v_a_3026_: *mut crate::leanh::LeanObject,
    mut v_a_3027_: *mut crate::leanh::LeanObject,
    mut v_a_3028_: *mut crate::leanh::LeanObject,
    mut v_a_3029_: *mut crate::leanh::LeanObject,
    mut v_a_3030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3031_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(
        v_00_u03b1_3022_,
        v_cfg_3023_,
        v_goal_3024_,
        v_x_3025_,
        v_a_3026_,
        v_a_3027_,
        v_a_3028_,
        v_a_3029_,
    );
    crate::leanh::lean_dec(v_a_3029_);
    crate::leanh::lean_dec_ref(v_a_3028_);
    crate::leanh::lean_dec(v_a_3027_);
    crate::leanh::lean_dec_ref(v_a_3026_);
    return v_res_3031_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3033_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0;
    v___x_3034_ = l_Lean_stringToMessageData(v___x_3033_);
    return v___x_3034_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3036_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__2;
    v___x_3037_ = l_Lean_stringToMessageData(v___x_3036_);
    return v___x_3037_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(
    mut v_name_3038_: *mut crate::leanh::LeanObject,
    mut v_goal_3039_: *mut crate::leanh::LeanObject,
    mut v_x_3040_: *mut crate::leanh::LeanObject,
    mut v___y_3041_: *mut crate::leanh::LeanObject,
    mut v___y_3042_: *mut crate::leanh::LeanObject,
    mut v___y_3043_: *mut crate::leanh::LeanObject,
    mut v___y_3044_: *mut crate::leanh::LeanObject,
    mut v___y_3045_: *mut crate::leanh::LeanObject,
    mut v___y_3046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3048_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1,
    );
    v___x_3049_ = l_Lean_MessageData_ofName(v_name_3038_);
    v___x_3050_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3050_, 0, v___x_3048_);
    crate::leanh::lean_ctor_set(v___x_3050_, 1, v___x_3049_);
    v___x_3051_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__3_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__3,
    );
    v___x_3052_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3052_, 0, v___x_3050_);
    crate::leanh::lean_ctor_set(v___x_3052_, 1, v___x_3051_);
    v___x_3053_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3053_, 0, v_goal_3039_);
    v___x_3054_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3054_, 0, v___x_3052_);
    crate::leanh::lean_ctor_set(v___x_3054_, 1, v___x_3053_);
    v___x_3055_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3055_, 0, v___x_3054_);
    return v___x_3055_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed(
    mut v_name_3056_: *mut crate::leanh::LeanObject,
    mut v_goal_3057_: *mut crate::leanh::LeanObject,
    mut v_x_3058_: *mut crate::leanh::LeanObject,
    mut v___y_3059_: *mut crate::leanh::LeanObject,
    mut v___y_3060_: *mut crate::leanh::LeanObject,
    mut v___y_3061_: *mut crate::leanh::LeanObject,
    mut v___y_3062_: *mut crate::leanh::LeanObject,
    mut v___y_3063_: *mut crate::leanh::LeanObject,
    mut v___y_3064_: *mut crate::leanh::LeanObject,
    mut v___y_3065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3066_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(
        v_name_3056_,
        v_goal_3057_,
        v_x_3058_,
        v___y_3059_,
        v___y_3060_,
        v___y_3061_,
        v___y_3062_,
        v___y_3063_,
        v___y_3064_,
    );
    crate::leanh::lean_dec(v___y_3064_);
    crate::leanh::lean_dec_ref(v___y_3063_);
    crate::leanh::lean_dec(v___y_3062_);
    crate::leanh::lean_dec_ref(v___y_3061_);
    crate::leanh::lean_dec(v___y_3060_);
    crate::leanh::lean_dec_ref(v___y_3059_);
    crate::leanh::lean_dec_ref(v_x_3058_);
    return v_res_3066_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3069_ = l_Lean_Core_instMonadTraceCoreM;
    v___x_3070_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1;
    v___x_3071_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_3070_, v___x_3069_);
    return v___x_3071_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3072_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2_once),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2,
    );
    v___f_3073_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0;
    v___x_3074_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_3073_, v___x_3072_);
    return v___x_3074_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3075_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3_once),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3,
    );
    v___x_3076_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1;
    v___x_3077_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_3076_, v___x_3075_);
    return v___x_3077_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3078_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4_once),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4,
    );
    v___f_3079_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0;
    v___x_3080_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_3079_, v___x_3078_);
    return v___x_3080_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3083_ = l_Lean_Core_instMonadQuotationCoreM;
    v___x_3084_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1;
    v___x_3085_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7;
    v___x_3086_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v___x_3085_,
        v___x_3084_,
        v___x_3083_,
    );
    return v___x_3086_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3087_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8_once),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8,
    );
    v___f_3088_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0;
    v___f_3089_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6;
    v___x_3090_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v___f_3089_,
        v___f_3088_,
        v___x_3087_,
    );
    return v___x_3090_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3091_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9_once),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9,
    );
    v___x_3092_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1;
    v___x_3093_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7;
    v___x_3094_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v___x_3093_,
        v___x_3092_,
        v___x_3091_,
    );
    return v___x_3094_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3095_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10_once),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10,
    );
    v___f_3096_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0;
    v___f_3097_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6;
    v___x_3098_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v___f_3097_,
        v___f_3096_,
        v___x_3095_,
    );
    return v___x_3098_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3099_ = l_instMonadExceptOfEIO(crate::leanh::lean_box(0));
    return v___x_3099_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3100_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12_once),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12,
    );
    v___x_3101_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_3100_);
    return v___x_3101_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3102_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13_once),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13,
    );
    v___x_3103_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_3102_);
    return v___x_3103_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3104_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__14_once),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__14,
    );
    v___x_3105_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_3104_);
    return v___x_3105_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3106_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__15_once),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__15,
    );
    v___x_3107_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_3106_);
    return v___x_3107_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3108_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__16_once),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__16,
    );
    v___x_3109_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_3108_);
    return v___x_3109_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3110_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__17_once),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__17,
    );
    v___x_3111_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_3110_);
    return v___x_3111_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3112_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1;
    v___x_3113_ = l_Lean_Meta_instAddMessageContextMetaM;
    v___f_3114_ = crate::leanh::lean_alloc_closure(
        l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3114_, 0, v___x_3113_);
    crate::leanh::lean_closure_set(v___f_3114_, 1, v___x_3112_);
    return v___f_3114_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___f_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3115_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0;
    v___f_3116_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__19_once),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__19,
    );
    v___f_3117_ = crate::leanh::lean_alloc_closure(
        l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3117_, 0, v___f_3116_);
    crate::leanh::lean_closure_set(v___f_3117_, 1, v___f_3115_);
    return v___f_3117_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3130_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25;
    v___x_3131_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__28;
    v___x_3132_ = l_Lean_Name_append(v___x_3131_, v___x_3130_);
    return v___x_3132_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30() -> f64 {
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: f64 = 0.0;
    v___x_3133_ = crate::leanh::lean_unsigned_to_nat(1000000000);
    v___x_3134_ = lean_float_of_nat(v___x_3133_);
    return v___x_3134_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(
    mut v_pass_3135_: *mut crate::leanh::LeanObject,
    mut v_goal_3136_: *mut crate::leanh::LeanObject,
    mut v_a_3137_: *mut crate::leanh::LeanObject,
    mut v_a_3138_: *mut crate::leanh::LeanObject,
    mut v_a_3139_: *mut crate::leanh::LeanObject,
    mut v_a_3140_: *mut crate::leanh::LeanObject,
    mut v_a_3141_: *mut crate::leanh::LeanObject,
    mut v_a_3142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3164_: u8 = 0;
    let mut v_toFunctor_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3171_: u8 = 0;
    let mut v___f_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadRef_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3191_: u8 = 0;
    let mut v_run_x27_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_run_x27_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3198_: u8 = 0;
    let mut v_inheritedTraceOptions_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: u8 = 0;
    let mut v___y_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: f64 = 0.0;
    let mut v___x_3213_: f64 = 0.0;
    let mut v___x_3214_: f64 = 0.0;
    let mut v___x_3215_: f64 = 0.0;
    let mut v___x_3216_: f64 = 0.0;
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9546__overap_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: f64 = 0.0;
    let mut v___x_3231_: f64 = 0.0;
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9567__overap_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9523__overap_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: u8 = 0;
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3251_: u8 = 0;
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3255_: u8 = 0;
    let mut v_a_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3259_: u8 = 0;
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3263_: u8 = 0;
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3269_: u8 = 0;
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3273_: u8 = 0;
    let mut v_a_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3277_: u8 = 0;
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3281_: u8 = 0;
    let mut v_a_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3285_: u8 = 0;
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3289_: u8 = 0;
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: u8 = 0;
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3295_: u8 = 0;
    let mut v_reuseFailAlloc_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3298_: u8 = 0;
    let mut v_unused_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3300_: u8 = 0;
    let mut v_unused_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3144_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1);
                v_toApplicative_3145_ = crate::leanh::lean_ctor_get(v___x_3144_, 0);
                v_toFunctor_3146_ = crate::leanh::lean_ctor_get(v_toApplicative_3145_, 0);
                v_toSeq_3147_ = crate::leanh::lean_ctor_get(v_toApplicative_3145_, 2);
                v_toSeqLeft_3148_ = crate::leanh::lean_ctor_get(v_toApplicative_3145_, 3);
                v_toSeqRight_3149_ = crate::leanh::lean_ctor_get(v_toApplicative_3145_, 4);
                v___f_3150_ =
                    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2;
                v___f_3151_ =
                    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_3146_, 2);
                v___f_3152_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3152_, 0, v_toFunctor_3146_);
                v___f_3153_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3153_, 0, v_toFunctor_3146_);
                v___x_3154_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3154_, 0, v___f_3152_);
                crate::leanh::lean_ctor_set(v___x_3154_, 1, v___f_3153_);
                crate::leanh::lean_inc(v_toSeqRight_3149_);
                v___f_3155_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3155_, 0, v_toSeqRight_3149_);
                crate::leanh::lean_inc(v_toSeqLeft_3148_);
                v___f_3156_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3156_, 0, v_toSeqLeft_3148_);
                crate::leanh::lean_inc(v_toSeq_3147_);
                v___f_3157_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3157_, 0, v_toSeq_3147_);
                v___x_3158_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3158_, 0, v___x_3154_);
                crate::leanh::lean_ctor_set(v___x_3158_, 1, v___f_3150_);
                crate::leanh::lean_ctor_set(v___x_3158_, 2, v___f_3157_);
                crate::leanh::lean_ctor_set(v___x_3158_, 3, v___f_3156_);
                crate::leanh::lean_ctor_set(v___x_3158_, 4, v___f_3155_);
                v___x_3159_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3159_, 0, v___x_3158_);
                crate::leanh::lean_ctor_set(v___x_3159_, 1, v___f_3151_);
                v___x_3160_ = l_StateRefT_x27_instMonad___redArg(v___x_3159_);
                v_toApplicative_3161_ = crate::leanh::lean_ctor_get(v___x_3160_, 0);
                v_isSharedCheck_3300_ = (!crate::leanh::lean_is_exclusive(v___x_3160_)) as u8;
                if v_isSharedCheck_3300_ == 0 {
                    v_unused_3301_ = crate::leanh::lean_ctor_get(v___x_3160_, 1);
                    crate::leanh::lean_dec(v_unused_3301_);
                    v___x_3163_ = v___x_3160_;
                    v_isShared_3164_ = v_isSharedCheck_3300_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_3161_);
                    crate::leanh::lean_dec(v___x_3160_);
                    v___x_3163_ = crate::leanh::lean_box(0);
                    v_isShared_3164_ = v_isSharedCheck_3300_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_3165_ = crate::leanh::lean_ctor_get(v_toApplicative_3161_, 0);
                v_toSeq_3166_ = crate::leanh::lean_ctor_get(v_toApplicative_3161_, 2);
                v_toSeqLeft_3167_ = crate::leanh::lean_ctor_get(v_toApplicative_3161_, 3);
                v_toSeqRight_3168_ = crate::leanh::lean_ctor_get(v_toApplicative_3161_, 4);
                v_isSharedCheck_3298_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_3161_)) as u8;
                if v_isSharedCheck_3298_ == 0 {
                    v_unused_3299_ = crate::leanh::lean_ctor_get(v_toApplicative_3161_, 1);
                    crate::leanh::lean_dec(v_unused_3299_);
                    v___x_3170_ = v_toApplicative_3161_;
                    v_isShared_3171_ = v_isSharedCheck_3298_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_3168_);
                    crate::leanh::lean_inc(v_toSeqLeft_3167_);
                    crate::leanh::lean_inc(v_toSeq_3166_);
                    crate::leanh::lean_inc(v_toFunctor_3165_);
                    crate::leanh::lean_dec(v_toApplicative_3161_);
                    v___x_3170_ = crate::leanh::lean_box(0);
                    v_isShared_3171_ = v_isSharedCheck_3298_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_3172_ =
                    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__4;
                v___f_3173_ =
                    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__5;
                crate::leanh::lean_inc_ref(v_toFunctor_3165_);
                v___f_3174_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3174_, 0, v_toFunctor_3165_);
                v___f_3175_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3175_, 0, v_toFunctor_3165_);
                v___x_3176_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3176_, 0, v___f_3174_);
                crate::leanh::lean_ctor_set(v___x_3176_, 1, v___f_3175_);
                v___f_3177_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3177_, 0, v_toSeqRight_3168_);
                v___f_3178_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3178_, 0, v_toSeqLeft_3167_);
                v___f_3179_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3179_, 0, v_toSeq_3166_);
                if v_isShared_3171_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3170_, 4, v___f_3177_);
                    crate::leanh::lean_ctor_set(v___x_3170_, 3, v___f_3178_);
                    crate::leanh::lean_ctor_set(v___x_3170_, 2, v___f_3179_);
                    crate::leanh::lean_ctor_set(v___x_3170_, 1, v___f_3172_);
                    crate::leanh::lean_ctor_set(v___x_3170_, 0, v___x_3176_);
                    v___x_3181_ = v___x_3170_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3297_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3297_, 0, v___x_3176_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3297_, 1, v___f_3172_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3297_, 2, v___f_3179_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3297_, 3, v___f_3178_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3297_, 4, v___f_3177_);
                    v___x_3181_ = v_reuseFailAlloc_3297_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3164_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3163_, 1, v___f_3173_);
                    crate::leanh::lean_ctor_set(v___x_3163_, 0, v___x_3181_);
                    v___x_3183_ = v___x_3163_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3296_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___x_3181_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 1, v___f_3173_);
                    v___x_3183_ = v_reuseFailAlloc_3296_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3184_ = l_StateRefT_x27_instMonad___redArg(v___x_3183_);
                v___x_3185_ = l_ReaderT_instMonad___redArg(v___x_3184_);
                v___x_3186_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5,
                );
                v___x_3187_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11,
                );
                v_toMonadRef_3188_ = crate::leanh::lean_ctor_get(v___x_3187_, 0);
                v___x_3189_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__18
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__18_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__18,
                );
                v_options_3190_ = crate::leanh::lean_ctor_get(v_a_3141_, 2);
                v_hasTrace_3191_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_3190_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_3191_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3185_);
                    v_run_x27_3192_ = crate::leanh::lean_ctor_get(v_pass_3135_, 1);
                    crate::leanh::lean_inc_ref(v_run_x27_3192_);
                    crate::leanh::lean_dec_ref(v_pass_3135_);
                    crate::leanh::lean_inc(v_a_3142_);
                    crate::leanh::lean_inc_ref(v_a_3141_);
                    crate::leanh::lean_inc(v_a_3140_);
                    crate::leanh::lean_inc_ref(v_a_3139_);
                    crate::leanh::lean_inc(v_a_3138_);
                    crate::leanh::lean_inc_ref(v_a_3137_);
                    v___x_3193_ = crate::leanh::lean_apply_8(
                        v_run_x27_3192_,
                        v_goal_3136_,
                        v_a_3137_,
                        v_a_3138_,
                        v_a_3139_,
                        v_a_3140_,
                        v_a_3141_,
                        v_a_3142_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_3193_;
                } else {
                    v_name_3194_ = crate::leanh::lean_ctor_get(v_pass_3135_, 0);
                    v_run_x27_3195_ = crate::leanh::lean_ctor_get(v_pass_3135_, 1);
                    v_isSharedCheck_3295_ = (!crate::leanh::lean_is_exclusive(v_pass_3135_)) as u8;
                    if v_isSharedCheck_3295_ == 0 {
                        v___x_3197_ = v_pass_3135_;
                        v_isShared_3198_ = v_isSharedCheck_3295_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_run_x27_3195_);
                        crate::leanh::lean_inc(v_name_3194_);
                        crate::leanh::lean_dec(v_pass_3135_);
                        v___x_3197_ = crate::leanh::lean_box(0);
                        v_isShared_3198_ = v_isSharedCheck_3295_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v_inheritedTraceOptions_3199_ = crate::leanh::lean_ctor_get(v_a_3141_, 13);
                crate::leanh::lean_inc(v_goal_3136_);
                v___f_3200_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed
                        as *mut core::ffi::c_void,
                    10,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3200_, 0, v_name_3194_);
                crate::leanh::lean_closure_set(v___f_3200_, 1, v_goal_3136_);
                v___f_3201_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__20
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__20_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__20,
                );
                v___f_3202_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__21;
                v___x_3203_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25;
                v___x_3204_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__26;
                v___x_3205_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29,
                );
                v___x_3206_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                    v_inheritedTraceOptions_3199_,
                    v_options_3190_,
                    v___x_3205_,
                );
                if v___x_3206_ == 0 {
                    v___x_3290_ = l_Lean_KVMap_instValueBool;
                    v___x_3291_ = l_Lean_trace_profiler;
                    v___x_3292_ =
                        l_Lean_Option_get___redArg(v___x_3290_, v_options_3190_, v___x_3291_);
                    v___x_3293_ = (crate::leanh::lean_unbox(v___x_3292_) as u8);
                    crate::leanh::lean_dec(v___x_3292_);
                    if v___x_3293_ == 0 {
                        crate::leanh::lean_dec_ref(v___f_3200_);
                        crate::leanh::lean_del_object(v___x_3197_);
                        crate::leanh::lean_dec_ref(v___x_3185_);
                        crate::leanh::lean_inc(v_a_3142_);
                        crate::leanh::lean_inc_ref(v_a_3141_);
                        crate::leanh::lean_inc(v_a_3140_);
                        crate::leanh::lean_inc_ref(v_a_3139_);
                        crate::leanh::lean_inc(v_a_3138_);
                        crate::leanh::lean_inc_ref(v_a_3137_);
                        v___x_3294_ = crate::leanh::lean_apply_8(
                            v_run_x27_3195_,
                            v_goal_3136_,
                            v_a_3137_,
                            v_a_3138_,
                            v_a_3139_,
                            v_a_3140_,
                            v_a_3141_,
                            v_a_3142_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_3294_;
                    } else {
                        state = 9;
                        continue;
                    }
                } else {
                    state = 9;
                    continue;
                }
            }
            6 => {
                v___x_3211_ = lean_io_mono_nanos_now();
                v___x_3212_ = lean_float_of_nat(v___y_3208_);
                v___x_3213_ = crate::leanh::lean_float_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30,
                );
                v___x_3214_ = lean_float_div(v___x_3212_, v___x_3213_);
                v___x_3215_ = lean_float_of_nat(v___x_3211_);
                v___x_3216_ = lean_float_div(v___x_3215_, v___x_3213_);
                v___x_3217_ = crate::leanh::lean_box_float(v___x_3214_);
                v___x_3218_ = crate::leanh::lean_box_float(v___x_3216_);
                if v_isShared_3198_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3197_, 1, v___x_3218_);
                    crate::leanh::lean_ctor_set(v___x_3197_, 0, v___x_3217_);
                    v___x_3220_ = v___x_3197_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3224_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3217_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3224_, 1, v___x_3218_);
                    v___x_3220_ = v_reuseFailAlloc_3224_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3221_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3221_, 0, v_a_3210_);
                crate::leanh::lean_ctor_set(v___x_3221_, 1, v___x_3220_);
                crate::leanh::lean_inc_ref(v_toMonadRef_3188_);
                v___x_9546__overap_3222_ =
                    l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_3185_,
                        v___x_3186_,
                        v_toMonadRef_3188_,
                        v___f_3201_,
                        crate::leanh::lean_box(0),
                        v___x_3189_,
                        v___f_3202_,
                        v___x_3203_,
                        v_hasTrace_3191_,
                        v___x_3204_,
                        v_options_3190_,
                        v___x_3206_,
                        v___y_3209_,
                        v___f_3200_,
                        v___x_3221_,
                    );
                crate::leanh::lean_inc(v_a_3142_);
                crate::leanh::lean_inc_ref(v_a_3141_);
                crate::leanh::lean_inc(v_a_3140_);
                crate::leanh::lean_inc_ref(v_a_3139_);
                crate::leanh::lean_inc(v_a_3138_);
                crate::leanh::lean_inc_ref(v_a_3137_);
                v___x_3223_ = crate::leanh::lean_apply_7(
                    v___x_9546__overap_3222_,
                    v_a_3137_,
                    v_a_3138_,
                    v_a_3139_,
                    v_a_3140_,
                    v_a_3141_,
                    v_a_3142_,
                    crate::leanh::lean_box(0),
                );
                return v___x_3223_;
            }
            8 => {
                v___x_3229_ = lean_io_get_num_heartbeats();
                v___x_3230_ = lean_float_of_nat(v___y_3226_);
                v___x_3231_ = lean_float_of_nat(v___x_3229_);
                v___x_3232_ = crate::leanh::lean_box_float(v___x_3230_);
                v___x_3233_ = crate::leanh::lean_box_float(v___x_3231_);
                v___x_3234_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3234_, 0, v___x_3232_);
                crate::leanh::lean_ctor_set(v___x_3234_, 1, v___x_3233_);
                v___x_3235_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3235_, 0, v_a_3228_);
                crate::leanh::lean_ctor_set(v___x_3235_, 1, v___x_3234_);
                crate::leanh::lean_inc_ref(v_toMonadRef_3188_);
                v___x_9567__overap_3236_ =
                    l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_3185_,
                        v___x_3186_,
                        v_toMonadRef_3188_,
                        v___f_3201_,
                        crate::leanh::lean_box(0),
                        v___x_3189_,
                        v___f_3202_,
                        v___x_3203_,
                        v_hasTrace_3191_,
                        v___x_3204_,
                        v_options_3190_,
                        v___x_3206_,
                        v___y_3227_,
                        v___f_3200_,
                        v___x_3235_,
                    );
                crate::leanh::lean_inc(v_a_3142_);
                crate::leanh::lean_inc_ref(v_a_3141_);
                crate::leanh::lean_inc(v_a_3140_);
                crate::leanh::lean_inc_ref(v_a_3139_);
                crate::leanh::lean_inc(v_a_3138_);
                crate::leanh::lean_inc_ref(v_a_3137_);
                v___x_3237_ = crate::leanh::lean_apply_7(
                    v___x_9567__overap_3236_,
                    v_a_3137_,
                    v_a_3138_,
                    v_a_3139_,
                    v_a_3140_,
                    v_a_3141_,
                    v_a_3142_,
                    crate::leanh::lean_box(0),
                );
                return v___x_3237_;
            }
            9 => {
                crate::leanh::lean_inc_ref(v___x_3185_);
                v___x_9523__overap_3239_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(
                    crate::leanh::lean_box(0),
                    v___x_3185_,
                    v___x_3186_,
                );
                crate::leanh::lean_inc(v_a_3142_);
                crate::leanh::lean_inc_ref(v_a_3141_);
                crate::leanh::lean_inc(v_a_3140_);
                crate::leanh::lean_inc_ref(v_a_3139_);
                crate::leanh::lean_inc(v_a_3138_);
                crate::leanh::lean_inc_ref(v_a_3137_);
                v___x_3240_ = crate::leanh::lean_apply_7(
                    v___x_9523__overap_3239_,
                    v_a_3137_,
                    v_a_3138_,
                    v_a_3139_,
                    v_a_3140_,
                    v_a_3141_,
                    v_a_3142_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_3240_) == 0 {
                    v_a_3241_ = crate::leanh::lean_ctor_get(v___x_3240_, 0);
                    crate::leanh::lean_inc(v_a_3241_);
                    crate::leanh::lean_dec_ref_known(v___x_3240_, 1);
                    v___x_3242_ = l_Lean_KVMap_instValueBool;
                    v___x_3243_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_3244_ =
                        l_Lean_Option_get___redArg(v___x_3242_, v_options_3190_, v___x_3243_);
                    v___x_3245_ = (crate::leanh::lean_unbox(v___x_3244_) as u8);
                    crate::leanh::lean_dec(v___x_3244_);
                    if v___x_3245_ == 0 {
                        v___x_3246_ = lean_io_mono_nanos_now();
                        crate::leanh::lean_inc(v_a_3142_);
                        crate::leanh::lean_inc_ref(v_a_3141_);
                        crate::leanh::lean_inc(v_a_3140_);
                        crate::leanh::lean_inc_ref(v_a_3139_);
                        crate::leanh::lean_inc(v_a_3138_);
                        crate::leanh::lean_inc_ref(v_a_3137_);
                        v___x_3247_ = crate::leanh::lean_apply_8(
                            v_run_x27_3195_,
                            v_goal_3136_,
                            v_a_3137_,
                            v_a_3138_,
                            v_a_3139_,
                            v_a_3140_,
                            v_a_3141_,
                            v_a_3142_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_3247_) == 0 {
                            v_a_3248_ = crate::leanh::lean_ctor_get(v___x_3247_, 0);
                            v_isSharedCheck_3255_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3247_)) as u8;
                            if v_isSharedCheck_3255_ == 0 {
                                v___x_3250_ = v___x_3247_;
                                v_isShared_3251_ = v_isSharedCheck_3255_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3248_);
                                crate::leanh::lean_dec(v___x_3247_);
                                v___x_3250_ = crate::leanh::lean_box(0);
                                v_isShared_3251_ = v_isSharedCheck_3255_;
                                state = 10;
                                continue;
                            }
                        } else {
                            v_a_3256_ = crate::leanh::lean_ctor_get(v___x_3247_, 0);
                            v_isSharedCheck_3263_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3247_)) as u8;
                            if v_isSharedCheck_3263_ == 0 {
                                v___x_3258_ = v___x_3247_;
                                v_isShared_3259_ = v_isSharedCheck_3263_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3256_);
                                crate::leanh::lean_dec(v___x_3247_);
                                v___x_3258_ = crate::leanh::lean_box(0);
                                v_isShared_3259_ = v_isSharedCheck_3263_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3197_);
                        v___x_3264_ = lean_io_get_num_heartbeats();
                        crate::leanh::lean_inc(v_a_3142_);
                        crate::leanh::lean_inc_ref(v_a_3141_);
                        crate::leanh::lean_inc(v_a_3140_);
                        crate::leanh::lean_inc_ref(v_a_3139_);
                        crate::leanh::lean_inc(v_a_3138_);
                        crate::leanh::lean_inc_ref(v_a_3137_);
                        v___x_3265_ = crate::leanh::lean_apply_8(
                            v_run_x27_3195_,
                            v_goal_3136_,
                            v_a_3137_,
                            v_a_3138_,
                            v_a_3139_,
                            v_a_3140_,
                            v_a_3141_,
                            v_a_3142_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_3265_) == 0 {
                            v_a_3266_ = crate::leanh::lean_ctor_get(v___x_3265_, 0);
                            v_isSharedCheck_3273_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3265_)) as u8;
                            if v_isSharedCheck_3273_ == 0 {
                                v___x_3268_ = v___x_3265_;
                                v_isShared_3269_ = v_isSharedCheck_3273_;
                                state = 14;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3266_);
                                crate::leanh::lean_dec(v___x_3265_);
                                v___x_3268_ = crate::leanh::lean_box(0);
                                v_isShared_3269_ = v_isSharedCheck_3273_;
                                state = 14;
                                continue;
                            }
                        } else {
                            v_a_3274_ = crate::leanh::lean_ctor_get(v___x_3265_, 0);
                            v_isSharedCheck_3281_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3265_)) as u8;
                            if v_isSharedCheck_3281_ == 0 {
                                v___x_3276_ = v___x_3265_;
                                v_isShared_3277_ = v_isSharedCheck_3281_;
                                state = 16;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3274_);
                                crate::leanh::lean_dec(v___x_3265_);
                                v___x_3276_ = crate::leanh::lean_box(0);
                                v_isShared_3277_ = v_isSharedCheck_3281_;
                                state = 16;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_3200_);
                    crate::leanh::lean_del_object(v___x_3197_);
                    crate::leanh::lean_dec_ref(v_run_x27_3195_);
                    crate::leanh::lean_dec_ref(v___x_3185_);
                    crate::leanh::lean_dec(v_goal_3136_);
                    v_a_3282_ = crate::leanh::lean_ctor_get(v___x_3240_, 0);
                    v_isSharedCheck_3289_ = (!crate::leanh::lean_is_exclusive(v___x_3240_)) as u8;
                    if v_isSharedCheck_3289_ == 0 {
                        v___x_3284_ = v___x_3240_;
                        v_isShared_3285_ = v_isSharedCheck_3289_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3282_);
                        crate::leanh::lean_dec(v___x_3240_);
                        v___x_3284_ = crate::leanh::lean_box(0);
                        v_isShared_3285_ = v_isSharedCheck_3289_;
                        state = 18;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_3251_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3250_, 1);
                    v___x_3253_ = v___x_3250_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3254_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
                    v___x_3253_ = v_reuseFailAlloc_3254_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___y_3208_ = v___x_3246_;
                v___y_3209_ = v_a_3241_;
                v_a_3210_ = v___x_3253_;
                state = 6;
                continue;
            }
            12 => {
                if v_isShared_3259_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3258_, 0);
                    v___x_3261_ = v___x_3258_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3262_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3256_);
                    v___x_3261_ = v_reuseFailAlloc_3262_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___y_3208_ = v___x_3246_;
                v___y_3209_ = v_a_3241_;
                v_a_3210_ = v___x_3261_;
                state = 6;
                continue;
            }
            14 => {
                if v_isShared_3269_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3268_, 1);
                    v___x_3271_ = v___x_3268_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3272_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3266_);
                    v___x_3271_ = v_reuseFailAlloc_3272_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___y_3226_ = v___x_3264_;
                v___y_3227_ = v_a_3241_;
                v_a_3228_ = v___x_3271_;
                state = 8;
                continue;
            }
            16 => {
                if v_isShared_3277_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3276_, 0);
                    v___x_3279_ = v___x_3276_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3280_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3274_);
                    v___x_3279_ = v_reuseFailAlloc_3280_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___y_3226_ = v___x_3264_;
                v___y_3227_ = v_a_3241_;
                v_a_3228_ = v___x_3279_;
                state = 8;
                continue;
            }
            18 => {
                if v_isShared_3285_ == 0 {
                    v___x_3287_ = v___x_3284_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3288_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_a_3282_);
                    v___x_3287_ = v_reuseFailAlloc_3288_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3287_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___boxed(
    mut v_pass_3302_: *mut crate::leanh::LeanObject,
    mut v_goal_3303_: *mut crate::leanh::LeanObject,
    mut v_a_3304_: *mut crate::leanh::LeanObject,
    mut v_a_3305_: *mut crate::leanh::LeanObject,
    mut v_a_3306_: *mut crate::leanh::LeanObject,
    mut v_a_3307_: *mut crate::leanh::LeanObject,
    mut v_a_3308_: *mut crate::leanh::LeanObject,
    mut v_a_3309_: *mut crate::leanh::LeanObject,
    mut v_a_3310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3311_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(
        v_pass_3302_,
        v_goal_3303_,
        v_a_3304_,
        v_a_3305_,
        v_a_3306_,
        v_a_3307_,
        v_a_3308_,
        v_a_3309_,
    );
    crate::leanh::lean_dec(v_a_3309_);
    crate::leanh::lean_dec_ref(v_a_3308_);
    crate::leanh::lean_dec(v_a_3307_);
    crate::leanh::lean_dec_ref(v_a_3306_);
    crate::leanh::lean_dec(v_a_3305_);
    crate::leanh::lean_dec_ref(v_a_3304_);
    return v_res_3311_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3312_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3313_ = lean_mk_empty_array_with_capacity(v___x_3312_);
    v___x_3314_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3314_, 0, v___x_3313_);
    return v___x_3314_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3315_: usize = 0;
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3315_ = 5usize;
    v___x_3316_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3317_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3318_ = lean_mk_empty_array_with_capacity(v___x_3317_);
    v___x_3319_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__0_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__0);
    v___x_3320_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_3320_, 0, v___x_3319_);
    crate::leanh::lean_ctor_set(v___x_3320_, 1, v___x_3318_);
    crate::leanh::lean_ctor_set(v___x_3320_, 2, v___x_3316_);
    crate::leanh::lean_ctor_set(v___x_3320_, 3, v___x_3316_);
    crate::leanh::lean_ctor_set_usize(v___x_3320_, 4, v___x_3315_);
    return v___x_3320_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg(
    mut v___y_3321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3338_: u8 = 0;
    let mut v_tid_3339_: u64 = 0;
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3342_: u8 = 0;
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3352_: u8 = 0;
    let mut v_unused_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3354_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3323_ = lean_st_ref_get(v___y_3321_);
                v_traceState_3324_ = crate::leanh::lean_ctor_get(v___x_3323_, 4);
                crate::leanh::lean_inc_ref(v_traceState_3324_);
                crate::leanh::lean_dec(v___x_3323_);
                v_traces_3325_ = crate::leanh::lean_ctor_get(v_traceState_3324_, 0);
                crate::leanh::lean_inc_ref(v_traces_3325_);
                crate::leanh::lean_dec_ref(v_traceState_3324_);
                v___x_3326_ = lean_st_ref_take(v___y_3321_);
                v_traceState_3327_ = crate::leanh::lean_ctor_get(v___x_3326_, 4);
                v_env_3328_ = crate::leanh::lean_ctor_get(v___x_3326_, 0);
                v_nextMacroScope_3329_ = crate::leanh::lean_ctor_get(v___x_3326_, 1);
                v_ngen_3330_ = crate::leanh::lean_ctor_get(v___x_3326_, 2);
                v_auxDeclNGen_3331_ = crate::leanh::lean_ctor_get(v___x_3326_, 3);
                v_cache_3332_ = crate::leanh::lean_ctor_get(v___x_3326_, 5);
                v_messages_3333_ = crate::leanh::lean_ctor_get(v___x_3326_, 6);
                v_infoState_3334_ = crate::leanh::lean_ctor_get(v___x_3326_, 7);
                v_snapshotTasks_3335_ = crate::leanh::lean_ctor_get(v___x_3326_, 8);
                v_isSharedCheck_3354_ = (!crate::leanh::lean_is_exclusive(v___x_3326_)) as u8;
                if v_isSharedCheck_3354_ == 0 {
                    v___x_3337_ = v___x_3326_;
                    v_isShared_3338_ = v_isSharedCheck_3354_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3335_);
                    crate::leanh::lean_inc(v_infoState_3334_);
                    crate::leanh::lean_inc(v_messages_3333_);
                    crate::leanh::lean_inc(v_cache_3332_);
                    crate::leanh::lean_inc(v_traceState_3327_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3331_);
                    crate::leanh::lean_inc(v_ngen_3330_);
                    crate::leanh::lean_inc(v_nextMacroScope_3329_);
                    crate::leanh::lean_inc(v_env_3328_);
                    crate::leanh::lean_dec(v___x_3326_);
                    v___x_3337_ = crate::leanh::lean_box(0);
                    v_isShared_3338_ = v_isSharedCheck_3354_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_tid_3339_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_3327_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3352_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_3327_)) as u8;
                if v_isSharedCheck_3352_ == 0 {
                    v_unused_3353_ = crate::leanh::lean_ctor_get(v_traceState_3327_, 0);
                    crate::leanh::lean_dec(v_unused_3353_);
                    v___x_3341_ = v_traceState_3327_;
                    v_isShared_3342_ = v_isSharedCheck_3352_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_traceState_3327_);
                    v___x_3341_ = crate::leanh::lean_box(0);
                    v_isShared_3342_ = v_isSharedCheck_3352_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3343_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__1);
                if v_isShared_3342_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3341_, 0, v___x_3343_);
                    v___x_3345_ = v___x_3341_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3351_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3351_, 0, v___x_3343_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3351_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_3339_,
                    );
                    v___x_3345_ = v_reuseFailAlloc_3351_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3338_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3337_, 4, v___x_3345_);
                    v___x_3347_ = v___x_3337_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3350_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_env_3328_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3350_, 1, v_nextMacroScope_3329_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3350_, 2, v_ngen_3330_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3350_, 3, v_auxDeclNGen_3331_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3350_, 4, v___x_3345_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3350_, 5, v_cache_3332_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3350_, 6, v_messages_3333_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3350_, 7, v_infoState_3334_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3350_, 8, v_snapshotTasks_3335_);
                    v___x_3347_ = v_reuseFailAlloc_3350_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3348_ = lean_st_ref_set(v___y_3321_, v___x_3347_);
                v___x_3349_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3349_, 0, v_traces_3325_);
                return v___x_3349_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___boxed(
    mut v___y_3355_: *mut crate::leanh::LeanObject,
    mut v___y_3356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3357_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg(v___y_3355_);
    crate::leanh::lean_dec(v___y_3355_);
    return v_res_3357_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1(
    mut v___y_3358_: *mut crate::leanh::LeanObject,
    mut v___y_3359_: *mut crate::leanh::LeanObject,
    mut v___y_3360_: *mut crate::leanh::LeanObject,
    mut v___y_3361_: *mut crate::leanh::LeanObject,
    mut v___y_3362_: *mut crate::leanh::LeanObject,
    mut v___y_3363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3365_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg(v___y_3363_);
    return v___x_3365_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___boxed(
    mut v___y_3366_: *mut crate::leanh::LeanObject,
    mut v___y_3367_: *mut crate::leanh::LeanObject,
    mut v___y_3368_: *mut crate::leanh::LeanObject,
    mut v___y_3369_: *mut crate::leanh::LeanObject,
    mut v___y_3370_: *mut crate::leanh::LeanObject,
    mut v___y_3371_: *mut crate::leanh::LeanObject,
    mut v___y_3372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3373_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1(v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
    crate::leanh::lean_dec(v___y_3371_);
    crate::leanh::lean_dec_ref(v___y_3370_);
    crate::leanh::lean_dec(v___y_3369_);
    crate::leanh::lean_dec_ref(v___y_3368_);
    crate::leanh::lean_dec(v___y_3367_);
    crate::leanh::lean_dec_ref(v___y_3366_);
    return v_res_3373_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__2(
    mut v_opts_3374_: *mut crate::leanh::LeanObject,
    mut v_opt_3375_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_3376_ = crate::leanh::lean_ctor_get(v_opt_3375_, 0);
    v_defValue_3377_ = crate::leanh::lean_ctor_get(v_opt_3375_, 1);
    v_map_3378_ = crate::leanh::lean_ctor_get(v_opts_3374_, 0);
    v___x_3379_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3378_,
            v_name_3376_,
        );
    if crate::leanh::lean_obj_tag(v___x_3379_) == 0 {
        let mut v___x_3380_: u8 = 0;
        v___x_3380_ = (crate::leanh::lean_unbox(v_defValue_3377_) as u8);
        return v___x_3380_;
    } else {
        let mut v_val_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3381_ = crate::leanh::lean_ctor_get(v___x_3379_, 0);
        crate::leanh::lean_inc(v_val_3381_);
        crate::leanh::lean_dec_ref_known(v___x_3379_, 1);
        if crate::leanh::lean_obj_tag(v_val_3381_) == 1 {
            let mut v_v_3382_: u8 = 0;
            v_v_3382_ = crate::leanh::lean_ctor_get_uint8(v_val_3381_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_3381_, 0);
            return v_v_3382_;
        } else {
            let mut v___x_3383_: u8 = 0;
            crate::leanh::lean_dec(v_val_3381_);
            v___x_3383_ = (crate::leanh::lean_unbox(v_defValue_3377_) as u8);
            return v___x_3383_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__2___boxed(
    mut v_opts_3384_: *mut crate::leanh::LeanObject,
    mut v_opt_3385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3386_: u8 = 0;
    let mut v_r_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3386_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__2(v_opts_3384_, v_opt_3385_);
    crate::leanh::lean_dec_ref(v_opt_3385_);
    crate::leanh::lean_dec_ref(v_opts_3384_);
    v_r_3387_ = crate::leanh::lean_box((v_res_3386_) as usize);
    return v_r_3387_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___lam__0(
    mut v_name_3388_: *mut crate::leanh::LeanObject,
    mut v_snd_3389_: *mut crate::leanh::LeanObject,
    mut v_x_3390_: *mut crate::leanh::LeanObject,
    mut v___y_3391_: *mut crate::leanh::LeanObject,
    mut v___y_3392_: *mut crate::leanh::LeanObject,
    mut v___y_3393_: *mut crate::leanh::LeanObject,
    mut v___y_3394_: *mut crate::leanh::LeanObject,
    mut v___y_3395_: *mut crate::leanh::LeanObject,
    mut v___y_3396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3398_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1,
    );
    v___x_3399_ = l_Lean_MessageData_ofName(v_name_3388_);
    v___x_3400_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3400_, 0, v___x_3398_);
    crate::leanh::lean_ctor_set(v___x_3400_, 1, v___x_3399_);
    v___x_3401_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__3_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__3,
    );
    v___x_3402_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3402_, 0, v___x_3400_);
    crate::leanh::lean_ctor_set(v___x_3402_, 1, v___x_3401_);
    v___x_3403_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3403_, 0, v_snd_3389_);
    v___x_3404_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3404_, 0, v___x_3402_);
    crate::leanh::lean_ctor_set(v___x_3404_, 1, v___x_3403_);
    v___x_3405_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3405_, 0, v___x_3404_);
    return v___x_3405_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___lam__0___boxed(
    mut v_name_3406_: *mut crate::leanh::LeanObject,
    mut v_snd_3407_: *mut crate::leanh::LeanObject,
    mut v_x_3408_: *mut crate::leanh::LeanObject,
    mut v___y_3409_: *mut crate::leanh::LeanObject,
    mut v___y_3410_: *mut crate::leanh::LeanObject,
    mut v___y_3411_: *mut crate::leanh::LeanObject,
    mut v___y_3412_: *mut crate::leanh::LeanObject,
    mut v___y_3413_: *mut crate::leanh::LeanObject,
    mut v___y_3414_: *mut crate::leanh::LeanObject,
    mut v___y_3415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3416_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___lam__0(v_name_3406_, v_snd_3407_, v_x_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_);
    crate::leanh::lean_dec(v___y_3414_);
    crate::leanh::lean_dec_ref(v___y_3413_);
    crate::leanh::lean_dec(v___y_3412_);
    crate::leanh::lean_dec_ref(v___y_3411_);
    crate::leanh::lean_dec(v___y_3410_);
    crate::leanh::lean_dec_ref(v___y_3409_);
    crate::leanh::lean_dec_ref(v_x_3408_);
    return v_res_3416_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__7(
    mut v_opts_3417_: *mut crate::leanh::LeanObject,
    mut v_opt_3418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_3419_ = crate::leanh::lean_ctor_get(v_opt_3418_, 0);
    v_defValue_3420_ = crate::leanh::lean_ctor_get(v_opt_3418_, 1);
    v_map_3421_ = crate::leanh::lean_ctor_get(v_opts_3417_, 0);
    v___x_3422_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3421_,
            v_name_3419_,
        );
    if crate::leanh::lean_obj_tag(v___x_3422_) == 0 {
        crate::leanh::lean_inc(v_defValue_3420_);
        return v_defValue_3420_;
    } else {
        let mut v_val_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3423_ = crate::leanh::lean_ctor_get(v___x_3422_, 0);
        crate::leanh::lean_inc(v_val_3423_);
        crate::leanh::lean_dec_ref_known(v___x_3422_, 1);
        if crate::leanh::lean_obj_tag(v_val_3423_) == 3 {
            let mut v_v_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_v_3424_ = crate::leanh::lean_ctor_get(v_val_3423_, 0);
            crate::leanh::lean_inc(v_v_3424_);
            crate::leanh::lean_dec_ref_known(v_val_3423_, 1);
            return v_v_3424_;
        } else {
            crate::leanh::lean_dec(v_val_3423_);
            crate::leanh::lean_inc(v_defValue_3420_);
            return v_defValue_3420_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__7___boxed(
    mut v_opts_3425_: *mut crate::leanh::LeanObject,
    mut v_opt_3426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3427_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__7(v_opts_3425_, v_opt_3426_);
    crate::leanh::lean_dec_ref(v_opt_3426_);
    crate::leanh::lean_dec_ref(v_opts_3425_);
    return v_res_3427_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__6___redArg(
    mut v_x_3428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3433_: u8 = 0;
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3437_: u8 = 0;
    let mut v_a_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3441_: u8 = 0;
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3445_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3428_) == 0 {
                    v_a_3430_ = crate::leanh::lean_ctor_get(v_x_3428_, 0);
                    v_isSharedCheck_3437_ = (!crate::leanh::lean_is_exclusive(v_x_3428_)) as u8;
                    if v_isSharedCheck_3437_ == 0 {
                        v___x_3432_ = v_x_3428_;
                        v_isShared_3433_ = v_isSharedCheck_3437_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3430_);
                        crate::leanh::lean_dec(v_x_3428_);
                        v___x_3432_ = crate::leanh::lean_box(0);
                        v_isShared_3433_ = v_isSharedCheck_3437_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3438_ = crate::leanh::lean_ctor_get(v_x_3428_, 0);
                    v_isSharedCheck_3445_ = (!crate::leanh::lean_is_exclusive(v_x_3428_)) as u8;
                    if v_isSharedCheck_3445_ == 0 {
                        v___x_3440_ = v_x_3428_;
                        v_isShared_3441_ = v_isSharedCheck_3445_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3438_);
                        crate::leanh::lean_dec(v_x_3428_);
                        v___x_3440_ = crate::leanh::lean_box(0);
                        v_isShared_3441_ = v_isSharedCheck_3445_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3433_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3432_, 1);
                    v___x_3435_ = v___x_3432_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3436_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_a_3430_);
                    v___x_3435_ = v_reuseFailAlloc_3436_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3435_;
            }
            3 => {
                if v_isShared_3441_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3440_, 0);
                    v___x_3443_ = v___x_3440_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3444_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3438_);
                    v___x_3443_ = v_reuseFailAlloc_3444_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3443_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__6___redArg___boxed(
    mut v_x_3446_: *mut crate::leanh::LeanObject,
    mut v___y_3447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3448_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__6___redArg(v_x_3446_);
    return v_res_3448_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0_spec__0(
    mut v_msgData_3449_: *mut crate::leanh::LeanObject,
    mut v___y_3450_: *mut crate::leanh::LeanObject,
    mut v___y_3451_: *mut crate::leanh::LeanObject,
    mut v___y_3452_: *mut crate::leanh::LeanObject,
    mut v___y_3453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3455_ = lean_st_ref_get(v___y_3453_);
    v_env_3456_ = crate::leanh::lean_ctor_get(v___x_3455_, 0);
    crate::leanh::lean_inc_ref(v_env_3456_);
    crate::leanh::lean_dec(v___x_3455_);
    v___x_3457_ = lean_st_ref_get(v___y_3451_);
    v_mctx_3458_ = crate::leanh::lean_ctor_get(v___x_3457_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3458_);
    crate::leanh::lean_dec(v___x_3457_);
    v_lctx_3459_ = crate::leanh::lean_ctor_get(v___y_3450_, 2);
    v_options_3460_ = crate::leanh::lean_ctor_get(v___y_3452_, 2);
    crate::leanh::lean_inc_ref(v_options_3460_);
    crate::leanh::lean_inc_ref(v_lctx_3459_);
    v___x_3461_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3461_, 0, v_env_3456_);
    crate::leanh::lean_ctor_set(v___x_3461_, 1, v_mctx_3458_);
    crate::leanh::lean_ctor_set(v___x_3461_, 2, v_lctx_3459_);
    crate::leanh::lean_ctor_set(v___x_3461_, 3, v_options_3460_);
    v___x_3462_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3462_, 0, v___x_3461_);
    crate::leanh::lean_ctor_set(v___x_3462_, 1, v_msgData_3449_);
    v___x_3463_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3463_, 0, v___x_3462_);
    return v___x_3463_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0_spec__0___boxed(
    mut v_msgData_3464_: *mut crate::leanh::LeanObject,
    mut v___y_3465_: *mut crate::leanh::LeanObject,
    mut v___y_3466_: *mut crate::leanh::LeanObject,
    mut v___y_3467_: *mut crate::leanh::LeanObject,
    mut v___y_3468_: *mut crate::leanh::LeanObject,
    mut v___y_3469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3470_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0_spec__0(v_msgData_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
    crate::leanh::lean_dec(v___y_3468_);
    crate::leanh::lean_dec_ref(v___y_3467_);
    crate::leanh::lean_dec(v___y_3466_);
    crate::leanh::lean_dec_ref(v___y_3465_);
    return v_res_3470_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5_spec__6(
    mut v_sz_3471_: usize,
    mut v_i_3472_: usize,
    mut v_bs_3473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3474_: u8 = 0;
    let mut v_v_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: usize = 0;
    let mut v___x_3480_: usize = 0;
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3474_ = lean_usize_dec_lt(v_i_3472_, v_sz_3471_);
                if v___x_3474_ == 0 {
                    return v_bs_3473_;
                } else {
                    v_v_3475_ = lean_array_uget_borrowed(v_bs_3473_, v_i_3472_);
                    v_msg_3476_ = crate::leanh::lean_ctor_get(v_v_3475_, 1);
                    crate::leanh::lean_inc_ref(v_msg_3476_);
                    v___x_3477_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3478_ = lean_array_uset(v_bs_3473_, v_i_3472_, v___x_3477_);
                    v___x_3479_ = 1usize;
                    v___x_3480_ = lean_usize_add(v_i_3472_, v___x_3479_);
                    v___x_3481_ = lean_array_uset(v_bs_x27_3478_, v_i_3472_, v_msg_3476_);
                    v_i_3472_ = v___x_3480_;
                    v_bs_3473_ = v___x_3481_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5_spec__6___boxed(
    mut v_sz_3483_: *mut crate::leanh::LeanObject,
    mut v_i_3484_: *mut crate::leanh::LeanObject,
    mut v_bs_3485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3486_: usize = 0;
    let mut v_i_boxed_3487_: usize = 0;
    let mut v_res_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3486_ = crate::leanh::lean_unbox_usize(v_sz_3483_);
    crate::leanh::lean_dec(v_sz_3483_);
    v_i_boxed_3487_ = crate::leanh::lean_unbox_usize(v_i_3484_);
    crate::leanh::lean_dec(v_i_3484_);
    v_res_3488_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5_spec__6(v_sz_boxed_3486_, v_i_boxed_3487_, v_bs_3485_);
    return v_res_3488_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5___redArg(
    mut v_oldTraces_3489_: *mut crate::leanh::LeanObject,
    mut v_data_3490_: *mut crate::leanh::LeanObject,
    mut v_ref_3491_: *mut crate::leanh::LeanObject,
    mut v_msg_3492_: *mut crate::leanh::LeanObject,
    mut v___y_3493_: *mut crate::leanh::LeanObject,
    mut v___y_3494_: *mut crate::leanh::LeanObject,
    mut v___y_3495_: *mut crate::leanh::LeanObject,
    mut v___y_3496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3510_: u8 = 0;
    let mut v_cancelTk_x3f_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3512_: u8 = 0;
    let mut v_inheritedTraceOptions_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3520_: usize = 0;
    let mut v___x_3521_: usize = 0;
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3528_: u8 = 0;
    let mut v___x_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3541_: u8 = 0;
    let mut v_tid_3542_: u64 = 0;
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3545_: u8 = 0;
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3559_: u8 = 0;
    let mut v_unused_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3561_: u8 = 0;
    let mut v_isSharedCheck_3562_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_3498_ = crate::leanh::lean_ctor_get(v___y_3495_, 0);
                v_fileMap_3499_ = crate::leanh::lean_ctor_get(v___y_3495_, 1);
                v_options_3500_ = crate::leanh::lean_ctor_get(v___y_3495_, 2);
                v_currRecDepth_3501_ = crate::leanh::lean_ctor_get(v___y_3495_, 3);
                v_maxRecDepth_3502_ = crate::leanh::lean_ctor_get(v___y_3495_, 4);
                v_ref_3503_ = crate::leanh::lean_ctor_get(v___y_3495_, 5);
                v_currNamespace_3504_ = crate::leanh::lean_ctor_get(v___y_3495_, 6);
                v_openDecls_3505_ = crate::leanh::lean_ctor_get(v___y_3495_, 7);
                v_initHeartbeats_3506_ = crate::leanh::lean_ctor_get(v___y_3495_, 8);
                v_maxHeartbeats_3507_ = crate::leanh::lean_ctor_get(v___y_3495_, 9);
                v_quotContext_3508_ = crate::leanh::lean_ctor_get(v___y_3495_, 10);
                v_currMacroScope_3509_ = crate::leanh::lean_ctor_get(v___y_3495_, 11);
                v_diag_3510_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3495_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_3511_ = crate::leanh::lean_ctor_get(v___y_3495_, 12);
                v_suppressElabErrors_3512_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3495_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_3513_ = crate::leanh::lean_ctor_get(v___y_3495_, 13);
                v___x_3514_ = lean_st_ref_get(v___y_3496_);
                v_traceState_3515_ = crate::leanh::lean_ctor_get(v___x_3514_, 4);
                crate::leanh::lean_inc_ref(v_traceState_3515_);
                crate::leanh::lean_dec(v___x_3514_);
                v_traces_3516_ = crate::leanh::lean_ctor_get(v_traceState_3515_, 0);
                crate::leanh::lean_inc_ref(v_traces_3516_);
                crate::leanh::lean_dec_ref(v_traceState_3515_);
                v_ref_3517_ = l_Lean_replaceRef(v_ref_3491_, v_ref_3503_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_3513_);
                crate::leanh::lean_inc(v_cancelTk_x3f_3511_);
                crate::leanh::lean_inc(v_currMacroScope_3509_);
                crate::leanh::lean_inc(v_quotContext_3508_);
                crate::leanh::lean_inc(v_maxHeartbeats_3507_);
                crate::leanh::lean_inc(v_initHeartbeats_3506_);
                crate::leanh::lean_inc(v_openDecls_3505_);
                crate::leanh::lean_inc(v_currNamespace_3504_);
                crate::leanh::lean_inc(v_maxRecDepth_3502_);
                crate::leanh::lean_inc(v_currRecDepth_3501_);
                crate::leanh::lean_inc_ref(v_options_3500_);
                crate::leanh::lean_inc_ref(v_fileMap_3499_);
                crate::leanh::lean_inc_ref(v_fileName_3498_);
                v___x_3518_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_3518_, 0, v_fileName_3498_);
                crate::leanh::lean_ctor_set(v___x_3518_, 1, v_fileMap_3499_);
                crate::leanh::lean_ctor_set(v___x_3518_, 2, v_options_3500_);
                crate::leanh::lean_ctor_set(v___x_3518_, 3, v_currRecDepth_3501_);
                crate::leanh::lean_ctor_set(v___x_3518_, 4, v_maxRecDepth_3502_);
                crate::leanh::lean_ctor_set(v___x_3518_, 5, v_ref_3517_);
                crate::leanh::lean_ctor_set(v___x_3518_, 6, v_currNamespace_3504_);
                crate::leanh::lean_ctor_set(v___x_3518_, 7, v_openDecls_3505_);
                crate::leanh::lean_ctor_set(v___x_3518_, 8, v_initHeartbeats_3506_);
                crate::leanh::lean_ctor_set(v___x_3518_, 9, v_maxHeartbeats_3507_);
                crate::leanh::lean_ctor_set(v___x_3518_, 10, v_quotContext_3508_);
                crate::leanh::lean_ctor_set(v___x_3518_, 11, v_currMacroScope_3509_);
                crate::leanh::lean_ctor_set(v___x_3518_, 12, v_cancelTk_x3f_3511_);
                crate::leanh::lean_ctor_set(v___x_3518_, 13, v_inheritedTraceOptions_3513_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3518_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_3510_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3518_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_3512_,
                );
                v___x_3519_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3516_);
                crate::leanh::lean_dec_ref(v_traces_3516_);
                v_sz_3520_ = lean_array_size(v___x_3519_);
                v___x_3521_ = 0usize;
                v___x_3522_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5_spec__6(v_sz_3520_, v___x_3521_, v___x_3519_);
                v_msg_3523_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v_msg_3523_, 0, v_data_3490_);
                crate::leanh::lean_ctor_set(v_msg_3523_, 1, v_msg_3492_);
                crate::leanh::lean_ctor_set(v_msg_3523_, 2, v___x_3522_);
                v___x_3524_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0_spec__0(v_msg_3523_, v___y_3493_, v___y_3494_, v___x_3518_, v___y_3496_);
                crate::leanh::lean_dec_ref_known(v___x_3518_, 14);
                v_a_3525_ = crate::leanh::lean_ctor_get(v___x_3524_, 0);
                v_isSharedCheck_3562_ = (!crate::leanh::lean_is_exclusive(v___x_3524_)) as u8;
                if v_isSharedCheck_3562_ == 0 {
                    v___x_3527_ = v___x_3524_;
                    v_isShared_3528_ = v_isSharedCheck_3562_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3525_);
                    crate::leanh::lean_dec(v___x_3524_);
                    v___x_3527_ = crate::leanh::lean_box(0);
                    v_isShared_3528_ = v_isSharedCheck_3562_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3529_ = lean_st_ref_take(v___y_3496_);
                v_traceState_3530_ = crate::leanh::lean_ctor_get(v___x_3529_, 4);
                v_env_3531_ = crate::leanh::lean_ctor_get(v___x_3529_, 0);
                v_nextMacroScope_3532_ = crate::leanh::lean_ctor_get(v___x_3529_, 1);
                v_ngen_3533_ = crate::leanh::lean_ctor_get(v___x_3529_, 2);
                v_auxDeclNGen_3534_ = crate::leanh::lean_ctor_get(v___x_3529_, 3);
                v_cache_3535_ = crate::leanh::lean_ctor_get(v___x_3529_, 5);
                v_messages_3536_ = crate::leanh::lean_ctor_get(v___x_3529_, 6);
                v_infoState_3537_ = crate::leanh::lean_ctor_get(v___x_3529_, 7);
                v_snapshotTasks_3538_ = crate::leanh::lean_ctor_get(v___x_3529_, 8);
                v_isSharedCheck_3561_ = (!crate::leanh::lean_is_exclusive(v___x_3529_)) as u8;
                if v_isSharedCheck_3561_ == 0 {
                    v___x_3540_ = v___x_3529_;
                    v_isShared_3541_ = v_isSharedCheck_3561_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3538_);
                    crate::leanh::lean_inc(v_infoState_3537_);
                    crate::leanh::lean_inc(v_messages_3536_);
                    crate::leanh::lean_inc(v_cache_3535_);
                    crate::leanh::lean_inc(v_traceState_3530_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3534_);
                    crate::leanh::lean_inc(v_ngen_3533_);
                    crate::leanh::lean_inc(v_nextMacroScope_3532_);
                    crate::leanh::lean_inc(v_env_3531_);
                    crate::leanh::lean_dec(v___x_3529_);
                    v___x_3540_ = crate::leanh::lean_box(0);
                    v_isShared_3541_ = v_isSharedCheck_3561_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3542_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_3530_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3559_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_3530_)) as u8;
                if v_isSharedCheck_3559_ == 0 {
                    v_unused_3560_ = crate::leanh::lean_ctor_get(v_traceState_3530_, 0);
                    crate::leanh::lean_dec(v_unused_3560_);
                    v___x_3544_ = v_traceState_3530_;
                    v_isShared_3545_ = v_isSharedCheck_3559_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_traceState_3530_);
                    v___x_3544_ = crate::leanh::lean_box(0);
                    v_isShared_3545_ = v_isSharedCheck_3559_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3546_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3546_, 0, v_ref_3491_);
                crate::leanh::lean_ctor_set(v___x_3546_, 1, v_a_3525_);
                v___x_3547_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3489_, v___x_3546_);
                if v_isShared_3545_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3544_, 0, v___x_3547_);
                    v___x_3549_ = v___x_3544_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3558_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3558_, 0, v___x_3547_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3558_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_3542_,
                    );
                    v___x_3549_ = v_reuseFailAlloc_3558_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3541_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3540_, 4, v___x_3549_);
                    v___x_3551_ = v___x_3540_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3557_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_env_3531_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3557_, 1, v_nextMacroScope_3532_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3557_, 2, v_ngen_3533_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3557_, 3, v_auxDeclNGen_3534_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3557_, 4, v___x_3549_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3557_, 5, v_cache_3535_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3557_, 6, v_messages_3536_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3557_, 7, v_infoState_3537_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3557_, 8, v_snapshotTasks_3538_);
                    v___x_3551_ = v_reuseFailAlloc_3557_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3552_ = lean_st_ref_set(v___y_3496_, v___x_3551_);
                v___x_3553_ = crate::leanh::lean_box(0);
                if v_isShared_3528_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3527_, 0, v___x_3553_);
                    v___x_3555_ = v___x_3527_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3556_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3556_, 0, v___x_3553_);
                    v___x_3555_ = v_reuseFailAlloc_3556_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3555_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5___redArg___boxed(
    mut v_oldTraces_3563_: *mut crate::leanh::LeanObject,
    mut v_data_3564_: *mut crate::leanh::LeanObject,
    mut v_ref_3565_: *mut crate::leanh::LeanObject,
    mut v_msg_3566_: *mut crate::leanh::LeanObject,
    mut v___y_3567_: *mut crate::leanh::LeanObject,
    mut v___y_3568_: *mut crate::leanh::LeanObject,
    mut v___y_3569_: *mut crate::leanh::LeanObject,
    mut v___y_3570_: *mut crate::leanh::LeanObject,
    mut v___y_3571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3572_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5___redArg(v_oldTraces_3563_, v_data_3564_, v_ref_3565_, v_msg_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_);
    crate::leanh::lean_dec(v___y_3570_);
    crate::leanh::lean_dec_ref(v___y_3569_);
    crate::leanh::lean_dec(v___y_3568_);
    crate::leanh::lean_dec_ref(v___y_3567_);
    return v_res_3572_;
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__4(
    mut v_e_3573_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_e_3573_) == 0 {
        let mut v___x_3574_: u8 = 0;
        v___x_3574_ = 2;
        return v___x_3574_;
    } else {
        let mut v_a_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_3575_ = crate::leanh::lean_ctor_get(v_e_3573_, 0);
        if crate::leanh::lean_obj_tag(v_a_3575_) == 0 {
            let mut v___x_3576_: u8 = 0;
            v___x_3576_ = 1;
            return v___x_3576_;
        } else {
            let mut v___x_3577_: u8 = 0;
            v___x_3577_ = 0;
            return v___x_3577_;
        }
    }
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__4___boxed(
    mut v_e_3578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3579_: u8 = 0;
    let mut v_r_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3579_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__4(v_e_3578_);
    crate::leanh::lean_dec_ref(v_e_3578_);
    v_r_3580_ = crate::leanh::lean_box((v_res_3579_) as usize);
    return v_r_3580_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3582_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__0;
    v___x_3583_ = l_Lean_stringToMessageData(v___x_3582_);
    return v___x_3583_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__2()
-> f64 {
    let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: f64 = 0.0;
    v___x_3584_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3585_ = lean_float_of_nat(v___x_3584_);
    return v___x_3585_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3587_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__3;
    v___x_3588_ = l_Lean_stringToMessageData(v___x_3587_);
    return v___x_3588_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__5()
-> f64 {
    let mut v___x_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: f64 = 0.0;
    v___x_3589_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_3590_ = lean_float_of_nat(v___x_3589_);
    return v___x_3590_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3(
    mut v_cls_3591_: *mut crate::leanh::LeanObject,
    mut v_collapsed_3592_: u8,
    mut v_tag_3593_: *mut crate::leanh::LeanObject,
    mut v_opts_3594_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_3595_: u8,
    mut v_oldTraces_3596_: *mut crate::leanh::LeanObject,
    mut v_msg_3597_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_3598_: *mut crate::leanh::LeanObject,
    mut v___y_3599_: *mut crate::leanh::LeanObject,
    mut v___y_3600_: *mut crate::leanh::LeanObject,
    mut v___y_3601_: *mut crate::leanh::LeanObject,
    mut v___y_3602_: *mut crate::leanh::LeanObject,
    mut v___y_3603_: *mut crate::leanh::LeanObject,
    mut v___y_3604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3610_: u8 = 0;
    let mut v___y_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3620_: u8 = 0;
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3624_: u8 = 0;
    let mut v_fst_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3629_: u8 = 0;
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: u8 = 0;
    let mut v___y_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_3635_: u8 = 0;
    let mut v___x_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: f64 = 0.0;
    let mut v_data_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: f64 = 0.0;
    let mut v___x_3649_: f64 = 0.0;
    let mut v_reuseFailAlloc_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3658_: u8 = 0;
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3671_: u8 = 0;
    let mut v_tid_3672_: u64 = 0;
    let mut v_traces_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3676_: u8 = 0;
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3686_: u8 = 0;
    let mut v_isSharedCheck_3687_: u8 = 0;
    let mut v___y_3689_: f64 = 0.0;
    let mut v___x_3690_: f64 = 0.0;
    let mut v___x_3691_: f64 = 0.0;
    let mut v___x_3692_: f64 = 0.0;
    let mut v___x_3693_: u8 = 0;
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: u8 = 0;
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: f64 = 0.0;
    let mut v___x_3699_: f64 = 0.0;
    let mut v___x_3700_: f64 = 0.0;
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: f64 = 0.0;
    let mut v_isSharedCheck_3704_: u8 = 0;
    let mut v_isSharedCheck_3705_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3606_ = crate::leanh::lean_ctor_get(v_resStartStop_3598_, 0);
                v_snd_3607_ = crate::leanh::lean_ctor_get(v_resStartStop_3598_, 1);
                v_isSharedCheck_3705_ =
                    (!crate::leanh::lean_is_exclusive(v_resStartStop_3598_)) as u8;
                if v_isSharedCheck_3705_ == 0 {
                    v___x_3609_ = v_resStartStop_3598_;
                    v_isShared_3610_ = v_isSharedCheck_3705_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3607_);
                    crate::leanh::lean_inc(v_fst_3606_);
                    crate::leanh::lean_dec(v_resStartStop_3598_);
                    v___x_3609_ = crate::leanh::lean_box(0);
                    v_isShared_3610_ = v_isSharedCheck_3705_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_3625_ = crate::leanh::lean_ctor_get(v_snd_3607_, 0);
                v_snd_3626_ = crate::leanh::lean_ctor_get(v_snd_3607_, 1);
                v_isSharedCheck_3704_ = (!crate::leanh::lean_is_exclusive(v_snd_3607_)) as u8;
                if v_isSharedCheck_3704_ == 0 {
                    v___x_3628_ = v_snd_3607_;
                    v_isShared_3629_ = v_isSharedCheck_3704_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3626_);
                    crate::leanh::lean_inc(v_fst_3625_);
                    crate::leanh::lean_dec(v_snd_3607_);
                    v___x_3628_ = crate::leanh::lean_box(0);
                    v_isShared_3629_ = v_isSharedCheck_3704_;
                    state = 5;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v___y_3612_);
                v___x_3615_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5___redArg(v_oldTraces_3596_, v_data_3614_, v___y_3612_, v___y_3613_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
                if crate::leanh::lean_obj_tag(v___x_3615_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3615_, 1);
                    v___x_3616_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__6___redArg(v_fst_3606_);
                    return v___x_3616_;
                } else {
                    crate::leanh::lean_dec(v_fst_3606_);
                    v_a_3617_ = crate::leanh::lean_ctor_get(v___x_3615_, 0);
                    v_isSharedCheck_3624_ = (!crate::leanh::lean_is_exclusive(v___x_3615_)) as u8;
                    if v_isSharedCheck_3624_ == 0 {
                        v___x_3619_ = v___x_3615_;
                        v_isShared_3620_ = v_isSharedCheck_3624_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3617_);
                        crate::leanh::lean_dec(v___x_3615_);
                        v___x_3619_ = crate::leanh::lean_box(0);
                        v_isShared_3620_ = v_isSharedCheck_3624_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3620_ == 0 {
                    v___x_3622_ = v___x_3619_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3623_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
                    v___x_3622_ = v_reuseFailAlloc_3623_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3622_;
            }
            5 => {
                v___x_3630_ = l_Lean_trace_profiler;
                v___x_3631_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__2(v_opts_3594_, v___x_3630_);
                if v___x_3631_ == 0 {
                    v___y_3658_ = v___x_3631_;
                    state = 10;
                    continue;
                } else {
                    v___x_3694_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_3695_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__2(v_opts_3594_, v___x_3694_);
                    if v___x_3695_ == 0 {
                        v___x_3696_ = l_Lean_trace_profiler_threshold;
                        v___x_3697_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__7(v_opts_3594_, v___x_3696_);
                        v___x_3698_ = lean_float_of_nat(v___x_3697_);
                        v___x_3699_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__5_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__5);
                        v___x_3700_ = lean_float_div(v___x_3698_, v___x_3699_);
                        v___y_3689_ = v___x_3700_;
                        state = 15;
                        continue;
                    } else {
                        v___x_3701_ = l_Lean_trace_profiler_threshold;
                        v___x_3702_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__7(v_opts_3594_, v___x_3701_);
                        v___x_3703_ = lean_float_of_nat(v___x_3702_);
                        v___y_3689_ = v___x_3703_;
                        state = 15;
                        continue;
                    }
                }
            }
            6 => {
                v_result_3635_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__4(v_fst_3606_);
                v___x_3636_ = l_Lean_TraceResult_toEmoji(v_result_3635_);
                v___x_3637_ = l_Lean_stringToMessageData(v___x_3636_);
                v___x_3638_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__1);
                if v_isShared_3629_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3628_, 7);
                    crate::leanh::lean_ctor_set(v___x_3628_, 1, v___x_3638_);
                    crate::leanh::lean_ctor_set(v___x_3628_, 0, v___x_3637_);
                    v___x_3640_ = v___x_3628_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3651_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3637_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3651_, 1, v___x_3638_);
                    v___x_3640_ = v_reuseFailAlloc_3651_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3610_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3609_, 7);
                    crate::leanh::lean_ctor_set(v___x_3609_, 1, v_a_3634_);
                    crate::leanh::lean_ctor_set(v___x_3609_, 0, v___x_3640_);
                    v_m_3642_ = v___x_3609_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3650_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___x_3640_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3650_, 1, v_a_3634_);
                    v_m_3642_ = v_reuseFailAlloc_3650_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3643_ = crate::leanh::lean_box((v_result_3635_) as usize);
                v___x_3644_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3644_, 0, v___x_3643_);
                v___x_3645_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__2_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__2);
                crate::leanh::lean_inc_ref(v_tag_3593_);
                crate::leanh::lean_inc_ref(v___x_3644_);
                crate::leanh::lean_inc(v_cls_3591_);
                v_data_3646_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v_data_3646_, 0, v_cls_3591_);
                crate::leanh::lean_ctor_set(v_data_3646_, 1, v___x_3644_);
                crate::leanh::lean_ctor_set(v_data_3646_, 2, v_tag_3593_);
                crate::leanh::lean_ctor_set_float(
                    v_data_3646_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_3645_,
                );
                crate::leanh::lean_ctor_set_float(
                    v_data_3646_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3645_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_data_3646_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v_collapsed_3592_,
                );
                if v___x_3631_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3644_, 1);
                    crate::leanh::lean_dec(v_snd_3626_);
                    crate::leanh::lean_dec(v_fst_3625_);
                    crate::leanh::lean_dec_ref(v_tag_3593_);
                    crate::leanh::lean_dec(v_cls_3591_);
                    v___y_3612_ = v___y_3633_;
                    v___y_3613_ = v_m_3642_;
                    v_data_3614_ = v_data_3646_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_data_3646_, 3);
                    v_data_3647_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                    crate::leanh::lean_ctor_set(v_data_3647_, 0, v_cls_3591_);
                    crate::leanh::lean_ctor_set(v_data_3647_, 1, v___x_3644_);
                    crate::leanh::lean_ctor_set(v_data_3647_, 2, v_tag_3593_);
                    v___x_3648_ = crate::leanh::lean_unbox_float(v_fst_3625_);
                    crate::leanh::lean_dec(v_fst_3625_);
                    crate::leanh::lean_ctor_set_float(
                        v_data_3647_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v___x_3648_,
                    );
                    v___x_3649_ = crate::leanh::lean_unbox_float(v_snd_3626_);
                    crate::leanh::lean_dec(v_snd_3626_);
                    crate::leanh::lean_ctor_set_float(
                        v_data_3647_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        v___x_3649_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_data_3647_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                        v_collapsed_3592_,
                    );
                    v___y_3612_ = v___y_3633_;
                    v___y_3613_ = v_m_3642_;
                    v_data_3614_ = v_data_3647_;
                    state = 2;
                    continue;
                }
            }
            9 => {
                v_ref_3653_ = crate::leanh::lean_ctor_get(v___y_3603_, 5);
                crate::leanh::lean_inc(v___y_3604_);
                crate::leanh::lean_inc_ref(v___y_3603_);
                crate::leanh::lean_inc(v___y_3602_);
                crate::leanh::lean_inc_ref(v___y_3601_);
                crate::leanh::lean_inc(v___y_3600_);
                crate::leanh::lean_inc_ref(v___y_3599_);
                crate::leanh::lean_inc(v_fst_3606_);
                v___x_3654_ = crate::leanh::lean_apply_8(
                    v_msg_3597_,
                    v_fst_3606_,
                    v___y_3599_,
                    v___y_3600_,
                    v___y_3601_,
                    v___y_3602_,
                    v___y_3603_,
                    v___y_3604_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_3654_) == 0 {
                    v_a_3655_ = crate::leanh::lean_ctor_get(v___x_3654_, 0);
                    crate::leanh::lean_inc(v_a_3655_);
                    crate::leanh::lean_dec_ref_known(v___x_3654_, 1);
                    v___y_3633_ = v_ref_3653_;
                    v_a_3634_ = v_a_3655_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_3654_, 1);
                    v___x_3656_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__4_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__4);
                    v___y_3633_ = v_ref_3653_;
                    v_a_3634_ = v___x_3656_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                if v_clsEnabled_3595_ == 0 {
                    if v___y_3658_ == 0 {
                        crate::leanh::lean_del_object(v___x_3628_);
                        crate::leanh::lean_dec(v_snd_3626_);
                        crate::leanh::lean_dec(v_fst_3625_);
                        crate::leanh::lean_del_object(v___x_3609_);
                        crate::leanh::lean_dec_ref(v_msg_3597_);
                        crate::leanh::lean_dec_ref(v_tag_3593_);
                        crate::leanh::lean_dec(v_cls_3591_);
                        v___x_3659_ = lean_st_ref_take(v___y_3604_);
                        v_traceState_3660_ = crate::leanh::lean_ctor_get(v___x_3659_, 4);
                        v_env_3661_ = crate::leanh::lean_ctor_get(v___x_3659_, 0);
                        v_nextMacroScope_3662_ = crate::leanh::lean_ctor_get(v___x_3659_, 1);
                        v_ngen_3663_ = crate::leanh::lean_ctor_get(v___x_3659_, 2);
                        v_auxDeclNGen_3664_ = crate::leanh::lean_ctor_get(v___x_3659_, 3);
                        v_cache_3665_ = crate::leanh::lean_ctor_get(v___x_3659_, 5);
                        v_messages_3666_ = crate::leanh::lean_ctor_get(v___x_3659_, 6);
                        v_infoState_3667_ = crate::leanh::lean_ctor_get(v___x_3659_, 7);
                        v_snapshotTasks_3668_ = crate::leanh::lean_ctor_get(v___x_3659_, 8);
                        v_isSharedCheck_3687_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3659_)) as u8;
                        if v_isSharedCheck_3687_ == 0 {
                            v___x_3670_ = v___x_3659_;
                            v_isShared_3671_ = v_isSharedCheck_3687_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snapshotTasks_3668_);
                            crate::leanh::lean_inc(v_infoState_3667_);
                            crate::leanh::lean_inc(v_messages_3666_);
                            crate::leanh::lean_inc(v_cache_3665_);
                            crate::leanh::lean_inc(v_traceState_3660_);
                            crate::leanh::lean_inc(v_auxDeclNGen_3664_);
                            crate::leanh::lean_inc(v_ngen_3663_);
                            crate::leanh::lean_inc(v_nextMacroScope_3662_);
                            crate::leanh::lean_inc(v_env_3661_);
                            crate::leanh::lean_dec(v___x_3659_);
                            v___x_3670_ = crate::leanh::lean_box(0);
                            v_isShared_3671_ = v_isSharedCheck_3687_;
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
                v_tid_3672_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_3660_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3673_ = crate::leanh::lean_ctor_get(v_traceState_3660_, 0);
                v_isSharedCheck_3686_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_3660_)) as u8;
                if v_isSharedCheck_3686_ == 0 {
                    v___x_3675_ = v_traceState_3660_;
                    v_isShared_3676_ = v_isSharedCheck_3686_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_3673_);
                    crate::leanh::lean_dec(v_traceState_3660_);
                    v___x_3675_ = crate::leanh::lean_box(0);
                    v_isShared_3676_ = v_isSharedCheck_3686_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_3677_ =
                    l_Lean_PersistentArray_append___redArg(v_oldTraces_3596_, v_traces_3673_);
                crate::leanh::lean_dec_ref(v_traces_3673_);
                if v_isShared_3676_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3675_, 0, v___x_3677_);
                    v___x_3679_ = v___x_3675_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3685_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3685_, 0, v___x_3677_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3685_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_3672_,
                    );
                    v___x_3679_ = v_reuseFailAlloc_3685_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_3671_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3670_, 4, v___x_3679_);
                    v___x_3681_ = v___x_3670_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3684_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_env_3661_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3684_, 1, v_nextMacroScope_3662_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3684_, 2, v_ngen_3663_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3684_, 3, v_auxDeclNGen_3664_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3684_, 4, v___x_3679_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3684_, 5, v_cache_3665_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3684_, 6, v_messages_3666_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3684_, 7, v_infoState_3667_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3684_, 8, v_snapshotTasks_3668_);
                    v___x_3681_ = v_reuseFailAlloc_3684_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_3682_ = lean_st_ref_set(v___y_3604_, v___x_3681_);
                v___x_3683_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__6___redArg(v_fst_3606_);
                return v___x_3683_;
            }
            15 => {
                v___x_3690_ = crate::leanh::lean_unbox_float(v_snd_3626_);
                v___x_3691_ = crate::leanh::lean_unbox_float(v_fst_3625_);
                v___x_3692_ = lean_float_sub(v___x_3690_, v___x_3691_);
                v___x_3693_ = lean_float_decLt(v___y_3689_, v___x_3692_);
                v___y_3658_ = v___x_3693_;
                state = 10;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___boxed(
    mut v_cls_3706_: *mut crate::leanh::LeanObject,
    mut v_collapsed_3707_: *mut crate::leanh::LeanObject,
    mut v_tag_3708_: *mut crate::leanh::LeanObject,
    mut v_opts_3709_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_3710_: *mut crate::leanh::LeanObject,
    mut v_oldTraces_3711_: *mut crate::leanh::LeanObject,
    mut v_msg_3712_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_3713_: *mut crate::leanh::LeanObject,
    mut v___y_3714_: *mut crate::leanh::LeanObject,
    mut v___y_3715_: *mut crate::leanh::LeanObject,
    mut v___y_3716_: *mut crate::leanh::LeanObject,
    mut v___y_3717_: *mut crate::leanh::LeanObject,
    mut v___y_3718_: *mut crate::leanh::LeanObject,
    mut v___y_3719_: *mut crate::leanh::LeanObject,
    mut v___y_3720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsed_boxed_3721_: u8 = 0;
    let mut v_clsEnabled_boxed_3722_: u8 = 0;
    let mut v_res_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_3721_ = (crate::leanh::lean_unbox(v_collapsed_3707_) as u8);
    v_clsEnabled_boxed_3722_ = (crate::leanh::lean_unbox(v_clsEnabled_3710_) as u8);
    v_res_3723_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3(v_cls_3706_, v_collapsed_boxed_3721_, v_tag_3708_, v_opts_3709_, v_clsEnabled_boxed_3722_, v_oldTraces_3711_, v_msg_3712_, v_resStartStop_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_);
    crate::leanh::lean_dec(v___y_3719_);
    crate::leanh::lean_dec_ref(v___y_3718_);
    crate::leanh::lean_dec(v___y_3717_);
    crate::leanh::lean_dec_ref(v___y_3716_);
    crate::leanh::lean_dec(v___y_3715_);
    crate::leanh::lean_dec_ref(v___y_3714_);
    crate::leanh::lean_dec_ref(v_opts_3709_);
    return v_res_3723_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg(
    mut v_cls_3726_: *mut crate::leanh::LeanObject,
    mut v_msg_3727_: *mut crate::leanh::LeanObject,
    mut v___y_3728_: *mut crate::leanh::LeanObject,
    mut v___y_3729_: *mut crate::leanh::LeanObject,
    mut v___y_3730_: *mut crate::leanh::LeanObject,
    mut v___y_3731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3738_: u8 = 0;
    let mut v___x_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3751_: u8 = 0;
    let mut v_tid_3752_: u64 = 0;
    let mut v_traces_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3756_: u8 = 0;
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: f64 = 0.0;
    let mut v___x_3759_: u8 = 0;
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3777_: u8 = 0;
    let mut v_isSharedCheck_3778_: u8 = 0;
    let mut v_isSharedCheck_3779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3733_ = crate::leanh::lean_ctor_get(v___y_3730_, 5);
                v___x_3734_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0_spec__0(v_msg_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_);
                v_a_3735_ = crate::leanh::lean_ctor_get(v___x_3734_, 0);
                v_isSharedCheck_3779_ = (!crate::leanh::lean_is_exclusive(v___x_3734_)) as u8;
                if v_isSharedCheck_3779_ == 0 {
                    v___x_3737_ = v___x_3734_;
                    v_isShared_3738_ = v_isSharedCheck_3779_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3735_);
                    crate::leanh::lean_dec(v___x_3734_);
                    v___x_3737_ = crate::leanh::lean_box(0);
                    v_isShared_3738_ = v_isSharedCheck_3779_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3739_ = lean_st_ref_take(v___y_3731_);
                v_traceState_3740_ = crate::leanh::lean_ctor_get(v___x_3739_, 4);
                v_env_3741_ = crate::leanh::lean_ctor_get(v___x_3739_, 0);
                v_nextMacroScope_3742_ = crate::leanh::lean_ctor_get(v___x_3739_, 1);
                v_ngen_3743_ = crate::leanh::lean_ctor_get(v___x_3739_, 2);
                v_auxDeclNGen_3744_ = crate::leanh::lean_ctor_get(v___x_3739_, 3);
                v_cache_3745_ = crate::leanh::lean_ctor_get(v___x_3739_, 5);
                v_messages_3746_ = crate::leanh::lean_ctor_get(v___x_3739_, 6);
                v_infoState_3747_ = crate::leanh::lean_ctor_get(v___x_3739_, 7);
                v_snapshotTasks_3748_ = crate::leanh::lean_ctor_get(v___x_3739_, 8);
                v_isSharedCheck_3778_ = (!crate::leanh::lean_is_exclusive(v___x_3739_)) as u8;
                if v_isSharedCheck_3778_ == 0 {
                    v___x_3750_ = v___x_3739_;
                    v_isShared_3751_ = v_isSharedCheck_3778_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3748_);
                    crate::leanh::lean_inc(v_infoState_3747_);
                    crate::leanh::lean_inc(v_messages_3746_);
                    crate::leanh::lean_inc(v_cache_3745_);
                    crate::leanh::lean_inc(v_traceState_3740_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3744_);
                    crate::leanh::lean_inc(v_ngen_3743_);
                    crate::leanh::lean_inc(v_nextMacroScope_3742_);
                    crate::leanh::lean_inc(v_env_3741_);
                    crate::leanh::lean_dec(v___x_3739_);
                    v___x_3750_ = crate::leanh::lean_box(0);
                    v_isShared_3751_ = v_isSharedCheck_3778_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3752_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_3740_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3753_ = crate::leanh::lean_ctor_get(v_traceState_3740_, 0);
                v_isSharedCheck_3777_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_3740_)) as u8;
                if v_isSharedCheck_3777_ == 0 {
                    v___x_3755_ = v_traceState_3740_;
                    v_isShared_3756_ = v_isSharedCheck_3777_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_3753_);
                    crate::leanh::lean_dec(v_traceState_3740_);
                    v___x_3755_ = crate::leanh::lean_box(0);
                    v_isShared_3756_ = v_isSharedCheck_3777_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3757_ = crate::leanh::lean_box(0);
                v___x_3758_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__2_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__2);
                v___x_3759_ = 0;
                v___x_3760_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__26;
                v___x_3761_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_3761_, 0, v_cls_3726_);
                crate::leanh::lean_ctor_set(v___x_3761_, 1, v___x_3757_);
                crate::leanh::lean_ctor_set(v___x_3761_, 2, v___x_3760_);
                crate::leanh::lean_ctor_set_float(
                    v___x_3761_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_3758_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_3761_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3758_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3761_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_3759_,
                );
                v___x_3762_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg___closed__0;
                v___x_3763_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3763_, 0, v___x_3761_);
                crate::leanh::lean_ctor_set(v___x_3763_, 1, v_a_3735_);
                crate::leanh::lean_ctor_set(v___x_3763_, 2, v___x_3762_);
                crate::leanh::lean_inc(v_ref_3733_);
                v___x_3764_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3764_, 0, v_ref_3733_);
                crate::leanh::lean_ctor_set(v___x_3764_, 1, v___x_3763_);
                v___x_3765_ = l_Lean_PersistentArray_push___redArg(v_traces_3753_, v___x_3764_);
                if v_isShared_3756_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3755_, 0, v___x_3765_);
                    v___x_3767_ = v___x_3755_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3776_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3776_, 0, v___x_3765_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3776_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_3752_,
                    );
                    v___x_3767_ = v_reuseFailAlloc_3776_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3751_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3750_, 4, v___x_3767_);
                    v___x_3769_ = v___x_3750_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3775_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_env_3741_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 1, v_nextMacroScope_3742_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 2, v_ngen_3743_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 3, v_auxDeclNGen_3744_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 4, v___x_3767_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 5, v_cache_3745_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 6, v_messages_3746_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 7, v_infoState_3747_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 8, v_snapshotTasks_3748_);
                    v___x_3769_ = v_reuseFailAlloc_3775_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3770_ = lean_st_ref_set(v___y_3731_, v___x_3769_);
                v___x_3771_ = crate::leanh::lean_box(0);
                if v_isShared_3738_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3737_, 0, v___x_3771_);
                    v___x_3773_ = v___x_3737_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3774_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3771_);
                    v___x_3773_ = v_reuseFailAlloc_3774_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3773_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg___boxed(
    mut v_cls_3780_: *mut crate::leanh::LeanObject,
    mut v_msg_3781_: *mut crate::leanh::LeanObject,
    mut v___y_3782_: *mut crate::leanh::LeanObject,
    mut v___y_3783_: *mut crate::leanh::LeanObject,
    mut v___y_3784_: *mut crate::leanh::LeanObject,
    mut v___y_3785_: *mut crate::leanh::LeanObject,
    mut v___y_3786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3787_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg(v_cls_3780_, v_msg_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
    crate::leanh::lean_dec(v___y_3785_);
    crate::leanh::lean_dec_ref(v___y_3784_);
    crate::leanh::lean_dec(v___y_3783_);
    crate::leanh::lean_dec_ref(v___y_3782_);
    return v_res_3787_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3791_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__1;
    v___x_3792_ = l_Lean_stringToMessageData(v___x_3791_);
    return v___x_3792_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg(
    mut v_as_x27_3793_: *mut crate::leanh::LeanObject,
    mut v_b_3794_: *mut crate::leanh::LeanObject,
    mut v___y_3795_: *mut crate::leanh::LeanObject,
    mut v___y_3796_: *mut crate::leanh::LeanObject,
    mut v___y_3797_: *mut crate::leanh::LeanObject,
    mut v___y_3798_: *mut crate::leanh::LeanObject,
    mut v___y_3799_: *mut crate::leanh::LeanObject,
    mut v___y_3800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3808_: u8 = 0;
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_run_x27_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3819_: u8 = 0;
    let mut v___x_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: u8 = 0;
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3835_: u8 = 0;
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3839_: u8 = 0;
    let mut v_a_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3843_: u8 = 0;
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3847_: u8 = 0;
    let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: u8 = 0;
    let mut v___y_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: f64 = 0.0;
    let mut v___x_3860_: f64 = 0.0;
    let mut v___x_3861_: f64 = 0.0;
    let mut v___x_3862_: f64 = 0.0;
    let mut v___x_3863_: f64 = 0.0;
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: f64 = 0.0;
    let mut v___x_3875_: f64 = 0.0;
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: u8 = 0;
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3891_: u8 = 0;
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3895_: u8 = 0;
    let mut v_a_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3899_: u8 = 0;
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3903_: u8 = 0;
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3909_: u8 = 0;
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3913_: u8 = 0;
    let mut v_a_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3917_: u8 = 0;
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3921_: u8 = 0;
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: u8 = 0;
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3925_: u8 = 0;
    let mut v_unused_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_3793_) == 0 {
                    v___x_3802_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3802_, 0, v_b_3794_);
                    return v___x_3802_;
                } else {
                    v_head_3803_ = crate::leanh::lean_ctor_get(v_as_x27_3793_, 0);
                    v_tail_3804_ = crate::leanh::lean_ctor_get(v_as_x27_3793_, 1);
                    v_snd_3805_ = crate::leanh::lean_ctor_get(v_b_3794_, 1);
                    v_isSharedCheck_3925_ = (!crate::leanh::lean_is_exclusive(v_b_3794_)) as u8;
                    if v_isSharedCheck_3925_ == 0 {
                        v_unused_3926_ = crate::leanh::lean_ctor_get(v_b_3794_, 0);
                        crate::leanh::lean_dec(v_unused_3926_);
                        v___x_3807_ = v_b_3794_;
                        v_isShared_3808_ = v_isSharedCheck_3925_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3805_);
                        crate::leanh::lean_dec(v_b_3794_);
                        v___x_3807_ = crate::leanh::lean_box(0);
                        v_isShared_3808_ = v_isSharedCheck_3925_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_options_3815_ = crate::leanh::lean_ctor_get(v___y_3799_, 2);
                v_name_3816_ = crate::leanh::lean_ctor_get(v_head_3803_, 0);
                v_run_x27_3817_ = crate::leanh::lean_ctor_get(v_head_3803_, 1);
                v_inheritedTraceOptions_3818_ = crate::leanh::lean_ctor_get(v___y_3799_, 13);
                v_hasTrace_3819_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_3815_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v___x_3820_ = crate::leanh::lean_box(0);
                if v_hasTrace_3819_ == 0 {
                    crate::leanh::lean_inc_ref(v_run_x27_3817_);
                    crate::leanh::lean_inc(v___y_3800_);
                    crate::leanh::lean_inc_ref(v___y_3799_);
                    crate::leanh::lean_inc(v___y_3798_);
                    crate::leanh::lean_inc_ref(v___y_3797_);
                    crate::leanh::lean_inc(v___y_3796_);
                    crate::leanh::lean_inc_ref(v___y_3795_);
                    crate::leanh::lean_inc(v_snd_3805_);
                    v___x_3848_ = crate::leanh::lean_apply_8(
                        v_run_x27_3817_,
                        v_snd_3805_,
                        v___y_3795_,
                        v___y_3796_,
                        v___y_3797_,
                        v___y_3798_,
                        v___y_3799_,
                        v___y_3800_,
                        crate::leanh::lean_box(0),
                    );
                    v___y_3822_ = v___x_3848_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3805_);
                    crate::leanh::lean_inc(v_name_3816_);
                    v___f_3849_ = crate::leanh::lean_alloc_closure(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 2);
                    crate::leanh::lean_closure_set(v___f_3849_, 0, v_name_3816_);
                    crate::leanh::lean_closure_set(v___f_3849_, 1, v_snd_3805_);
                    v___x_3850_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25;
                    v___x_3851_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__26;
                    v___x_3852_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29_once
                        ),
                        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29,
                    );
                    v___x_3853_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_3818_,
                        v_options_3815_,
                        v___x_3852_,
                    );
                    if v___x_3853_ == 0 {
                        v___x_3922_ = l_Lean_trace_profiler;
                        v___x_3923_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__2(v_options_3815_, v___x_3922_);
                        if v___x_3923_ == 0 {
                            crate::leanh::lean_dec_ref(v___f_3849_);
                            crate::leanh::lean_inc_ref(v_run_x27_3817_);
                            crate::leanh::lean_inc(v___y_3800_);
                            crate::leanh::lean_inc_ref(v___y_3799_);
                            crate::leanh::lean_inc(v___y_3798_);
                            crate::leanh::lean_inc_ref(v___y_3797_);
                            crate::leanh::lean_inc(v___y_3796_);
                            crate::leanh::lean_inc_ref(v___y_3795_);
                            crate::leanh::lean_inc(v_snd_3805_);
                            v___x_3924_ = crate::leanh::lean_apply_8(
                                v_run_x27_3817_,
                                v_snd_3805_,
                                v___y_3795_,
                                v___y_3796_,
                                v___y_3797_,
                                v___y_3798_,
                                v___y_3799_,
                                v___y_3800_,
                                crate::leanh::lean_box(0),
                            );
                            v___y_3822_ = v___x_3924_;
                            state = 4;
                            continue;
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
            2 => {
                v___x_3810_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__0;
                if v_isShared_3808_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3807_, 0, v___x_3810_);
                    v___x_3812_ = v___x_3807_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3814_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3814_, 0, v___x_3810_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3814_, 1, v_snd_3805_);
                    v___x_3812_ = v_reuseFailAlloc_3814_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3813_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3813_, 0, v___x_3812_);
                return v___x_3813_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v___y_3822_) == 0 {
                    v_a_3823_ = crate::leanh::lean_ctor_get(v___y_3822_, 0);
                    crate::leanh::lean_inc(v_a_3823_);
                    crate::leanh::lean_dec_ref_known(v___y_3822_, 1);
                    if crate::leanh::lean_obj_tag(v_a_3823_) == 1 {
                        crate::leanh::lean_del_object(v___x_3807_);
                        crate::leanh::lean_dec(v_snd_3805_);
                        v_val_3824_ = crate::leanh::lean_ctor_get(v_a_3823_, 0);
                        crate::leanh::lean_inc(v_val_3824_);
                        crate::leanh::lean_dec_ref_known(v_a_3823_, 1);
                        v___x_3825_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3825_, 0, v___x_3820_);
                        crate::leanh::lean_ctor_set(v___x_3825_, 1, v_val_3824_);
                        v_as_x27_3793_ = v_tail_3804_;
                        v_b_3794_ = v___x_3825_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_3823_);
                        if v_hasTrace_3819_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v___x_3827_ =
                                l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25;
                            v___x_3828_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29);
                            v___x_3829_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_3818_,
                                v_options_3815_,
                                v___x_3828_,
                            );
                            if v___x_3829_ == 0 {
                                state = 2;
                                continue;
                            } else {
                                v___x_3830_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__2_once), _init_l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__2);
                                v___x_3831_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg(v___x_3827_, v___x_3830_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
                                if crate::leanh::lean_obj_tag(v___x_3831_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3831_, 1);
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_del_object(v___x_3807_);
                                    crate::leanh::lean_dec(v_snd_3805_);
                                    v_a_3832_ = crate::leanh::lean_ctor_get(v___x_3831_, 0);
                                    v_isSharedCheck_3839_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3831_)) as u8;
                                    if v_isSharedCheck_3839_ == 0 {
                                        v___x_3834_ = v___x_3831_;
                                        v_isShared_3835_ = v_isSharedCheck_3839_;
                                        state = 5;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3832_);
                                        crate::leanh::lean_dec(v___x_3831_);
                                        v___x_3834_ = crate::leanh::lean_box(0);
                                        v_isShared_3835_ = v_isSharedCheck_3839_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3807_);
                    crate::leanh::lean_dec(v_snd_3805_);
                    v_a_3840_ = crate::leanh::lean_ctor_get(v___y_3822_, 0);
                    v_isSharedCheck_3847_ = (!crate::leanh::lean_is_exclusive(v___y_3822_)) as u8;
                    if v_isSharedCheck_3847_ == 0 {
                        v___x_3842_ = v___y_3822_;
                        v_isShared_3843_ = v_isSharedCheck_3847_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3840_);
                        crate::leanh::lean_dec(v___y_3822_);
                        v___x_3842_ = crate::leanh::lean_box(0);
                        v_isShared_3843_ = v_isSharedCheck_3847_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_3835_ == 0 {
                    v___x_3837_ = v___x_3834_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3838_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3832_);
                    v___x_3837_ = v_reuseFailAlloc_3838_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3837_;
            }
            7 => {
                if v_isShared_3843_ == 0 {
                    v___x_3845_ = v___x_3842_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3846_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3846_, 0, v_a_3840_);
                    v___x_3845_ = v_reuseFailAlloc_3846_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3845_;
            }
            9 => {
                v___x_3858_ = lean_io_mono_nanos_now();
                v___x_3859_ = lean_float_of_nat(v___y_3855_);
                v___x_3860_ = crate::leanh::lean_float_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30,
                );
                v___x_3861_ = lean_float_div(v___x_3859_, v___x_3860_);
                v___x_3862_ = lean_float_of_nat(v___x_3858_);
                v___x_3863_ = lean_float_div(v___x_3862_, v___x_3860_);
                v___x_3864_ = crate::leanh::lean_box_float(v___x_3861_);
                v___x_3865_ = crate::leanh::lean_box_float(v___x_3863_);
                v___x_3866_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3866_, 0, v___x_3864_);
                crate::leanh::lean_ctor_set(v___x_3866_, 1, v___x_3865_);
                v___x_3867_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3867_, 0, v_a_3857_);
                crate::leanh::lean_ctor_set(v___x_3867_, 1, v___x_3866_);
                v___x_3868_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3(v___x_3850_, v_hasTrace_3819_, v___x_3851_, v_options_3815_, v___x_3853_, v___y_3856_, v___f_3849_, v___x_3867_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
                v___y_3822_ = v___x_3868_;
                state = 4;
                continue;
            }
            10 => {
                v___x_3873_ = lean_io_get_num_heartbeats();
                v___x_3874_ = lean_float_of_nat(v___y_3870_);
                v___x_3875_ = lean_float_of_nat(v___x_3873_);
                v___x_3876_ = crate::leanh::lean_box_float(v___x_3874_);
                v___x_3877_ = crate::leanh::lean_box_float(v___x_3875_);
                v___x_3878_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3878_, 0, v___x_3876_);
                crate::leanh::lean_ctor_set(v___x_3878_, 1, v___x_3877_);
                v___x_3879_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3879_, 0, v_a_3872_);
                crate::leanh::lean_ctor_set(v___x_3879_, 1, v___x_3878_);
                v___x_3880_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3(v___x_3850_, v_hasTrace_3819_, v___x_3851_, v_options_3815_, v___x_3853_, v___y_3871_, v___f_3849_, v___x_3879_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
                v___y_3822_ = v___x_3880_;
                state = 4;
                continue;
            }
            11 => {
                v___x_3882_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg(v___y_3800_);
                v_a_3883_ = crate::leanh::lean_ctor_get(v___x_3882_, 0);
                crate::leanh::lean_inc(v_a_3883_);
                crate::leanh::lean_dec_ref(v___x_3882_);
                v___x_3884_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_3885_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__2(v_options_3815_, v___x_3884_);
                if v___x_3885_ == 0 {
                    v___x_3886_ = lean_io_mono_nanos_now();
                    crate::leanh::lean_inc_ref(v_run_x27_3817_);
                    crate::leanh::lean_inc(v___y_3800_);
                    crate::leanh::lean_inc_ref(v___y_3799_);
                    crate::leanh::lean_inc(v___y_3798_);
                    crate::leanh::lean_inc_ref(v___y_3797_);
                    crate::leanh::lean_inc(v___y_3796_);
                    crate::leanh::lean_inc_ref(v___y_3795_);
                    crate::leanh::lean_inc(v_snd_3805_);
                    v___x_3887_ = crate::leanh::lean_apply_8(
                        v_run_x27_3817_,
                        v_snd_3805_,
                        v___y_3795_,
                        v___y_3796_,
                        v___y_3797_,
                        v___y_3798_,
                        v___y_3799_,
                        v___y_3800_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3887_) == 0 {
                        v_a_3888_ = crate::leanh::lean_ctor_get(v___x_3887_, 0);
                        v_isSharedCheck_3895_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3887_)) as u8;
                        if v_isSharedCheck_3895_ == 0 {
                            v___x_3890_ = v___x_3887_;
                            v_isShared_3891_ = v_isSharedCheck_3895_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3888_);
                            crate::leanh::lean_dec(v___x_3887_);
                            v___x_3890_ = crate::leanh::lean_box(0);
                            v_isShared_3891_ = v_isSharedCheck_3895_;
                            state = 12;
                            continue;
                        }
                    } else {
                        v_a_3896_ = crate::leanh::lean_ctor_get(v___x_3887_, 0);
                        v_isSharedCheck_3903_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3887_)) as u8;
                        if v_isSharedCheck_3903_ == 0 {
                            v___x_3898_ = v___x_3887_;
                            v_isShared_3899_ = v_isSharedCheck_3903_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3896_);
                            crate::leanh::lean_dec(v___x_3887_);
                            v___x_3898_ = crate::leanh::lean_box(0);
                            v_isShared_3899_ = v_isSharedCheck_3903_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    v___x_3904_ = lean_io_get_num_heartbeats();
                    crate::leanh::lean_inc_ref(v_run_x27_3817_);
                    crate::leanh::lean_inc(v___y_3800_);
                    crate::leanh::lean_inc_ref(v___y_3799_);
                    crate::leanh::lean_inc(v___y_3798_);
                    crate::leanh::lean_inc_ref(v___y_3797_);
                    crate::leanh::lean_inc(v___y_3796_);
                    crate::leanh::lean_inc_ref(v___y_3795_);
                    crate::leanh::lean_inc(v_snd_3805_);
                    v___x_3905_ = crate::leanh::lean_apply_8(
                        v_run_x27_3817_,
                        v_snd_3805_,
                        v___y_3795_,
                        v___y_3796_,
                        v___y_3797_,
                        v___y_3798_,
                        v___y_3799_,
                        v___y_3800_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3905_) == 0 {
                        v_a_3906_ = crate::leanh::lean_ctor_get(v___x_3905_, 0);
                        v_isSharedCheck_3913_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3905_)) as u8;
                        if v_isSharedCheck_3913_ == 0 {
                            v___x_3908_ = v___x_3905_;
                            v_isShared_3909_ = v_isSharedCheck_3913_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3906_);
                            crate::leanh::lean_dec(v___x_3905_);
                            v___x_3908_ = crate::leanh::lean_box(0);
                            v_isShared_3909_ = v_isSharedCheck_3913_;
                            state = 16;
                            continue;
                        }
                    } else {
                        v_a_3914_ = crate::leanh::lean_ctor_get(v___x_3905_, 0);
                        v_isSharedCheck_3921_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3905_)) as u8;
                        if v_isSharedCheck_3921_ == 0 {
                            v___x_3916_ = v___x_3905_;
                            v_isShared_3917_ = v_isSharedCheck_3921_;
                            state = 18;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3914_);
                            crate::leanh::lean_dec(v___x_3905_);
                            v___x_3916_ = crate::leanh::lean_box(0);
                            v_isShared_3917_ = v_isSharedCheck_3921_;
                            state = 18;
                            continue;
                        }
                    }
                }
            }
            12 => {
                if v_isShared_3891_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3890_, 1);
                    v___x_3893_ = v___x_3890_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3894_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3888_);
                    v___x_3893_ = v_reuseFailAlloc_3894_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___y_3855_ = v___x_3886_;
                v___y_3856_ = v_a_3883_;
                v_a_3857_ = v___x_3893_;
                state = 9;
                continue;
            }
            14 => {
                if v_isShared_3899_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3898_, 0);
                    v___x_3901_ = v___x_3898_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3902_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_a_3896_);
                    v___x_3901_ = v_reuseFailAlloc_3902_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___y_3855_ = v___x_3886_;
                v___y_3856_ = v_a_3883_;
                v_a_3857_ = v___x_3901_;
                state = 9;
                continue;
            }
            16 => {
                if v_isShared_3909_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3908_, 1);
                    v___x_3911_ = v___x_3908_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3912_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
                    v___x_3911_ = v_reuseFailAlloc_3912_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___y_3870_ = v___x_3904_;
                v___y_3871_ = v_a_3883_;
                v_a_3872_ = v___x_3911_;
                state = 10;
                continue;
            }
            18 => {
                if v_isShared_3917_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3916_, 0);
                    v___x_3919_ = v___x_3916_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3920_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3914_);
                    v___x_3919_ = v_reuseFailAlloc_3920_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___y_3870_ = v___x_3904_;
                v___y_3871_ = v_a_3883_;
                v_a_3872_ = v___x_3919_;
                state = 10;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___boxed(
    mut v_as_x27_3927_: *mut crate::leanh::LeanObject,
    mut v_b_3928_: *mut crate::leanh::LeanObject,
    mut v___y_3929_: *mut crate::leanh::LeanObject,
    mut v___y_3930_: *mut crate::leanh::LeanObject,
    mut v___y_3931_: *mut crate::leanh::LeanObject,
    mut v___y_3932_: *mut crate::leanh::LeanObject,
    mut v___y_3933_: *mut crate::leanh::LeanObject,
    mut v___y_3934_: *mut crate::leanh::LeanObject,
    mut v___y_3935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3936_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg(v_as_x27_3927_, v_b_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_);
    crate::leanh::lean_dec(v___y_3934_);
    crate::leanh::lean_dec_ref(v___y_3933_);
    crate::leanh::lean_dec(v___y_3932_);
    crate::leanh::lean_dec_ref(v___y_3931_);
    crate::leanh::lean_dec(v___y_3930_);
    crate::leanh::lean_dec_ref(v___y_3929_);
    crate::leanh::lean_dec(v_as_x27_3927_);
    return v_res_3936_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3939_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__1;
    v___x_3940_ = l_Lean_stringToMessageData(v___x_3939_);
    return v___x_3940_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3942_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__3;
    v___x_3943_ = l_Lean_stringToMessageData(v___x_3942_);
    return v___x_3943_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(
    mut v_passes_3944_: *mut crate::leanh::LeanObject,
    mut v_goal_3945_: *mut crate::leanh::LeanObject,
    mut v_a_3946_: *mut crate::leanh::LeanObject,
    mut v_a_3947_: *mut crate::leanh::LeanObject,
    mut v_a_3948_: *mut crate::leanh::LeanObject,
    mut v_a_3949_: *mut crate::leanh::LeanObject,
    mut v_a_3950_: *mut crate::leanh::LeanObject,
    mut v_a_3951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3957_: u8 = 0;
    let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3964_: u8 = 0;
    let mut v_fst_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3969_: u8 = 0;
    let mut v___x_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: u8 = 0;
    let mut v_options_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3977_: u8 = 0;
    let mut v_inheritedTraceOptions_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: u8 = 0;
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3993_: u8 = 0;
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3997_: u8 = 0;
    let mut v_reuseFailAlloc_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4000_: u8 = 0;
    let mut v_inheritedTraceOptions_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: u8 = 0;
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4010_: u8 = 0;
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4014_: u8 = 0;
    let mut v_val_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4019_: u8 = 0;
    let mut v_isSharedCheck_4020_: u8 = 0;
    let mut v_a_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4024_: u8 = 0;
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4028_: u8 = 0;
    let mut v_isSharedCheck_4029_: u8 = 0;
    let mut v_unused_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4034_: u8 = 0;
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4038_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3953_ =
                    l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__0;
                v___x_3954_ = l_Lean_Core_checkSystem(v___x_3953_, v_a_3950_, v_a_3951_);
                if crate::leanh::lean_obj_tag(v___x_3954_) == 0 {
                    v_isSharedCheck_4029_ = (!crate::leanh::lean_is_exclusive(v___x_3954_)) as u8;
                    if v_isSharedCheck_4029_ == 0 {
                        v_unused_4030_ = crate::leanh::lean_ctor_get(v___x_3954_, 0);
                        crate::leanh::lean_dec(v_unused_4030_);
                        v___x_3956_ = v___x_3954_;
                        v_isShared_3957_ = v_isSharedCheck_4029_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3954_);
                        v___x_3956_ = crate::leanh::lean_box(0);
                        v_isShared_3957_ = v_isSharedCheck_4029_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_goal_3945_);
                    v_a_4031_ = crate::leanh::lean_ctor_get(v___x_3954_, 0);
                    v_isSharedCheck_4038_ = (!crate::leanh::lean_is_exclusive(v___x_3954_)) as u8;
                    if v_isSharedCheck_4038_ == 0 {
                        v___x_4033_ = v___x_3954_;
                        v_isShared_4034_ = v_isSharedCheck_4038_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4031_);
                        crate::leanh::lean_dec(v___x_3954_);
                        v___x_4033_ = crate::leanh::lean_box(0);
                        v_isShared_4034_ = v_isSharedCheck_4038_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3958_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_goal_3945_);
                v___x_3959_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3959_, 0, v___x_3958_);
                crate::leanh::lean_ctor_set(v___x_3959_, 1, v_goal_3945_);
                v___x_3960_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg(v_passes_3944_, v___x_3959_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_);
                if crate::leanh::lean_obj_tag(v___x_3960_) == 0 {
                    v_a_3961_ = crate::leanh::lean_ctor_get(v___x_3960_, 0);
                    v_isSharedCheck_4020_ = (!crate::leanh::lean_is_exclusive(v___x_3960_)) as u8;
                    if v_isSharedCheck_4020_ == 0 {
                        v___x_3963_ = v___x_3960_;
                        v_isShared_3964_ = v_isSharedCheck_4020_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3961_);
                        crate::leanh::lean_dec(v___x_3960_);
                        v___x_3963_ = crate::leanh::lean_box(0);
                        v_isShared_3964_ = v_isSharedCheck_4020_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3956_);
                    crate::leanh::lean_dec(v_goal_3945_);
                    v_a_4021_ = crate::leanh::lean_ctor_get(v___x_3960_, 0);
                    v_isSharedCheck_4028_ = (!crate::leanh::lean_is_exclusive(v___x_3960_)) as u8;
                    if v_isSharedCheck_4028_ == 0 {
                        v___x_4023_ = v___x_3960_;
                        v_isShared_4024_ = v_isSharedCheck_4028_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4021_);
                        crate::leanh::lean_dec(v___x_3960_);
                        v___x_4023_ = crate::leanh::lean_box(0);
                        v_isShared_4024_ = v_isSharedCheck_4028_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_3965_ = crate::leanh::lean_ctor_get(v_a_3961_, 0);
                v_snd_3966_ = crate::leanh::lean_ctor_get(v_a_3961_, 1);
                v_isSharedCheck_4019_ = (!crate::leanh::lean_is_exclusive(v_a_3961_)) as u8;
                if v_isSharedCheck_4019_ == 0 {
                    v___x_3968_ = v_a_3961_;
                    v_isShared_3969_ = v_isSharedCheck_4019_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3966_);
                    crate::leanh::lean_inc(v_fst_3965_);
                    crate::leanh::lean_dec(v_a_3961_);
                    v___x_3968_ = crate::leanh::lean_box(0);
                    v_isShared_3969_ = v_isSharedCheck_4019_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_fst_3965_) == 0 {
                    crate::leanh::lean_del_object(v___x_3956_);
                    v___x_3975_ = l_Lean_instBEqMVarId_beq(v_goal_3945_, v_snd_3966_);
                    crate::leanh::lean_dec(v_goal_3945_);
                    if v___x_3975_ == 0 {
                        crate::leanh::lean_del_object(v___x_3963_);
                        v_options_3976_ = crate::leanh::lean_ctor_get(v_a_3950_, 2);
                        v_hasTrace_3977_ = crate::leanh::lean_ctor_get_uint8(
                            v_options_3976_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_3977_ == 0 {
                            crate::leanh::lean_del_object(v___x_3968_);
                            v_goal_3945_ = v_snd_3966_;
                            state = 0;
                            continue;
                        } else {
                            v_inheritedTraceOptions_3979_ =
                                crate::leanh::lean_ctor_get(v_a_3950_, 13);
                            v___x_3980_ =
                                l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25;
                            v___x_3981_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29);
                            v___x_3982_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_3979_,
                                v_options_3976_,
                                v___x_3981_,
                            );
                            if v___x_3982_ == 0 {
                                crate::leanh::lean_del_object(v___x_3968_);
                                v_goal_3945_ = v_snd_3966_;
                                state = 0;
                                continue;
                            } else {
                                v___x_3984_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__2_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__2);
                                crate::leanh::lean_inc(v_snd_3966_);
                                v___x_3985_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3985_, 0, v_snd_3966_);
                                if v_isShared_3969_ == 0 {
                                    crate::leanh::lean_ctor_set_tag(v___x_3968_, 7);
                                    crate::leanh::lean_ctor_set(v___x_3968_, 1, v___x_3985_);
                                    crate::leanh::lean_ctor_set(v___x_3968_, 0, v___x_3984_);
                                    v___x_3987_ = v___x_3968_;
                                    state = 6;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3998_ =
                                        crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3998_,
                                        0,
                                        v___x_3984_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3998_,
                                        1,
                                        v___x_3985_,
                                    );
                                    v___x_3987_ = v_reuseFailAlloc_3998_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3968_);
                        v_options_3999_ = crate::leanh::lean_ctor_get(v_a_3950_, 2);
                        v_hasTrace_4000_ = crate::leanh::lean_ctor_get_uint8(
                            v_options_3999_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_4000_ == 0 {
                            state = 4;
                            continue;
                        } else {
                            v_inheritedTraceOptions_4001_ =
                                crate::leanh::lean_ctor_get(v_a_3950_, 13);
                            v___x_4002_ =
                                l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25;
                            v___x_4003_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29);
                            v___x_4004_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_4001_,
                                v_options_3999_,
                                v___x_4003_,
                            );
                            if v___x_4004_ == 0 {
                                state = 4;
                                continue;
                            } else {
                                v___x_4005_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__4), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__4_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__4);
                                v___x_4006_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg(v___x_4002_, v___x_4005_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_);
                                if crate::leanh::lean_obj_tag(v___x_4006_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_4006_, 1);
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_snd_3966_);
                                    crate::leanh::lean_del_object(v___x_3963_);
                                    v_a_4007_ = crate::leanh::lean_ctor_get(v___x_4006_, 0);
                                    v_isSharedCheck_4014_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4006_)) as u8;
                                    if v_isSharedCheck_4014_ == 0 {
                                        v___x_4009_ = v___x_4006_;
                                        v_isShared_4010_ = v_isSharedCheck_4014_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4007_);
                                        crate::leanh::lean_dec(v___x_4006_);
                                        v___x_4009_ = crate::leanh::lean_box(0);
                                        v_isShared_4010_ = v_isSharedCheck_4014_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3968_);
                    crate::leanh::lean_dec(v_snd_3966_);
                    crate::leanh::lean_del_object(v___x_3963_);
                    crate::leanh::lean_dec(v_goal_3945_);
                    v_val_4015_ = crate::leanh::lean_ctor_get(v_fst_3965_, 0);
                    crate::leanh::lean_inc(v_val_4015_);
                    crate::leanh::lean_dec_ref_known(v_fst_3965_, 1);
                    if v_isShared_3957_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3956_, 0, v_val_4015_);
                        v___x_4017_ = v___x_3956_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_4018_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_val_4015_);
                        v___x_4017_ = v_reuseFailAlloc_4018_;
                        state = 11;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3971_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3971_, 0, v_snd_3966_);
                if v_isShared_3964_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3963_, 0, v___x_3971_);
                    v___x_3973_ = v___x_3963_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3974_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3974_, 0, v___x_3971_);
                    v___x_3973_ = v_reuseFailAlloc_3974_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3973_;
            }
            6 => {
                v___x_3988_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg(v___x_3980_, v___x_3987_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_);
                if crate::leanh::lean_obj_tag(v___x_3988_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3988_, 1);
                    v_goal_3945_ = v_snd_3966_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_snd_3966_);
                    v_a_3990_ = crate::leanh::lean_ctor_get(v___x_3988_, 0);
                    v_isSharedCheck_3997_ = (!crate::leanh::lean_is_exclusive(v___x_3988_)) as u8;
                    if v_isSharedCheck_3997_ == 0 {
                        v___x_3992_ = v___x_3988_;
                        v_isShared_3993_ = v_isSharedCheck_3997_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3990_);
                        crate::leanh::lean_dec(v___x_3988_);
                        v___x_3992_ = crate::leanh::lean_box(0);
                        v_isShared_3993_ = v_isSharedCheck_3997_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_3993_ == 0 {
                    v___x_3995_ = v___x_3992_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3996_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3990_);
                    v___x_3995_ = v_reuseFailAlloc_3996_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3995_;
            }
            9 => {
                if v_isShared_4010_ == 0 {
                    v___x_4012_ = v___x_4009_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4013_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_a_4007_);
                    v___x_4012_ = v_reuseFailAlloc_4013_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4012_;
            }
            11 => {
                return v___x_4017_;
            }
            12 => {
                if v_isShared_4024_ == 0 {
                    v___x_4026_ = v___x_4023_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4027_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4027_, 0, v_a_4021_);
                    v___x_4026_ = v_reuseFailAlloc_4027_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4026_;
            }
            14 => {
                if v_isShared_4034_ == 0 {
                    v___x_4036_ = v___x_4033_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4037_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_a_4031_);
                    v___x_4036_ = v_reuseFailAlloc_4037_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4036_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___boxed(
    mut v_passes_4039_: *mut crate::leanh::LeanObject,
    mut v_goal_4040_: *mut crate::leanh::LeanObject,
    mut v_a_4041_: *mut crate::leanh::LeanObject,
    mut v_a_4042_: *mut crate::leanh::LeanObject,
    mut v_a_4043_: *mut crate::leanh::LeanObject,
    mut v_a_4044_: *mut crate::leanh::LeanObject,
    mut v_a_4045_: *mut crate::leanh::LeanObject,
    mut v_a_4046_: *mut crate::leanh::LeanObject,
    mut v_a_4047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4048_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(
        v_passes_4039_,
        v_goal_4040_,
        v_a_4041_,
        v_a_4042_,
        v_a_4043_,
        v_a_4044_,
        v_a_4045_,
        v_a_4046_,
    );
    crate::leanh::lean_dec(v_a_4046_);
    crate::leanh::lean_dec_ref(v_a_4045_);
    crate::leanh::lean_dec(v_a_4044_);
    crate::leanh::lean_dec_ref(v_a_4043_);
    crate::leanh::lean_dec(v_a_4042_);
    crate::leanh::lean_dec_ref(v_a_4041_);
    crate::leanh::lean_dec(v_passes_4039_);
    return v_res_4048_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0(
    mut v_cls_4049_: *mut crate::leanh::LeanObject,
    mut v_msg_4050_: *mut crate::leanh::LeanObject,
    mut v___y_4051_: *mut crate::leanh::LeanObject,
    mut v___y_4052_: *mut crate::leanh::LeanObject,
    mut v___y_4053_: *mut crate::leanh::LeanObject,
    mut v___y_4054_: *mut crate::leanh::LeanObject,
    mut v___y_4055_: *mut crate::leanh::LeanObject,
    mut v___y_4056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4058_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg(v_cls_4049_, v_msg_4050_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
    return v___x_4058_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___boxed(
    mut v_cls_4059_: *mut crate::leanh::LeanObject,
    mut v_msg_4060_: *mut crate::leanh::LeanObject,
    mut v___y_4061_: *mut crate::leanh::LeanObject,
    mut v___y_4062_: *mut crate::leanh::LeanObject,
    mut v___y_4063_: *mut crate::leanh::LeanObject,
    mut v___y_4064_: *mut crate::leanh::LeanObject,
    mut v___y_4065_: *mut crate::leanh::LeanObject,
    mut v___y_4066_: *mut crate::leanh::LeanObject,
    mut v___y_4067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4068_ =
        l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0(
            v_cls_4059_,
            v_msg_4060_,
            v___y_4061_,
            v___y_4062_,
            v___y_4063_,
            v___y_4064_,
            v___y_4065_,
            v___y_4066_,
        );
    crate::leanh::lean_dec(v___y_4066_);
    crate::leanh::lean_dec_ref(v___y_4065_);
    crate::leanh::lean_dec(v___y_4064_);
    crate::leanh::lean_dec_ref(v___y_4063_);
    crate::leanh::lean_dec(v___y_4062_);
    crate::leanh::lean_dec_ref(v___y_4061_);
    return v_res_4068_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__6(
    mut v_00_u03b1_4069_: *mut crate::leanh::LeanObject,
    mut v_x_4070_: *mut crate::leanh::LeanObject,
    mut v___y_4071_: *mut crate::leanh::LeanObject,
    mut v___y_4072_: *mut crate::leanh::LeanObject,
    mut v___y_4073_: *mut crate::leanh::LeanObject,
    mut v___y_4074_: *mut crate::leanh::LeanObject,
    mut v___y_4075_: *mut crate::leanh::LeanObject,
    mut v___y_4076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4078_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__6___redArg(v_x_4070_);
    return v___x_4078_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__6___boxed(
    mut v_00_u03b1_4079_: *mut crate::leanh::LeanObject,
    mut v_x_4080_: *mut crate::leanh::LeanObject,
    mut v___y_4081_: *mut crate::leanh::LeanObject,
    mut v___y_4082_: *mut crate::leanh::LeanObject,
    mut v___y_4083_: *mut crate::leanh::LeanObject,
    mut v___y_4084_: *mut crate::leanh::LeanObject,
    mut v___y_4085_: *mut crate::leanh::LeanObject,
    mut v___y_4086_: *mut crate::leanh::LeanObject,
    mut v___y_4087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4088_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__6(v_00_u03b1_4079_, v_x_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_);
    crate::leanh::lean_dec(v___y_4086_);
    crate::leanh::lean_dec_ref(v___y_4085_);
    crate::leanh::lean_dec(v___y_4084_);
    crate::leanh::lean_dec_ref(v___y_4083_);
    crate::leanh::lean_dec(v___y_4082_);
    crate::leanh::lean_dec_ref(v___y_4081_);
    return v_res_4088_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4(
    mut v_as_4089_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4090_: *mut crate::leanh::LeanObject,
    mut v_b_4091_: *mut crate::leanh::LeanObject,
    mut v_a_4092_: *mut crate::leanh::LeanObject,
    mut v___y_4093_: *mut crate::leanh::LeanObject,
    mut v___y_4094_: *mut crate::leanh::LeanObject,
    mut v___y_4095_: *mut crate::leanh::LeanObject,
    mut v___y_4096_: *mut crate::leanh::LeanObject,
    mut v___y_4097_: *mut crate::leanh::LeanObject,
    mut v___y_4098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4100_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg(v_as_x27_4090_, v_b_4091_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_);
    return v___x_4100_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___boxed(
    mut v_as_4101_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4102_: *mut crate::leanh::LeanObject,
    mut v_b_4103_: *mut crate::leanh::LeanObject,
    mut v_a_4104_: *mut crate::leanh::LeanObject,
    mut v___y_4105_: *mut crate::leanh::LeanObject,
    mut v___y_4106_: *mut crate::leanh::LeanObject,
    mut v___y_4107_: *mut crate::leanh::LeanObject,
    mut v___y_4108_: *mut crate::leanh::LeanObject,
    mut v___y_4109_: *mut crate::leanh::LeanObject,
    mut v___y_4110_: *mut crate::leanh::LeanObject,
    mut v___y_4111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4112_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4(v_as_4101_, v_as_x27_4102_, v_b_4103_, v_a_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
    crate::leanh::lean_dec(v___y_4110_);
    crate::leanh::lean_dec_ref(v___y_4109_);
    crate::leanh::lean_dec(v___y_4108_);
    crate::leanh::lean_dec_ref(v___y_4107_);
    crate::leanh::lean_dec(v___y_4106_);
    crate::leanh::lean_dec_ref(v___y_4105_);
    crate::leanh::lean_dec(v_as_x27_4102_);
    crate::leanh::lean_dec(v_as_4101_);
    return v_res_4112_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5(
    mut v_oldTraces_4113_: *mut crate::leanh::LeanObject,
    mut v_data_4114_: *mut crate::leanh::LeanObject,
    mut v_ref_4115_: *mut crate::leanh::LeanObject,
    mut v_msg_4116_: *mut crate::leanh::LeanObject,
    mut v___y_4117_: *mut crate::leanh::LeanObject,
    mut v___y_4118_: *mut crate::leanh::LeanObject,
    mut v___y_4119_: *mut crate::leanh::LeanObject,
    mut v___y_4120_: *mut crate::leanh::LeanObject,
    mut v___y_4121_: *mut crate::leanh::LeanObject,
    mut v___y_4122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4124_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5___redArg(v_oldTraces_4113_, v_data_4114_, v_ref_4115_, v_msg_4116_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_);
    return v___x_4124_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5___boxed(
    mut v_oldTraces_4125_: *mut crate::leanh::LeanObject,
    mut v_data_4126_: *mut crate::leanh::LeanObject,
    mut v_ref_4127_: *mut crate::leanh::LeanObject,
    mut v_msg_4128_: *mut crate::leanh::LeanObject,
    mut v___y_4129_: *mut crate::leanh::LeanObject,
    mut v___y_4130_: *mut crate::leanh::LeanObject,
    mut v___y_4131_: *mut crate::leanh::LeanObject,
    mut v___y_4132_: *mut crate::leanh::LeanObject,
    mut v___y_4133_: *mut crate::leanh::LeanObject,
    mut v___y_4134_: *mut crate::leanh::LeanObject,
    mut v___y_4135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4136_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5(v_oldTraces_4125_, v_data_4126_, v_ref_4127_, v_msg_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_);
    crate::leanh::lean_dec(v___y_4134_);
    crate::leanh::lean_dec_ref(v___y_4133_);
    crate::leanh::lean_dec(v___y_4132_);
    crate::leanh::lean_dec_ref(v___y_4131_);
    crate::leanh::lean_dec(v___y_4130_);
    crate::leanh::lean_dec_ref(v___y_4129_);
    return v_res_4136_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Attr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(
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
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_BVDecide_Attr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
}
