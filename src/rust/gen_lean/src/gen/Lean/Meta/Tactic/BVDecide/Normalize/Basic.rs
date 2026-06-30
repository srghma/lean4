// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.Basic
// Imports: Lean.Meta.Tactic.BVDecide.Attr Std.Tactic.BVDecide.Syntax
use crate::ffi::{
    lean_array_get_size, lean_array_size, lean_array_uget_borrowed, lean_array_uset,
    lean_float_decLt, lean_float_div, lean_float_sub, lean_io_get_num_heartbeats,
    lean_io_mono_nanos_now, lean_mk_array, lean_mk_empty_array_with_capacity, lean_nat_div,
    lean_nat_mul, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_usize_add, lean_usize_dec_lt,
};
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
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqFVarId_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableFVarId_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__4_value:
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
    m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__5_value:
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
    m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__6_value:
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
    m_fun: l_Lean_Meta_getPropHyps___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__6_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0_value:
    leanh::LeanStringObject<15> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__2_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0_value:
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
    m_fun: l_ReaderT_instMonadLift___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1_value:
    leanh::LeanClosureObject<3> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateRefT_x27_lift___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6_value:
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
    m_fun: l_ReaderT_instMonadFunctor___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7_value:
    leanh::LeanClosureObject<3> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateRefT_x27_instMonadFunctor___aux__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__14:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__16_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__16:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__17_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__17:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__18_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__18:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__19_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__19:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__20_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__20:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__21_value:
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
    m_fun: l_Lean_instExceptToTraceResultOption___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__21:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__22_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__23_value:
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
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__23:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__23_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__24_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__24_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__22_value)
            as *mut leanh::LeanObject,
        142734480563613395 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__23_value)
            as *mut leanh::LeanObject,
        15847151208953044930 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__24_value)
            as *mut leanh::LeanObject,
        10551690841954068875 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__26_value:
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
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__26:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__26_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__27_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
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
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__27:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__27_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__28_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__27_value)
            as *mut leanh::LeanObject,
        14231257465488249300 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__28:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__28_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30: f64 = 0.0;
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__2: f64 = 0.0;
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__3_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [60, 101, 120, 99, 101, 112, 116, 105, 111, 110, 32, 116, 104, 114, 111, 119, 110, 32, 119, 104, 105, 108, 101, 32, 112, 114, 111, 100, 117, 99, 105, 110, 103, 32, 116, 114, 97, 99, 101, 32, 110, 111, 100, 101, 32, 109, 101, 115, 115, 97, 103, 101, 62, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__5: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__1_value: leanh::LeanStringObject<35> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [70, 105, 120, 112, 111, 105, 110, 116, 32, 105, 116, 101, 114, 97, 116, 105, 111, 110, 32, 115, 111, 108, 118, 101, 100, 32, 116, 104, 101, 32, 103, 111, 97, 108, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__0_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__1_value:
    leanh::LeanStringObject<24> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__1_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__3_value:
    leanh::LeanStringObject<28> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__3_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx(
    mut v_x_2069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2069_) == 0 {
        let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2070_ = leanh::lean_unsigned_to_nat(0);
        return v___x_2070_;
    } else {
        let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2071_ = leanh::lean_unsigned_to_nat(1);
        return v___x_2071_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx___boxed(
    mut v_x_2072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2073_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorIdx(v_x_2072_);
    leanh::lean_dec_ref(v_x_2072_);
    return v_res_2073_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(
    mut v_t_2074_: *mut leanh::LeanObject,
    mut v_k_2075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_info_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_info_2076_ = leanh::lean_ctor_get(v_t_2074_, 0);
    leanh::lean_inc_ref(v_info_2076_);
    v_ctors_2077_ = leanh::lean_ctor_get(v_t_2074_, 1);
    leanh::lean_inc_ref(v_ctors_2077_);
    leanh::lean_dec_ref(v_t_2074_);
    v___x_2078_ = leanh::lean_apply_2(v_k_2075_, v_info_2076_, v_ctors_2077_);
    return v___x_2078_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim(
    mut v_motive_2079_: *mut leanh::LeanObject,
    mut v_ctorIdx_2080_: *mut leanh::LeanObject,
    mut v_t_2081_: *mut leanh::LeanObject,
    mut v_h_2082_: *mut leanh::LeanObject,
    mut v_k_2083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2084_ =
        l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(v_t_2081_, v_k_2083_);
    return v___x_2084_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___boxed(
    mut v_motive_2085_: *mut leanh::LeanObject,
    mut v_ctorIdx_2086_: *mut leanh::LeanObject,
    mut v_t_2087_: *mut leanh::LeanObject,
    mut v_h_2088_: *mut leanh::LeanObject,
    mut v_k_2089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2090_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim(
        v_motive_2085_,
        v_ctorIdx_2086_,
        v_t_2087_,
        v_h_2088_,
        v_k_2089_,
    );
    leanh::lean_dec(v_ctorIdx_2086_);
    return v_res_2090_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_simpleEnum_elim___redArg(
    mut v_t_2091_: *mut leanh::LeanObject,
    mut v_simpleEnum_2092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2093_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(
        v_t_2091_,
        v_simpleEnum_2092_,
    );
    return v___x_2093_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_simpleEnum_elim(
    mut v_motive_2094_: *mut leanh::LeanObject,
    mut v_t_2095_: *mut leanh::LeanObject,
    mut v_h_2096_: *mut leanh::LeanObject,
    mut v_simpleEnum_2097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2098_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(
        v_t_2095_,
        v_simpleEnum_2097_,
    );
    return v___x_2098_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_enumWithDefault_elim___redArg(
    mut v_t_2099_: *mut leanh::LeanObject,
    mut v_enumWithDefault_2100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2101_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(
        v_t_2099_,
        v_enumWithDefault_2100_,
    );
    return v___x_2101_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_enumWithDefault_elim(
    mut v_motive_2102_: *mut leanh::LeanObject,
    mut v_t_2103_: *mut leanh::LeanObject,
    mut v_h_2104_: *mut leanh::LeanObject,
    mut v_enumWithDefault_2105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2106_ = l_Lean_Meta_Tactic_BVDecide_Normalize_MatchKind_ctorElim___redArg(
        v_t_2103_,
        v_enumWithDefault_2105_,
    );
    return v___x_2106_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg(
    mut v_a_2107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_a_2107_);
    v___x_2109_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2109_, 0, v_a_2107_);
    return v___x_2109_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg___boxed(
    mut v_a_2110_: *mut leanh::LeanObject,
    mut v_a_2111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2112_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___redArg(v_a_2110_);
    leanh::lean_dec_ref(v_a_2110_);
    return v_res_2112_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig(
    mut v_a_2113_: *mut leanh::LeanObject,
    mut v_a_2114_: *mut leanh::LeanObject,
    mut v_a_2115_: *mut leanh::LeanObject,
    mut v_a_2116_: *mut leanh::LeanObject,
    mut v_a_2117_: *mut leanh::LeanObject,
    mut v_a_2118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_a_2113_);
    v___x_2120_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2120_, 0, v_a_2113_);
    return v___x_2120_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig___boxed(
    mut v_a_2121_: *mut leanh::LeanObject,
    mut v_a_2122_: *mut leanh::LeanObject,
    mut v_a_2123_: *mut leanh::LeanObject,
    mut v_a_2124_: *mut leanh::LeanObject,
    mut v_a_2125_: *mut leanh::LeanObject,
    mut v_a_2126_: *mut leanh::LeanObject,
    mut v_a_2127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2128_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getConfig(
        v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_,
    );
    leanh::lean_dec(v_a_2126_);
    leanh::lean_dec_ref(v_a_2125_);
    leanh::lean_dec(v_a_2124_);
    leanh::lean_dec_ref(v_a_2123_);
    leanh::lean_dec(v_a_2122_);
    leanh::lean_dec_ref(v_a_2121_);
    return v_res_2128_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg(
    mut v_fvar_2131_: *mut leanh::LeanObject,
    mut v_a_2132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: u8 = 0;
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2134_ = lean_st_ref_get(v_a_2132_);
    v_rewriteCache_2135_ = leanh::lean_ctor_get(v___x_2134_, 0);
    leanh::lean_inc_ref(v_rewriteCache_2135_);
    leanh::lean_dec(v___x_2134_);
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
    leanh::lean_dec_ref(v_rewriteCache_2135_);
    v___x_2139_ = leanh::lean_box((v___x_2138_) as usize);
    v___x_2140_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2140_, 0, v___x_2139_);
    return v___x_2140_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___boxed(
    mut v_fvar_2141_: *mut leanh::LeanObject,
    mut v_a_2142_: *mut leanh::LeanObject,
    mut v_a_2143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2144_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg(
        v_fvar_2141_,
        v_a_2142_,
    );
    leanh::lean_dec(v_a_2142_);
    return v_res_2144_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten(
    mut v_fvar_2145_: *mut leanh::LeanObject,
    mut v_a_2146_: *mut leanh::LeanObject,
    mut v_a_2147_: *mut leanh::LeanObject,
    mut v_a_2148_: *mut leanh::LeanObject,
    mut v_a_2149_: *mut leanh::LeanObject,
    mut v_a_2150_: *mut leanh::LeanObject,
    mut v_a_2151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: u8 = 0;
    let mut v___x_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2153_ = lean_st_ref_get(v_a_2147_);
    v_rewriteCache_2154_ = leanh::lean_ctor_get(v___x_2153_, 0);
    leanh::lean_inc_ref(v_rewriteCache_2154_);
    leanh::lean_dec(v___x_2153_);
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
    leanh::lean_dec_ref(v_rewriteCache_2154_);
    v___x_2158_ = leanh::lean_box((v___x_2157_) as usize);
    v___x_2159_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2159_, 0, v___x_2158_);
    return v___x_2159_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___boxed(
    mut v_fvar_2160_: *mut leanh::LeanObject,
    mut v_a_2161_: *mut leanh::LeanObject,
    mut v_a_2162_: *mut leanh::LeanObject,
    mut v_a_2163_: *mut leanh::LeanObject,
    mut v_a_2164_: *mut leanh::LeanObject,
    mut v_a_2165_: *mut leanh::LeanObject,
    mut v_a_2166_: *mut leanh::LeanObject,
    mut v_a_2167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2168_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten(
        v_fvar_2160_,
        v_a_2161_,
        v_a_2162_,
        v_a_2163_,
        v_a_2164_,
        v_a_2165_,
        v_a_2166_,
    );
    leanh::lean_dec(v_a_2166_);
    leanh::lean_dec_ref(v_a_2165_);
    leanh::lean_dec(v_a_2164_);
    leanh::lean_dec_ref(v_a_2163_);
    leanh::lean_dec(v_a_2162_);
    leanh::lean_dec_ref(v_a_2161_);
    return v_res_2168_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkAcNf___redArg(
    mut v_fvar_2169_: *mut leanh::LeanObject,
    mut v_a_2170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: u8 = 0;
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2172_ = lean_st_ref_get(v_a_2170_);
    v_acNfCache_2173_ = leanh::lean_ctor_get(v___x_2172_, 1);
    leanh::lean_inc_ref(v_acNfCache_2173_);
    leanh::lean_dec(v___x_2172_);
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
    leanh::lean_dec_ref(v_acNfCache_2173_);
    v___x_2177_ = leanh::lean_box((v___x_2176_) as usize);
    v___x_2178_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2178_, 0, v___x_2177_);
    return v___x_2178_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkAcNf___redArg___boxed(
    mut v_fvar_2179_: *mut leanh::LeanObject,
    mut v_a_2180_: *mut leanh::LeanObject,
    mut v_a_2181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2182_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkAcNf___redArg(
        v_fvar_2179_,
        v_a_2180_,
    );
    leanh::lean_dec(v_a_2180_);
    return v_res_2182_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkAcNf(
    mut v_fvar_2183_: *mut leanh::LeanObject,
    mut v_a_2184_: *mut leanh::LeanObject,
    mut v_a_2185_: *mut leanh::LeanObject,
    mut v_a_2186_: *mut leanh::LeanObject,
    mut v_a_2187_: *mut leanh::LeanObject,
    mut v_a_2188_: *mut leanh::LeanObject,
    mut v_a_2189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: u8 = 0;
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2191_ = lean_st_ref_get(v_a_2185_);
    v_acNfCache_2192_ = leanh::lean_ctor_get(v___x_2191_, 1);
    leanh::lean_inc_ref(v_acNfCache_2192_);
    leanh::lean_dec(v___x_2191_);
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
    leanh::lean_dec_ref(v_acNfCache_2192_);
    v___x_2196_ = leanh::lean_box((v___x_2195_) as usize);
    v___x_2197_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2197_, 0, v___x_2196_);
    return v___x_2197_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkAcNf___boxed(
    mut v_fvar_2198_: *mut leanh::LeanObject,
    mut v_a_2199_: *mut leanh::LeanObject,
    mut v_a_2200_: *mut leanh::LeanObject,
    mut v_a_2201_: *mut leanh::LeanObject,
    mut v_a_2202_: *mut leanh::LeanObject,
    mut v_a_2203_: *mut leanh::LeanObject,
    mut v_a_2204_: *mut leanh::LeanObject,
    mut v_a_2205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2206_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkAcNf(
        v_fvar_2198_,
        v_a_2199_,
        v_a_2200_,
        v_a_2201_,
        v_a_2202_,
        v_a_2203_,
        v_a_2204_,
    );
    leanh::lean_dec(v_a_2204_);
    leanh::lean_dec_ref(v_a_2203_);
    leanh::lean_dec(v_a_2202_);
    leanh::lean_dec_ref(v_a_2201_);
    leanh::lean_dec(v_a_2200_);
    leanh::lean_dec_ref(v_a_2199_);
    return v_res_2206_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_rewriteFinished___redArg(
    mut v_fvar_2207_: *mut leanh::LeanObject,
    mut v_a_2208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2216_: u8 = 0;
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2226_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2210_ = lean_st_ref_take(v_a_2208_);
                v_rewriteCache_2211_ = leanh::lean_ctor_get(v___x_2210_, 0);
                v_acNfCache_2212_ = leanh::lean_ctor_get(v___x_2210_, 1);
                v_typeAnalysis_2213_ = leanh::lean_ctor_get(v___x_2210_, 2);
                v_isSharedCheck_2226_ = (!leanh::lean_is_exclusive(v___x_2210_)) as u8;
                if v_isSharedCheck_2226_ == 0 {
                    v___x_2215_ = v___x_2210_;
                    v_isShared_2216_ = v_isSharedCheck_2226_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_typeAnalysis_2213_);
                    leanh::lean_inc(v_acNfCache_2212_);
                    leanh::lean_inc(v_rewriteCache_2211_);
                    leanh::lean_dec(v___x_2210_);
                    v___x_2215_ = leanh::lean_box(0);
                    v_isShared_2216_ = v_isSharedCheck_2226_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2217_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__0;
                v___x_2218_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__1;
                v___x_2219_ = leanh::lean_box(0);
                v___x_2220_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_2217_,
                    v___x_2218_,
                    v_rewriteCache_2211_,
                    v_fvar_2207_,
                    v___x_2219_,
                );
                if v_isShared_2216_ == 0 {
                    leanh::lean_ctor_set(v___x_2215_, 0, v___x_2220_);
                    v___x_2222_ = v___x_2215_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2225_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2220_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2225_, 1, v_acNfCache_2212_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2225_, 2, v_typeAnalysis_2213_);
                    v___x_2222_ = v_reuseFailAlloc_2225_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2223_ = lean_st_ref_set(v_a_2208_, v___x_2222_);
                v___x_2224_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2224_, 0, v___x_2219_);
                return v___x_2224_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_rewriteFinished___redArg___boxed(
    mut v_fvar_2227_: *mut leanh::LeanObject,
    mut v_a_2228_: *mut leanh::LeanObject,
    mut v_a_2229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2230_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_rewriteFinished___redArg(
        v_fvar_2227_,
        v_a_2228_,
    );
    leanh::lean_dec(v_a_2228_);
    return v_res_2230_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_rewriteFinished(
    mut v_fvar_2231_: *mut leanh::LeanObject,
    mut v_a_2232_: *mut leanh::LeanObject,
    mut v_a_2233_: *mut leanh::LeanObject,
    mut v_a_2234_: *mut leanh::LeanObject,
    mut v_a_2235_: *mut leanh::LeanObject,
    mut v_a_2236_: *mut leanh::LeanObject,
    mut v_a_2237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2245_: u8 = 0;
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2255_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2239_ = lean_st_ref_take(v_a_2233_);
                v_rewriteCache_2240_ = leanh::lean_ctor_get(v___x_2239_, 0);
                v_acNfCache_2241_ = leanh::lean_ctor_get(v___x_2239_, 1);
                v_typeAnalysis_2242_ = leanh::lean_ctor_get(v___x_2239_, 2);
                v_isSharedCheck_2255_ = (!leanh::lean_is_exclusive(v___x_2239_)) as u8;
                if v_isSharedCheck_2255_ == 0 {
                    v___x_2244_ = v___x_2239_;
                    v_isShared_2245_ = v_isSharedCheck_2255_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_typeAnalysis_2242_);
                    leanh::lean_inc(v_acNfCache_2241_);
                    leanh::lean_inc(v_rewriteCache_2240_);
                    leanh::lean_dec(v___x_2239_);
                    v___x_2244_ = leanh::lean_box(0);
                    v_isShared_2245_ = v_isSharedCheck_2255_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2246_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__0;
                v___x_2247_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__1;
                v___x_2248_ = leanh::lean_box(0);
                v___x_2249_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_2246_,
                    v___x_2247_,
                    v_rewriteCache_2240_,
                    v_fvar_2231_,
                    v___x_2248_,
                );
                if v_isShared_2245_ == 0 {
                    leanh::lean_ctor_set(v___x_2244_, 0, v___x_2249_);
                    v___x_2251_ = v___x_2244_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2254_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2254_, 0, v___x_2249_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2254_, 1, v_acNfCache_2241_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2254_, 2, v_typeAnalysis_2242_);
                    v___x_2251_ = v_reuseFailAlloc_2254_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2252_ = lean_st_ref_set(v_a_2233_, v___x_2251_);
                v___x_2253_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2253_, 0, v___x_2248_);
                return v___x_2253_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_rewriteFinished___boxed(
    mut v_fvar_2256_: *mut leanh::LeanObject,
    mut v_a_2257_: *mut leanh::LeanObject,
    mut v_a_2258_: *mut leanh::LeanObject,
    mut v_a_2259_: *mut leanh::LeanObject,
    mut v_a_2260_: *mut leanh::LeanObject,
    mut v_a_2261_: *mut leanh::LeanObject,
    mut v_a_2262_: *mut leanh::LeanObject,
    mut v_a_2263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2264_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_rewriteFinished(
        v_fvar_2256_,
        v_a_2257_,
        v_a_2258_,
        v_a_2259_,
        v_a_2260_,
        v_a_2261_,
        v_a_2262_,
    );
    leanh::lean_dec(v_a_2262_);
    leanh::lean_dec_ref(v_a_2261_);
    leanh::lean_dec(v_a_2260_);
    leanh::lean_dec_ref(v_a_2259_);
    leanh::lean_dec(v_a_2258_);
    leanh::lean_dec_ref(v_a_2257_);
    return v_res_2264_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_acNfFinished___redArg(
    mut v_fvar_2265_: *mut leanh::LeanObject,
    mut v_a_2266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2274_: u8 = 0;
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2284_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2268_ = lean_st_ref_take(v_a_2266_);
                v_rewriteCache_2269_ = leanh::lean_ctor_get(v___x_2268_, 0);
                v_acNfCache_2270_ = leanh::lean_ctor_get(v___x_2268_, 1);
                v_typeAnalysis_2271_ = leanh::lean_ctor_get(v___x_2268_, 2);
                v_isSharedCheck_2284_ = (!leanh::lean_is_exclusive(v___x_2268_)) as u8;
                if v_isSharedCheck_2284_ == 0 {
                    v___x_2273_ = v___x_2268_;
                    v_isShared_2274_ = v_isSharedCheck_2284_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_typeAnalysis_2271_);
                    leanh::lean_inc(v_acNfCache_2270_);
                    leanh::lean_inc(v_rewriteCache_2269_);
                    leanh::lean_dec(v___x_2268_);
                    v___x_2273_ = leanh::lean_box(0);
                    v_isShared_2274_ = v_isSharedCheck_2284_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2275_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__0;
                v___x_2276_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__1;
                v___x_2277_ = leanh::lean_box(0);
                v___x_2278_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_2275_,
                    v___x_2276_,
                    v_acNfCache_2270_,
                    v_fvar_2265_,
                    v___x_2277_,
                );
                if v_isShared_2274_ == 0 {
                    leanh::lean_ctor_set(v___x_2273_, 1, v___x_2278_);
                    v___x_2280_ = v___x_2273_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2283_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_rewriteCache_2269_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2283_, 1, v___x_2278_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2283_, 2, v_typeAnalysis_2271_);
                    v___x_2280_ = v_reuseFailAlloc_2283_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2281_ = lean_st_ref_set(v_a_2266_, v___x_2280_);
                v___x_2282_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2282_, 0, v___x_2277_);
                return v___x_2282_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_acNfFinished___redArg___boxed(
    mut v_fvar_2285_: *mut leanh::LeanObject,
    mut v_a_2286_: *mut leanh::LeanObject,
    mut v_a_2287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2288_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_acNfFinished___redArg(
        v_fvar_2285_,
        v_a_2286_,
    );
    leanh::lean_dec(v_a_2286_);
    return v_res_2288_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_acNfFinished(
    mut v_fvar_2289_: *mut leanh::LeanObject,
    mut v_a_2290_: *mut leanh::LeanObject,
    mut v_a_2291_: *mut leanh::LeanObject,
    mut v_a_2292_: *mut leanh::LeanObject,
    mut v_a_2293_: *mut leanh::LeanObject,
    mut v_a_2294_: *mut leanh::LeanObject,
    mut v_a_2295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2303_: u8 = 0;
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2313_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2297_ = lean_st_ref_take(v_a_2291_);
                v_rewriteCache_2298_ = leanh::lean_ctor_get(v___x_2297_, 0);
                v_acNfCache_2299_ = leanh::lean_ctor_get(v___x_2297_, 1);
                v_typeAnalysis_2300_ = leanh::lean_ctor_get(v___x_2297_, 2);
                v_isSharedCheck_2313_ = (!leanh::lean_is_exclusive(v___x_2297_)) as u8;
                if v_isSharedCheck_2313_ == 0 {
                    v___x_2302_ = v___x_2297_;
                    v_isShared_2303_ = v_isSharedCheck_2313_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_typeAnalysis_2300_);
                    leanh::lean_inc(v_acNfCache_2299_);
                    leanh::lean_inc(v_rewriteCache_2298_);
                    leanh::lean_dec(v___x_2297_);
                    v___x_2302_ = leanh::lean_box(0);
                    v_isShared_2303_ = v_isSharedCheck_2313_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2304_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__0;
                v___x_2305_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_checkRewritten___redArg___closed__1;
                v___x_2306_ = leanh::lean_box(0);
                v___x_2307_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_2304_,
                    v___x_2305_,
                    v_acNfCache_2299_,
                    v_fvar_2289_,
                    v___x_2306_,
                );
                if v_isShared_2303_ == 0 {
                    leanh::lean_ctor_set(v___x_2302_, 1, v___x_2307_);
                    v___x_2309_ = v___x_2302_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2312_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_rewriteCache_2298_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2312_, 1, v___x_2307_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2312_, 2, v_typeAnalysis_2300_);
                    v___x_2309_ = v_reuseFailAlloc_2312_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2310_ = lean_st_ref_set(v_a_2291_, v___x_2309_);
                v___x_2311_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2311_, 0, v___x_2306_);
                return v___x_2311_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_acNfFinished___boxed(
    mut v_fvar_2314_: *mut leanh::LeanObject,
    mut v_a_2315_: *mut leanh::LeanObject,
    mut v_a_2316_: *mut leanh::LeanObject,
    mut v_a_2317_: *mut leanh::LeanObject,
    mut v_a_2318_: *mut leanh::LeanObject,
    mut v_a_2319_: *mut leanh::LeanObject,
    mut v_a_2320_: *mut leanh::LeanObject,
    mut v_a_2321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2322_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_acNfFinished(
        v_fvar_2314_,
        v_a_2315_,
        v_a_2316_,
        v_a_2317_,
        v_a_2318_,
        v_a_2319_,
        v_a_2320_,
    );
    leanh::lean_dec(v_a_2320_);
    leanh::lean_dec_ref(v_a_2319_);
    leanh::lean_dec(v_a_2318_);
    leanh::lean_dec_ref(v_a_2317_);
    leanh::lean_dec(v_a_2316_);
    leanh::lean_dec_ref(v_a_2315_);
    return v_res_2322_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg(
    mut v_a_2323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2325_ = lean_st_ref_get(v_a_2323_);
    v_typeAnalysis_2326_ = leanh::lean_ctor_get(v___x_2325_, 2);
    leanh::lean_inc_ref(v_typeAnalysis_2326_);
    leanh::lean_dec(v___x_2325_);
    v___x_2327_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2327_, 0, v_typeAnalysis_2326_);
    return v___x_2327_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg___boxed(
    mut v_a_2328_: *mut leanh::LeanObject,
    mut v_a_2329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2330_ =
        l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___redArg(v_a_2328_);
    leanh::lean_dec(v_a_2328_);
    return v_res_2330_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis(
    mut v_a_2331_: *mut leanh::LeanObject,
    mut v_a_2332_: *mut leanh::LeanObject,
    mut v_a_2333_: *mut leanh::LeanObject,
    mut v_a_2334_: *mut leanh::LeanObject,
    mut v_a_2335_: *mut leanh::LeanObject,
    mut v_a_2336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2338_ = lean_st_ref_get(v_a_2332_);
    v_typeAnalysis_2339_ = leanh::lean_ctor_get(v___x_2338_, 2);
    leanh::lean_inc_ref(v_typeAnalysis_2339_);
    leanh::lean_dec(v___x_2338_);
    v___x_2340_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2340_, 0, v_typeAnalysis_2339_);
    return v___x_2340_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis___boxed(
    mut v_a_2341_: *mut leanh::LeanObject,
    mut v_a_2342_: *mut leanh::LeanObject,
    mut v_a_2343_: *mut leanh::LeanObject,
    mut v_a_2344_: *mut leanh::LeanObject,
    mut v_a_2345_: *mut leanh::LeanObject,
    mut v_a_2346_: *mut leanh::LeanObject,
    mut v_a_2347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2348_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_getTypeAnalysis(
        v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_,
    );
    leanh::lean_dec(v_a_2346_);
    leanh::lean_dec_ref(v_a_2345_);
    leanh::lean_dec(v_a_2344_);
    leanh::lean_dec_ref(v_a_2343_);
    leanh::lean_dec(v_a_2342_);
    leanh::lean_dec_ref(v_a_2341_);
    return v_res_2348_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg(
    mut v_n_2354_: *mut leanh::LeanObject,
    mut v_a_2355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingStructures_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninteresting_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: u8 = 0;
    v___x_2357_ = lean_st_ref_get(v_a_2355_);
    v_typeAnalysis_2358_ = leanh::lean_ctor_get(v___x_2357_, 2);
    leanh::lean_inc_ref(v_typeAnalysis_2358_);
    leanh::lean_dec(v___x_2357_);
    v_interestingStructures_2359_ = leanh::lean_ctor_get(v_typeAnalysis_2358_, 0);
    leanh::lean_inc_ref(v_interestingStructures_2359_);
    v_uninteresting_2360_ = leanh::lean_ctor_get(v_typeAnalysis_2358_, 3);
    leanh::lean_inc_ref(v_uninteresting_2360_);
    leanh::lean_dec_ref(v_typeAnalysis_2358_);
    v___x_2361_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0;
    v___x_2362_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1;
    leanh::lean_inc(v_n_2354_);
    v___x_2363_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v___x_2361_,
        v___x_2362_,
        v_uninteresting_2360_,
        v_n_2354_,
    );
    leanh::lean_dec_ref(v_uninteresting_2360_);
    if v___x_2363_ == 0 {
        let mut v___x_2364_: u8 = 0;
        v___x_2364_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
            v___x_2361_,
            v___x_2362_,
            v_interestingStructures_2359_,
            v_n_2354_,
        );
        leanh::lean_dec_ref(v_interestingStructures_2359_);
        if v___x_2364_ == 0 {
            let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2365_ = leanh::lean_box(0);
            v___x_2366_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_2366_, 0, v___x_2365_);
            return v___x_2366_;
        } else {
            let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2367_ = leanh::lean_box((v___x_2364_) as usize);
            v___x_2368_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_2368_, 0, v___x_2367_);
            v___x_2369_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_2369_, 0, v___x_2368_);
            return v___x_2369_;
        }
    } else {
        let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_interestingStructures_2359_);
        leanh::lean_dec(v_n_2354_);
        v___x_2370_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2;
        v___x_2371_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2371_, 0, v___x_2370_);
        return v___x_2371_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___boxed(
    mut v_n_2372_: *mut leanh::LeanObject,
    mut v_a_2373_: *mut leanh::LeanObject,
    mut v_a_2374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2375_ =
        l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg(
            v_n_2372_, v_a_2373_,
        );
    leanh::lean_dec(v_a_2373_);
    return v_res_2375_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure(
    mut v_n_2376_: *mut leanh::LeanObject,
    mut v_a_2377_: *mut leanh::LeanObject,
    mut v_a_2378_: *mut leanh::LeanObject,
    mut v_a_2379_: *mut leanh::LeanObject,
    mut v_a_2380_: *mut leanh::LeanObject,
    mut v_a_2381_: *mut leanh::LeanObject,
    mut v_a_2382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingStructures_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninteresting_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: u8 = 0;
    v___x_2384_ = lean_st_ref_get(v_a_2378_);
    v_typeAnalysis_2385_ = leanh::lean_ctor_get(v___x_2384_, 2);
    leanh::lean_inc_ref(v_typeAnalysis_2385_);
    leanh::lean_dec(v___x_2384_);
    v_interestingStructures_2386_ = leanh::lean_ctor_get(v_typeAnalysis_2385_, 0);
    leanh::lean_inc_ref(v_interestingStructures_2386_);
    v_uninteresting_2387_ = leanh::lean_ctor_get(v_typeAnalysis_2385_, 3);
    leanh::lean_inc_ref(v_uninteresting_2387_);
    leanh::lean_dec_ref(v_typeAnalysis_2385_);
    v___x_2388_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0;
    v___x_2389_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1;
    leanh::lean_inc(v_n_2376_);
    v___x_2390_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v___x_2388_,
        v___x_2389_,
        v_uninteresting_2387_,
        v_n_2376_,
    );
    leanh::lean_dec_ref(v_uninteresting_2387_);
    if v___x_2390_ == 0 {
        let mut v___x_2391_: u8 = 0;
        v___x_2391_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
            v___x_2388_,
            v___x_2389_,
            v_interestingStructures_2386_,
            v_n_2376_,
        );
        leanh::lean_dec_ref(v_interestingStructures_2386_);
        if v___x_2391_ == 0 {
            let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2392_ = leanh::lean_box(0);
            v___x_2393_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_2393_, 0, v___x_2392_);
            return v___x_2393_;
        } else {
            let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2394_ = leanh::lean_box((v___x_2391_) as usize);
            v___x_2395_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_2395_, 0, v___x_2394_);
            v___x_2396_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_2396_, 0, v___x_2395_);
            return v___x_2396_;
        }
    } else {
        let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_interestingStructures_2386_);
        leanh::lean_dec(v_n_2376_);
        v___x_2397_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__2;
        v___x_2398_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2398_, 0, v___x_2397_);
        return v___x_2398_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___boxed(
    mut v_n_2399_: *mut leanh::LeanObject,
    mut v_a_2400_: *mut leanh::LeanObject,
    mut v_a_2401_: *mut leanh::LeanObject,
    mut v_a_2402_: *mut leanh::LeanObject,
    mut v_a_2403_: *mut leanh::LeanObject,
    mut v_a_2404_: *mut leanh::LeanObject,
    mut v_a_2405_: *mut leanh::LeanObject,
    mut v_a_2406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2407_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure(
        v_n_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_,
    );
    leanh::lean_dec(v_a_2405_);
    leanh::lean_dec_ref(v_a_2404_);
    leanh::lean_dec(v_a_2403_);
    leanh::lean_dec_ref(v_a_2402_);
    leanh::lean_dec(v_a_2401_);
    leanh::lean_dec_ref(v_a_2400_);
    return v_res_2407_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg(
    mut v_f_2408_: *mut leanh::LeanObject,
    mut v_a_2409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2417_: u8 = 0;
    let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2425_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2411_ = lean_st_ref_take(v_a_2409_);
                v_rewriteCache_2412_ = leanh::lean_ctor_get(v___x_2411_, 0);
                v_acNfCache_2413_ = leanh::lean_ctor_get(v___x_2411_, 1);
                v_typeAnalysis_2414_ = leanh::lean_ctor_get(v___x_2411_, 2);
                v_isSharedCheck_2425_ = (!leanh::lean_is_exclusive(v___x_2411_)) as u8;
                if v_isSharedCheck_2425_ == 0 {
                    v___x_2416_ = v___x_2411_;
                    v_isShared_2417_ = v_isSharedCheck_2425_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_typeAnalysis_2414_);
                    leanh::lean_inc(v_acNfCache_2413_);
                    leanh::lean_inc(v_rewriteCache_2412_);
                    leanh::lean_dec(v___x_2411_);
                    v___x_2416_ = leanh::lean_box(0);
                    v_isShared_2417_ = v_isSharedCheck_2425_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2418_ = leanh::lean_apply_1(v_f_2408_, v_typeAnalysis_2414_);
                if v_isShared_2417_ == 0 {
                    leanh::lean_ctor_set(v___x_2416_, 2, v___x_2418_);
                    v___x_2420_ = v___x_2416_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2424_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_rewriteCache_2412_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2424_, 1, v_acNfCache_2413_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2424_, 2, v___x_2418_);
                    v___x_2420_ = v_reuseFailAlloc_2424_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2421_ = lean_st_ref_set(v_a_2409_, v___x_2420_);
                v___x_2422_ = leanh::lean_box(0);
                v___x_2423_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2423_, 0, v___x_2422_);
                return v___x_2423_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg___boxed(
    mut v_f_2426_: *mut leanh::LeanObject,
    mut v_a_2427_: *mut leanh::LeanObject,
    mut v_a_2428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2429_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___redArg(
        v_f_2426_, v_a_2427_,
    );
    leanh::lean_dec(v_a_2427_);
    return v_res_2429_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis(
    mut v_f_2430_: *mut leanh::LeanObject,
    mut v_a_2431_: *mut leanh::LeanObject,
    mut v_a_2432_: *mut leanh::LeanObject,
    mut v_a_2433_: *mut leanh::LeanObject,
    mut v_a_2434_: *mut leanh::LeanObject,
    mut v_a_2435_: *mut leanh::LeanObject,
    mut v_a_2436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2444_: u8 = 0;
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2452_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2438_ = lean_st_ref_take(v_a_2432_);
                v_rewriteCache_2439_ = leanh::lean_ctor_get(v___x_2438_, 0);
                v_acNfCache_2440_ = leanh::lean_ctor_get(v___x_2438_, 1);
                v_typeAnalysis_2441_ = leanh::lean_ctor_get(v___x_2438_, 2);
                v_isSharedCheck_2452_ = (!leanh::lean_is_exclusive(v___x_2438_)) as u8;
                if v_isSharedCheck_2452_ == 0 {
                    v___x_2443_ = v___x_2438_;
                    v_isShared_2444_ = v_isSharedCheck_2452_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_typeAnalysis_2441_);
                    leanh::lean_inc(v_acNfCache_2440_);
                    leanh::lean_inc(v_rewriteCache_2439_);
                    leanh::lean_dec(v___x_2438_);
                    v___x_2443_ = leanh::lean_box(0);
                    v_isShared_2444_ = v_isSharedCheck_2452_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2445_ = leanh::lean_apply_1(v_f_2430_, v_typeAnalysis_2441_);
                if v_isShared_2444_ == 0 {
                    leanh::lean_ctor_set(v___x_2443_, 2, v___x_2445_);
                    v___x_2447_ = v___x_2443_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2451_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_rewriteCache_2439_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2451_, 1, v_acNfCache_2440_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2451_, 2, v___x_2445_);
                    v___x_2447_ = v_reuseFailAlloc_2451_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2448_ = lean_st_ref_set(v_a_2432_, v___x_2447_);
                v___x_2449_ = leanh::lean_box(0);
                v___x_2450_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2450_, 0, v___x_2449_);
                return v___x_2450_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis___boxed(
    mut v_f_2453_: *mut leanh::LeanObject,
    mut v_a_2454_: *mut leanh::LeanObject,
    mut v_a_2455_: *mut leanh::LeanObject,
    mut v_a_2456_: *mut leanh::LeanObject,
    mut v_a_2457_: *mut leanh::LeanObject,
    mut v_a_2458_: *mut leanh::LeanObject,
    mut v_a_2459_: *mut leanh::LeanObject,
    mut v_a_2460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2461_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_modifyTypeAnalysis(
        v_f_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_,
    );
    leanh::lean_dec(v_a_2459_);
    leanh::lean_dec_ref(v_a_2458_);
    leanh::lean_dec(v_a_2457_);
    leanh::lean_dec_ref(v_a_2456_);
    leanh::lean_dec(v_a_2455_);
    leanh::lean_dec_ref(v_a_2454_);
    return v_res_2461_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg(
    mut v_n_2462_: *mut leanh::LeanObject,
    mut v_a_2463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2471_: u8 = 0;
    let mut v_interestingStructures_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingEnums_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingMatchers_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninteresting_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2478_: u8 = 0;
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2491_: u8 = 0;
    let mut v_isSharedCheck_2492_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2465_ = lean_st_ref_take(v_a_2463_);
                v_typeAnalysis_2466_ = leanh::lean_ctor_get(v___x_2465_, 2);
                v_rewriteCache_2467_ = leanh::lean_ctor_get(v___x_2465_, 0);
                v_acNfCache_2468_ = leanh::lean_ctor_get(v___x_2465_, 1);
                v_isSharedCheck_2492_ = (!leanh::lean_is_exclusive(v___x_2465_)) as u8;
                if v_isSharedCheck_2492_ == 0 {
                    v___x_2470_ = v___x_2465_;
                    v_isShared_2471_ = v_isSharedCheck_2492_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_typeAnalysis_2466_);
                    leanh::lean_inc(v_acNfCache_2468_);
                    leanh::lean_inc(v_rewriteCache_2467_);
                    leanh::lean_dec(v___x_2465_);
                    v___x_2470_ = leanh::lean_box(0);
                    v_isShared_2471_ = v_isSharedCheck_2492_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_interestingStructures_2472_ =
                    leanh::lean_ctor_get(v_typeAnalysis_2466_, 0);
                v_interestingEnums_2473_ = leanh::lean_ctor_get(v_typeAnalysis_2466_, 1);
                v_interestingMatchers_2474_ = leanh::lean_ctor_get(v_typeAnalysis_2466_, 2);
                v_uninteresting_2475_ = leanh::lean_ctor_get(v_typeAnalysis_2466_, 3);
                v_isSharedCheck_2491_ =
                    (!leanh::lean_is_exclusive(v_typeAnalysis_2466_)) as u8;
                if v_isSharedCheck_2491_ == 0 {
                    v___x_2477_ = v_typeAnalysis_2466_;
                    v_isShared_2478_ = v_isSharedCheck_2491_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_uninteresting_2475_);
                    leanh::lean_inc(v_interestingMatchers_2474_);
                    leanh::lean_inc(v_interestingEnums_2473_);
                    leanh::lean_inc(v_interestingStructures_2472_);
                    leanh::lean_dec(v_typeAnalysis_2466_);
                    v___x_2477_ = leanh::lean_box(0);
                    v_isShared_2478_ = v_isSharedCheck_2491_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2479_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0;
                v___x_2480_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1;
                v___x_2481_ = leanh::lean_box(0);
                v___x_2482_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_2479_,
                    v___x_2480_,
                    v_interestingStructures_2472_,
                    v_n_2462_,
                    v___x_2481_,
                );
                if v_isShared_2478_ == 0 {
                    leanh::lean_ctor_set(v___x_2477_, 0, v___x_2482_);
                    v___x_2484_ = v___x_2477_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2490_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2482_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2490_,
                        1,
                        v_interestingEnums_2473_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2490_,
                        2,
                        v_interestingMatchers_2474_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2490_, 3, v_uninteresting_2475_);
                    v___x_2484_ = v_reuseFailAlloc_2490_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2471_ == 0 {
                    leanh::lean_ctor_set(v___x_2470_, 2, v___x_2484_);
                    v___x_2486_ = v___x_2470_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2489_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_rewriteCache_2467_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2489_, 1, v_acNfCache_2468_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2489_, 2, v___x_2484_);
                    v___x_2486_ = v_reuseFailAlloc_2489_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2487_ = lean_st_ref_set(v_a_2463_, v___x_2486_);
                v___x_2488_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2488_, 0, v___x_2481_);
                return v___x_2488_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg___boxed(
    mut v_n_2493_: *mut leanh::LeanObject,
    mut v_a_2494_: *mut leanh::LeanObject,
    mut v_a_2495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2496_ =
        l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___redArg(
            v_n_2493_, v_a_2494_,
        );
    leanh::lean_dec(v_a_2494_);
    return v_res_2496_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(
    mut v_n_2497_: *mut leanh::LeanObject,
    mut v_a_2498_: *mut leanh::LeanObject,
    mut v_a_2499_: *mut leanh::LeanObject,
    mut v_a_2500_: *mut leanh::LeanObject,
    mut v_a_2501_: *mut leanh::LeanObject,
    mut v_a_2502_: *mut leanh::LeanObject,
    mut v_a_2503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2511_: u8 = 0;
    let mut v_interestingStructures_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingEnums_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingMatchers_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninteresting_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2518_: u8 = 0;
    let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2531_: u8 = 0;
    let mut v_isSharedCheck_2532_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2505_ = lean_st_ref_take(v_a_2499_);
                v_typeAnalysis_2506_ = leanh::lean_ctor_get(v___x_2505_, 2);
                v_rewriteCache_2507_ = leanh::lean_ctor_get(v___x_2505_, 0);
                v_acNfCache_2508_ = leanh::lean_ctor_get(v___x_2505_, 1);
                v_isSharedCheck_2532_ = (!leanh::lean_is_exclusive(v___x_2505_)) as u8;
                if v_isSharedCheck_2532_ == 0 {
                    v___x_2510_ = v___x_2505_;
                    v_isShared_2511_ = v_isSharedCheck_2532_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_typeAnalysis_2506_);
                    leanh::lean_inc(v_acNfCache_2508_);
                    leanh::lean_inc(v_rewriteCache_2507_);
                    leanh::lean_dec(v___x_2505_);
                    v___x_2510_ = leanh::lean_box(0);
                    v_isShared_2511_ = v_isSharedCheck_2532_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_interestingStructures_2512_ =
                    leanh::lean_ctor_get(v_typeAnalysis_2506_, 0);
                v_interestingEnums_2513_ = leanh::lean_ctor_get(v_typeAnalysis_2506_, 1);
                v_interestingMatchers_2514_ = leanh::lean_ctor_get(v_typeAnalysis_2506_, 2);
                v_uninteresting_2515_ = leanh::lean_ctor_get(v_typeAnalysis_2506_, 3);
                v_isSharedCheck_2531_ =
                    (!leanh::lean_is_exclusive(v_typeAnalysis_2506_)) as u8;
                if v_isSharedCheck_2531_ == 0 {
                    v___x_2517_ = v_typeAnalysis_2506_;
                    v_isShared_2518_ = v_isSharedCheck_2531_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_uninteresting_2515_);
                    leanh::lean_inc(v_interestingMatchers_2514_);
                    leanh::lean_inc(v_interestingEnums_2513_);
                    leanh::lean_inc(v_interestingStructures_2512_);
                    leanh::lean_dec(v_typeAnalysis_2506_);
                    v___x_2517_ = leanh::lean_box(0);
                    v_isShared_2518_ = v_isSharedCheck_2531_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2519_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0;
                v___x_2520_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1;
                v___x_2521_ = leanh::lean_box(0);
                v___x_2522_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_2519_,
                    v___x_2520_,
                    v_interestingStructures_2512_,
                    v_n_2497_,
                    v___x_2521_,
                );
                if v_isShared_2518_ == 0 {
                    leanh::lean_ctor_set(v___x_2517_, 0, v___x_2522_);
                    v___x_2524_ = v___x_2517_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2530_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2522_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2530_,
                        1,
                        v_interestingEnums_2513_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2530_,
                        2,
                        v_interestingMatchers_2514_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2530_, 3, v_uninteresting_2515_);
                    v___x_2524_ = v_reuseFailAlloc_2530_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2511_ == 0 {
                    leanh::lean_ctor_set(v___x_2510_, 2, v___x_2524_);
                    v___x_2526_ = v___x_2510_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2529_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_rewriteCache_2507_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2529_, 1, v_acNfCache_2508_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2529_, 2, v___x_2524_);
                    v___x_2526_ = v_reuseFailAlloc_2529_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2527_ = lean_st_ref_set(v_a_2499_, v___x_2526_);
                v___x_2528_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2528_, 0, v___x_2521_);
                return v___x_2528_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure___boxed(
    mut v_n_2533_: *mut leanh::LeanObject,
    mut v_a_2534_: *mut leanh::LeanObject,
    mut v_a_2535_: *mut leanh::LeanObject,
    mut v_a_2536_: *mut leanh::LeanObject,
    mut v_a_2537_: *mut leanh::LeanObject,
    mut v_a_2538_: *mut leanh::LeanObject,
    mut v_a_2539_: *mut leanh::LeanObject,
    mut v_a_2540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2541_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingStructure(
        v_n_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_,
    );
    leanh::lean_dec(v_a_2539_);
    leanh::lean_dec_ref(v_a_2538_);
    leanh::lean_dec(v_a_2537_);
    leanh::lean_dec_ref(v_a_2536_);
    leanh::lean_dec(v_a_2535_);
    leanh::lean_dec_ref(v_a_2534_);
    return v_res_2541_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(
    mut v_n_2542_: *mut leanh::LeanObject,
    mut v_a_2543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2551_: u8 = 0;
    let mut v_interestingStructures_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingEnums_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingMatchers_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninteresting_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2558_: u8 = 0;
    let mut v___x_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2571_: u8 = 0;
    let mut v_isSharedCheck_2572_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2545_ = lean_st_ref_take(v_a_2543_);
                v_typeAnalysis_2546_ = leanh::lean_ctor_get(v___x_2545_, 2);
                v_rewriteCache_2547_ = leanh::lean_ctor_get(v___x_2545_, 0);
                v_acNfCache_2548_ = leanh::lean_ctor_get(v___x_2545_, 1);
                v_isSharedCheck_2572_ = (!leanh::lean_is_exclusive(v___x_2545_)) as u8;
                if v_isSharedCheck_2572_ == 0 {
                    v___x_2550_ = v___x_2545_;
                    v_isShared_2551_ = v_isSharedCheck_2572_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_typeAnalysis_2546_);
                    leanh::lean_inc(v_acNfCache_2548_);
                    leanh::lean_inc(v_rewriteCache_2547_);
                    leanh::lean_dec(v___x_2545_);
                    v___x_2550_ = leanh::lean_box(0);
                    v_isShared_2551_ = v_isSharedCheck_2572_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_interestingStructures_2552_ =
                    leanh::lean_ctor_get(v_typeAnalysis_2546_, 0);
                v_interestingEnums_2553_ = leanh::lean_ctor_get(v_typeAnalysis_2546_, 1);
                v_interestingMatchers_2554_ = leanh::lean_ctor_get(v_typeAnalysis_2546_, 2);
                v_uninteresting_2555_ = leanh::lean_ctor_get(v_typeAnalysis_2546_, 3);
                v_isSharedCheck_2571_ =
                    (!leanh::lean_is_exclusive(v_typeAnalysis_2546_)) as u8;
                if v_isSharedCheck_2571_ == 0 {
                    v___x_2557_ = v_typeAnalysis_2546_;
                    v_isShared_2558_ = v_isSharedCheck_2571_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_uninteresting_2555_);
                    leanh::lean_inc(v_interestingMatchers_2554_);
                    leanh::lean_inc(v_interestingEnums_2553_);
                    leanh::lean_inc(v_interestingStructures_2552_);
                    leanh::lean_dec(v_typeAnalysis_2546_);
                    v___x_2557_ = leanh::lean_box(0);
                    v_isShared_2558_ = v_isSharedCheck_2571_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2559_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0;
                v___x_2560_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1;
                v___x_2561_ = leanh::lean_box(0);
                v___x_2562_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_2559_,
                    v___x_2560_,
                    v_interestingEnums_2553_,
                    v_n_2542_,
                    v___x_2561_,
                );
                if v_isShared_2558_ == 0 {
                    leanh::lean_ctor_set(v___x_2557_, 1, v___x_2562_);
                    v___x_2564_ = v___x_2557_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2570_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2570_,
                        0,
                        v_interestingStructures_2552_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2570_, 1, v___x_2562_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2570_,
                        2,
                        v_interestingMatchers_2554_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2570_, 3, v_uninteresting_2555_);
                    v___x_2564_ = v_reuseFailAlloc_2570_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2551_ == 0 {
                    leanh::lean_ctor_set(v___x_2550_, 2, v___x_2564_);
                    v___x_2566_ = v___x_2550_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2569_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_rewriteCache_2547_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2569_, 1, v_acNfCache_2548_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2569_, 2, v___x_2564_);
                    v___x_2566_ = v_reuseFailAlloc_2569_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2567_ = lean_st_ref_set(v_a_2543_, v___x_2566_);
                v___x_2568_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2568_, 0, v___x_2561_);
                return v___x_2568_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg___boxed(
    mut v_n_2573_: *mut leanh::LeanObject,
    mut v_a_2574_: *mut leanh::LeanObject,
    mut v_a_2575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2576_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___redArg(
        v_n_2573_, v_a_2574_,
    );
    leanh::lean_dec(v_a_2574_);
    return v_res_2576_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(
    mut v_n_2577_: *mut leanh::LeanObject,
    mut v_a_2578_: *mut leanh::LeanObject,
    mut v_a_2579_: *mut leanh::LeanObject,
    mut v_a_2580_: *mut leanh::LeanObject,
    mut v_a_2581_: *mut leanh::LeanObject,
    mut v_a_2582_: *mut leanh::LeanObject,
    mut v_a_2583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2591_: u8 = 0;
    let mut v_interestingStructures_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingEnums_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingMatchers_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninteresting_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2598_: u8 = 0;
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2611_: u8 = 0;
    let mut v_isSharedCheck_2612_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2585_ = lean_st_ref_take(v_a_2579_);
                v_typeAnalysis_2586_ = leanh::lean_ctor_get(v___x_2585_, 2);
                v_rewriteCache_2587_ = leanh::lean_ctor_get(v___x_2585_, 0);
                v_acNfCache_2588_ = leanh::lean_ctor_get(v___x_2585_, 1);
                v_isSharedCheck_2612_ = (!leanh::lean_is_exclusive(v___x_2585_)) as u8;
                if v_isSharedCheck_2612_ == 0 {
                    v___x_2590_ = v___x_2585_;
                    v_isShared_2591_ = v_isSharedCheck_2612_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_typeAnalysis_2586_);
                    leanh::lean_inc(v_acNfCache_2588_);
                    leanh::lean_inc(v_rewriteCache_2587_);
                    leanh::lean_dec(v___x_2585_);
                    v___x_2590_ = leanh::lean_box(0);
                    v_isShared_2591_ = v_isSharedCheck_2612_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_interestingStructures_2592_ =
                    leanh::lean_ctor_get(v_typeAnalysis_2586_, 0);
                v_interestingEnums_2593_ = leanh::lean_ctor_get(v_typeAnalysis_2586_, 1);
                v_interestingMatchers_2594_ = leanh::lean_ctor_get(v_typeAnalysis_2586_, 2);
                v_uninteresting_2595_ = leanh::lean_ctor_get(v_typeAnalysis_2586_, 3);
                v_isSharedCheck_2611_ =
                    (!leanh::lean_is_exclusive(v_typeAnalysis_2586_)) as u8;
                if v_isSharedCheck_2611_ == 0 {
                    v___x_2597_ = v_typeAnalysis_2586_;
                    v_isShared_2598_ = v_isSharedCheck_2611_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_uninteresting_2595_);
                    leanh::lean_inc(v_interestingMatchers_2594_);
                    leanh::lean_inc(v_interestingEnums_2593_);
                    leanh::lean_inc(v_interestingStructures_2592_);
                    leanh::lean_dec(v_typeAnalysis_2586_);
                    v___x_2597_ = leanh::lean_box(0);
                    v_isShared_2598_ = v_isSharedCheck_2611_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2599_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0;
                v___x_2600_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1;
                v___x_2601_ = leanh::lean_box(0);
                v___x_2602_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_2599_,
                    v___x_2600_,
                    v_interestingEnums_2593_,
                    v_n_2577_,
                    v___x_2601_,
                );
                if v_isShared_2598_ == 0 {
                    leanh::lean_ctor_set(v___x_2597_, 1, v___x_2602_);
                    v___x_2604_ = v___x_2597_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2610_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2610_,
                        0,
                        v_interestingStructures_2592_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2610_, 1, v___x_2602_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2610_,
                        2,
                        v_interestingMatchers_2594_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2610_, 3, v_uninteresting_2595_);
                    v___x_2604_ = v_reuseFailAlloc_2610_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2591_ == 0 {
                    leanh::lean_ctor_set(v___x_2590_, 2, v___x_2604_);
                    v___x_2606_ = v___x_2590_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2609_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_rewriteCache_2587_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2609_, 1, v_acNfCache_2588_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2609_, 2, v___x_2604_);
                    v___x_2606_ = v_reuseFailAlloc_2609_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2607_ = lean_st_ref_set(v_a_2579_, v___x_2606_);
                v___x_2608_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2608_, 0, v___x_2601_);
                return v___x_2608_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum___boxed(
    mut v_n_2613_: *mut leanh::LeanObject,
    mut v_a_2614_: *mut leanh::LeanObject,
    mut v_a_2615_: *mut leanh::LeanObject,
    mut v_a_2616_: *mut leanh::LeanObject,
    mut v_a_2617_: *mut leanh::LeanObject,
    mut v_a_2618_: *mut leanh::LeanObject,
    mut v_a_2619_: *mut leanh::LeanObject,
    mut v_a_2620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2621_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingEnum(
        v_n_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_,
    );
    leanh::lean_dec(v_a_2619_);
    leanh::lean_dec_ref(v_a_2618_);
    leanh::lean_dec(v_a_2617_);
    leanh::lean_dec_ref(v_a_2616_);
    leanh::lean_dec(v_a_2615_);
    leanh::lean_dec_ref(v_a_2614_);
    return v_res_2621_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(
    mut v_n_2622_: *mut leanh::LeanObject,
    mut v_k_2623_: *mut leanh::LeanObject,
    mut v_a_2624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2632_: u8 = 0;
    let mut v_interestingStructures_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingEnums_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingMatchers_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninteresting_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2639_: u8 = 0;
    let mut v___x_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2652_: u8 = 0;
    let mut v_isSharedCheck_2653_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2626_ = lean_st_ref_take(v_a_2624_);
                v_typeAnalysis_2627_ = leanh::lean_ctor_get(v___x_2626_, 2);
                v_rewriteCache_2628_ = leanh::lean_ctor_get(v___x_2626_, 0);
                v_acNfCache_2629_ = leanh::lean_ctor_get(v___x_2626_, 1);
                v_isSharedCheck_2653_ = (!leanh::lean_is_exclusive(v___x_2626_)) as u8;
                if v_isSharedCheck_2653_ == 0 {
                    v___x_2631_ = v___x_2626_;
                    v_isShared_2632_ = v_isSharedCheck_2653_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_typeAnalysis_2627_);
                    leanh::lean_inc(v_acNfCache_2629_);
                    leanh::lean_inc(v_rewriteCache_2628_);
                    leanh::lean_dec(v___x_2626_);
                    v___x_2631_ = leanh::lean_box(0);
                    v_isShared_2632_ = v_isSharedCheck_2653_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_interestingStructures_2633_ =
                    leanh::lean_ctor_get(v_typeAnalysis_2627_, 0);
                v_interestingEnums_2634_ = leanh::lean_ctor_get(v_typeAnalysis_2627_, 1);
                v_interestingMatchers_2635_ = leanh::lean_ctor_get(v_typeAnalysis_2627_, 2);
                v_uninteresting_2636_ = leanh::lean_ctor_get(v_typeAnalysis_2627_, 3);
                v_isSharedCheck_2652_ =
                    (!leanh::lean_is_exclusive(v_typeAnalysis_2627_)) as u8;
                if v_isSharedCheck_2652_ == 0 {
                    v___x_2638_ = v_typeAnalysis_2627_;
                    v_isShared_2639_ = v_isSharedCheck_2652_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_uninteresting_2636_);
                    leanh::lean_inc(v_interestingMatchers_2635_);
                    leanh::lean_inc(v_interestingEnums_2634_);
                    leanh::lean_inc(v_interestingStructures_2633_);
                    leanh::lean_dec(v_typeAnalysis_2627_);
                    v___x_2638_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_2638_, 2, v___x_2642_);
                    v___x_2644_ = v___x_2638_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2651_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2651_,
                        0,
                        v_interestingStructures_2633_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2651_,
                        1,
                        v_interestingEnums_2634_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2651_, 2, v___x_2642_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2651_, 3, v_uninteresting_2636_);
                    v___x_2644_ = v_reuseFailAlloc_2651_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2632_ == 0 {
                    leanh::lean_ctor_set(v___x_2631_, 2, v___x_2644_);
                    v___x_2646_ = v___x_2631_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2650_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_rewriteCache_2628_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2650_, 1, v_acNfCache_2629_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2650_, 2, v___x_2644_);
                    v___x_2646_ = v_reuseFailAlloc_2650_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2647_ = lean_st_ref_set(v_a_2624_, v___x_2646_);
                v___x_2648_ = leanh::lean_box(0);
                v___x_2649_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2649_, 0, v___x_2648_);
                return v___x_2649_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg___boxed(
    mut v_n_2654_: *mut leanh::LeanObject,
    mut v_k_2655_: *mut leanh::LeanObject,
    mut v_a_2656_: *mut leanh::LeanObject,
    mut v_a_2657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2658_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___redArg(
        v_n_2654_, v_k_2655_, v_a_2656_,
    );
    leanh::lean_dec(v_a_2656_);
    return v_res_2658_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(
    mut v_n_2659_: *mut leanh::LeanObject,
    mut v_k_2660_: *mut leanh::LeanObject,
    mut v_a_2661_: *mut leanh::LeanObject,
    mut v_a_2662_: *mut leanh::LeanObject,
    mut v_a_2663_: *mut leanh::LeanObject,
    mut v_a_2664_: *mut leanh::LeanObject,
    mut v_a_2665_: *mut leanh::LeanObject,
    mut v_a_2666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2674_: u8 = 0;
    let mut v_interestingStructures_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingEnums_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingMatchers_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninteresting_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2681_: u8 = 0;
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2694_: u8 = 0;
    let mut v_isSharedCheck_2695_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2668_ = lean_st_ref_take(v_a_2662_);
                v_typeAnalysis_2669_ = leanh::lean_ctor_get(v___x_2668_, 2);
                v_rewriteCache_2670_ = leanh::lean_ctor_get(v___x_2668_, 0);
                v_acNfCache_2671_ = leanh::lean_ctor_get(v___x_2668_, 1);
                v_isSharedCheck_2695_ = (!leanh::lean_is_exclusive(v___x_2668_)) as u8;
                if v_isSharedCheck_2695_ == 0 {
                    v___x_2673_ = v___x_2668_;
                    v_isShared_2674_ = v_isSharedCheck_2695_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_typeAnalysis_2669_);
                    leanh::lean_inc(v_acNfCache_2671_);
                    leanh::lean_inc(v_rewriteCache_2670_);
                    leanh::lean_dec(v___x_2668_);
                    v___x_2673_ = leanh::lean_box(0);
                    v_isShared_2674_ = v_isSharedCheck_2695_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_interestingStructures_2675_ =
                    leanh::lean_ctor_get(v_typeAnalysis_2669_, 0);
                v_interestingEnums_2676_ = leanh::lean_ctor_get(v_typeAnalysis_2669_, 1);
                v_interestingMatchers_2677_ = leanh::lean_ctor_get(v_typeAnalysis_2669_, 2);
                v_uninteresting_2678_ = leanh::lean_ctor_get(v_typeAnalysis_2669_, 3);
                v_isSharedCheck_2694_ =
                    (!leanh::lean_is_exclusive(v_typeAnalysis_2669_)) as u8;
                if v_isSharedCheck_2694_ == 0 {
                    v___x_2680_ = v_typeAnalysis_2669_;
                    v_isShared_2681_ = v_isSharedCheck_2694_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_uninteresting_2678_);
                    leanh::lean_inc(v_interestingMatchers_2677_);
                    leanh::lean_inc(v_interestingEnums_2676_);
                    leanh::lean_inc(v_interestingStructures_2675_);
                    leanh::lean_dec(v_typeAnalysis_2669_);
                    v___x_2680_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_2680_, 2, v___x_2684_);
                    v___x_2686_ = v___x_2680_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2693_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2693_,
                        0,
                        v_interestingStructures_2675_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2693_,
                        1,
                        v_interestingEnums_2676_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2693_, 2, v___x_2684_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2693_, 3, v_uninteresting_2678_);
                    v___x_2686_ = v_reuseFailAlloc_2693_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2674_ == 0 {
                    leanh::lean_ctor_set(v___x_2673_, 2, v___x_2686_);
                    v___x_2688_ = v___x_2673_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2692_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_rewriteCache_2670_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 1, v_acNfCache_2671_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 2, v___x_2686_);
                    v___x_2688_ = v_reuseFailAlloc_2692_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2689_ = lean_st_ref_set(v_a_2662_, v___x_2688_);
                v___x_2690_ = leanh::lean_box(0);
                v___x_2691_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2691_, 0, v___x_2690_);
                return v___x_2691_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher___boxed(
    mut v_n_2696_: *mut leanh::LeanObject,
    mut v_k_2697_: *mut leanh::LeanObject,
    mut v_a_2698_: *mut leanh::LeanObject,
    mut v_a_2699_: *mut leanh::LeanObject,
    mut v_a_2700_: *mut leanh::LeanObject,
    mut v_a_2701_: *mut leanh::LeanObject,
    mut v_a_2702_: *mut leanh::LeanObject,
    mut v_a_2703_: *mut leanh::LeanObject,
    mut v_a_2704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2705_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markInterestingMatcher(
        v_n_2696_, v_k_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_,
    );
    leanh::lean_dec(v_a_2703_);
    leanh::lean_dec_ref(v_a_2702_);
    leanh::lean_dec(v_a_2701_);
    leanh::lean_dec_ref(v_a_2700_);
    leanh::lean_dec(v_a_2699_);
    leanh::lean_dec_ref(v_a_2698_);
    return v_res_2705_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(
    mut v_n_2706_: *mut leanh::LeanObject,
    mut v_a_2707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2715_: u8 = 0;
    let mut v_interestingStructures_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingEnums_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingMatchers_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninteresting_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2722_: u8 = 0;
    let mut v___x_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2735_: u8 = 0;
    let mut v_isSharedCheck_2736_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2709_ = lean_st_ref_take(v_a_2707_);
                v_typeAnalysis_2710_ = leanh::lean_ctor_get(v___x_2709_, 2);
                v_rewriteCache_2711_ = leanh::lean_ctor_get(v___x_2709_, 0);
                v_acNfCache_2712_ = leanh::lean_ctor_get(v___x_2709_, 1);
                v_isSharedCheck_2736_ = (!leanh::lean_is_exclusive(v___x_2709_)) as u8;
                if v_isSharedCheck_2736_ == 0 {
                    v___x_2714_ = v___x_2709_;
                    v_isShared_2715_ = v_isSharedCheck_2736_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_typeAnalysis_2710_);
                    leanh::lean_inc(v_acNfCache_2712_);
                    leanh::lean_inc(v_rewriteCache_2711_);
                    leanh::lean_dec(v___x_2709_);
                    v___x_2714_ = leanh::lean_box(0);
                    v_isShared_2715_ = v_isSharedCheck_2736_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_interestingStructures_2716_ =
                    leanh::lean_ctor_get(v_typeAnalysis_2710_, 0);
                v_interestingEnums_2717_ = leanh::lean_ctor_get(v_typeAnalysis_2710_, 1);
                v_interestingMatchers_2718_ = leanh::lean_ctor_get(v_typeAnalysis_2710_, 2);
                v_uninteresting_2719_ = leanh::lean_ctor_get(v_typeAnalysis_2710_, 3);
                v_isSharedCheck_2735_ =
                    (!leanh::lean_is_exclusive(v_typeAnalysis_2710_)) as u8;
                if v_isSharedCheck_2735_ == 0 {
                    v___x_2721_ = v_typeAnalysis_2710_;
                    v_isShared_2722_ = v_isSharedCheck_2735_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_uninteresting_2719_);
                    leanh::lean_inc(v_interestingMatchers_2718_);
                    leanh::lean_inc(v_interestingEnums_2717_);
                    leanh::lean_inc(v_interestingStructures_2716_);
                    leanh::lean_dec(v_typeAnalysis_2710_);
                    v___x_2721_ = leanh::lean_box(0);
                    v_isShared_2722_ = v_isSharedCheck_2735_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2723_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0;
                v___x_2724_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1;
                v___x_2725_ = leanh::lean_box(0);
                v___x_2726_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_2723_,
                    v___x_2724_,
                    v_uninteresting_2719_,
                    v_n_2706_,
                    v___x_2725_,
                );
                if v_isShared_2722_ == 0 {
                    leanh::lean_ctor_set(v___x_2721_, 3, v___x_2726_);
                    v___x_2728_ = v___x_2721_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2734_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2734_,
                        0,
                        v_interestingStructures_2716_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2734_,
                        1,
                        v_interestingEnums_2717_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2734_,
                        2,
                        v_interestingMatchers_2718_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2734_, 3, v___x_2726_);
                    v___x_2728_ = v_reuseFailAlloc_2734_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2715_ == 0 {
                    leanh::lean_ctor_set(v___x_2714_, 2, v___x_2728_);
                    v___x_2730_ = v___x_2714_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2733_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_rewriteCache_2711_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2733_, 1, v_acNfCache_2712_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2733_, 2, v___x_2728_);
                    v___x_2730_ = v_reuseFailAlloc_2733_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2731_ = lean_st_ref_set(v_a_2707_, v___x_2730_);
                v___x_2732_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2732_, 0, v___x_2725_);
                return v___x_2732_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg___boxed(
    mut v_n_2737_: *mut leanh::LeanObject,
    mut v_a_2738_: *mut leanh::LeanObject,
    mut v_a_2739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2740_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___redArg(
        v_n_2737_, v_a_2738_,
    );
    leanh::lean_dec(v_a_2738_);
    return v_res_2740_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(
    mut v_n_2741_: *mut leanh::LeanObject,
    mut v_a_2742_: *mut leanh::LeanObject,
    mut v_a_2743_: *mut leanh::LeanObject,
    mut v_a_2744_: *mut leanh::LeanObject,
    mut v_a_2745_: *mut leanh::LeanObject,
    mut v_a_2746_: *mut leanh::LeanObject,
    mut v_a_2747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2755_: u8 = 0;
    let mut v_interestingStructures_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingEnums_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_interestingMatchers_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uninteresting_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2762_: u8 = 0;
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2775_: u8 = 0;
    let mut v_isSharedCheck_2776_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2749_ = lean_st_ref_take(v_a_2743_);
                v_typeAnalysis_2750_ = leanh::lean_ctor_get(v___x_2749_, 2);
                v_rewriteCache_2751_ = leanh::lean_ctor_get(v___x_2749_, 0);
                v_acNfCache_2752_ = leanh::lean_ctor_get(v___x_2749_, 1);
                v_isSharedCheck_2776_ = (!leanh::lean_is_exclusive(v___x_2749_)) as u8;
                if v_isSharedCheck_2776_ == 0 {
                    v___x_2754_ = v___x_2749_;
                    v_isShared_2755_ = v_isSharedCheck_2776_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_typeAnalysis_2750_);
                    leanh::lean_inc(v_acNfCache_2752_);
                    leanh::lean_inc(v_rewriteCache_2751_);
                    leanh::lean_dec(v___x_2749_);
                    v___x_2754_ = leanh::lean_box(0);
                    v_isShared_2755_ = v_isSharedCheck_2776_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_interestingStructures_2756_ =
                    leanh::lean_ctor_get(v_typeAnalysis_2750_, 0);
                v_interestingEnums_2757_ = leanh::lean_ctor_get(v_typeAnalysis_2750_, 1);
                v_interestingMatchers_2758_ = leanh::lean_ctor_get(v_typeAnalysis_2750_, 2);
                v_uninteresting_2759_ = leanh::lean_ctor_get(v_typeAnalysis_2750_, 3);
                v_isSharedCheck_2775_ =
                    (!leanh::lean_is_exclusive(v_typeAnalysis_2750_)) as u8;
                if v_isSharedCheck_2775_ == 0 {
                    v___x_2761_ = v_typeAnalysis_2750_;
                    v_isShared_2762_ = v_isSharedCheck_2775_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_uninteresting_2759_);
                    leanh::lean_inc(v_interestingMatchers_2758_);
                    leanh::lean_inc(v_interestingEnums_2757_);
                    leanh::lean_inc(v_interestingStructures_2756_);
                    leanh::lean_dec(v_typeAnalysis_2750_);
                    v___x_2761_ = leanh::lean_box(0);
                    v_isShared_2762_ = v_isSharedCheck_2775_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2763_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__0;
                v___x_2764_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_lookupInterestingStructure___redArg___closed__1;
                v___x_2765_ = leanh::lean_box(0);
                v___x_2766_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_2763_,
                    v___x_2764_,
                    v_uninteresting_2759_,
                    v_n_2741_,
                    v___x_2765_,
                );
                if v_isShared_2762_ == 0 {
                    leanh::lean_ctor_set(v___x_2761_, 3, v___x_2766_);
                    v___x_2768_ = v___x_2761_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2774_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2774_,
                        0,
                        v_interestingStructures_2756_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2774_,
                        1,
                        v_interestingEnums_2757_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2774_,
                        2,
                        v_interestingMatchers_2758_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2774_, 3, v___x_2766_);
                    v___x_2768_ = v_reuseFailAlloc_2774_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2755_ == 0 {
                    leanh::lean_ctor_set(v___x_2754_, 2, v___x_2768_);
                    v___x_2770_ = v___x_2754_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2773_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_rewriteCache_2751_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2773_, 1, v_acNfCache_2752_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2773_, 2, v___x_2768_);
                    v___x_2770_ = v_reuseFailAlloc_2773_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2771_ = lean_st_ref_set(v_a_2743_, v___x_2770_);
                v___x_2772_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2772_, 0, v___x_2765_);
                return v___x_2772_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst___boxed(
    mut v_n_2777_: *mut leanh::LeanObject,
    mut v_a_2778_: *mut leanh::LeanObject,
    mut v_a_2779_: *mut leanh::LeanObject,
    mut v_a_2780_: *mut leanh::LeanObject,
    mut v_a_2781_: *mut leanh::LeanObject,
    mut v_a_2782_: *mut leanh::LeanObject,
    mut v_a_2783_: *mut leanh::LeanObject,
    mut v_a_2784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2785_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_markUninterestingConst(
        v_n_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_,
    );
    leanh::lean_dec(v_a_2783_);
    leanh::lean_dec_ref(v_a_2782_);
    leanh::lean_dec(v_a_2781_);
    leanh::lean_dec_ref(v_a_2780_);
    leanh::lean_dec(v_a_2779_);
    leanh::lean_dec_ref(v_a_2778_);
    return v_res_2785_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2786_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_2786_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2787_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2794_ = leanh::lean_box(0);
    v___x_2795_ = leanh::lean_unsigned_to_nat(16);
    v___x_2796_ = lean_mk_array(v___x_2795_, v___x_2794_);
    return v___x_2796_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2797_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__7_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__7,
    );
    v___x_2798_ = leanh::lean_unsigned_to_nat(0);
    v___x_2799_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2799_, 0, v___x_2798_);
    leanh::lean_ctor_set(v___x_2799_, 1, v___x_2797_);
    return v___x_2799_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2800_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__8
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__8_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__8,
    );
    v___x_2801_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2801_, 0, v___x_2800_);
    leanh::lean_ctor_set(v___x_2801_, 1, v___x_2800_);
    leanh::lean_ctor_set(v___x_2801_, 2, v___x_2800_);
    leanh::lean_ctor_set(v___x_2801_, 3, v___x_2800_);
    return v___x_2801_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(
    mut v_cfg_2802_: *mut leanh::LeanObject,
    mut v_goal_2803_: *mut leanh::LeanObject,
    mut v_x_2804_: *mut leanh::LeanObject,
    mut v_a_2805_: *mut leanh::LeanObject,
    mut v_a_2806_: *mut leanh::LeanObject,
    mut v_a_2807_: *mut leanh::LeanObject,
    mut v_a_2808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2830_: u8 = 0;
    let mut v_toFunctor_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2837_: u8 = 0;
    let mut v___f_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664__overap_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2887_: u8 = 0;
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2892_: u8 = 0;
    let mut v_a_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2896_: u8 = 0;
    let mut v___x_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2900_: u8 = 0;
    let mut v_reuseFailAlloc_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2903_: u8 = 0;
    let mut v_unused_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2905_: u8 = 0;
    let mut v_unused_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2810_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1);
                v_toApplicative_2811_ = leanh::lean_ctor_get(v___x_2810_, 0);
                v_toFunctor_2812_ = leanh::lean_ctor_get(v_toApplicative_2811_, 0);
                v_toSeq_2813_ = leanh::lean_ctor_get(v_toApplicative_2811_, 2);
                v_toSeqLeft_2814_ = leanh::lean_ctor_get(v_toApplicative_2811_, 3);
                v_toSeqRight_2815_ = leanh::lean_ctor_get(v_toApplicative_2811_, 4);
                v___f_2816_ =
                    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2;
                v___f_2817_ =
                    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3;
                leanh::lean_inc_ref_n(v_toFunctor_2812_, 2);
                v___f_2818_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2818_, 0, v_toFunctor_2812_);
                v___f_2819_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2819_, 0, v_toFunctor_2812_);
                v___x_2820_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2820_, 0, v___f_2818_);
                leanh::lean_ctor_set(v___x_2820_, 1, v___f_2819_);
                leanh::lean_inc(v_toSeqRight_2815_);
                v___f_2821_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2821_, 0, v_toSeqRight_2815_);
                leanh::lean_inc(v_toSeqLeft_2814_);
                v___f_2822_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2822_, 0, v_toSeqLeft_2814_);
                leanh::lean_inc(v_toSeq_2813_);
                v___f_2823_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2823_, 0, v_toSeq_2813_);
                v___x_2824_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_2824_, 0, v___x_2820_);
                leanh::lean_ctor_set(v___x_2824_, 1, v___f_2816_);
                leanh::lean_ctor_set(v___x_2824_, 2, v___f_2823_);
                leanh::lean_ctor_set(v___x_2824_, 3, v___f_2822_);
                leanh::lean_ctor_set(v___x_2824_, 4, v___f_2821_);
                v___x_2825_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2825_, 0, v___x_2824_);
                leanh::lean_ctor_set(v___x_2825_, 1, v___f_2817_);
                v___x_2826_ = l_StateRefT_x27_instMonad___redArg(v___x_2825_);
                v_toApplicative_2827_ = leanh::lean_ctor_get(v___x_2826_, 0);
                v_isSharedCheck_2905_ = (!leanh::lean_is_exclusive(v___x_2826_)) as u8;
                if v_isSharedCheck_2905_ == 0 {
                    v_unused_2906_ = leanh::lean_ctor_get(v___x_2826_, 1);
                    leanh::lean_dec(v_unused_2906_);
                    v___x_2829_ = v___x_2826_;
                    v_isShared_2830_ = v_isSharedCheck_2905_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_2827_);
                    leanh::lean_dec(v___x_2826_);
                    v___x_2829_ = leanh::lean_box(0);
                    v_isShared_2830_ = v_isSharedCheck_2905_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2831_ = leanh::lean_ctor_get(v_toApplicative_2827_, 0);
                v_toSeq_2832_ = leanh::lean_ctor_get(v_toApplicative_2827_, 2);
                v_toSeqLeft_2833_ = leanh::lean_ctor_get(v_toApplicative_2827_, 3);
                v_toSeqRight_2834_ = leanh::lean_ctor_get(v_toApplicative_2827_, 4);
                v_isSharedCheck_2903_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_2827_)) as u8;
                if v_isSharedCheck_2903_ == 0 {
                    v_unused_2904_ = leanh::lean_ctor_get(v_toApplicative_2827_, 1);
                    leanh::lean_dec(v_unused_2904_);
                    v___x_2836_ = v_toApplicative_2827_;
                    v_isShared_2837_ = v_isSharedCheck_2903_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_2834_);
                    leanh::lean_inc(v_toSeqLeft_2833_);
                    leanh::lean_inc(v_toSeq_2832_);
                    leanh::lean_inc(v_toFunctor_2831_);
                    leanh::lean_dec(v_toApplicative_2827_);
                    v___x_2836_ = leanh::lean_box(0);
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
                leanh::lean_inc_ref(v_toFunctor_2831_);
                v___f_2840_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2840_, 0, v_toFunctor_2831_);
                v___f_2841_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2841_, 0, v_toFunctor_2831_);
                v___x_2842_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2842_, 0, v___f_2840_);
                leanh::lean_ctor_set(v___x_2842_, 1, v___f_2841_);
                v___f_2843_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2843_, 0, v_toSeqRight_2834_);
                v___f_2844_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2844_, 0, v_toSeqLeft_2833_);
                v___f_2845_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2845_, 0, v_toSeq_2832_);
                if v_isShared_2837_ == 0 {
                    leanh::lean_ctor_set(v___x_2836_, 4, v___f_2843_);
                    leanh::lean_ctor_set(v___x_2836_, 3, v___f_2844_);
                    leanh::lean_ctor_set(v___x_2836_, 2, v___f_2845_);
                    leanh::lean_ctor_set(v___x_2836_, 1, v___f_2838_);
                    leanh::lean_ctor_set(v___x_2836_, 0, v___x_2842_);
                    v___x_2847_ = v___x_2836_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2902_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2842_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2902_, 1, v___f_2838_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2902_, 2, v___f_2845_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2902_, 3, v___f_2844_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2902_, 4, v___f_2843_);
                    v___x_2847_ = v_reuseFailAlloc_2902_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2830_ == 0 {
                    leanh::lean_ctor_set(v___x_2829_, 1, v___f_2839_);
                    leanh::lean_ctor_set(v___x_2829_, 0, v___x_2847_);
                    v___x_2849_ = v___x_2829_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2901_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2901_, 0, v___x_2847_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2901_, 1, v___f_2839_);
                    v___x_2849_ = v_reuseFailAlloc_2901_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_toApplicative_2850_ = leanh::lean_ctor_get(v___x_2810_, 0);
                v_toFunctor_2851_ = leanh::lean_ctor_get(v_toApplicative_2850_, 0);
                v_toSeq_2852_ = leanh::lean_ctor_get(v_toApplicative_2850_, 2);
                v_toSeqLeft_2853_ = leanh::lean_ctor_get(v_toApplicative_2850_, 3);
                v_toSeqRight_2854_ = leanh::lean_ctor_get(v_toApplicative_2850_, 4);
                leanh::lean_inc_ref_n(v_toFunctor_2851_, 2);
                v___f_2855_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2855_, 0, v_toFunctor_2851_);
                v___f_2856_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2856_, 0, v_toFunctor_2851_);
                v___x_2857_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2857_, 0, v___f_2855_);
                leanh::lean_ctor_set(v___x_2857_, 1, v___f_2856_);
                leanh::lean_inc(v_toSeqRight_2854_);
                v___f_2858_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2858_, 0, v_toSeqRight_2854_);
                leanh::lean_inc(v_toSeqLeft_2853_);
                v___f_2859_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2859_, 0, v_toSeqLeft_2853_);
                leanh::lean_inc(v_toSeq_2852_);
                v___f_2860_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2860_, 0, v_toSeq_2852_);
                v___x_2861_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_2861_, 0, v___x_2857_);
                leanh::lean_ctor_set(v___x_2861_, 1, v___f_2816_);
                leanh::lean_ctor_set(v___x_2861_, 2, v___f_2860_);
                leanh::lean_ctor_set(v___x_2861_, 3, v___f_2859_);
                leanh::lean_ctor_set(v___x_2861_, 4, v___f_2858_);
                v___x_2862_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2862_, 0, v___x_2861_);
                leanh::lean_ctor_set(v___x_2862_, 1, v___f_2817_);
                v___x_2863_ = l_StateRefT_x27_instMonad___redArg(v___x_2862_);
                v___x_2864_ = leanh::lean_alloc_closure(
                    l_ReaderT_pure___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                leanh::lean_closure_set(v___x_2864_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2864_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2864_, 2, v___x_2863_);
                v___x_2865_ = l_instMonadControlTOfPure___redArg(v___x_2864_);
                v___x_2866_ =
                    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__6;
                v___x_664__overap_2867_ = l_Lean_MVarId_withContext___redArg(
                    v___x_2865_,
                    v___x_2849_,
                    v_goal_2803_,
                    v___x_2866_,
                );
                leanh::lean_inc(v_a_2808_);
                leanh::lean_inc_ref(v_a_2807_);
                leanh::lean_inc(v_a_2806_);
                leanh::lean_inc_ref(v_a_2805_);
                v___x_2868_ = leanh::lean_apply_5(
                    v___x_664__overap_2867_,
                    v_a_2805_,
                    v_a_2806_,
                    v_a_2807_,
                    v_a_2808_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_2868_) == 0 {
                    v_a_2869_ = leanh::lean_ctor_get(v___x_2868_, 0);
                    leanh::lean_inc(v_a_2869_);
                    leanh::lean_dec_ref_known(v___x_2868_, 1);
                    v___x_2870_ = lean_array_get_size(v_a_2869_);
                    leanh::lean_dec(v_a_2869_);
                    v___x_2871_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2872_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2873_ = lean_nat_mul(v___x_2870_, v___x_2872_);
                    v___x_2874_ = leanh::lean_unsigned_to_nat(3);
                    v___x_2875_ = lean_nat_div(v___x_2873_, v___x_2874_);
                    leanh::lean_dec(v___x_2873_);
                    v___x_2876_ = l_Nat_nextPowerOfTwo(v___x_2875_);
                    leanh::lean_dec(v___x_2875_);
                    v___x_2877_ = leanh::lean_box(0);
                    v___x_2878_ = lean_mk_array(v___x_2876_, v___x_2877_);
                    v___x_2879_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2879_, 0, v___x_2871_);
                    leanh::lean_ctor_set(v___x_2879_, 1, v___x_2878_);
                    v___x_2880_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__9_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__9);
                    leanh::lean_inc_ref(v___x_2879_);
                    v___x_2881_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2881_, 0, v___x_2879_);
                    leanh::lean_ctor_set(v___x_2881_, 1, v___x_2879_);
                    leanh::lean_ctor_set(v___x_2881_, 2, v___x_2880_);
                    v___x_2882_ = lean_st_mk_ref(v___x_2881_);
                    leanh::lean_inc(v_a_2808_);
                    leanh::lean_inc_ref(v_a_2807_);
                    leanh::lean_inc(v_a_2806_);
                    leanh::lean_inc_ref(v_a_2805_);
                    leanh::lean_inc(v___x_2882_);
                    v___x_2883_ = leanh::lean_apply_7(
                        v_x_2804_,
                        v_cfg_2802_,
                        v___x_2882_,
                        v_a_2805_,
                        v_a_2806_,
                        v_a_2807_,
                        v_a_2808_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_2883_) == 0 {
                        v_a_2884_ = leanh::lean_ctor_get(v___x_2883_, 0);
                        v_isSharedCheck_2892_ =
                            (!leanh::lean_is_exclusive(v___x_2883_)) as u8;
                        if v_isSharedCheck_2892_ == 0 {
                            v___x_2886_ = v___x_2883_;
                            v_isShared_2887_ = v_isSharedCheck_2892_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2884_);
                            leanh::lean_dec(v___x_2883_);
                            v___x_2886_ = leanh::lean_box(0);
                            v_isShared_2887_ = v_isSharedCheck_2892_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_2882_);
                        return v___x_2883_;
                    }
                } else {
                    leanh::lean_dec_ref(v_x_2804_);
                    leanh::lean_dec_ref(v_cfg_2802_);
                    v_a_2893_ = leanh::lean_ctor_get(v___x_2868_, 0);
                    v_isSharedCheck_2900_ = (!leanh::lean_is_exclusive(v___x_2868_)) as u8;
                    if v_isSharedCheck_2900_ == 0 {
                        v___x_2895_ = v___x_2868_;
                        v_isShared_2896_ = v_isSharedCheck_2900_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2893_);
                        leanh::lean_dec(v___x_2868_);
                        v___x_2895_ = leanh::lean_box(0);
                        v_isShared_2896_ = v_isSharedCheck_2900_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v___x_2888_ = lean_st_ref_get(v___x_2882_);
                leanh::lean_dec(v___x_2882_);
                leanh::lean_dec(v___x_2888_);
                if v_isShared_2887_ == 0 {
                    v___x_2890_ = v___x_2886_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2891_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2884_);
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
                    v_reuseFailAlloc_2899_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2893_);
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
    mut v_cfg_2907_: *mut leanh::LeanObject,
    mut v_goal_2908_: *mut leanh::LeanObject,
    mut v_x_2909_: *mut leanh::LeanObject,
    mut v_a_2910_: *mut leanh::LeanObject,
    mut v_a_2911_: *mut leanh::LeanObject,
    mut v_a_2912_: *mut leanh::LeanObject,
    mut v_a_2913_: *mut leanh::LeanObject,
    mut v_a_2914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2915_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg(
        v_cfg_2907_,
        v_goal_2908_,
        v_x_2909_,
        v_a_2910_,
        v_a_2911_,
        v_a_2912_,
        v_a_2913_,
    );
    leanh::lean_dec(v_a_2913_);
    leanh::lean_dec_ref(v_a_2912_);
    leanh::lean_dec(v_a_2911_);
    leanh::lean_dec_ref(v_a_2910_);
    return v_res_2915_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run(
    mut v_00_u03b1_2916_: *mut leanh::LeanObject,
    mut v_cfg_2917_: *mut leanh::LeanObject,
    mut v_goal_2918_: *mut leanh::LeanObject,
    mut v_x_2919_: *mut leanh::LeanObject,
    mut v_a_2920_: *mut leanh::LeanObject,
    mut v_a_2921_: *mut leanh::LeanObject,
    mut v_a_2922_: *mut leanh::LeanObject,
    mut v_a_2923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2945_: u8 = 0;
    let mut v_toFunctor_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2952_: u8 = 0;
    let mut v___f_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887__overap_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3002_: u8 = 0;
    let mut v___x_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3007_: u8 = 0;
    let mut v_a_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3011_: u8 = 0;
    let mut v___x_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3015_: u8 = 0;
    let mut v_reuseFailAlloc_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3018_: u8 = 0;
    let mut v_unused_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3020_: u8 = 0;
    let mut v_unused_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2925_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1);
                v_toApplicative_2926_ = leanh::lean_ctor_get(v___x_2925_, 0);
                v_toFunctor_2927_ = leanh::lean_ctor_get(v_toApplicative_2926_, 0);
                v_toSeq_2928_ = leanh::lean_ctor_get(v_toApplicative_2926_, 2);
                v_toSeqLeft_2929_ = leanh::lean_ctor_get(v_toApplicative_2926_, 3);
                v_toSeqRight_2930_ = leanh::lean_ctor_get(v_toApplicative_2926_, 4);
                v___f_2931_ =
                    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2;
                v___f_2932_ =
                    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3;
                leanh::lean_inc_ref_n(v_toFunctor_2927_, 2);
                v___f_2933_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2933_, 0, v_toFunctor_2927_);
                v___f_2934_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2934_, 0, v_toFunctor_2927_);
                v___x_2935_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2935_, 0, v___f_2933_);
                leanh::lean_ctor_set(v___x_2935_, 1, v___f_2934_);
                leanh::lean_inc(v_toSeqRight_2930_);
                v___f_2936_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2936_, 0, v_toSeqRight_2930_);
                leanh::lean_inc(v_toSeqLeft_2929_);
                v___f_2937_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2937_, 0, v_toSeqLeft_2929_);
                leanh::lean_inc(v_toSeq_2928_);
                v___f_2938_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2938_, 0, v_toSeq_2928_);
                v___x_2939_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_2939_, 0, v___x_2935_);
                leanh::lean_ctor_set(v___x_2939_, 1, v___f_2931_);
                leanh::lean_ctor_set(v___x_2939_, 2, v___f_2938_);
                leanh::lean_ctor_set(v___x_2939_, 3, v___f_2937_);
                leanh::lean_ctor_set(v___x_2939_, 4, v___f_2936_);
                v___x_2940_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2940_, 0, v___x_2939_);
                leanh::lean_ctor_set(v___x_2940_, 1, v___f_2932_);
                v___x_2941_ = l_StateRefT_x27_instMonad___redArg(v___x_2940_);
                v_toApplicative_2942_ = leanh::lean_ctor_get(v___x_2941_, 0);
                v_isSharedCheck_3020_ = (!leanh::lean_is_exclusive(v___x_2941_)) as u8;
                if v_isSharedCheck_3020_ == 0 {
                    v_unused_3021_ = leanh::lean_ctor_get(v___x_2941_, 1);
                    leanh::lean_dec(v_unused_3021_);
                    v___x_2944_ = v___x_2941_;
                    v_isShared_2945_ = v_isSharedCheck_3020_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_2942_);
                    leanh::lean_dec(v___x_2941_);
                    v___x_2944_ = leanh::lean_box(0);
                    v_isShared_2945_ = v_isSharedCheck_3020_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2946_ = leanh::lean_ctor_get(v_toApplicative_2942_, 0);
                v_toSeq_2947_ = leanh::lean_ctor_get(v_toApplicative_2942_, 2);
                v_toSeqLeft_2948_ = leanh::lean_ctor_get(v_toApplicative_2942_, 3);
                v_toSeqRight_2949_ = leanh::lean_ctor_get(v_toApplicative_2942_, 4);
                v_isSharedCheck_3018_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_2942_)) as u8;
                if v_isSharedCheck_3018_ == 0 {
                    v_unused_3019_ = leanh::lean_ctor_get(v_toApplicative_2942_, 1);
                    leanh::lean_dec(v_unused_3019_);
                    v___x_2951_ = v_toApplicative_2942_;
                    v_isShared_2952_ = v_isSharedCheck_3018_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_2949_);
                    leanh::lean_inc(v_toSeqLeft_2948_);
                    leanh::lean_inc(v_toSeq_2947_);
                    leanh::lean_inc(v_toFunctor_2946_);
                    leanh::lean_dec(v_toApplicative_2942_);
                    v___x_2951_ = leanh::lean_box(0);
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
                leanh::lean_inc_ref(v_toFunctor_2946_);
                v___f_2955_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2955_, 0, v_toFunctor_2946_);
                v___f_2956_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2956_, 0, v_toFunctor_2946_);
                v___x_2957_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2957_, 0, v___f_2955_);
                leanh::lean_ctor_set(v___x_2957_, 1, v___f_2956_);
                v___f_2958_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2958_, 0, v_toSeqRight_2949_);
                v___f_2959_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2959_, 0, v_toSeqLeft_2948_);
                v___f_2960_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2960_, 0, v_toSeq_2947_);
                if v_isShared_2952_ == 0 {
                    leanh::lean_ctor_set(v___x_2951_, 4, v___f_2958_);
                    leanh::lean_ctor_set(v___x_2951_, 3, v___f_2959_);
                    leanh::lean_ctor_set(v___x_2951_, 2, v___f_2960_);
                    leanh::lean_ctor_set(v___x_2951_, 1, v___f_2953_);
                    leanh::lean_ctor_set(v___x_2951_, 0, v___x_2957_);
                    v___x_2962_ = v___x_2951_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3017_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3017_, 0, v___x_2957_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3017_, 1, v___f_2953_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3017_, 2, v___f_2960_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3017_, 3, v___f_2959_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3017_, 4, v___f_2958_);
                    v___x_2962_ = v_reuseFailAlloc_3017_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2945_ == 0 {
                    leanh::lean_ctor_set(v___x_2944_, 1, v___f_2954_);
                    leanh::lean_ctor_set(v___x_2944_, 0, v___x_2962_);
                    v___x_2964_ = v___x_2944_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3016_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_2962_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3016_, 1, v___f_2954_);
                    v___x_2964_ = v_reuseFailAlloc_3016_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_toApplicative_2965_ = leanh::lean_ctor_get(v___x_2925_, 0);
                v_toFunctor_2966_ = leanh::lean_ctor_get(v_toApplicative_2965_, 0);
                v_toSeq_2967_ = leanh::lean_ctor_get(v_toApplicative_2965_, 2);
                v_toSeqLeft_2968_ = leanh::lean_ctor_get(v_toApplicative_2965_, 3);
                v_toSeqRight_2969_ = leanh::lean_ctor_get(v_toApplicative_2965_, 4);
                leanh::lean_inc_ref_n(v_toFunctor_2966_, 2);
                v___f_2970_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2970_, 0, v_toFunctor_2966_);
                v___f_2971_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2971_, 0, v_toFunctor_2966_);
                v___x_2972_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2972_, 0, v___f_2970_);
                leanh::lean_ctor_set(v___x_2972_, 1, v___f_2971_);
                leanh::lean_inc(v_toSeqRight_2969_);
                v___f_2973_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2973_, 0, v_toSeqRight_2969_);
                leanh::lean_inc(v_toSeqLeft_2968_);
                v___f_2974_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2974_, 0, v_toSeqLeft_2968_);
                leanh::lean_inc(v_toSeq_2967_);
                v___f_2975_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2975_, 0, v_toSeq_2967_);
                v___x_2976_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_2976_, 0, v___x_2972_);
                leanh::lean_ctor_set(v___x_2976_, 1, v___f_2931_);
                leanh::lean_ctor_set(v___x_2976_, 2, v___f_2975_);
                leanh::lean_ctor_set(v___x_2976_, 3, v___f_2974_);
                leanh::lean_ctor_set(v___x_2976_, 4, v___f_2973_);
                v___x_2977_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2977_, 0, v___x_2976_);
                leanh::lean_ctor_set(v___x_2977_, 1, v___f_2932_);
                v___x_2978_ = l_StateRefT_x27_instMonad___redArg(v___x_2977_);
                v___x_2979_ = leanh::lean_alloc_closure(
                    l_ReaderT_pure___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                leanh::lean_closure_set(v___x_2979_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2979_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2979_, 2, v___x_2978_);
                v___x_2980_ = l_instMonadControlTOfPure___redArg(v___x_2979_);
                v___x_2981_ =
                    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__6;
                v___x_887__overap_2982_ = l_Lean_MVarId_withContext___redArg(
                    v___x_2980_,
                    v___x_2964_,
                    v_goal_2918_,
                    v___x_2981_,
                );
                leanh::lean_inc(v_a_2923_);
                leanh::lean_inc_ref(v_a_2922_);
                leanh::lean_inc(v_a_2921_);
                leanh::lean_inc_ref(v_a_2920_);
                v___x_2983_ = leanh::lean_apply_5(
                    v___x_887__overap_2982_,
                    v_a_2920_,
                    v_a_2921_,
                    v_a_2922_,
                    v_a_2923_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_2983_) == 0 {
                    v_a_2984_ = leanh::lean_ctor_get(v___x_2983_, 0);
                    leanh::lean_inc(v_a_2984_);
                    leanh::lean_dec_ref_known(v___x_2983_, 1);
                    v___x_2985_ = lean_array_get_size(v_a_2984_);
                    leanh::lean_dec(v_a_2984_);
                    v___x_2986_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2987_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2988_ = lean_nat_mul(v___x_2985_, v___x_2987_);
                    v___x_2989_ = leanh::lean_unsigned_to_nat(3);
                    v___x_2990_ = lean_nat_div(v___x_2988_, v___x_2989_);
                    leanh::lean_dec(v___x_2988_);
                    v___x_2991_ = l_Nat_nextPowerOfTwo(v___x_2990_);
                    leanh::lean_dec(v___x_2990_);
                    v___x_2992_ = leanh::lean_box(0);
                    v___x_2993_ = lean_mk_array(v___x_2991_, v___x_2992_);
                    v___x_2994_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2994_, 0, v___x_2986_);
                    leanh::lean_ctor_set(v___x_2994_, 1, v___x_2993_);
                    v___x_2995_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__9_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__9);
                    leanh::lean_inc_ref(v___x_2994_);
                    v___x_2996_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2996_, 0, v___x_2994_);
                    leanh::lean_ctor_set(v___x_2996_, 1, v___x_2994_);
                    leanh::lean_ctor_set(v___x_2996_, 2, v___x_2995_);
                    v___x_2997_ = lean_st_mk_ref(v___x_2996_);
                    leanh::lean_inc(v_a_2923_);
                    leanh::lean_inc_ref(v_a_2922_);
                    leanh::lean_inc(v_a_2921_);
                    leanh::lean_inc_ref(v_a_2920_);
                    leanh::lean_inc(v___x_2997_);
                    v___x_2998_ = leanh::lean_apply_7(
                        v_x_2919_,
                        v_cfg_2917_,
                        v___x_2997_,
                        v_a_2920_,
                        v_a_2921_,
                        v_a_2922_,
                        v_a_2923_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_2998_) == 0 {
                        v_a_2999_ = leanh::lean_ctor_get(v___x_2998_, 0);
                        v_isSharedCheck_3007_ =
                            (!leanh::lean_is_exclusive(v___x_2998_)) as u8;
                        if v_isSharedCheck_3007_ == 0 {
                            v___x_3001_ = v___x_2998_;
                            v_isShared_3002_ = v_isSharedCheck_3007_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2999_);
                            leanh::lean_dec(v___x_2998_);
                            v___x_3001_ = leanh::lean_box(0);
                            v_isShared_3002_ = v_isSharedCheck_3007_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_2997_);
                        return v___x_2998_;
                    }
                } else {
                    leanh::lean_dec_ref(v_x_2919_);
                    leanh::lean_dec_ref(v_cfg_2917_);
                    v_a_3008_ = leanh::lean_ctor_get(v___x_2983_, 0);
                    v_isSharedCheck_3015_ = (!leanh::lean_is_exclusive(v___x_2983_)) as u8;
                    if v_isSharedCheck_3015_ == 0 {
                        v___x_3010_ = v___x_2983_;
                        v_isShared_3011_ = v_isSharedCheck_3015_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3008_);
                        leanh::lean_dec(v___x_2983_);
                        v___x_3010_ = leanh::lean_box(0);
                        v_isShared_3011_ = v_isSharedCheck_3015_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v___x_3003_ = lean_st_ref_get(v___x_2997_);
                leanh::lean_dec(v___x_2997_);
                leanh::lean_dec(v___x_3003_);
                if v_isShared_3002_ == 0 {
                    v___x_3005_ = v___x_3001_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3006_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_a_2999_);
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
                    v_reuseFailAlloc_3014_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_a_3008_);
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
    mut v_00_u03b1_3022_: *mut leanh::LeanObject,
    mut v_cfg_3023_: *mut leanh::LeanObject,
    mut v_goal_3024_: *mut leanh::LeanObject,
    mut v_x_3025_: *mut leanh::LeanObject,
    mut v_a_3026_: *mut leanh::LeanObject,
    mut v_a_3027_: *mut leanh::LeanObject,
    mut v_a_3028_: *mut leanh::LeanObject,
    mut v_a_3029_: *mut leanh::LeanObject,
    mut v_a_3030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_3029_);
    leanh::lean_dec_ref(v_a_3028_);
    leanh::lean_dec(v_a_3027_);
    leanh::lean_dec_ref(v_a_3026_);
    return v_res_3031_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3033_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__0;
    v___x_3034_ = l_Lean_stringToMessageData(v___x_3033_);
    return v___x_3034_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3036_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__2;
    v___x_3037_ = l_Lean_stringToMessageData(v___x_3036_);
    return v___x_3037_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0(
    mut v_name_3038_: *mut leanh::LeanObject,
    mut v_goal_3039_: *mut leanh::LeanObject,
    mut v_x_3040_: *mut leanh::LeanObject,
    mut v___y_3041_: *mut leanh::LeanObject,
    mut v___y_3042_: *mut leanh::LeanObject,
    mut v___y_3043_: *mut leanh::LeanObject,
    mut v___y_3044_: *mut leanh::LeanObject,
    mut v___y_3045_: *mut leanh::LeanObject,
    mut v___y_3046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3048_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1,
    );
    v___x_3049_ = l_Lean_MessageData_ofName(v_name_3038_);
    v___x_3050_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3050_, 0, v___x_3048_);
    leanh::lean_ctor_set(v___x_3050_, 1, v___x_3049_);
    v___x_3051_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__3_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__3,
    );
    v___x_3052_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3052_, 0, v___x_3050_);
    leanh::lean_ctor_set(v___x_3052_, 1, v___x_3051_);
    v___x_3053_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3053_, 0, v_goal_3039_);
    v___x_3054_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3054_, 0, v___x_3052_);
    leanh::lean_ctor_set(v___x_3054_, 1, v___x_3053_);
    v___x_3055_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3055_, 0, v___x_3054_);
    return v___x_3055_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed(
    mut v_name_3056_: *mut leanh::LeanObject,
    mut v_goal_3057_: *mut leanh::LeanObject,
    mut v_x_3058_: *mut leanh::LeanObject,
    mut v___y_3059_: *mut leanh::LeanObject,
    mut v___y_3060_: *mut leanh::LeanObject,
    mut v___y_3061_: *mut leanh::LeanObject,
    mut v___y_3062_: *mut leanh::LeanObject,
    mut v___y_3063_: *mut leanh::LeanObject,
    mut v___y_3064_: *mut leanh::LeanObject,
    mut v___y_3065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_3064_);
    leanh::lean_dec_ref(v___y_3063_);
    leanh::lean_dec(v___y_3062_);
    leanh::lean_dec_ref(v___y_3061_);
    leanh::lean_dec(v___y_3060_);
    leanh::lean_dec_ref(v___y_3059_);
    leanh::lean_dec_ref(v_x_3058_);
    return v_res_3066_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3069_ = l_Lean_Core_instMonadTraceCoreM;
    v___x_3070_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1;
    v___x_3071_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_3070_, v___x_3069_);
    return v___x_3071_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3072_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2_once),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__2,
    );
    v___f_3073_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0;
    v___x_3074_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_3073_, v___x_3072_);
    return v___x_3074_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3075_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3_once),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__3,
    );
    v___x_3076_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1;
    v___x_3077_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_3076_, v___x_3075_);
    return v___x_3077_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3078_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4_once),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__4,
    );
    v___f_3079_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0;
    v___x_3080_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_3079_, v___x_3078_);
    return v___x_3080_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
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
-> *mut leanh::LeanObject {
    let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3087_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3091_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3095_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3099_ = l_instMonadExceptOfEIO(leanh::lean_box(0));
    return v___x_3099_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3100_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12_once),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__12,
    );
    v___x_3101_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_3100_);
    return v___x_3101_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3102_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13_once),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__13,
    );
    v___x_3103_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_3102_);
    return v___x_3103_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3104_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__14_once),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__14,
    );
    v___x_3105_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_3104_);
    return v___x_3105_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3106_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__15_once),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__15,
    );
    v___x_3107_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_3106_);
    return v___x_3107_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3108_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__16_once),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__16,
    );
    v___x_3109_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_3108_);
    return v___x_3109_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3110_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__17_once),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__17,
    );
    v___x_3111_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_3110_);
    return v___x_3111_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3112_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__1;
    v___x_3113_ = l_Lean_Meta_instAddMessageContextMetaM;
    v___f_3114_ = leanh::lean_alloc_closure(
        l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3114_, 0, v___x_3113_);
    leanh::lean_closure_set(v___f_3114_, 1, v___x_3112_);
    return v___f_3114_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__20()
-> *mut leanh::LeanObject {
    let mut v___f_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3115_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__0;
    v___f_3116_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__19_once),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__19,
    );
    v___f_3117_ = leanh::lean_alloc_closure(
        l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3117_, 0, v___f_3116_);
    leanh::lean_closure_set(v___f_3117_, 1, v___f_3115_);
    return v___f_3117_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29()
-> *mut leanh::LeanObject {
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3130_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25;
    v___x_3131_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__28;
    v___x_3132_ = l_Lean_Name_append(v___x_3131_, v___x_3130_);
    return v___x_3132_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__30() -> f64 {
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: f64 = 0.0;
    v___x_3133_ = leanh::lean_unsigned_to_nat(1000000000);
    v___x_3134_ = lean_float_of_nat(v___x_3133_);
    return v___x_3134_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run(
    mut v_pass_3135_: *mut leanh::LeanObject,
    mut v_goal_3136_: *mut leanh::LeanObject,
    mut v_a_3137_: *mut leanh::LeanObject,
    mut v_a_3138_: *mut leanh::LeanObject,
    mut v_a_3139_: *mut leanh::LeanObject,
    mut v_a_3140_: *mut leanh::LeanObject,
    mut v_a_3141_: *mut leanh::LeanObject,
    mut v_a_3142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3164_: u8 = 0;
    let mut v_toFunctor_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3171_: u8 = 0;
    let mut v___f_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadRef_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3191_: u8 = 0;
    let mut v_run_x27_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_run_x27_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3198_: u8 = 0;
    let mut v_inheritedTraceOptions_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: u8 = 0;
    let mut v___y_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: f64 = 0.0;
    let mut v___x_3213_: f64 = 0.0;
    let mut v___x_3214_: f64 = 0.0;
    let mut v___x_3215_: f64 = 0.0;
    let mut v___x_3216_: f64 = 0.0;
    let mut v___x_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9546__overap_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: f64 = 0.0;
    let mut v___x_3231_: f64 = 0.0;
    let mut v___x_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9567__overap_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9523__overap_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: u8 = 0;
    let mut v___x_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3251_: u8 = 0;
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3255_: u8 = 0;
    let mut v_a_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3259_: u8 = 0;
    let mut v___x_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3263_: u8 = 0;
    let mut v___x_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3269_: u8 = 0;
    let mut v___x_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3273_: u8 = 0;
    let mut v_a_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3277_: u8 = 0;
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3281_: u8 = 0;
    let mut v_a_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3285_: u8 = 0;
    let mut v___x_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3289_: u8 = 0;
    let mut v___x_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: u8 = 0;
    let mut v___x_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3295_: u8 = 0;
    let mut v_reuseFailAlloc_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3298_: u8 = 0;
    let mut v_unused_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3300_: u8 = 0;
    let mut v_unused_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3144_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__1);
                v_toApplicative_3145_ = leanh::lean_ctor_get(v___x_3144_, 0);
                v_toFunctor_3146_ = leanh::lean_ctor_get(v_toApplicative_3145_, 0);
                v_toSeq_3147_ = leanh::lean_ctor_get(v_toApplicative_3145_, 2);
                v_toSeqLeft_3148_ = leanh::lean_ctor_get(v_toApplicative_3145_, 3);
                v_toSeqRight_3149_ = leanh::lean_ctor_get(v_toApplicative_3145_, 4);
                v___f_3150_ =
                    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__2;
                v___f_3151_ =
                    l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_run___redArg___closed__3;
                leanh::lean_inc_ref_n(v_toFunctor_3146_, 2);
                v___f_3152_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3152_, 0, v_toFunctor_3146_);
                v___f_3153_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3153_, 0, v_toFunctor_3146_);
                v___x_3154_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3154_, 0, v___f_3152_);
                leanh::lean_ctor_set(v___x_3154_, 1, v___f_3153_);
                leanh::lean_inc(v_toSeqRight_3149_);
                v___f_3155_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3155_, 0, v_toSeqRight_3149_);
                leanh::lean_inc(v_toSeqLeft_3148_);
                v___f_3156_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3156_, 0, v_toSeqLeft_3148_);
                leanh::lean_inc(v_toSeq_3147_);
                v___f_3157_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3157_, 0, v_toSeq_3147_);
                v___x_3158_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_3158_, 0, v___x_3154_);
                leanh::lean_ctor_set(v___x_3158_, 1, v___f_3150_);
                leanh::lean_ctor_set(v___x_3158_, 2, v___f_3157_);
                leanh::lean_ctor_set(v___x_3158_, 3, v___f_3156_);
                leanh::lean_ctor_set(v___x_3158_, 4, v___f_3155_);
                v___x_3159_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3159_, 0, v___x_3158_);
                leanh::lean_ctor_set(v___x_3159_, 1, v___f_3151_);
                v___x_3160_ = l_StateRefT_x27_instMonad___redArg(v___x_3159_);
                v_toApplicative_3161_ = leanh::lean_ctor_get(v___x_3160_, 0);
                v_isSharedCheck_3300_ = (!leanh::lean_is_exclusive(v___x_3160_)) as u8;
                if v_isSharedCheck_3300_ == 0 {
                    v_unused_3301_ = leanh::lean_ctor_get(v___x_3160_, 1);
                    leanh::lean_dec(v_unused_3301_);
                    v___x_3163_ = v___x_3160_;
                    v_isShared_3164_ = v_isSharedCheck_3300_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_3161_);
                    leanh::lean_dec(v___x_3160_);
                    v___x_3163_ = leanh::lean_box(0);
                    v_isShared_3164_ = v_isSharedCheck_3300_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_3165_ = leanh::lean_ctor_get(v_toApplicative_3161_, 0);
                v_toSeq_3166_ = leanh::lean_ctor_get(v_toApplicative_3161_, 2);
                v_toSeqLeft_3167_ = leanh::lean_ctor_get(v_toApplicative_3161_, 3);
                v_toSeqRight_3168_ = leanh::lean_ctor_get(v_toApplicative_3161_, 4);
                v_isSharedCheck_3298_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_3161_)) as u8;
                if v_isSharedCheck_3298_ == 0 {
                    v_unused_3299_ = leanh::lean_ctor_get(v_toApplicative_3161_, 1);
                    leanh::lean_dec(v_unused_3299_);
                    v___x_3170_ = v_toApplicative_3161_;
                    v_isShared_3171_ = v_isSharedCheck_3298_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_3168_);
                    leanh::lean_inc(v_toSeqLeft_3167_);
                    leanh::lean_inc(v_toSeq_3166_);
                    leanh::lean_inc(v_toFunctor_3165_);
                    leanh::lean_dec(v_toApplicative_3161_);
                    v___x_3170_ = leanh::lean_box(0);
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
                leanh::lean_inc_ref(v_toFunctor_3165_);
                v___f_3174_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3174_, 0, v_toFunctor_3165_);
                v___f_3175_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3175_, 0, v_toFunctor_3165_);
                v___x_3176_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3176_, 0, v___f_3174_);
                leanh::lean_ctor_set(v___x_3176_, 1, v___f_3175_);
                v___f_3177_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3177_, 0, v_toSeqRight_3168_);
                v___f_3178_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3178_, 0, v_toSeqLeft_3167_);
                v___f_3179_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3179_, 0, v_toSeq_3166_);
                if v_isShared_3171_ == 0 {
                    leanh::lean_ctor_set(v___x_3170_, 4, v___f_3177_);
                    leanh::lean_ctor_set(v___x_3170_, 3, v___f_3178_);
                    leanh::lean_ctor_set(v___x_3170_, 2, v___f_3179_);
                    leanh::lean_ctor_set(v___x_3170_, 1, v___f_3172_);
                    leanh::lean_ctor_set(v___x_3170_, 0, v___x_3176_);
                    v___x_3181_ = v___x_3170_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3297_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3297_, 0, v___x_3176_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3297_, 1, v___f_3172_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3297_, 2, v___f_3179_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3297_, 3, v___f_3178_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3297_, 4, v___f_3177_);
                    v___x_3181_ = v_reuseFailAlloc_3297_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3164_ == 0 {
                    leanh::lean_ctor_set(v___x_3163_, 1, v___f_3173_);
                    leanh::lean_ctor_set(v___x_3163_, 0, v___x_3181_);
                    v___x_3183_ = v___x_3163_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3296_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___x_3181_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 1, v___f_3173_);
                    v___x_3183_ = v_reuseFailAlloc_3296_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3184_ = l_StateRefT_x27_instMonad___redArg(v___x_3183_);
                v___x_3185_ = l_ReaderT_instMonad___redArg(v___x_3184_);
                v___x_3186_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__5,
                );
                v___x_3187_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__11,
                );
                v_toMonadRef_3188_ = leanh::lean_ctor_get(v___x_3187_, 0);
                v___x_3189_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__18
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__18_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__18,
                );
                v_options_3190_ = leanh::lean_ctor_get(v_a_3141_, 2);
                v_hasTrace_3191_ = leanh::lean_ctor_get_uint8(
                    v_options_3190_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_3191_ == 0 {
                    leanh::lean_dec_ref(v___x_3185_);
                    v_run_x27_3192_ = leanh::lean_ctor_get(v_pass_3135_, 1);
                    leanh::lean_inc_ref(v_run_x27_3192_);
                    leanh::lean_dec_ref(v_pass_3135_);
                    leanh::lean_inc(v_a_3142_);
                    leanh::lean_inc_ref(v_a_3141_);
                    leanh::lean_inc(v_a_3140_);
                    leanh::lean_inc_ref(v_a_3139_);
                    leanh::lean_inc(v_a_3138_);
                    leanh::lean_inc_ref(v_a_3137_);
                    v___x_3193_ = leanh::lean_apply_8(
                        v_run_x27_3192_,
                        v_goal_3136_,
                        v_a_3137_,
                        v_a_3138_,
                        v_a_3139_,
                        v_a_3140_,
                        v_a_3141_,
                        v_a_3142_,
                        leanh::lean_box(0),
                    );
                    return v___x_3193_;
                } else {
                    v_name_3194_ = leanh::lean_ctor_get(v_pass_3135_, 0);
                    v_run_x27_3195_ = leanh::lean_ctor_get(v_pass_3135_, 1);
                    v_isSharedCheck_3295_ = (!leanh::lean_is_exclusive(v_pass_3135_)) as u8;
                    if v_isSharedCheck_3295_ == 0 {
                        v___x_3197_ = v_pass_3135_;
                        v_isShared_3198_ = v_isSharedCheck_3295_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_run_x27_3195_);
                        leanh::lean_inc(v_name_3194_);
                        leanh::lean_dec(v_pass_3135_);
                        v___x_3197_ = leanh::lean_box(0);
                        v_isShared_3198_ = v_isSharedCheck_3295_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v_inheritedTraceOptions_3199_ = leanh::lean_ctor_get(v_a_3141_, 13);
                leanh::lean_inc(v_goal_3136_);
                v___f_3200_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___boxed
                        as *mut core::ffi::c_void,
                    10,
                    2,
                );
                leanh::lean_closure_set(v___f_3200_, 0, v_name_3194_);
                leanh::lean_closure_set(v___f_3200_, 1, v_goal_3136_);
                v___f_3201_ = leanh::lean_obj_once(
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
                v___x_3205_ = leanh::lean_obj_once(
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
                    v___x_3293_ = (leanh::lean_unbox(v___x_3292_) as u8);
                    leanh::lean_dec(v___x_3292_);
                    if v___x_3293_ == 0 {
                        leanh::lean_dec_ref(v___f_3200_);
                        leanh::lean_del_object(v___x_3197_);
                        leanh::lean_dec_ref(v___x_3185_);
                        leanh::lean_inc(v_a_3142_);
                        leanh::lean_inc_ref(v_a_3141_);
                        leanh::lean_inc(v_a_3140_);
                        leanh::lean_inc_ref(v_a_3139_);
                        leanh::lean_inc(v_a_3138_);
                        leanh::lean_inc_ref(v_a_3137_);
                        v___x_3294_ = leanh::lean_apply_8(
                            v_run_x27_3195_,
                            v_goal_3136_,
                            v_a_3137_,
                            v_a_3138_,
                            v_a_3139_,
                            v_a_3140_,
                            v_a_3141_,
                            v_a_3142_,
                            leanh::lean_box(0),
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
                v___x_3213_ = leanh::lean_float_once(
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
                v___x_3217_ = leanh::lean_box_float(v___x_3214_);
                v___x_3218_ = leanh::lean_box_float(v___x_3216_);
                if v_isShared_3198_ == 0 {
                    leanh::lean_ctor_set(v___x_3197_, 1, v___x_3218_);
                    leanh::lean_ctor_set(v___x_3197_, 0, v___x_3217_);
                    v___x_3220_ = v___x_3197_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3224_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3217_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3224_, 1, v___x_3218_);
                    v___x_3220_ = v_reuseFailAlloc_3224_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3221_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3221_, 0, v_a_3210_);
                leanh::lean_ctor_set(v___x_3221_, 1, v___x_3220_);
                leanh::lean_inc_ref(v_toMonadRef_3188_);
                v___x_9546__overap_3222_ =
                    l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_3185_,
                        v___x_3186_,
                        v_toMonadRef_3188_,
                        v___f_3201_,
                        leanh::lean_box(0),
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
                leanh::lean_inc(v_a_3142_);
                leanh::lean_inc_ref(v_a_3141_);
                leanh::lean_inc(v_a_3140_);
                leanh::lean_inc_ref(v_a_3139_);
                leanh::lean_inc(v_a_3138_);
                leanh::lean_inc_ref(v_a_3137_);
                v___x_3223_ = leanh::lean_apply_7(
                    v___x_9546__overap_3222_,
                    v_a_3137_,
                    v_a_3138_,
                    v_a_3139_,
                    v_a_3140_,
                    v_a_3141_,
                    v_a_3142_,
                    leanh::lean_box(0),
                );
                return v___x_3223_;
            }
            8 => {
                v___x_3229_ = lean_io_get_num_heartbeats();
                v___x_3230_ = lean_float_of_nat(v___y_3226_);
                v___x_3231_ = lean_float_of_nat(v___x_3229_);
                v___x_3232_ = leanh::lean_box_float(v___x_3230_);
                v___x_3233_ = leanh::lean_box_float(v___x_3231_);
                v___x_3234_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3234_, 0, v___x_3232_);
                leanh::lean_ctor_set(v___x_3234_, 1, v___x_3233_);
                v___x_3235_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3235_, 0, v_a_3228_);
                leanh::lean_ctor_set(v___x_3235_, 1, v___x_3234_);
                leanh::lean_inc_ref(v_toMonadRef_3188_);
                v___x_9567__overap_3236_ =
                    l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_3185_,
                        v___x_3186_,
                        v_toMonadRef_3188_,
                        v___f_3201_,
                        leanh::lean_box(0),
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
                leanh::lean_inc(v_a_3142_);
                leanh::lean_inc_ref(v_a_3141_);
                leanh::lean_inc(v_a_3140_);
                leanh::lean_inc_ref(v_a_3139_);
                leanh::lean_inc(v_a_3138_);
                leanh::lean_inc_ref(v_a_3137_);
                v___x_3237_ = leanh::lean_apply_7(
                    v___x_9567__overap_3236_,
                    v_a_3137_,
                    v_a_3138_,
                    v_a_3139_,
                    v_a_3140_,
                    v_a_3141_,
                    v_a_3142_,
                    leanh::lean_box(0),
                );
                return v___x_3237_;
            }
            9 => {
                leanh::lean_inc_ref(v___x_3185_);
                v___x_9523__overap_3239_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(
                    leanh::lean_box(0),
                    v___x_3185_,
                    v___x_3186_,
                );
                leanh::lean_inc(v_a_3142_);
                leanh::lean_inc_ref(v_a_3141_);
                leanh::lean_inc(v_a_3140_);
                leanh::lean_inc_ref(v_a_3139_);
                leanh::lean_inc(v_a_3138_);
                leanh::lean_inc_ref(v_a_3137_);
                v___x_3240_ = leanh::lean_apply_7(
                    v___x_9523__overap_3239_,
                    v_a_3137_,
                    v_a_3138_,
                    v_a_3139_,
                    v_a_3140_,
                    v_a_3141_,
                    v_a_3142_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_3240_) == 0 {
                    v_a_3241_ = leanh::lean_ctor_get(v___x_3240_, 0);
                    leanh::lean_inc(v_a_3241_);
                    leanh::lean_dec_ref_known(v___x_3240_, 1);
                    v___x_3242_ = l_Lean_KVMap_instValueBool;
                    v___x_3243_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_3244_ =
                        l_Lean_Option_get___redArg(v___x_3242_, v_options_3190_, v___x_3243_);
                    v___x_3245_ = (leanh::lean_unbox(v___x_3244_) as u8);
                    leanh::lean_dec(v___x_3244_);
                    if v___x_3245_ == 0 {
                        v___x_3246_ = lean_io_mono_nanos_now();
                        leanh::lean_inc(v_a_3142_);
                        leanh::lean_inc_ref(v_a_3141_);
                        leanh::lean_inc(v_a_3140_);
                        leanh::lean_inc_ref(v_a_3139_);
                        leanh::lean_inc(v_a_3138_);
                        leanh::lean_inc_ref(v_a_3137_);
                        v___x_3247_ = leanh::lean_apply_8(
                            v_run_x27_3195_,
                            v_goal_3136_,
                            v_a_3137_,
                            v_a_3138_,
                            v_a_3139_,
                            v_a_3140_,
                            v_a_3141_,
                            v_a_3142_,
                            leanh::lean_box(0),
                        );
                        if leanh::lean_obj_tag(v___x_3247_) == 0 {
                            v_a_3248_ = leanh::lean_ctor_get(v___x_3247_, 0);
                            v_isSharedCheck_3255_ =
                                (!leanh::lean_is_exclusive(v___x_3247_)) as u8;
                            if v_isSharedCheck_3255_ == 0 {
                                v___x_3250_ = v___x_3247_;
                                v_isShared_3251_ = v_isSharedCheck_3255_;
                                state = 10;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3248_);
                                leanh::lean_dec(v___x_3247_);
                                v___x_3250_ = leanh::lean_box(0);
                                v_isShared_3251_ = v_isSharedCheck_3255_;
                                state = 10;
                                continue;
                            }
                        } else {
                            v_a_3256_ = leanh::lean_ctor_get(v___x_3247_, 0);
                            v_isSharedCheck_3263_ =
                                (!leanh::lean_is_exclusive(v___x_3247_)) as u8;
                            if v_isSharedCheck_3263_ == 0 {
                                v___x_3258_ = v___x_3247_;
                                v_isShared_3259_ = v_isSharedCheck_3263_;
                                state = 12;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3256_);
                                leanh::lean_dec(v___x_3247_);
                                v___x_3258_ = leanh::lean_box(0);
                                v_isShared_3259_ = v_isSharedCheck_3263_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_del_object(v___x_3197_);
                        v___x_3264_ = lean_io_get_num_heartbeats();
                        leanh::lean_inc(v_a_3142_);
                        leanh::lean_inc_ref(v_a_3141_);
                        leanh::lean_inc(v_a_3140_);
                        leanh::lean_inc_ref(v_a_3139_);
                        leanh::lean_inc(v_a_3138_);
                        leanh::lean_inc_ref(v_a_3137_);
                        v___x_3265_ = leanh::lean_apply_8(
                            v_run_x27_3195_,
                            v_goal_3136_,
                            v_a_3137_,
                            v_a_3138_,
                            v_a_3139_,
                            v_a_3140_,
                            v_a_3141_,
                            v_a_3142_,
                            leanh::lean_box(0),
                        );
                        if leanh::lean_obj_tag(v___x_3265_) == 0 {
                            v_a_3266_ = leanh::lean_ctor_get(v___x_3265_, 0);
                            v_isSharedCheck_3273_ =
                                (!leanh::lean_is_exclusive(v___x_3265_)) as u8;
                            if v_isSharedCheck_3273_ == 0 {
                                v___x_3268_ = v___x_3265_;
                                v_isShared_3269_ = v_isSharedCheck_3273_;
                                state = 14;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3266_);
                                leanh::lean_dec(v___x_3265_);
                                v___x_3268_ = leanh::lean_box(0);
                                v_isShared_3269_ = v_isSharedCheck_3273_;
                                state = 14;
                                continue;
                            }
                        } else {
                            v_a_3274_ = leanh::lean_ctor_get(v___x_3265_, 0);
                            v_isSharedCheck_3281_ =
                                (!leanh::lean_is_exclusive(v___x_3265_)) as u8;
                            if v_isSharedCheck_3281_ == 0 {
                                v___x_3276_ = v___x_3265_;
                                v_isShared_3277_ = v_isSharedCheck_3281_;
                                state = 16;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3274_);
                                leanh::lean_dec(v___x_3265_);
                                v___x_3276_ = leanh::lean_box(0);
                                v_isShared_3277_ = v_isSharedCheck_3281_;
                                state = 16;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___f_3200_);
                    leanh::lean_del_object(v___x_3197_);
                    leanh::lean_dec_ref(v_run_x27_3195_);
                    leanh::lean_dec_ref(v___x_3185_);
                    leanh::lean_dec(v_goal_3136_);
                    v_a_3282_ = leanh::lean_ctor_get(v___x_3240_, 0);
                    v_isSharedCheck_3289_ = (!leanh::lean_is_exclusive(v___x_3240_)) as u8;
                    if v_isSharedCheck_3289_ == 0 {
                        v___x_3284_ = v___x_3240_;
                        v_isShared_3285_ = v_isSharedCheck_3289_;
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3282_);
                        leanh::lean_dec(v___x_3240_);
                        v___x_3284_ = leanh::lean_box(0);
                        v_isShared_3285_ = v_isSharedCheck_3289_;
                        state = 18;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_3251_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3250_, 1);
                    v___x_3253_ = v___x_3250_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3254_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
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
                    leanh::lean_ctor_set_tag(v___x_3258_, 0);
                    v___x_3261_ = v___x_3258_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3262_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3256_);
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
                    leanh::lean_ctor_set_tag(v___x_3268_, 1);
                    v___x_3271_ = v___x_3268_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3272_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3266_);
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
                    leanh::lean_ctor_set_tag(v___x_3276_, 0);
                    v___x_3279_ = v___x_3276_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3280_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3274_);
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
                    v_reuseFailAlloc_3288_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_a_3282_);
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
    mut v_pass_3302_: *mut leanh::LeanObject,
    mut v_goal_3303_: *mut leanh::LeanObject,
    mut v_a_3304_: *mut leanh::LeanObject,
    mut v_a_3305_: *mut leanh::LeanObject,
    mut v_a_3306_: *mut leanh::LeanObject,
    mut v_a_3307_: *mut leanh::LeanObject,
    mut v_a_3308_: *mut leanh::LeanObject,
    mut v_a_3309_: *mut leanh::LeanObject,
    mut v_a_3310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_3309_);
    leanh::lean_dec_ref(v_a_3308_);
    leanh::lean_dec(v_a_3307_);
    leanh::lean_dec_ref(v_a_3306_);
    leanh::lean_dec(v_a_3305_);
    leanh::lean_dec_ref(v_a_3304_);
    return v_res_3311_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3312_ = leanh::lean_unsigned_to_nat(32);
    v___x_3313_ = lean_mk_empty_array_with_capacity(v___x_3312_);
    v___x_3314_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3314_, 0, v___x_3313_);
    return v___x_3314_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3315_: usize = 0;
    let mut v___x_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3315_ = 5usize;
    v___x_3316_ = leanh::lean_unsigned_to_nat(0);
    v___x_3317_ = leanh::lean_unsigned_to_nat(32);
    v___x_3318_ = lean_mk_empty_array_with_capacity(v___x_3317_);
    v___x_3319_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__0_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__0);
    v___x_3320_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_3320_, 0, v___x_3319_);
    leanh::lean_ctor_set(v___x_3320_, 1, v___x_3318_);
    leanh::lean_ctor_set(v___x_3320_, 2, v___x_3316_);
    leanh::lean_ctor_set(v___x_3320_, 3, v___x_3316_);
    leanh::lean_ctor_set_usize(v___x_3320_, 4, v___x_3315_);
    return v___x_3320_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg(
    mut v___y_3321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3338_: u8 = 0;
    let mut v_tid_3339_: u64 = 0;
    let mut v___x_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3342_: u8 = 0;
    let mut v___x_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3352_: u8 = 0;
    let mut v_unused_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3354_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3323_ = lean_st_ref_get(v___y_3321_);
                v_traceState_3324_ = leanh::lean_ctor_get(v___x_3323_, 4);
                leanh::lean_inc_ref(v_traceState_3324_);
                leanh::lean_dec(v___x_3323_);
                v_traces_3325_ = leanh::lean_ctor_get(v_traceState_3324_, 0);
                leanh::lean_inc_ref(v_traces_3325_);
                leanh::lean_dec_ref(v_traceState_3324_);
                v___x_3326_ = lean_st_ref_take(v___y_3321_);
                v_traceState_3327_ = leanh::lean_ctor_get(v___x_3326_, 4);
                v_env_3328_ = leanh::lean_ctor_get(v___x_3326_, 0);
                v_nextMacroScope_3329_ = leanh::lean_ctor_get(v___x_3326_, 1);
                v_ngen_3330_ = leanh::lean_ctor_get(v___x_3326_, 2);
                v_auxDeclNGen_3331_ = leanh::lean_ctor_get(v___x_3326_, 3);
                v_cache_3332_ = leanh::lean_ctor_get(v___x_3326_, 5);
                v_messages_3333_ = leanh::lean_ctor_get(v___x_3326_, 6);
                v_infoState_3334_ = leanh::lean_ctor_get(v___x_3326_, 7);
                v_snapshotTasks_3335_ = leanh::lean_ctor_get(v___x_3326_, 8);
                v_isSharedCheck_3354_ = (!leanh::lean_is_exclusive(v___x_3326_)) as u8;
                if v_isSharedCheck_3354_ == 0 {
                    v___x_3337_ = v___x_3326_;
                    v_isShared_3338_ = v_isSharedCheck_3354_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3335_);
                    leanh::lean_inc(v_infoState_3334_);
                    leanh::lean_inc(v_messages_3333_);
                    leanh::lean_inc(v_cache_3332_);
                    leanh::lean_inc(v_traceState_3327_);
                    leanh::lean_inc(v_auxDeclNGen_3331_);
                    leanh::lean_inc(v_ngen_3330_);
                    leanh::lean_inc(v_nextMacroScope_3329_);
                    leanh::lean_inc(v_env_3328_);
                    leanh::lean_dec(v___x_3326_);
                    v___x_3337_ = leanh::lean_box(0);
                    v_isShared_3338_ = v_isSharedCheck_3354_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_tid_3339_ = leanh::lean_ctor_get_uint64(
                    v_traceState_3327_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3352_ =
                    (!leanh::lean_is_exclusive(v_traceState_3327_)) as u8;
                if v_isSharedCheck_3352_ == 0 {
                    v_unused_3353_ = leanh::lean_ctor_get(v_traceState_3327_, 0);
                    leanh::lean_dec(v_unused_3353_);
                    v___x_3341_ = v_traceState_3327_;
                    v_isShared_3342_ = v_isSharedCheck_3352_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_traceState_3327_);
                    v___x_3341_ = leanh::lean_box(0);
                    v_isShared_3342_ = v_isSharedCheck_3352_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3343_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___closed__1);
                if v_isShared_3342_ == 0 {
                    leanh::lean_ctor_set(v___x_3341_, 0, v___x_3343_);
                    v___x_3345_ = v___x_3341_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3351_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3351_, 0, v___x_3343_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3351_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_3339_,
                    );
                    v___x_3345_ = v_reuseFailAlloc_3351_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3338_ == 0 {
                    leanh::lean_ctor_set(v___x_3337_, 4, v___x_3345_);
                    v___x_3347_ = v___x_3337_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3350_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_env_3328_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3350_, 1, v_nextMacroScope_3329_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3350_, 2, v_ngen_3330_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3350_, 3, v_auxDeclNGen_3331_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3350_, 4, v___x_3345_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3350_, 5, v_cache_3332_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3350_, 6, v_messages_3333_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3350_, 7, v_infoState_3334_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3350_, 8, v_snapshotTasks_3335_);
                    v___x_3347_ = v_reuseFailAlloc_3350_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3348_ = lean_st_ref_set(v___y_3321_, v___x_3347_);
                v___x_3349_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3349_, 0, v_traces_3325_);
                return v___x_3349_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg___boxed(
    mut v___y_3355_: *mut leanh::LeanObject,
    mut v___y_3356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3357_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg(v___y_3355_);
    leanh::lean_dec(v___y_3355_);
    return v_res_3357_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1(
    mut v___y_3358_: *mut leanh::LeanObject,
    mut v___y_3359_: *mut leanh::LeanObject,
    mut v___y_3360_: *mut leanh::LeanObject,
    mut v___y_3361_: *mut leanh::LeanObject,
    mut v___y_3362_: *mut leanh::LeanObject,
    mut v___y_3363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3365_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg(v___y_3363_);
    return v___x_3365_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___boxed(
    mut v___y_3366_: *mut leanh::LeanObject,
    mut v___y_3367_: *mut leanh::LeanObject,
    mut v___y_3368_: *mut leanh::LeanObject,
    mut v___y_3369_: *mut leanh::LeanObject,
    mut v___y_3370_: *mut leanh::LeanObject,
    mut v___y_3371_: *mut leanh::LeanObject,
    mut v___y_3372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3373_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1(v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
    leanh::lean_dec(v___y_3371_);
    leanh::lean_dec_ref(v___y_3370_);
    leanh::lean_dec(v___y_3369_);
    leanh::lean_dec_ref(v___y_3368_);
    leanh::lean_dec(v___y_3367_);
    leanh::lean_dec_ref(v___y_3366_);
    return v_res_3373_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__2(
    mut v_opts_3374_: *mut leanh::LeanObject,
    mut v_opt_3375_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_3376_ = leanh::lean_ctor_get(v_opt_3375_, 0);
    v_defValue_3377_ = leanh::lean_ctor_get(v_opt_3375_, 1);
    v_map_3378_ = leanh::lean_ctor_get(v_opts_3374_, 0);
    v___x_3379_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3378_,
            v_name_3376_,
        );
    if leanh::lean_obj_tag(v___x_3379_) == 0 {
        let mut v___x_3380_: u8 = 0;
        v___x_3380_ = (leanh::lean_unbox(v_defValue_3377_) as u8);
        return v___x_3380_;
    } else {
        let mut v_val_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3381_ = leanh::lean_ctor_get(v___x_3379_, 0);
        leanh::lean_inc(v_val_3381_);
        leanh::lean_dec_ref_known(v___x_3379_, 1);
        if leanh::lean_obj_tag(v_val_3381_) == 1 {
            let mut v_v_3382_: u8 = 0;
            v_v_3382_ = leanh::lean_ctor_get_uint8(v_val_3381_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_3381_, 0);
            return v_v_3382_;
        } else {
            let mut v___x_3383_: u8 = 0;
            leanh::lean_dec(v_val_3381_);
            v___x_3383_ = (leanh::lean_unbox(v_defValue_3377_) as u8);
            return v___x_3383_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__2___boxed(
    mut v_opts_3384_: *mut leanh::LeanObject,
    mut v_opt_3385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3386_: u8 = 0;
    let mut v_r_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3386_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__2(v_opts_3384_, v_opt_3385_);
    leanh::lean_dec_ref(v_opt_3385_);
    leanh::lean_dec_ref(v_opts_3384_);
    v_r_3387_ = leanh::lean_box((v_res_3386_) as usize);
    return v_r_3387_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___lam__0(
    mut v_name_3388_: *mut leanh::LeanObject,
    mut v_snd_3389_: *mut leanh::LeanObject,
    mut v_x_3390_: *mut leanh::LeanObject,
    mut v___y_3391_: *mut leanh::LeanObject,
    mut v___y_3392_: *mut leanh::LeanObject,
    mut v___y_3393_: *mut leanh::LeanObject,
    mut v___y_3394_: *mut leanh::LeanObject,
    mut v___y_3395_: *mut leanh::LeanObject,
    mut v___y_3396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3398_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__1,
    );
    v___x_3399_ = l_Lean_MessageData_ofName(v_name_3388_);
    v___x_3400_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3400_, 0, v___x_3398_);
    leanh::lean_ctor_set(v___x_3400_, 1, v___x_3399_);
    v___x_3401_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__3_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___lam__0___closed__3,
    );
    v___x_3402_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3402_, 0, v___x_3400_);
    leanh::lean_ctor_set(v___x_3402_, 1, v___x_3401_);
    v___x_3403_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3403_, 0, v_snd_3389_);
    v___x_3404_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3404_, 0, v___x_3402_);
    leanh::lean_ctor_set(v___x_3404_, 1, v___x_3403_);
    v___x_3405_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3405_, 0, v___x_3404_);
    return v___x_3405_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___lam__0___boxed(
    mut v_name_3406_: *mut leanh::LeanObject,
    mut v_snd_3407_: *mut leanh::LeanObject,
    mut v_x_3408_: *mut leanh::LeanObject,
    mut v___y_3409_: *mut leanh::LeanObject,
    mut v___y_3410_: *mut leanh::LeanObject,
    mut v___y_3411_: *mut leanh::LeanObject,
    mut v___y_3412_: *mut leanh::LeanObject,
    mut v___y_3413_: *mut leanh::LeanObject,
    mut v___y_3414_: *mut leanh::LeanObject,
    mut v___y_3415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3416_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___lam__0(v_name_3406_, v_snd_3407_, v_x_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_);
    leanh::lean_dec(v___y_3414_);
    leanh::lean_dec_ref(v___y_3413_);
    leanh::lean_dec(v___y_3412_);
    leanh::lean_dec_ref(v___y_3411_);
    leanh::lean_dec(v___y_3410_);
    leanh::lean_dec_ref(v___y_3409_);
    leanh::lean_dec_ref(v_x_3408_);
    return v_res_3416_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__7(
    mut v_opts_3417_: *mut leanh::LeanObject,
    mut v_opt_3418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_3419_ = leanh::lean_ctor_get(v_opt_3418_, 0);
    v_defValue_3420_ = leanh::lean_ctor_get(v_opt_3418_, 1);
    v_map_3421_ = leanh::lean_ctor_get(v_opts_3417_, 0);
    v___x_3422_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3421_,
            v_name_3419_,
        );
    if leanh::lean_obj_tag(v___x_3422_) == 0 {
        leanh::lean_inc(v_defValue_3420_);
        return v_defValue_3420_;
    } else {
        let mut v_val_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3423_ = leanh::lean_ctor_get(v___x_3422_, 0);
        leanh::lean_inc(v_val_3423_);
        leanh::lean_dec_ref_known(v___x_3422_, 1);
        if leanh::lean_obj_tag(v_val_3423_) == 3 {
            let mut v_v_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_3424_ = leanh::lean_ctor_get(v_val_3423_, 0);
            leanh::lean_inc(v_v_3424_);
            leanh::lean_dec_ref_known(v_val_3423_, 1);
            return v_v_3424_;
        } else {
            leanh::lean_dec(v_val_3423_);
            leanh::lean_inc(v_defValue_3420_);
            return v_defValue_3420_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__7___boxed(
    mut v_opts_3425_: *mut leanh::LeanObject,
    mut v_opt_3426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3427_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__7(v_opts_3425_, v_opt_3426_);
    leanh::lean_dec_ref(v_opt_3426_);
    leanh::lean_dec_ref(v_opts_3425_);
    return v_res_3427_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__6___redArg(
    mut v_x_3428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3433_: u8 = 0;
    let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3437_: u8 = 0;
    let mut v_a_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3441_: u8 = 0;
    let mut v___x_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3445_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3428_) == 0 {
                    v_a_3430_ = leanh::lean_ctor_get(v_x_3428_, 0);
                    v_isSharedCheck_3437_ = (!leanh::lean_is_exclusive(v_x_3428_)) as u8;
                    if v_isSharedCheck_3437_ == 0 {
                        v___x_3432_ = v_x_3428_;
                        v_isShared_3433_ = v_isSharedCheck_3437_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3430_);
                        leanh::lean_dec(v_x_3428_);
                        v___x_3432_ = leanh::lean_box(0);
                        v_isShared_3433_ = v_isSharedCheck_3437_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3438_ = leanh::lean_ctor_get(v_x_3428_, 0);
                    v_isSharedCheck_3445_ = (!leanh::lean_is_exclusive(v_x_3428_)) as u8;
                    if v_isSharedCheck_3445_ == 0 {
                        v___x_3440_ = v_x_3428_;
                        v_isShared_3441_ = v_isSharedCheck_3445_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3438_);
                        leanh::lean_dec(v_x_3428_);
                        v___x_3440_ = leanh::lean_box(0);
                        v_isShared_3441_ = v_isSharedCheck_3445_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3433_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3432_, 1);
                    v___x_3435_ = v___x_3432_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3436_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_a_3430_);
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
                    leanh::lean_ctor_set_tag(v___x_3440_, 0);
                    v___x_3443_ = v___x_3440_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3444_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3438_);
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
    mut v_x_3446_: *mut leanh::LeanObject,
    mut v___y_3447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3448_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__6___redArg(v_x_3446_);
    return v_res_3448_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0_spec__0(
    mut v_msgData_3449_: *mut leanh::LeanObject,
    mut v___y_3450_: *mut leanh::LeanObject,
    mut v___y_3451_: *mut leanh::LeanObject,
    mut v___y_3452_: *mut leanh::LeanObject,
    mut v___y_3453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3455_ = lean_st_ref_get(v___y_3453_);
    v_env_3456_ = leanh::lean_ctor_get(v___x_3455_, 0);
    leanh::lean_inc_ref(v_env_3456_);
    leanh::lean_dec(v___x_3455_);
    v___x_3457_ = lean_st_ref_get(v___y_3451_);
    v_mctx_3458_ = leanh::lean_ctor_get(v___x_3457_, 0);
    leanh::lean_inc_ref(v_mctx_3458_);
    leanh::lean_dec(v___x_3457_);
    v_lctx_3459_ = leanh::lean_ctor_get(v___y_3450_, 2);
    v_options_3460_ = leanh::lean_ctor_get(v___y_3452_, 2);
    leanh::lean_inc_ref(v_options_3460_);
    leanh::lean_inc_ref(v_lctx_3459_);
    v___x_3461_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3461_, 0, v_env_3456_);
    leanh::lean_ctor_set(v___x_3461_, 1, v_mctx_3458_);
    leanh::lean_ctor_set(v___x_3461_, 2, v_lctx_3459_);
    leanh::lean_ctor_set(v___x_3461_, 3, v_options_3460_);
    v___x_3462_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3462_, 0, v___x_3461_);
    leanh::lean_ctor_set(v___x_3462_, 1, v_msgData_3449_);
    v___x_3463_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3463_, 0, v___x_3462_);
    return v___x_3463_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0_spec__0___boxed(
    mut v_msgData_3464_: *mut leanh::LeanObject,
    mut v___y_3465_: *mut leanh::LeanObject,
    mut v___y_3466_: *mut leanh::LeanObject,
    mut v___y_3467_: *mut leanh::LeanObject,
    mut v___y_3468_: *mut leanh::LeanObject,
    mut v___y_3469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3470_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0_spec__0(v_msgData_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
    leanh::lean_dec(v___y_3468_);
    leanh::lean_dec_ref(v___y_3467_);
    leanh::lean_dec(v___y_3466_);
    leanh::lean_dec_ref(v___y_3465_);
    return v_res_3470_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5_spec__6(
    mut v_sz_3471_: usize,
    mut v_i_3472_: usize,
    mut v_bs_3473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3474_: u8 = 0;
    let mut v_v_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: usize = 0;
    let mut v___x_3480_: usize = 0;
    let mut v___x_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3474_ = lean_usize_dec_lt(v_i_3472_, v_sz_3471_);
                if v___x_3474_ == 0 {
                    return v_bs_3473_;
                } else {
                    v_v_3475_ = lean_array_uget_borrowed(v_bs_3473_, v_i_3472_);
                    v_msg_3476_ = leanh::lean_ctor_get(v_v_3475_, 1);
                    leanh::lean_inc_ref(v_msg_3476_);
                    v___x_3477_ = leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_3483_: *mut leanh::LeanObject,
    mut v_i_3484_: *mut leanh::LeanObject,
    mut v_bs_3485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3486_: usize = 0;
    let mut v_i_boxed_3487_: usize = 0;
    let mut v_res_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3486_ = leanh::lean_unbox_usize(v_sz_3483_);
    leanh::lean_dec(v_sz_3483_);
    v_i_boxed_3487_ = leanh::lean_unbox_usize(v_i_3484_);
    leanh::lean_dec(v_i_3484_);
    v_res_3488_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5_spec__6(v_sz_boxed_3486_, v_i_boxed_3487_, v_bs_3485_);
    return v_res_3488_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5___redArg(
    mut v_oldTraces_3489_: *mut leanh::LeanObject,
    mut v_data_3490_: *mut leanh::LeanObject,
    mut v_ref_3491_: *mut leanh::LeanObject,
    mut v_msg_3492_: *mut leanh::LeanObject,
    mut v___y_3493_: *mut leanh::LeanObject,
    mut v___y_3494_: *mut leanh::LeanObject,
    mut v___y_3495_: *mut leanh::LeanObject,
    mut v___y_3496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3510_: u8 = 0;
    let mut v_cancelTk_x3f_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3512_: u8 = 0;
    let mut v_inheritedTraceOptions_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3520_: usize = 0;
    let mut v___x_3521_: usize = 0;
    let mut v___x_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3528_: u8 = 0;
    let mut v___x_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3541_: u8 = 0;
    let mut v_tid_3542_: u64 = 0;
    let mut v___x_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3545_: u8 = 0;
    let mut v___x_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3559_: u8 = 0;
    let mut v_unused_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3561_: u8 = 0;
    let mut v_isSharedCheck_3562_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_3498_ = leanh::lean_ctor_get(v___y_3495_, 0);
                v_fileMap_3499_ = leanh::lean_ctor_get(v___y_3495_, 1);
                v_options_3500_ = leanh::lean_ctor_get(v___y_3495_, 2);
                v_currRecDepth_3501_ = leanh::lean_ctor_get(v___y_3495_, 3);
                v_maxRecDepth_3502_ = leanh::lean_ctor_get(v___y_3495_, 4);
                v_ref_3503_ = leanh::lean_ctor_get(v___y_3495_, 5);
                v_currNamespace_3504_ = leanh::lean_ctor_get(v___y_3495_, 6);
                v_openDecls_3505_ = leanh::lean_ctor_get(v___y_3495_, 7);
                v_initHeartbeats_3506_ = leanh::lean_ctor_get(v___y_3495_, 8);
                v_maxHeartbeats_3507_ = leanh::lean_ctor_get(v___y_3495_, 9);
                v_quotContext_3508_ = leanh::lean_ctor_get(v___y_3495_, 10);
                v_currMacroScope_3509_ = leanh::lean_ctor_get(v___y_3495_, 11);
                v_diag_3510_ = leanh::lean_ctor_get_uint8(
                    v___y_3495_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_3511_ = leanh::lean_ctor_get(v___y_3495_, 12);
                v_suppressElabErrors_3512_ = leanh::lean_ctor_get_uint8(
                    v___y_3495_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_3513_ = leanh::lean_ctor_get(v___y_3495_, 13);
                v___x_3514_ = lean_st_ref_get(v___y_3496_);
                v_traceState_3515_ = leanh::lean_ctor_get(v___x_3514_, 4);
                leanh::lean_inc_ref(v_traceState_3515_);
                leanh::lean_dec(v___x_3514_);
                v_traces_3516_ = leanh::lean_ctor_get(v_traceState_3515_, 0);
                leanh::lean_inc_ref(v_traces_3516_);
                leanh::lean_dec_ref(v_traceState_3515_);
                v_ref_3517_ = l_Lean_replaceRef(v_ref_3491_, v_ref_3503_);
                leanh::lean_inc_ref(v_inheritedTraceOptions_3513_);
                leanh::lean_inc(v_cancelTk_x3f_3511_);
                leanh::lean_inc(v_currMacroScope_3509_);
                leanh::lean_inc(v_quotContext_3508_);
                leanh::lean_inc(v_maxHeartbeats_3507_);
                leanh::lean_inc(v_initHeartbeats_3506_);
                leanh::lean_inc(v_openDecls_3505_);
                leanh::lean_inc(v_currNamespace_3504_);
                leanh::lean_inc(v_maxRecDepth_3502_);
                leanh::lean_inc(v_currRecDepth_3501_);
                leanh::lean_inc_ref(v_options_3500_);
                leanh::lean_inc_ref(v_fileMap_3499_);
                leanh::lean_inc_ref(v_fileName_3498_);
                v___x_3518_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_3518_, 0, v_fileName_3498_);
                leanh::lean_ctor_set(v___x_3518_, 1, v_fileMap_3499_);
                leanh::lean_ctor_set(v___x_3518_, 2, v_options_3500_);
                leanh::lean_ctor_set(v___x_3518_, 3, v_currRecDepth_3501_);
                leanh::lean_ctor_set(v___x_3518_, 4, v_maxRecDepth_3502_);
                leanh::lean_ctor_set(v___x_3518_, 5, v_ref_3517_);
                leanh::lean_ctor_set(v___x_3518_, 6, v_currNamespace_3504_);
                leanh::lean_ctor_set(v___x_3518_, 7, v_openDecls_3505_);
                leanh::lean_ctor_set(v___x_3518_, 8, v_initHeartbeats_3506_);
                leanh::lean_ctor_set(v___x_3518_, 9, v_maxHeartbeats_3507_);
                leanh::lean_ctor_set(v___x_3518_, 10, v_quotContext_3508_);
                leanh::lean_ctor_set(v___x_3518_, 11, v_currMacroScope_3509_);
                leanh::lean_ctor_set(v___x_3518_, 12, v_cancelTk_x3f_3511_);
                leanh::lean_ctor_set(v___x_3518_, 13, v_inheritedTraceOptions_3513_);
                leanh::lean_ctor_set_uint8(
                    v___x_3518_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v_diag_3510_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3518_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_3512_,
                );
                v___x_3519_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3516_);
                leanh::lean_dec_ref(v_traces_3516_);
                v_sz_3520_ = lean_array_size(v___x_3519_);
                v___x_3521_ = 0usize;
                v___x_3522_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5_spec__6(v_sz_3520_, v___x_3521_, v___x_3519_);
                v_msg_3523_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v_msg_3523_, 0, v_data_3490_);
                leanh::lean_ctor_set(v_msg_3523_, 1, v_msg_3492_);
                leanh::lean_ctor_set(v_msg_3523_, 2, v___x_3522_);
                v___x_3524_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0_spec__0(v_msg_3523_, v___y_3493_, v___y_3494_, v___x_3518_, v___y_3496_);
                leanh::lean_dec_ref_known(v___x_3518_, 14);
                v_a_3525_ = leanh::lean_ctor_get(v___x_3524_, 0);
                v_isSharedCheck_3562_ = (!leanh::lean_is_exclusive(v___x_3524_)) as u8;
                if v_isSharedCheck_3562_ == 0 {
                    v___x_3527_ = v___x_3524_;
                    v_isShared_3528_ = v_isSharedCheck_3562_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3525_);
                    leanh::lean_dec(v___x_3524_);
                    v___x_3527_ = leanh::lean_box(0);
                    v_isShared_3528_ = v_isSharedCheck_3562_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3529_ = lean_st_ref_take(v___y_3496_);
                v_traceState_3530_ = leanh::lean_ctor_get(v___x_3529_, 4);
                v_env_3531_ = leanh::lean_ctor_get(v___x_3529_, 0);
                v_nextMacroScope_3532_ = leanh::lean_ctor_get(v___x_3529_, 1);
                v_ngen_3533_ = leanh::lean_ctor_get(v___x_3529_, 2);
                v_auxDeclNGen_3534_ = leanh::lean_ctor_get(v___x_3529_, 3);
                v_cache_3535_ = leanh::lean_ctor_get(v___x_3529_, 5);
                v_messages_3536_ = leanh::lean_ctor_get(v___x_3529_, 6);
                v_infoState_3537_ = leanh::lean_ctor_get(v___x_3529_, 7);
                v_snapshotTasks_3538_ = leanh::lean_ctor_get(v___x_3529_, 8);
                v_isSharedCheck_3561_ = (!leanh::lean_is_exclusive(v___x_3529_)) as u8;
                if v_isSharedCheck_3561_ == 0 {
                    v___x_3540_ = v___x_3529_;
                    v_isShared_3541_ = v_isSharedCheck_3561_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3538_);
                    leanh::lean_inc(v_infoState_3537_);
                    leanh::lean_inc(v_messages_3536_);
                    leanh::lean_inc(v_cache_3535_);
                    leanh::lean_inc(v_traceState_3530_);
                    leanh::lean_inc(v_auxDeclNGen_3534_);
                    leanh::lean_inc(v_ngen_3533_);
                    leanh::lean_inc(v_nextMacroScope_3532_);
                    leanh::lean_inc(v_env_3531_);
                    leanh::lean_dec(v___x_3529_);
                    v___x_3540_ = leanh::lean_box(0);
                    v_isShared_3541_ = v_isSharedCheck_3561_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3542_ = leanh::lean_ctor_get_uint64(
                    v_traceState_3530_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3559_ =
                    (!leanh::lean_is_exclusive(v_traceState_3530_)) as u8;
                if v_isSharedCheck_3559_ == 0 {
                    v_unused_3560_ = leanh::lean_ctor_get(v_traceState_3530_, 0);
                    leanh::lean_dec(v_unused_3560_);
                    v___x_3544_ = v_traceState_3530_;
                    v_isShared_3545_ = v_isSharedCheck_3559_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v_traceState_3530_);
                    v___x_3544_ = leanh::lean_box(0);
                    v_isShared_3545_ = v_isSharedCheck_3559_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3546_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3546_, 0, v_ref_3491_);
                leanh::lean_ctor_set(v___x_3546_, 1, v_a_3525_);
                v___x_3547_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3489_, v___x_3546_);
                if v_isShared_3545_ == 0 {
                    leanh::lean_ctor_set(v___x_3544_, 0, v___x_3547_);
                    v___x_3549_ = v___x_3544_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3558_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3558_, 0, v___x_3547_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3558_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_3542_,
                    );
                    v___x_3549_ = v_reuseFailAlloc_3558_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3541_ == 0 {
                    leanh::lean_ctor_set(v___x_3540_, 4, v___x_3549_);
                    v___x_3551_ = v___x_3540_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3557_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_env_3531_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3557_, 1, v_nextMacroScope_3532_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3557_, 2, v_ngen_3533_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3557_, 3, v_auxDeclNGen_3534_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3557_, 4, v___x_3549_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3557_, 5, v_cache_3535_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3557_, 6, v_messages_3536_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3557_, 7, v_infoState_3537_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3557_, 8, v_snapshotTasks_3538_);
                    v___x_3551_ = v_reuseFailAlloc_3557_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3552_ = lean_st_ref_set(v___y_3496_, v___x_3551_);
                v___x_3553_ = leanh::lean_box(0);
                if v_isShared_3528_ == 0 {
                    leanh::lean_ctor_set(v___x_3527_, 0, v___x_3553_);
                    v___x_3555_ = v___x_3527_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3556_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3556_, 0, v___x_3553_);
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
    mut v_oldTraces_3563_: *mut leanh::LeanObject,
    mut v_data_3564_: *mut leanh::LeanObject,
    mut v_ref_3565_: *mut leanh::LeanObject,
    mut v_msg_3566_: *mut leanh::LeanObject,
    mut v___y_3567_: *mut leanh::LeanObject,
    mut v___y_3568_: *mut leanh::LeanObject,
    mut v___y_3569_: *mut leanh::LeanObject,
    mut v___y_3570_: *mut leanh::LeanObject,
    mut v___y_3571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3572_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5___redArg(v_oldTraces_3563_, v_data_3564_, v_ref_3565_, v_msg_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_);
    leanh::lean_dec(v___y_3570_);
    leanh::lean_dec_ref(v___y_3569_);
    leanh::lean_dec(v___y_3568_);
    leanh::lean_dec_ref(v___y_3567_);
    return v_res_3572_;
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__4(
    mut v_e_3573_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_e_3573_) == 0 {
        let mut v___x_3574_: u8 = 0;
        v___x_3574_ = 2;
        return v___x_3574_;
    } else {
        let mut v_a_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_3575_ = leanh::lean_ctor_get(v_e_3573_, 0);
        if leanh::lean_obj_tag(v_a_3575_) == 0 {
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
    mut v_e_3578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3579_: u8 = 0;
    let mut v_r_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3579_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__4(v_e_3578_);
    leanh::lean_dec_ref(v_e_3578_);
    v_r_3580_ = leanh::lean_box((v_res_3579_) as usize);
    return v_r_3580_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3582_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__0;
    v___x_3583_ = l_Lean_stringToMessageData(v___x_3582_);
    return v___x_3583_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__2()
-> f64 {
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: f64 = 0.0;
    v___x_3584_ = leanh::lean_unsigned_to_nat(0);
    v___x_3585_ = lean_float_of_nat(v___x_3584_);
    return v___x_3585_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3587_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__3;
    v___x_3588_ = l_Lean_stringToMessageData(v___x_3587_);
    return v___x_3588_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__5()
-> f64 {
    let mut v___x_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: f64 = 0.0;
    v___x_3589_ = leanh::lean_unsigned_to_nat(1000);
    v___x_3590_ = lean_float_of_nat(v___x_3589_);
    return v___x_3590_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3(
    mut v_cls_3591_: *mut leanh::LeanObject,
    mut v_collapsed_3592_: u8,
    mut v_tag_3593_: *mut leanh::LeanObject,
    mut v_opts_3594_: *mut leanh::LeanObject,
    mut v_clsEnabled_3595_: u8,
    mut v_oldTraces_3596_: *mut leanh::LeanObject,
    mut v_msg_3597_: *mut leanh::LeanObject,
    mut v_resStartStop_3598_: *mut leanh::LeanObject,
    mut v___y_3599_: *mut leanh::LeanObject,
    mut v___y_3600_: *mut leanh::LeanObject,
    mut v___y_3601_: *mut leanh::LeanObject,
    mut v___y_3602_: *mut leanh::LeanObject,
    mut v___y_3603_: *mut leanh::LeanObject,
    mut v___y_3604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3610_: u8 = 0;
    let mut v___y_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3620_: u8 = 0;
    let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3624_: u8 = 0;
    let mut v_fst_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3629_: u8 = 0;
    let mut v___x_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: u8 = 0;
    let mut v___y_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_3635_: u8 = 0;
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: f64 = 0.0;
    let mut v_data_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: f64 = 0.0;
    let mut v___x_3649_: f64 = 0.0;
    let mut v_reuseFailAlloc_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3658_: u8 = 0;
    let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3671_: u8 = 0;
    let mut v_tid_3672_: u64 = 0;
    let mut v_traces_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3676_: u8 = 0;
    let mut v___x_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3686_: u8 = 0;
    let mut v_isSharedCheck_3687_: u8 = 0;
    let mut v___y_3689_: f64 = 0.0;
    let mut v___x_3690_: f64 = 0.0;
    let mut v___x_3691_: f64 = 0.0;
    let mut v___x_3692_: f64 = 0.0;
    let mut v___x_3693_: u8 = 0;
    let mut v___x_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: u8 = 0;
    let mut v___x_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: f64 = 0.0;
    let mut v___x_3699_: f64 = 0.0;
    let mut v___x_3700_: f64 = 0.0;
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: f64 = 0.0;
    let mut v_isSharedCheck_3704_: u8 = 0;
    let mut v_isSharedCheck_3705_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3606_ = leanh::lean_ctor_get(v_resStartStop_3598_, 0);
                v_snd_3607_ = leanh::lean_ctor_get(v_resStartStop_3598_, 1);
                v_isSharedCheck_3705_ =
                    (!leanh::lean_is_exclusive(v_resStartStop_3598_)) as u8;
                if v_isSharedCheck_3705_ == 0 {
                    v___x_3609_ = v_resStartStop_3598_;
                    v_isShared_3610_ = v_isSharedCheck_3705_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3607_);
                    leanh::lean_inc(v_fst_3606_);
                    leanh::lean_dec(v_resStartStop_3598_);
                    v___x_3609_ = leanh::lean_box(0);
                    v_isShared_3610_ = v_isSharedCheck_3705_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_3625_ = leanh::lean_ctor_get(v_snd_3607_, 0);
                v_snd_3626_ = leanh::lean_ctor_get(v_snd_3607_, 1);
                v_isSharedCheck_3704_ = (!leanh::lean_is_exclusive(v_snd_3607_)) as u8;
                if v_isSharedCheck_3704_ == 0 {
                    v___x_3628_ = v_snd_3607_;
                    v_isShared_3629_ = v_isSharedCheck_3704_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3626_);
                    leanh::lean_inc(v_fst_3625_);
                    leanh::lean_dec(v_snd_3607_);
                    v___x_3628_ = leanh::lean_box(0);
                    v_isShared_3629_ = v_isSharedCheck_3704_;
                    state = 5;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v___y_3612_);
                v___x_3615_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5___redArg(v_oldTraces_3596_, v_data_3614_, v___y_3612_, v___y_3613_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
                if leanh::lean_obj_tag(v___x_3615_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3615_, 1);
                    v___x_3616_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__6___redArg(v_fst_3606_);
                    return v___x_3616_;
                } else {
                    leanh::lean_dec(v_fst_3606_);
                    v_a_3617_ = leanh::lean_ctor_get(v___x_3615_, 0);
                    v_isSharedCheck_3624_ = (!leanh::lean_is_exclusive(v___x_3615_)) as u8;
                    if v_isSharedCheck_3624_ == 0 {
                        v___x_3619_ = v___x_3615_;
                        v_isShared_3620_ = v_isSharedCheck_3624_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3617_);
                        leanh::lean_dec(v___x_3615_);
                        v___x_3619_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3623_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
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
                        v___x_3699_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__5_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__5);
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
                v___x_3638_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__1);
                if v_isShared_3629_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3628_, 7);
                    leanh::lean_ctor_set(v___x_3628_, 1, v___x_3638_);
                    leanh::lean_ctor_set(v___x_3628_, 0, v___x_3637_);
                    v___x_3640_ = v___x_3628_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3651_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3637_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3651_, 1, v___x_3638_);
                    v___x_3640_ = v_reuseFailAlloc_3651_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3610_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3609_, 7);
                    leanh::lean_ctor_set(v___x_3609_, 1, v_a_3634_);
                    leanh::lean_ctor_set(v___x_3609_, 0, v___x_3640_);
                    v_m_3642_ = v___x_3609_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3650_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___x_3640_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3650_, 1, v_a_3634_);
                    v_m_3642_ = v_reuseFailAlloc_3650_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3643_ = leanh::lean_box((v_result_3635_) as usize);
                v___x_3644_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3644_, 0, v___x_3643_);
                v___x_3645_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__2_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__2);
                leanh::lean_inc_ref(v_tag_3593_);
                leanh::lean_inc_ref(v___x_3644_);
                leanh::lean_inc(v_cls_3591_);
                v_data_3646_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v_data_3646_, 0, v_cls_3591_);
                leanh::lean_ctor_set(v_data_3646_, 1, v___x_3644_);
                leanh::lean_ctor_set(v_data_3646_, 2, v_tag_3593_);
                leanh::lean_ctor_set_float(
                    v_data_3646_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_3645_,
                );
                leanh::lean_ctor_set_float(
                    v_data_3646_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3645_,
                );
                leanh::lean_ctor_set_uint8(
                    v_data_3646_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v_collapsed_3592_,
                );
                if v___x_3631_ == 0 {
                    leanh::lean_dec_ref_known(v___x_3644_, 1);
                    leanh::lean_dec(v_snd_3626_);
                    leanh::lean_dec(v_fst_3625_);
                    leanh::lean_dec_ref(v_tag_3593_);
                    leanh::lean_dec(v_cls_3591_);
                    v___y_3612_ = v___y_3633_;
                    v___y_3613_ = v_m_3642_;
                    v_data_3614_ = v_data_3646_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v_data_3646_, 3);
                    v_data_3647_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                    leanh::lean_ctor_set(v_data_3647_, 0, v_cls_3591_);
                    leanh::lean_ctor_set(v_data_3647_, 1, v___x_3644_);
                    leanh::lean_ctor_set(v_data_3647_, 2, v_tag_3593_);
                    v___x_3648_ = leanh::lean_unbox_float(v_fst_3625_);
                    leanh::lean_dec(v_fst_3625_);
                    leanh::lean_ctor_set_float(
                        v_data_3647_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v___x_3648_,
                    );
                    v___x_3649_ = leanh::lean_unbox_float(v_snd_3626_);
                    leanh::lean_dec(v_snd_3626_);
                    leanh::lean_ctor_set_float(
                        v_data_3647_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                        v___x_3649_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_data_3647_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
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
                v_ref_3653_ = leanh::lean_ctor_get(v___y_3603_, 5);
                leanh::lean_inc(v___y_3604_);
                leanh::lean_inc_ref(v___y_3603_);
                leanh::lean_inc(v___y_3602_);
                leanh::lean_inc_ref(v___y_3601_);
                leanh::lean_inc(v___y_3600_);
                leanh::lean_inc_ref(v___y_3599_);
                leanh::lean_inc(v_fst_3606_);
                v___x_3654_ = leanh::lean_apply_8(
                    v_msg_3597_,
                    v_fst_3606_,
                    v___y_3599_,
                    v___y_3600_,
                    v___y_3601_,
                    v___y_3602_,
                    v___y_3603_,
                    v___y_3604_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_3654_) == 0 {
                    v_a_3655_ = leanh::lean_ctor_get(v___x_3654_, 0);
                    leanh::lean_inc(v_a_3655_);
                    leanh::lean_dec_ref_known(v___x_3654_, 1);
                    v___y_3633_ = v_ref_3653_;
                    v_a_3634_ = v_a_3655_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v___x_3654_, 1);
                    v___x_3656_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__4_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__4);
                    v___y_3633_ = v_ref_3653_;
                    v_a_3634_ = v___x_3656_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                if v_clsEnabled_3595_ == 0 {
                    if v___y_3658_ == 0 {
                        leanh::lean_del_object(v___x_3628_);
                        leanh::lean_dec(v_snd_3626_);
                        leanh::lean_dec(v_fst_3625_);
                        leanh::lean_del_object(v___x_3609_);
                        leanh::lean_dec_ref(v_msg_3597_);
                        leanh::lean_dec_ref(v_tag_3593_);
                        leanh::lean_dec(v_cls_3591_);
                        v___x_3659_ = lean_st_ref_take(v___y_3604_);
                        v_traceState_3660_ = leanh::lean_ctor_get(v___x_3659_, 4);
                        v_env_3661_ = leanh::lean_ctor_get(v___x_3659_, 0);
                        v_nextMacroScope_3662_ = leanh::lean_ctor_get(v___x_3659_, 1);
                        v_ngen_3663_ = leanh::lean_ctor_get(v___x_3659_, 2);
                        v_auxDeclNGen_3664_ = leanh::lean_ctor_get(v___x_3659_, 3);
                        v_cache_3665_ = leanh::lean_ctor_get(v___x_3659_, 5);
                        v_messages_3666_ = leanh::lean_ctor_get(v___x_3659_, 6);
                        v_infoState_3667_ = leanh::lean_ctor_get(v___x_3659_, 7);
                        v_snapshotTasks_3668_ = leanh::lean_ctor_get(v___x_3659_, 8);
                        v_isSharedCheck_3687_ =
                            (!leanh::lean_is_exclusive(v___x_3659_)) as u8;
                        if v_isSharedCheck_3687_ == 0 {
                            v___x_3670_ = v___x_3659_;
                            v_isShared_3671_ = v_isSharedCheck_3687_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_snapshotTasks_3668_);
                            leanh::lean_inc(v_infoState_3667_);
                            leanh::lean_inc(v_messages_3666_);
                            leanh::lean_inc(v_cache_3665_);
                            leanh::lean_inc(v_traceState_3660_);
                            leanh::lean_inc(v_auxDeclNGen_3664_);
                            leanh::lean_inc(v_ngen_3663_);
                            leanh::lean_inc(v_nextMacroScope_3662_);
                            leanh::lean_inc(v_env_3661_);
                            leanh::lean_dec(v___x_3659_);
                            v___x_3670_ = leanh::lean_box(0);
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
                v_tid_3672_ = leanh::lean_ctor_get_uint64(
                    v_traceState_3660_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3673_ = leanh::lean_ctor_get(v_traceState_3660_, 0);
                v_isSharedCheck_3686_ =
                    (!leanh::lean_is_exclusive(v_traceState_3660_)) as u8;
                if v_isSharedCheck_3686_ == 0 {
                    v___x_3675_ = v_traceState_3660_;
                    v_isShared_3676_ = v_isSharedCheck_3686_;
                    state = 12;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_3673_);
                    leanh::lean_dec(v_traceState_3660_);
                    v___x_3675_ = leanh::lean_box(0);
                    v_isShared_3676_ = v_isSharedCheck_3686_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_3677_ =
                    l_Lean_PersistentArray_append___redArg(v_oldTraces_3596_, v_traces_3673_);
                leanh::lean_dec_ref(v_traces_3673_);
                if v_isShared_3676_ == 0 {
                    leanh::lean_ctor_set(v___x_3675_, 0, v___x_3677_);
                    v___x_3679_ = v___x_3675_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3685_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3685_, 0, v___x_3677_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3685_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_3672_,
                    );
                    v___x_3679_ = v_reuseFailAlloc_3685_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_3671_ == 0 {
                    leanh::lean_ctor_set(v___x_3670_, 4, v___x_3679_);
                    v___x_3681_ = v___x_3670_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3684_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_env_3661_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3684_, 1, v_nextMacroScope_3662_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3684_, 2, v_ngen_3663_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3684_, 3, v_auxDeclNGen_3664_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3684_, 4, v___x_3679_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3684_, 5, v_cache_3665_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3684_, 6, v_messages_3666_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3684_, 7, v_infoState_3667_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3684_, 8, v_snapshotTasks_3668_);
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
                v___x_3690_ = leanh::lean_unbox_float(v_snd_3626_);
                v___x_3691_ = leanh::lean_unbox_float(v_fst_3625_);
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
    mut v_cls_3706_: *mut leanh::LeanObject,
    mut v_collapsed_3707_: *mut leanh::LeanObject,
    mut v_tag_3708_: *mut leanh::LeanObject,
    mut v_opts_3709_: *mut leanh::LeanObject,
    mut v_clsEnabled_3710_: *mut leanh::LeanObject,
    mut v_oldTraces_3711_: *mut leanh::LeanObject,
    mut v_msg_3712_: *mut leanh::LeanObject,
    mut v_resStartStop_3713_: *mut leanh::LeanObject,
    mut v___y_3714_: *mut leanh::LeanObject,
    mut v___y_3715_: *mut leanh::LeanObject,
    mut v___y_3716_: *mut leanh::LeanObject,
    mut v___y_3717_: *mut leanh::LeanObject,
    mut v___y_3718_: *mut leanh::LeanObject,
    mut v___y_3719_: *mut leanh::LeanObject,
    mut v___y_3720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_collapsed_boxed_3721_: u8 = 0;
    let mut v_clsEnabled_boxed_3722_: u8 = 0;
    let mut v_res_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_3721_ = (leanh::lean_unbox(v_collapsed_3707_) as u8);
    v_clsEnabled_boxed_3722_ = (leanh::lean_unbox(v_clsEnabled_3710_) as u8);
    v_res_3723_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3(v_cls_3706_, v_collapsed_boxed_3721_, v_tag_3708_, v_opts_3709_, v_clsEnabled_boxed_3722_, v_oldTraces_3711_, v_msg_3712_, v_resStartStop_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_);
    leanh::lean_dec(v___y_3719_);
    leanh::lean_dec_ref(v___y_3718_);
    leanh::lean_dec(v___y_3717_);
    leanh::lean_dec_ref(v___y_3716_);
    leanh::lean_dec(v___y_3715_);
    leanh::lean_dec_ref(v___y_3714_);
    leanh::lean_dec_ref(v_opts_3709_);
    return v_res_3723_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg(
    mut v_cls_3726_: *mut leanh::LeanObject,
    mut v_msg_3727_: *mut leanh::LeanObject,
    mut v___y_3728_: *mut leanh::LeanObject,
    mut v___y_3729_: *mut leanh::LeanObject,
    mut v___y_3730_: *mut leanh::LeanObject,
    mut v___y_3731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3738_: u8 = 0;
    let mut v___x_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3751_: u8 = 0;
    let mut v_tid_3752_: u64 = 0;
    let mut v_traces_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3756_: u8 = 0;
    let mut v___x_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: f64 = 0.0;
    let mut v___x_3759_: u8 = 0;
    let mut v___x_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3777_: u8 = 0;
    let mut v_isSharedCheck_3778_: u8 = 0;
    let mut v_isSharedCheck_3779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3733_ = leanh::lean_ctor_get(v___y_3730_, 5);
                v___x_3734_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0_spec__0(v_msg_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_);
                v_a_3735_ = leanh::lean_ctor_get(v___x_3734_, 0);
                v_isSharedCheck_3779_ = (!leanh::lean_is_exclusive(v___x_3734_)) as u8;
                if v_isSharedCheck_3779_ == 0 {
                    v___x_3737_ = v___x_3734_;
                    v_isShared_3738_ = v_isSharedCheck_3779_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3735_);
                    leanh::lean_dec(v___x_3734_);
                    v___x_3737_ = leanh::lean_box(0);
                    v_isShared_3738_ = v_isSharedCheck_3779_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3739_ = lean_st_ref_take(v___y_3731_);
                v_traceState_3740_ = leanh::lean_ctor_get(v___x_3739_, 4);
                v_env_3741_ = leanh::lean_ctor_get(v___x_3739_, 0);
                v_nextMacroScope_3742_ = leanh::lean_ctor_get(v___x_3739_, 1);
                v_ngen_3743_ = leanh::lean_ctor_get(v___x_3739_, 2);
                v_auxDeclNGen_3744_ = leanh::lean_ctor_get(v___x_3739_, 3);
                v_cache_3745_ = leanh::lean_ctor_get(v___x_3739_, 5);
                v_messages_3746_ = leanh::lean_ctor_get(v___x_3739_, 6);
                v_infoState_3747_ = leanh::lean_ctor_get(v___x_3739_, 7);
                v_snapshotTasks_3748_ = leanh::lean_ctor_get(v___x_3739_, 8);
                v_isSharedCheck_3778_ = (!leanh::lean_is_exclusive(v___x_3739_)) as u8;
                if v_isSharedCheck_3778_ == 0 {
                    v___x_3750_ = v___x_3739_;
                    v_isShared_3751_ = v_isSharedCheck_3778_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3748_);
                    leanh::lean_inc(v_infoState_3747_);
                    leanh::lean_inc(v_messages_3746_);
                    leanh::lean_inc(v_cache_3745_);
                    leanh::lean_inc(v_traceState_3740_);
                    leanh::lean_inc(v_auxDeclNGen_3744_);
                    leanh::lean_inc(v_ngen_3743_);
                    leanh::lean_inc(v_nextMacroScope_3742_);
                    leanh::lean_inc(v_env_3741_);
                    leanh::lean_dec(v___x_3739_);
                    v___x_3750_ = leanh::lean_box(0);
                    v_isShared_3751_ = v_isSharedCheck_3778_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3752_ = leanh::lean_ctor_get_uint64(
                    v_traceState_3740_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3753_ = leanh::lean_ctor_get(v_traceState_3740_, 0);
                v_isSharedCheck_3777_ =
                    (!leanh::lean_is_exclusive(v_traceState_3740_)) as u8;
                if v_isSharedCheck_3777_ == 0 {
                    v___x_3755_ = v_traceState_3740_;
                    v_isShared_3756_ = v_isSharedCheck_3777_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_3753_);
                    leanh::lean_dec(v_traceState_3740_);
                    v___x_3755_ = leanh::lean_box(0);
                    v_isShared_3756_ = v_isSharedCheck_3777_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3757_ = leanh::lean_box(0);
                v___x_3758_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__2_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3___closed__2);
                v___x_3759_ = 0;
                v___x_3760_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__26;
                v___x_3761_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_3761_, 0, v_cls_3726_);
                leanh::lean_ctor_set(v___x_3761_, 1, v___x_3757_);
                leanh::lean_ctor_set(v___x_3761_, 2, v___x_3760_);
                leanh::lean_ctor_set_float(
                    v___x_3761_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_3758_,
                );
                leanh::lean_ctor_set_float(
                    v___x_3761_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3758_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3761_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_3759_,
                );
                v___x_3762_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg___closed__0;
                v___x_3763_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3763_, 0, v___x_3761_);
                leanh::lean_ctor_set(v___x_3763_, 1, v_a_3735_);
                leanh::lean_ctor_set(v___x_3763_, 2, v___x_3762_);
                leanh::lean_inc(v_ref_3733_);
                v___x_3764_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3764_, 0, v_ref_3733_);
                leanh::lean_ctor_set(v___x_3764_, 1, v___x_3763_);
                v___x_3765_ = l_Lean_PersistentArray_push___redArg(v_traces_3753_, v___x_3764_);
                if v_isShared_3756_ == 0 {
                    leanh::lean_ctor_set(v___x_3755_, 0, v___x_3765_);
                    v___x_3767_ = v___x_3755_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3776_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3776_, 0, v___x_3765_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3776_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_3752_,
                    );
                    v___x_3767_ = v_reuseFailAlloc_3776_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3751_ == 0 {
                    leanh::lean_ctor_set(v___x_3750_, 4, v___x_3767_);
                    v___x_3769_ = v___x_3750_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3775_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_env_3741_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 1, v_nextMacroScope_3742_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 2, v_ngen_3743_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 3, v_auxDeclNGen_3744_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 4, v___x_3767_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 5, v_cache_3745_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 6, v_messages_3746_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 7, v_infoState_3747_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 8, v_snapshotTasks_3748_);
                    v___x_3769_ = v_reuseFailAlloc_3775_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3770_ = lean_st_ref_set(v___y_3731_, v___x_3769_);
                v___x_3771_ = leanh::lean_box(0);
                if v_isShared_3738_ == 0 {
                    leanh::lean_ctor_set(v___x_3737_, 0, v___x_3771_);
                    v___x_3773_ = v___x_3737_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3774_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3771_);
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
    mut v_cls_3780_: *mut leanh::LeanObject,
    mut v_msg_3781_: *mut leanh::LeanObject,
    mut v___y_3782_: *mut leanh::LeanObject,
    mut v___y_3783_: *mut leanh::LeanObject,
    mut v___y_3784_: *mut leanh::LeanObject,
    mut v___y_3785_: *mut leanh::LeanObject,
    mut v___y_3786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3787_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg(v_cls_3780_, v_msg_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
    leanh::lean_dec(v___y_3785_);
    leanh::lean_dec_ref(v___y_3784_);
    leanh::lean_dec(v___y_3783_);
    leanh::lean_dec_ref(v___y_3782_);
    return v_res_3787_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3791_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__1;
    v___x_3792_ = l_Lean_stringToMessageData(v___x_3791_);
    return v___x_3792_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg(
    mut v_as_x27_3793_: *mut leanh::LeanObject,
    mut v_b_3794_: *mut leanh::LeanObject,
    mut v___y_3795_: *mut leanh::LeanObject,
    mut v___y_3796_: *mut leanh::LeanObject,
    mut v___y_3797_: *mut leanh::LeanObject,
    mut v___y_3798_: *mut leanh::LeanObject,
    mut v___y_3799_: *mut leanh::LeanObject,
    mut v___y_3800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3808_: u8 = 0;
    let mut v___x_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_run_x27_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3819_: u8 = 0;
    let mut v___x_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: u8 = 0;
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3835_: u8 = 0;
    let mut v___x_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3839_: u8 = 0;
    let mut v_a_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3843_: u8 = 0;
    let mut v___x_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3847_: u8 = 0;
    let mut v___x_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: u8 = 0;
    let mut v___y_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: f64 = 0.0;
    let mut v___x_3860_: f64 = 0.0;
    let mut v___x_3861_: f64 = 0.0;
    let mut v___x_3862_: f64 = 0.0;
    let mut v___x_3863_: f64 = 0.0;
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: f64 = 0.0;
    let mut v___x_3875_: f64 = 0.0;
    let mut v___x_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: u8 = 0;
    let mut v___x_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3891_: u8 = 0;
    let mut v___x_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3895_: u8 = 0;
    let mut v_a_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3899_: u8 = 0;
    let mut v___x_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3903_: u8 = 0;
    let mut v___x_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3909_: u8 = 0;
    let mut v___x_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3913_: u8 = 0;
    let mut v_a_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3917_: u8 = 0;
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3921_: u8 = 0;
    let mut v___x_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: u8 = 0;
    let mut v___x_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3925_: u8 = 0;
    let mut v_unused_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_3793_) == 0 {
                    v___x_3802_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3802_, 0, v_b_3794_);
                    return v___x_3802_;
                } else {
                    v_head_3803_ = leanh::lean_ctor_get(v_as_x27_3793_, 0);
                    v_tail_3804_ = leanh::lean_ctor_get(v_as_x27_3793_, 1);
                    v_snd_3805_ = leanh::lean_ctor_get(v_b_3794_, 1);
                    v_isSharedCheck_3925_ = (!leanh::lean_is_exclusive(v_b_3794_)) as u8;
                    if v_isSharedCheck_3925_ == 0 {
                        v_unused_3926_ = leanh::lean_ctor_get(v_b_3794_, 0);
                        leanh::lean_dec(v_unused_3926_);
                        v___x_3807_ = v_b_3794_;
                        v_isShared_3808_ = v_isSharedCheck_3925_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3805_);
                        leanh::lean_dec(v_b_3794_);
                        v___x_3807_ = leanh::lean_box(0);
                        v_isShared_3808_ = v_isSharedCheck_3925_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_options_3815_ = leanh::lean_ctor_get(v___y_3799_, 2);
                v_name_3816_ = leanh::lean_ctor_get(v_head_3803_, 0);
                v_run_x27_3817_ = leanh::lean_ctor_get(v_head_3803_, 1);
                v_inheritedTraceOptions_3818_ = leanh::lean_ctor_get(v___y_3799_, 13);
                v_hasTrace_3819_ = leanh::lean_ctor_get_uint8(
                    v_options_3815_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v___x_3820_ = leanh::lean_box(0);
                if v_hasTrace_3819_ == 0 {
                    leanh::lean_inc_ref(v_run_x27_3817_);
                    leanh::lean_inc(v___y_3800_);
                    leanh::lean_inc_ref(v___y_3799_);
                    leanh::lean_inc(v___y_3798_);
                    leanh::lean_inc_ref(v___y_3797_);
                    leanh::lean_inc(v___y_3796_);
                    leanh::lean_inc_ref(v___y_3795_);
                    leanh::lean_inc(v_snd_3805_);
                    v___x_3848_ = leanh::lean_apply_8(
                        v_run_x27_3817_,
                        v_snd_3805_,
                        v___y_3795_,
                        v___y_3796_,
                        v___y_3797_,
                        v___y_3798_,
                        v___y_3799_,
                        v___y_3800_,
                        leanh::lean_box(0),
                    );
                    v___y_3822_ = v___x_3848_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3805_);
                    leanh::lean_inc(v_name_3816_);
                    v___f_3849_ = leanh::lean_alloc_closure(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 2);
                    leanh::lean_closure_set(v___f_3849_, 0, v_name_3816_);
                    leanh::lean_closure_set(v___f_3849_, 1, v_snd_3805_);
                    v___x_3850_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25;
                    v___x_3851_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__26;
                    v___x_3852_ = leanh::lean_obj_once(
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
                            leanh::lean_dec_ref(v___f_3849_);
                            leanh::lean_inc_ref(v_run_x27_3817_);
                            leanh::lean_inc(v___y_3800_);
                            leanh::lean_inc_ref(v___y_3799_);
                            leanh::lean_inc(v___y_3798_);
                            leanh::lean_inc_ref(v___y_3797_);
                            leanh::lean_inc(v___y_3796_);
                            leanh::lean_inc_ref(v___y_3795_);
                            leanh::lean_inc(v_snd_3805_);
                            v___x_3924_ = leanh::lean_apply_8(
                                v_run_x27_3817_,
                                v_snd_3805_,
                                v___y_3795_,
                                v___y_3796_,
                                v___y_3797_,
                                v___y_3798_,
                                v___y_3799_,
                                v___y_3800_,
                                leanh::lean_box(0),
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
                    leanh::lean_ctor_set(v___x_3807_, 0, v___x_3810_);
                    v___x_3812_ = v___x_3807_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3814_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3814_, 0, v___x_3810_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3814_, 1, v_snd_3805_);
                    v___x_3812_ = v_reuseFailAlloc_3814_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3813_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3813_, 0, v___x_3812_);
                return v___x_3813_;
            }
            4 => {
                if leanh::lean_obj_tag(v___y_3822_) == 0 {
                    v_a_3823_ = leanh::lean_ctor_get(v___y_3822_, 0);
                    leanh::lean_inc(v_a_3823_);
                    leanh::lean_dec_ref_known(v___y_3822_, 1);
                    if leanh::lean_obj_tag(v_a_3823_) == 1 {
                        leanh::lean_del_object(v___x_3807_);
                        leanh::lean_dec(v_snd_3805_);
                        v_val_3824_ = leanh::lean_ctor_get(v_a_3823_, 0);
                        leanh::lean_inc(v_val_3824_);
                        leanh::lean_dec_ref_known(v_a_3823_, 1);
                        v___x_3825_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3825_, 0, v___x_3820_);
                        leanh::lean_ctor_set(v___x_3825_, 1, v_val_3824_);
                        v_as_x27_3793_ = v_tail_3804_;
                        v_b_3794_ = v___x_3825_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_3823_);
                        if v_hasTrace_3819_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v___x_3827_ =
                                l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25;
                            v___x_3828_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29);
                            v___x_3829_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_3818_,
                                v_options_3815_,
                                v___x_3828_,
                            );
                            if v___x_3829_ == 0 {
                                state = 2;
                                continue;
                            } else {
                                v___x_3830_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__2_once), _init_l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg___closed__2);
                                v___x_3831_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg(v___x_3827_, v___x_3830_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
                                if leanh::lean_obj_tag(v___x_3831_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_3831_, 1);
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_del_object(v___x_3807_);
                                    leanh::lean_dec(v_snd_3805_);
                                    v_a_3832_ = leanh::lean_ctor_get(v___x_3831_, 0);
                                    v_isSharedCheck_3839_ =
                                        (!leanh::lean_is_exclusive(v___x_3831_)) as u8;
                                    if v_isSharedCheck_3839_ == 0 {
                                        v___x_3834_ = v___x_3831_;
                                        v_isShared_3835_ = v_isSharedCheck_3839_;
                                        state = 5;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3832_);
                                        leanh::lean_dec(v___x_3831_);
                                        v___x_3834_ = leanh::lean_box(0);
                                        v_isShared_3835_ = v_isSharedCheck_3839_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_3807_);
                    leanh::lean_dec(v_snd_3805_);
                    v_a_3840_ = leanh::lean_ctor_get(v___y_3822_, 0);
                    v_isSharedCheck_3847_ = (!leanh::lean_is_exclusive(v___y_3822_)) as u8;
                    if v_isSharedCheck_3847_ == 0 {
                        v___x_3842_ = v___y_3822_;
                        v_isShared_3843_ = v_isSharedCheck_3847_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3840_);
                        leanh::lean_dec(v___y_3822_);
                        v___x_3842_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3838_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3832_);
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
                    v_reuseFailAlloc_3846_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3846_, 0, v_a_3840_);
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
                v___x_3860_ = leanh::lean_float_once(
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
                v___x_3864_ = leanh::lean_box_float(v___x_3861_);
                v___x_3865_ = leanh::lean_box_float(v___x_3863_);
                v___x_3866_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3866_, 0, v___x_3864_);
                leanh::lean_ctor_set(v___x_3866_, 1, v___x_3865_);
                v___x_3867_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3867_, 0, v_a_3857_);
                leanh::lean_ctor_set(v___x_3867_, 1, v___x_3866_);
                v___x_3868_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3(v___x_3850_, v_hasTrace_3819_, v___x_3851_, v_options_3815_, v___x_3853_, v___y_3856_, v___f_3849_, v___x_3867_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
                v___y_3822_ = v___x_3868_;
                state = 4;
                continue;
            }
            10 => {
                v___x_3873_ = lean_io_get_num_heartbeats();
                v___x_3874_ = lean_float_of_nat(v___y_3870_);
                v___x_3875_ = lean_float_of_nat(v___x_3873_);
                v___x_3876_ = leanh::lean_box_float(v___x_3874_);
                v___x_3877_ = leanh::lean_box_float(v___x_3875_);
                v___x_3878_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3878_, 0, v___x_3876_);
                leanh::lean_ctor_set(v___x_3878_, 1, v___x_3877_);
                v___x_3879_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3879_, 0, v_a_3872_);
                leanh::lean_ctor_set(v___x_3879_, 1, v___x_3878_);
                v___x_3880_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3(v___x_3850_, v_hasTrace_3819_, v___x_3851_, v_options_3815_, v___x_3853_, v___y_3871_, v___f_3849_, v___x_3879_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
                v___y_3822_ = v___x_3880_;
                state = 4;
                continue;
            }
            11 => {
                v___x_3882_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__1___redArg(v___y_3800_);
                v_a_3883_ = leanh::lean_ctor_get(v___x_3882_, 0);
                leanh::lean_inc(v_a_3883_);
                leanh::lean_dec_ref(v___x_3882_);
                v___x_3884_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_3885_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__2(v_options_3815_, v___x_3884_);
                if v___x_3885_ == 0 {
                    v___x_3886_ = lean_io_mono_nanos_now();
                    leanh::lean_inc_ref(v_run_x27_3817_);
                    leanh::lean_inc(v___y_3800_);
                    leanh::lean_inc_ref(v___y_3799_);
                    leanh::lean_inc(v___y_3798_);
                    leanh::lean_inc_ref(v___y_3797_);
                    leanh::lean_inc(v___y_3796_);
                    leanh::lean_inc_ref(v___y_3795_);
                    leanh::lean_inc(v_snd_3805_);
                    v___x_3887_ = leanh::lean_apply_8(
                        v_run_x27_3817_,
                        v_snd_3805_,
                        v___y_3795_,
                        v___y_3796_,
                        v___y_3797_,
                        v___y_3798_,
                        v___y_3799_,
                        v___y_3800_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_3887_) == 0 {
                        v_a_3888_ = leanh::lean_ctor_get(v___x_3887_, 0);
                        v_isSharedCheck_3895_ =
                            (!leanh::lean_is_exclusive(v___x_3887_)) as u8;
                        if v_isSharedCheck_3895_ == 0 {
                            v___x_3890_ = v___x_3887_;
                            v_isShared_3891_ = v_isSharedCheck_3895_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3888_);
                            leanh::lean_dec(v___x_3887_);
                            v___x_3890_ = leanh::lean_box(0);
                            v_isShared_3891_ = v_isSharedCheck_3895_;
                            state = 12;
                            continue;
                        }
                    } else {
                        v_a_3896_ = leanh::lean_ctor_get(v___x_3887_, 0);
                        v_isSharedCheck_3903_ =
                            (!leanh::lean_is_exclusive(v___x_3887_)) as u8;
                        if v_isSharedCheck_3903_ == 0 {
                            v___x_3898_ = v___x_3887_;
                            v_isShared_3899_ = v_isSharedCheck_3903_;
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3896_);
                            leanh::lean_dec(v___x_3887_);
                            v___x_3898_ = leanh::lean_box(0);
                            v_isShared_3899_ = v_isSharedCheck_3903_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    v___x_3904_ = lean_io_get_num_heartbeats();
                    leanh::lean_inc_ref(v_run_x27_3817_);
                    leanh::lean_inc(v___y_3800_);
                    leanh::lean_inc_ref(v___y_3799_);
                    leanh::lean_inc(v___y_3798_);
                    leanh::lean_inc_ref(v___y_3797_);
                    leanh::lean_inc(v___y_3796_);
                    leanh::lean_inc_ref(v___y_3795_);
                    leanh::lean_inc(v_snd_3805_);
                    v___x_3905_ = leanh::lean_apply_8(
                        v_run_x27_3817_,
                        v_snd_3805_,
                        v___y_3795_,
                        v___y_3796_,
                        v___y_3797_,
                        v___y_3798_,
                        v___y_3799_,
                        v___y_3800_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_3905_) == 0 {
                        v_a_3906_ = leanh::lean_ctor_get(v___x_3905_, 0);
                        v_isSharedCheck_3913_ =
                            (!leanh::lean_is_exclusive(v___x_3905_)) as u8;
                        if v_isSharedCheck_3913_ == 0 {
                            v___x_3908_ = v___x_3905_;
                            v_isShared_3909_ = v_isSharedCheck_3913_;
                            state = 16;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3906_);
                            leanh::lean_dec(v___x_3905_);
                            v___x_3908_ = leanh::lean_box(0);
                            v_isShared_3909_ = v_isSharedCheck_3913_;
                            state = 16;
                            continue;
                        }
                    } else {
                        v_a_3914_ = leanh::lean_ctor_get(v___x_3905_, 0);
                        v_isSharedCheck_3921_ =
                            (!leanh::lean_is_exclusive(v___x_3905_)) as u8;
                        if v_isSharedCheck_3921_ == 0 {
                            v___x_3916_ = v___x_3905_;
                            v_isShared_3917_ = v_isSharedCheck_3921_;
                            state = 18;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3914_);
                            leanh::lean_dec(v___x_3905_);
                            v___x_3916_ = leanh::lean_box(0);
                            v_isShared_3917_ = v_isSharedCheck_3921_;
                            state = 18;
                            continue;
                        }
                    }
                }
            }
            12 => {
                if v_isShared_3891_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3890_, 1);
                    v___x_3893_ = v___x_3890_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3894_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3888_);
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
                    leanh::lean_ctor_set_tag(v___x_3898_, 0);
                    v___x_3901_ = v___x_3898_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3902_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_a_3896_);
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
                    leanh::lean_ctor_set_tag(v___x_3908_, 1);
                    v___x_3911_ = v___x_3908_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3912_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
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
                    leanh::lean_ctor_set_tag(v___x_3916_, 0);
                    v___x_3919_ = v___x_3916_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3920_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3914_);
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
    mut v_as_x27_3927_: *mut leanh::LeanObject,
    mut v_b_3928_: *mut leanh::LeanObject,
    mut v___y_3929_: *mut leanh::LeanObject,
    mut v___y_3930_: *mut leanh::LeanObject,
    mut v___y_3931_: *mut leanh::LeanObject,
    mut v___y_3932_: *mut leanh::LeanObject,
    mut v___y_3933_: *mut leanh::LeanObject,
    mut v___y_3934_: *mut leanh::LeanObject,
    mut v___y_3935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3936_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg(v_as_x27_3927_, v_b_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_);
    leanh::lean_dec(v___y_3934_);
    leanh::lean_dec_ref(v___y_3933_);
    leanh::lean_dec(v___y_3932_);
    leanh::lean_dec_ref(v___y_3931_);
    leanh::lean_dec(v___y_3930_);
    leanh::lean_dec_ref(v___y_3929_);
    leanh::lean_dec(v_as_x27_3927_);
    return v_res_3936_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3939_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__1;
    v___x_3940_ = l_Lean_stringToMessageData(v___x_3939_);
    return v___x_3940_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3942_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__3;
    v___x_3943_ = l_Lean_stringToMessageData(v___x_3942_);
    return v___x_3943_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline(
    mut v_passes_3944_: *mut leanh::LeanObject,
    mut v_goal_3945_: *mut leanh::LeanObject,
    mut v_a_3946_: *mut leanh::LeanObject,
    mut v_a_3947_: *mut leanh::LeanObject,
    mut v_a_3948_: *mut leanh::LeanObject,
    mut v_a_3949_: *mut leanh::LeanObject,
    mut v_a_3950_: *mut leanh::LeanObject,
    mut v_a_3951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3957_: u8 = 0;
    let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3964_: u8 = 0;
    let mut v_fst_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3969_: u8 = 0;
    let mut v___x_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: u8 = 0;
    let mut v_options_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3977_: u8 = 0;
    let mut v_inheritedTraceOptions_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: u8 = 0;
    let mut v___x_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3993_: u8 = 0;
    let mut v___x_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3997_: u8 = 0;
    let mut v_reuseFailAlloc_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4000_: u8 = 0;
    let mut v_inheritedTraceOptions_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: u8 = 0;
    let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4010_: u8 = 0;
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4014_: u8 = 0;
    let mut v_val_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4019_: u8 = 0;
    let mut v_isSharedCheck_4020_: u8 = 0;
    let mut v_a_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4024_: u8 = 0;
    let mut v___x_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4028_: u8 = 0;
    let mut v_isSharedCheck_4029_: u8 = 0;
    let mut v_unused_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4034_: u8 = 0;
    let mut v___x_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4038_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3953_ =
                    l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__0;
                v___x_3954_ = l_Lean_Core_checkSystem(v___x_3953_, v_a_3950_, v_a_3951_);
                if leanh::lean_obj_tag(v___x_3954_) == 0 {
                    v_isSharedCheck_4029_ = (!leanh::lean_is_exclusive(v___x_3954_)) as u8;
                    if v_isSharedCheck_4029_ == 0 {
                        v_unused_4030_ = leanh::lean_ctor_get(v___x_3954_, 0);
                        leanh::lean_dec(v_unused_4030_);
                        v___x_3956_ = v___x_3954_;
                        v_isShared_3957_ = v_isSharedCheck_4029_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3954_);
                        v___x_3956_ = leanh::lean_box(0);
                        v_isShared_3957_ = v_isSharedCheck_4029_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_goal_3945_);
                    v_a_4031_ = leanh::lean_ctor_get(v___x_3954_, 0);
                    v_isSharedCheck_4038_ = (!leanh::lean_is_exclusive(v___x_3954_)) as u8;
                    if v_isSharedCheck_4038_ == 0 {
                        v___x_4033_ = v___x_3954_;
                        v_isShared_4034_ = v_isSharedCheck_4038_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4031_);
                        leanh::lean_dec(v___x_3954_);
                        v___x_4033_ = leanh::lean_box(0);
                        v_isShared_4034_ = v_isSharedCheck_4038_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3958_ = leanh::lean_box(0);
                leanh::lean_inc(v_goal_3945_);
                v___x_3959_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3959_, 0, v___x_3958_);
                leanh::lean_ctor_set(v___x_3959_, 1, v_goal_3945_);
                v___x_3960_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg(v_passes_3944_, v___x_3959_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_);
                if leanh::lean_obj_tag(v___x_3960_) == 0 {
                    v_a_3961_ = leanh::lean_ctor_get(v___x_3960_, 0);
                    v_isSharedCheck_4020_ = (!leanh::lean_is_exclusive(v___x_3960_)) as u8;
                    if v_isSharedCheck_4020_ == 0 {
                        v___x_3963_ = v___x_3960_;
                        v_isShared_3964_ = v_isSharedCheck_4020_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3961_);
                        leanh::lean_dec(v___x_3960_);
                        v___x_3963_ = leanh::lean_box(0);
                        v_isShared_3964_ = v_isSharedCheck_4020_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3956_);
                    leanh::lean_dec(v_goal_3945_);
                    v_a_4021_ = leanh::lean_ctor_get(v___x_3960_, 0);
                    v_isSharedCheck_4028_ = (!leanh::lean_is_exclusive(v___x_3960_)) as u8;
                    if v_isSharedCheck_4028_ == 0 {
                        v___x_4023_ = v___x_3960_;
                        v_isShared_4024_ = v_isSharedCheck_4028_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4021_);
                        leanh::lean_dec(v___x_3960_);
                        v___x_4023_ = leanh::lean_box(0);
                        v_isShared_4024_ = v_isSharedCheck_4028_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_3965_ = leanh::lean_ctor_get(v_a_3961_, 0);
                v_snd_3966_ = leanh::lean_ctor_get(v_a_3961_, 1);
                v_isSharedCheck_4019_ = (!leanh::lean_is_exclusive(v_a_3961_)) as u8;
                if v_isSharedCheck_4019_ == 0 {
                    v___x_3968_ = v_a_3961_;
                    v_isShared_3969_ = v_isSharedCheck_4019_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3966_);
                    leanh::lean_inc(v_fst_3965_);
                    leanh::lean_dec(v_a_3961_);
                    v___x_3968_ = leanh::lean_box(0);
                    v_isShared_3969_ = v_isSharedCheck_4019_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_fst_3965_) == 0 {
                    leanh::lean_del_object(v___x_3956_);
                    v___x_3975_ = l_Lean_instBEqMVarId_beq(v_goal_3945_, v_snd_3966_);
                    leanh::lean_dec(v_goal_3945_);
                    if v___x_3975_ == 0 {
                        leanh::lean_del_object(v___x_3963_);
                        v_options_3976_ = leanh::lean_ctor_get(v_a_3950_, 2);
                        v_hasTrace_3977_ = leanh::lean_ctor_get_uint8(
                            v_options_3976_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_3977_ == 0 {
                            leanh::lean_del_object(v___x_3968_);
                            v_goal_3945_ = v_snd_3966_;
                            state = 0;
                            continue;
                        } else {
                            v_inheritedTraceOptions_3979_ =
                                leanh::lean_ctor_get(v_a_3950_, 13);
                            v___x_3980_ =
                                l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25;
                            v___x_3981_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29);
                            v___x_3982_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_3979_,
                                v_options_3976_,
                                v___x_3981_,
                            );
                            if v___x_3982_ == 0 {
                                leanh::lean_del_object(v___x_3968_);
                                v_goal_3945_ = v_snd_3966_;
                                state = 0;
                                continue;
                            } else {
                                v___x_3984_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__2_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__2);
                                leanh::lean_inc(v_snd_3966_);
                                v___x_3985_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3985_, 0, v_snd_3966_);
                                if v_isShared_3969_ == 0 {
                                    leanh::lean_ctor_set_tag(v___x_3968_, 7);
                                    leanh::lean_ctor_set(v___x_3968_, 1, v___x_3985_);
                                    leanh::lean_ctor_set(v___x_3968_, 0, v___x_3984_);
                                    v___x_3987_ = v___x_3968_;
                                    state = 6;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3998_ =
                                        leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3998_,
                                        0,
                                        v___x_3984_,
                                    );
                                    leanh::lean_ctor_set(
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
                        leanh::lean_del_object(v___x_3968_);
                        v_options_3999_ = leanh::lean_ctor_get(v_a_3950_, 2);
                        v_hasTrace_4000_ = leanh::lean_ctor_get_uint8(
                            v_options_3999_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_4000_ == 0 {
                            state = 4;
                            continue;
                        } else {
                            v_inheritedTraceOptions_4001_ =
                                leanh::lean_ctor_get(v_a_3950_, 13);
                            v___x_4002_ =
                                l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__25;
                            v___x_4003_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_run___closed__29);
                            v___x_4004_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_4001_,
                                v_options_3999_,
                                v___x_4003_,
                            );
                            if v___x_4004_ == 0 {
                                state = 4;
                                continue;
                            } else {
                                v___x_4005_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__4), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__4_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline___closed__4);
                                v___x_4006_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg(v___x_4002_, v___x_4005_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_);
                                if leanh::lean_obj_tag(v___x_4006_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_4006_, 1);
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_snd_3966_);
                                    leanh::lean_del_object(v___x_3963_);
                                    v_a_4007_ = leanh::lean_ctor_get(v___x_4006_, 0);
                                    v_isSharedCheck_4014_ =
                                        (!leanh::lean_is_exclusive(v___x_4006_)) as u8;
                                    if v_isSharedCheck_4014_ == 0 {
                                        v___x_4009_ = v___x_4006_;
                                        v_isShared_4010_ = v_isSharedCheck_4014_;
                                        state = 9;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4007_);
                                        leanh::lean_dec(v___x_4006_);
                                        v___x_4009_ = leanh::lean_box(0);
                                        v_isShared_4010_ = v_isSharedCheck_4014_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_3968_);
                    leanh::lean_dec(v_snd_3966_);
                    leanh::lean_del_object(v___x_3963_);
                    leanh::lean_dec(v_goal_3945_);
                    v_val_4015_ = leanh::lean_ctor_get(v_fst_3965_, 0);
                    leanh::lean_inc(v_val_4015_);
                    leanh::lean_dec_ref_known(v_fst_3965_, 1);
                    if v_isShared_3957_ == 0 {
                        leanh::lean_ctor_set(v___x_3956_, 0, v_val_4015_);
                        v___x_4017_ = v___x_3956_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_4018_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_val_4015_);
                        v___x_4017_ = v_reuseFailAlloc_4018_;
                        state = 11;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3971_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3971_, 0, v_snd_3966_);
                if v_isShared_3964_ == 0 {
                    leanh::lean_ctor_set(v___x_3963_, 0, v___x_3971_);
                    v___x_3973_ = v___x_3963_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3974_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3974_, 0, v___x_3971_);
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
                if leanh::lean_obj_tag(v___x_3988_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3988_, 1);
                    v_goal_3945_ = v_snd_3966_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_3966_);
                    v_a_3990_ = leanh::lean_ctor_get(v___x_3988_, 0);
                    v_isSharedCheck_3997_ = (!leanh::lean_is_exclusive(v___x_3988_)) as u8;
                    if v_isSharedCheck_3997_ == 0 {
                        v___x_3992_ = v___x_3988_;
                        v_isShared_3993_ = v_isSharedCheck_3997_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3990_);
                        leanh::lean_dec(v___x_3988_);
                        v___x_3992_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3996_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3990_);
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
                    v_reuseFailAlloc_4013_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_a_4007_);
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
                    v_reuseFailAlloc_4027_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4027_, 0, v_a_4021_);
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
                    v_reuseFailAlloc_4037_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_a_4031_);
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
    mut v_passes_4039_: *mut leanh::LeanObject,
    mut v_goal_4040_: *mut leanh::LeanObject,
    mut v_a_4041_: *mut leanh::LeanObject,
    mut v_a_4042_: *mut leanh::LeanObject,
    mut v_a_4043_: *mut leanh::LeanObject,
    mut v_a_4044_: *mut leanh::LeanObject,
    mut v_a_4045_: *mut leanh::LeanObject,
    mut v_a_4046_: *mut leanh::LeanObject,
    mut v_a_4047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_4046_);
    leanh::lean_dec_ref(v_a_4045_);
    leanh::lean_dec(v_a_4044_);
    leanh::lean_dec_ref(v_a_4043_);
    leanh::lean_dec(v_a_4042_);
    leanh::lean_dec_ref(v_a_4041_);
    leanh::lean_dec(v_passes_4039_);
    return v_res_4048_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0(
    mut v_cls_4049_: *mut leanh::LeanObject,
    mut v_msg_4050_: *mut leanh::LeanObject,
    mut v___y_4051_: *mut leanh::LeanObject,
    mut v___y_4052_: *mut leanh::LeanObject,
    mut v___y_4053_: *mut leanh::LeanObject,
    mut v___y_4054_: *mut leanh::LeanObject,
    mut v___y_4055_: *mut leanh::LeanObject,
    mut v___y_4056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4058_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___redArg(v_cls_4049_, v_msg_4050_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
    return v___x_4058_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__0___boxed(
    mut v_cls_4059_: *mut leanh::LeanObject,
    mut v_msg_4060_: *mut leanh::LeanObject,
    mut v___y_4061_: *mut leanh::LeanObject,
    mut v___y_4062_: *mut leanh::LeanObject,
    mut v___y_4063_: *mut leanh::LeanObject,
    mut v___y_4064_: *mut leanh::LeanObject,
    mut v___y_4065_: *mut leanh::LeanObject,
    mut v___y_4066_: *mut leanh::LeanObject,
    mut v___y_4067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_4066_);
    leanh::lean_dec_ref(v___y_4065_);
    leanh::lean_dec(v___y_4064_);
    leanh::lean_dec_ref(v___y_4063_);
    leanh::lean_dec(v___y_4062_);
    leanh::lean_dec_ref(v___y_4061_);
    return v_res_4068_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__6(
    mut v_00_u03b1_4069_: *mut leanh::LeanObject,
    mut v_x_4070_: *mut leanh::LeanObject,
    mut v___y_4071_: *mut leanh::LeanObject,
    mut v___y_4072_: *mut leanh::LeanObject,
    mut v___y_4073_: *mut leanh::LeanObject,
    mut v___y_4074_: *mut leanh::LeanObject,
    mut v___y_4075_: *mut leanh::LeanObject,
    mut v___y_4076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4078_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__6___redArg(v_x_4070_);
    return v___x_4078_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__6___boxed(
    mut v_00_u03b1_4079_: *mut leanh::LeanObject,
    mut v_x_4080_: *mut leanh::LeanObject,
    mut v___y_4081_: *mut leanh::LeanObject,
    mut v___y_4082_: *mut leanh::LeanObject,
    mut v___y_4083_: *mut leanh::LeanObject,
    mut v___y_4084_: *mut leanh::LeanObject,
    mut v___y_4085_: *mut leanh::LeanObject,
    mut v___y_4086_: *mut leanh::LeanObject,
    mut v___y_4087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4088_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__6(v_00_u03b1_4079_, v_x_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_);
    leanh::lean_dec(v___y_4086_);
    leanh::lean_dec_ref(v___y_4085_);
    leanh::lean_dec(v___y_4084_);
    leanh::lean_dec_ref(v___y_4083_);
    leanh::lean_dec(v___y_4082_);
    leanh::lean_dec_ref(v___y_4081_);
    return v_res_4088_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4(
    mut v_as_4089_: *mut leanh::LeanObject,
    mut v_as_x27_4090_: *mut leanh::LeanObject,
    mut v_b_4091_: *mut leanh::LeanObject,
    mut v_a_4092_: *mut leanh::LeanObject,
    mut v___y_4093_: *mut leanh::LeanObject,
    mut v___y_4094_: *mut leanh::LeanObject,
    mut v___y_4095_: *mut leanh::LeanObject,
    mut v___y_4096_: *mut leanh::LeanObject,
    mut v___y_4097_: *mut leanh::LeanObject,
    mut v___y_4098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4100_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___redArg(v_as_x27_4090_, v_b_4091_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_);
    return v___x_4100_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4___boxed(
    mut v_as_4101_: *mut leanh::LeanObject,
    mut v_as_x27_4102_: *mut leanh::LeanObject,
    mut v_b_4103_: *mut leanh::LeanObject,
    mut v_a_4104_: *mut leanh::LeanObject,
    mut v___y_4105_: *mut leanh::LeanObject,
    mut v___y_4106_: *mut leanh::LeanObject,
    mut v___y_4107_: *mut leanh::LeanObject,
    mut v___y_4108_: *mut leanh::LeanObject,
    mut v___y_4109_: *mut leanh::LeanObject,
    mut v___y_4110_: *mut leanh::LeanObject,
    mut v___y_4111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4112_ = l_List_forIn_x27_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__4(v_as_4101_, v_as_x27_4102_, v_b_4103_, v_a_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
    leanh::lean_dec(v___y_4110_);
    leanh::lean_dec_ref(v___y_4109_);
    leanh::lean_dec(v___y_4108_);
    leanh::lean_dec_ref(v___y_4107_);
    leanh::lean_dec(v___y_4106_);
    leanh::lean_dec_ref(v___y_4105_);
    leanh::lean_dec(v_as_x27_4102_);
    leanh::lean_dec(v_as_4101_);
    return v_res_4112_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5(
    mut v_oldTraces_4113_: *mut leanh::LeanObject,
    mut v_data_4114_: *mut leanh::LeanObject,
    mut v_ref_4115_: *mut leanh::LeanObject,
    mut v_msg_4116_: *mut leanh::LeanObject,
    mut v___y_4117_: *mut leanh::LeanObject,
    mut v___y_4118_: *mut leanh::LeanObject,
    mut v___y_4119_: *mut leanh::LeanObject,
    mut v___y_4120_: *mut leanh::LeanObject,
    mut v___y_4121_: *mut leanh::LeanObject,
    mut v___y_4122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4124_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5___redArg(v_oldTraces_4113_, v_data_4114_, v_ref_4115_, v_msg_4116_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_);
    return v___x_4124_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5___boxed(
    mut v_oldTraces_4125_: *mut leanh::LeanObject,
    mut v_data_4126_: *mut leanh::LeanObject,
    mut v_ref_4127_: *mut leanh::LeanObject,
    mut v_msg_4128_: *mut leanh::LeanObject,
    mut v___y_4129_: *mut leanh::LeanObject,
    mut v___y_4130_: *mut leanh::LeanObject,
    mut v___y_4131_: *mut leanh::LeanObject,
    mut v___y_4132_: *mut leanh::LeanObject,
    mut v___y_4133_: *mut leanh::LeanObject,
    mut v___y_4134_: *mut leanh::LeanObject,
    mut v___y_4135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4136_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_Pass_fixpointPipeline_spec__3_spec__5(v_oldTraces_4125_, v_data_4126_, v_ref_4127_, v_msg_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_);
    leanh::lean_dec(v___y_4134_);
    leanh::lean_dec_ref(v___y_4133_);
    leanh::lean_dec(v___y_4132_);
    leanh::lean_dec_ref(v___y_4131_);
    leanh::lean_dec(v___y_4130_);
    leanh::lean_dec_ref(v___y_4129_);
    return v_res_4136_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Attr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(
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
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_BVDecide_Attr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
}