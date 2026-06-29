// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
// Imports: Lean.Meta.Tactic.Grind.SynthInstance Lean.Meta.Tactic.Grind.Arith.CommRing.MonadRing Lean.Meta.Sym.Arith.Poly
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_find_x3f___redArg,
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_insert___redArg, l_Lean_PersistentHashMap_mkCollisionNode___redArg,
    l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Sym::Arith::Poly::{
    initialize_Lean_Meta_Sym_Arith_Poly, l_Lean_Grind_CommRing_Poly_degree,
    runtime_initialize_Lean_Meta_Sym_Arith_Poly,
};
use crate::r#gen::Lean::Meta::Sym::Canon::l_Lean_Meta_Sym_canon;
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1, l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed,
};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    l_Lean_Meta_Sym_getConfig___redArg, l_Lean_Meta_Sym_reportIssue,
    l_Lean_Meta_Sym_shareCommon___redArg,
};
use crate::r#gen::Lean::Meta::Sym::SynthInstance::l_Lean_Meta_Sym_synthInstanceMeta_x3f;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::MonadRing::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::Types::{
    l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare,
    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg, l_Lean_Meta_Grind_Arith_CommRing_ringExt,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::SynthInstance::{
    initialize_Lean_Meta_Tactic_Grind_SynthInstance,
    runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg,
    l_Lean_Meta_Grind_SolverExtension_markTerm___boxed,
    l_Lean_Meta_Grind_SolverExtension_markTerm___redArg, l_Lean_Meta_Grind_getConfig___redArg,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::{
    l_Std_DTreeMap_Internal_Impl_maxView___redArg, l_Std_DTreeMap_Internal_Impl_minView___redArg,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg;
use crate::ffi::lean_array_fset;
use crate::ffi::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul,
};
use crate::ffi::lean_st_ref_get;
pub static l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__0_value:
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
        114, 105, 110, 103, 32, 112, 111, 108, 121, 110, 111, 109, 105, 97, 108, 32, 100, 101, 103,
        114, 101, 101, 32, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__2_value:
    crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        32, 101, 120, 99, 101, 101, 100, 115, 32, 116, 104, 114, 101, 115, 104, 111, 108, 100, 32,
        96, 40, 114, 105, 110, 103, 77, 97, 120, 68, 101, 103, 114, 101, 101, 32, 58, 61, 32, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__4_value:
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
    m_data: [41, 96, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__1_value:
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
    m_fun: l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__0_value:
    crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        96, 103, 114, 105, 110, 100, 96, 32, 105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114,
        114, 111, 114, 44, 32, 105, 110, 118, 97, 108, 105, 100, 32, 114, 105, 110, 103, 73, 100,
        0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___boxed
        as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1: usize = 0;
pub static l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0_value:
    crate::leanh::LeanStringObject<60> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 60,
    m_capacity: 60,
    m_length: 59,
    m_data: [
        96, 103, 114, 105, 110, 100, 96, 32, 105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114,
        114, 111, 114, 44, 32, 114, 105, 110, 103, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32,
        104, 97, 118, 101, 32, 97, 32, 99, 104, 97, 114, 97, 99, 116, 101, 114, 105, 115, 116, 105,
        99, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__0_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
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
        101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 105, 110, 32, 116, 119, 111, 32, 100,
        105, 102, 102, 101, 114, 101, 110, 116, 32, 114, 105, 110, 103, 115, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0_value:
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
    m_fun: l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1_value:
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
    m_fun: l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(
    mut v_a_2671_: *mut crate::leanh::LeanObject,
    mut v_a_2672_: *mut crate::leanh::LeanObject,
    mut v_a_2673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2681_: u8 = 0;
    let mut v_ringSteps_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: u8 = 0;
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2689_: u8 = 0;
    let mut v_a_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2693_: u8 = 0;
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2697_: u8 = 0;
    let mut v_a_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2701_: u8 = 0;
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2705_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2675_ =
                    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_2671_, v_a_2673_);
                if crate::leanh::lean_obj_tag(v___x_2675_) == 0 {
                    v_a_2676_ = crate::leanh::lean_ctor_get(v___x_2675_, 0);
                    crate::leanh::lean_inc(v_a_2676_);
                    crate::leanh::lean_dec_ref_known(v___x_2675_, 1);
                    v___x_2677_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2672_);
                    if crate::leanh::lean_obj_tag(v___x_2677_) == 0 {
                        v_a_2678_ = crate::leanh::lean_ctor_get(v___x_2677_, 0);
                        v_isSharedCheck_2689_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2677_)) as u8;
                        if v_isSharedCheck_2689_ == 0 {
                            v___x_2680_ = v___x_2677_;
                            v_isShared_2681_ = v_isSharedCheck_2689_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2678_);
                            crate::leanh::lean_dec(v___x_2677_);
                            v___x_2680_ = crate::leanh::lean_box(0);
                            v_isShared_2681_ = v_isSharedCheck_2689_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2676_);
                        v_a_2690_ = crate::leanh::lean_ctor_get(v___x_2677_, 0);
                        v_isSharedCheck_2697_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2677_)) as u8;
                        if v_isSharedCheck_2697_ == 0 {
                            v___x_2692_ = v___x_2677_;
                            v_isShared_2693_ = v_isSharedCheck_2697_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2690_);
                            crate::leanh::lean_dec(v___x_2677_);
                            v___x_2692_ = crate::leanh::lean_box(0);
                            v_isShared_2693_ = v_isSharedCheck_2697_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_2698_ = crate::leanh::lean_ctor_get(v___x_2675_, 0);
                    v_isSharedCheck_2705_ = (!crate::leanh::lean_is_exclusive(v___x_2675_)) as u8;
                    if v_isSharedCheck_2705_ == 0 {
                        v___x_2700_ = v___x_2675_;
                        v_isShared_2701_ = v_isSharedCheck_2705_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2698_);
                        crate::leanh::lean_dec(v___x_2675_);
                        v___x_2700_ = crate::leanh::lean_box(0);
                        v_isShared_2701_ = v_isSharedCheck_2705_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_ringSteps_2682_ = crate::leanh::lean_ctor_get(v_a_2678_, 6);
                crate::leanh::lean_inc(v_ringSteps_2682_);
                crate::leanh::lean_dec(v_a_2678_);
                v_steps_2683_ = crate::leanh::lean_ctor_get(v_a_2676_, 12);
                crate::leanh::lean_inc(v_steps_2683_);
                crate::leanh::lean_dec(v_a_2676_);
                v___x_2684_ = lean_nat_dec_le(v_ringSteps_2682_, v_steps_2683_);
                crate::leanh::lean_dec(v_steps_2683_);
                crate::leanh::lean_dec(v_ringSteps_2682_);
                v___x_2685_ = crate::leanh::lean_box((v___x_2684_) as usize);
                if v_isShared_2681_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2680_, 0, v___x_2685_);
                    v___x_2687_ = v___x_2680_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2688_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___x_2685_);
                    v___x_2687_ = v_reuseFailAlloc_2688_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2687_;
            }
            3 => {
                if v_isShared_2693_ == 0 {
                    v___x_2695_ = v___x_2692_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2696_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2690_);
                    v___x_2695_ = v_reuseFailAlloc_2696_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2695_;
            }
            5 => {
                if v_isShared_2701_ == 0 {
                    v___x_2703_ = v___x_2700_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2704_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2698_);
                    v___x_2703_ = v_reuseFailAlloc_2704_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2703_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg___boxed(
    mut v_a_2706_: *mut crate::leanh::LeanObject,
    mut v_a_2707_: *mut crate::leanh::LeanObject,
    mut v_a_2708_: *mut crate::leanh::LeanObject,
    mut v_a_2709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2710_ =
        l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(v_a_2706_, v_a_2707_, v_a_2708_);
    crate::leanh::lean_dec_ref(v_a_2708_);
    crate::leanh::lean_dec_ref(v_a_2707_);
    crate::leanh::lean_dec(v_a_2706_);
    return v_res_2710_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps(
    mut v_a_2711_: *mut crate::leanh::LeanObject,
    mut v_a_2712_: *mut crate::leanh::LeanObject,
    mut v_a_2713_: *mut crate::leanh::LeanObject,
    mut v_a_2714_: *mut crate::leanh::LeanObject,
    mut v_a_2715_: *mut crate::leanh::LeanObject,
    mut v_a_2716_: *mut crate::leanh::LeanObject,
    mut v_a_2717_: *mut crate::leanh::LeanObject,
    mut v_a_2718_: *mut crate::leanh::LeanObject,
    mut v_a_2719_: *mut crate::leanh::LeanObject,
    mut v_a_2720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2722_ =
        l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(v_a_2711_, v_a_2713_, v_a_2719_);
    return v___x_2722_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___boxed(
    mut v_a_2723_: *mut crate::leanh::LeanObject,
    mut v_a_2724_: *mut crate::leanh::LeanObject,
    mut v_a_2725_: *mut crate::leanh::LeanObject,
    mut v_a_2726_: *mut crate::leanh::LeanObject,
    mut v_a_2727_: *mut crate::leanh::LeanObject,
    mut v_a_2728_: *mut crate::leanh::LeanObject,
    mut v_a_2729_: *mut crate::leanh::LeanObject,
    mut v_a_2730_: *mut crate::leanh::LeanObject,
    mut v_a_2731_: *mut crate::leanh::LeanObject,
    mut v_a_2732_: *mut crate::leanh::LeanObject,
    mut v_a_2733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2734_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps(
        v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_,
        v_a_2731_, v_a_2732_,
    );
    crate::leanh::lean_dec(v_a_2732_);
    crate::leanh::lean_dec_ref(v_a_2731_);
    crate::leanh::lean_dec(v_a_2730_);
    crate::leanh::lean_dec_ref(v_a_2729_);
    crate::leanh::lean_dec(v_a_2728_);
    crate::leanh::lean_dec_ref(v_a_2727_);
    crate::leanh::lean_dec(v_a_2726_);
    crate::leanh::lean_dec_ref(v_a_2725_);
    crate::leanh::lean_dec(v_a_2724_);
    crate::leanh::lean_dec(v_a_2723_);
    return v_res_2734_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0(
    mut v___x_2735_: u8,
    mut v_s_2736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_rings_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2752_: u8 = 0;
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2756_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_2737_ = crate::leanh::lean_ctor_get(v_s_2736_, 0);
                v_typeIdOf_2738_ = crate::leanh::lean_ctor_get(v_s_2736_, 1);
                v_exprToRingId_2739_ = crate::leanh::lean_ctor_get(v_s_2736_, 2);
                v_semirings_2740_ = crate::leanh::lean_ctor_get(v_s_2736_, 3);
                v_stypeIdOf_2741_ = crate::leanh::lean_ctor_get(v_s_2736_, 4);
                v_exprToSemiringId_2742_ = crate::leanh::lean_ctor_get(v_s_2736_, 5);
                v_ncRings_2743_ = crate::leanh::lean_ctor_get(v_s_2736_, 6);
                v_exprToNCRingId_2744_ = crate::leanh::lean_ctor_get(v_s_2736_, 7);
                v_nctypeIdOf_2745_ = crate::leanh::lean_ctor_get(v_s_2736_, 8);
                v_ncSemirings_2746_ = crate::leanh::lean_ctor_get(v_s_2736_, 9);
                v_exprToNCSemiringId_2747_ = crate::leanh::lean_ctor_get(v_s_2736_, 10);
                v_ncstypeIdOf_2748_ = crate::leanh::lean_ctor_get(v_s_2736_, 11);
                v_steps_2749_ = crate::leanh::lean_ctor_get(v_s_2736_, 12);
                v_isSharedCheck_2756_ = (!crate::leanh::lean_is_exclusive(v_s_2736_)) as u8;
                if v_isSharedCheck_2756_ == 0 {
                    v___x_2751_ = v_s_2736_;
                    v_isShared_2752_ = v_isSharedCheck_2756_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_steps_2749_);
                    crate::leanh::lean_inc(v_ncstypeIdOf_2748_);
                    crate::leanh::lean_inc(v_exprToNCSemiringId_2747_);
                    crate::leanh::lean_inc(v_ncSemirings_2746_);
                    crate::leanh::lean_inc(v_nctypeIdOf_2745_);
                    crate::leanh::lean_inc(v_exprToNCRingId_2744_);
                    crate::leanh::lean_inc(v_ncRings_2743_);
                    crate::leanh::lean_inc(v_exprToSemiringId_2742_);
                    crate::leanh::lean_inc(v_stypeIdOf_2741_);
                    crate::leanh::lean_inc(v_semirings_2740_);
                    crate::leanh::lean_inc(v_exprToRingId_2739_);
                    crate::leanh::lean_inc(v_typeIdOf_2738_);
                    crate::leanh::lean_inc(v_rings_2737_);
                    crate::leanh::lean_dec(v_s_2736_);
                    v___x_2751_ = crate::leanh::lean_box(0);
                    v_isShared_2752_ = v_isSharedCheck_2756_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2752_ == 0 {
                    v___x_2754_ = v___x_2751_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2755_ = crate::leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_rings_2737_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2755_, 1, v_typeIdOf_2738_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2755_, 2, v_exprToRingId_2739_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2755_, 3, v_semirings_2740_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2755_, 4, v_stypeIdOf_2741_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2755_,
                        5,
                        v_exprToSemiringId_2742_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2755_, 6, v_ncRings_2743_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2755_, 7, v_exprToNCRingId_2744_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2755_, 8, v_nctypeIdOf_2745_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2755_, 9, v_ncSemirings_2746_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2755_,
                        10,
                        v_exprToNCSemiringId_2747_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2755_, 11, v_ncstypeIdOf_2748_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2755_, 12, v_steps_2749_);
                    v___x_2754_ = v_reuseFailAlloc_2755_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2754_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                    v___x_2735_,
                );
                return v___x_2754_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0___boxed(
    mut v___x_2757_: *mut crate::leanh::LeanObject,
    mut v_s_2758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7553__boxed_2759_: u8 = 0;
    let mut v_res_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7553__boxed_2759_ = (crate::leanh::lean_unbox(v___x_2757_) as u8);
    v_res_2760_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0(
        v___x_7553__boxed_2759_,
        v_s_2758_,
    );
    return v_res_2760_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2762_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__0;
    v___x_2763_ = l_Lean_stringToMessageData(v___x_2762_);
    return v___x_2763_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2765_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__2;
    v___x_2766_ = l_Lean_stringToMessageData(v___x_2765_);
    return v___x_2766_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2768_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__4;
    v___x_2769_ = l_Lean_stringToMessageData(v___x_2768_);
    return v___x_2769_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg(
    mut v_p_2770_: *mut crate::leanh::LeanObject,
    mut v_a_2771_: *mut crate::leanh::LeanObject,
    mut v_a_2772_: *mut crate::leanh::LeanObject,
    mut v_a_2773_: *mut crate::leanh::LeanObject,
    mut v_a_2774_: *mut crate::leanh::LeanObject,
    mut v_a_2775_: *mut crate::leanh::LeanObject,
    mut v_a_2776_: *mut crate::leanh::LeanObject,
    mut v_a_2777_: *mut crate::leanh::LeanObject,
    mut v_a_2778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2784_: u8 = 0;
    let mut v_ringMaxDegree_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: u8 = 0;
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2796_: u8 = 0;
    let mut v_reportedMaxDegreeIssue_2797_: u8 = 0;
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2806_: u8 = 0;
    let mut v___x_2807_: u8 = 0;
    let mut v___x_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2825_: u8 = 0;
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2830_: u8 = 0;
    let mut v_unused_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2835_: u8 = 0;
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2839_: u8 = 0;
    let mut v_isSharedCheck_2840_: u8 = 0;
    let mut v_a_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2844_: u8 = 0;
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2848_: u8 = 0;
    let mut v_a_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2852_: u8 = 0;
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2856_: u8 = 0;
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2861_: u8 = 0;
    let mut v_a_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2865_: u8 = 0;
    let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2869_: u8 = 0;
    let mut v_isSharedCheck_2870_: u8 = 0;
    let mut v_a_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2874_: u8 = 0;
    let mut v___x_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2878_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2780_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2772_);
                if crate::leanh::lean_obj_tag(v___x_2780_) == 0 {
                    v_a_2781_ = crate::leanh::lean_ctor_get(v___x_2780_, 0);
                    v_isSharedCheck_2870_ = (!crate::leanh::lean_is_exclusive(v___x_2780_)) as u8;
                    if v_isSharedCheck_2870_ == 0 {
                        v___x_2783_ = v___x_2780_;
                        v_isShared_2784_ = v_isSharedCheck_2870_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2781_);
                        crate::leanh::lean_dec(v___x_2780_);
                        v___x_2783_ = crate::leanh::lean_box(0);
                        v_isShared_2784_ = v_isSharedCheck_2870_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2871_ = crate::leanh::lean_ctor_get(v___x_2780_, 0);
                    v_isSharedCheck_2878_ = (!crate::leanh::lean_is_exclusive(v___x_2780_)) as u8;
                    if v_isSharedCheck_2878_ == 0 {
                        v___x_2873_ = v___x_2780_;
                        v_isShared_2874_ = v_isSharedCheck_2878_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2871_);
                        crate::leanh::lean_dec(v___x_2780_);
                        v___x_2873_ = crate::leanh::lean_box(0);
                        v_isShared_2874_ = v_isSharedCheck_2878_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                v_ringMaxDegree_2785_ = crate::leanh::lean_ctor_get(v_a_2781_, 7);
                crate::leanh::lean_inc(v_ringMaxDegree_2785_);
                crate::leanh::lean_dec(v_a_2781_);
                v___x_2786_ = l_Lean_Grind_CommRing_Poly_degree(v_p_2770_);
                v___x_2787_ = lean_nat_dec_le(v_ringMaxDegree_2785_, v___x_2786_);
                crate::leanh::lean_dec(v_ringMaxDegree_2785_);
                if v___x_2787_ == 0 {
                    crate::leanh::lean_dec(v___x_2786_);
                    v___x_2788_ = crate::leanh::lean_box((v___x_2787_) as usize);
                    if v_isShared_2784_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2783_, 0, v___x_2788_);
                        v___x_2790_ = v___x_2783_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2791_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2791_, 0, v___x_2788_);
                        v___x_2790_ = v_reuseFailAlloc_2791_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2783_);
                    v___x_2792_ =
                        l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_2771_, v_a_2777_);
                    if crate::leanh::lean_obj_tag(v___x_2792_) == 0 {
                        v_a_2793_ = crate::leanh::lean_ctor_get(v___x_2792_, 0);
                        v_isSharedCheck_2861_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2792_)) as u8;
                        if v_isSharedCheck_2861_ == 0 {
                            v___x_2795_ = v___x_2792_;
                            v_isShared_2796_ = v_isSharedCheck_2861_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2793_);
                            crate::leanh::lean_dec(v___x_2792_);
                            v___x_2795_ = crate::leanh::lean_box(0);
                            v_isShared_2796_ = v_isSharedCheck_2861_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2786_);
                        v_a_2862_ = crate::leanh::lean_ctor_get(v___x_2792_, 0);
                        v_isSharedCheck_2869_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2792_)) as u8;
                        if v_isSharedCheck_2869_ == 0 {
                            v___x_2864_ = v___x_2792_;
                            v_isShared_2865_ = v_isSharedCheck_2869_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2862_);
                            crate::leanh::lean_dec(v___x_2792_);
                            v___x_2864_ = crate::leanh::lean_box(0);
                            v_isShared_2865_ = v_isSharedCheck_2869_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2790_;
            }
            3 => {
                v_reportedMaxDegreeIssue_2797_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2793_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                crate::leanh::lean_dec(v_a_2793_);
                if v_reportedMaxDegreeIssue_2797_ == 0 {
                    crate::leanh::lean_del_object(v___x_2795_);
                    v___x_2798_ = crate::leanh::lean_box((v___x_2787_) as usize);
                    v___f_2799_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_2799_, 0, v___x_2798_);
                    v___x_2800_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                    v___x_2801_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2800_, v___f_2799_, v_a_2771_);
                    if crate::leanh::lean_obj_tag(v___x_2801_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2801_, 1);
                        v___x_2802_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2773_);
                        if crate::leanh::lean_obj_tag(v___x_2802_) == 0 {
                            v_a_2803_ = crate::leanh::lean_ctor_get(v___x_2802_, 0);
                            v_isSharedCheck_2840_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2802_)) as u8;
                            if v_isSharedCheck_2840_ == 0 {
                                v___x_2805_ = v___x_2802_;
                                v_isShared_2806_ = v_isSharedCheck_2840_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2803_);
                                crate::leanh::lean_dec(v___x_2802_);
                                v___x_2805_ = crate::leanh::lean_box(0);
                                v_isShared_2806_ = v_isSharedCheck_2840_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_2786_);
                            v_a_2841_ = crate::leanh::lean_ctor_get(v___x_2802_, 0);
                            v_isSharedCheck_2848_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2802_)) as u8;
                            if v_isSharedCheck_2848_ == 0 {
                                v___x_2843_ = v___x_2802_;
                                v_isShared_2844_ = v_isSharedCheck_2848_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2841_);
                                crate::leanh::lean_dec(v___x_2802_);
                                v___x_2843_ = crate::leanh::lean_box(0);
                                v_isShared_2844_ = v_isSharedCheck_2848_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2786_);
                        v_a_2849_ = crate::leanh::lean_ctor_get(v___x_2801_, 0);
                        v_isSharedCheck_2856_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2801_)) as u8;
                        if v_isSharedCheck_2856_ == 0 {
                            v___x_2851_ = v___x_2801_;
                            v_isShared_2852_ = v_isSharedCheck_2856_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2849_);
                            crate::leanh::lean_dec(v___x_2801_);
                            v___x_2851_ = crate::leanh::lean_box(0);
                            v_isShared_2852_ = v_isSharedCheck_2856_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2786_);
                    v___x_2857_ = crate::leanh::lean_box((v___x_2787_) as usize);
                    if v_isShared_2796_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2795_, 0, v___x_2857_);
                        v___x_2859_ = v___x_2795_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_2860_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2857_);
                        v___x_2859_ = v_reuseFailAlloc_2860_;
                        state = 14;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2807_ = (crate::leanh::lean_unbox(v_a_2803_) as u8);
                crate::leanh::lean_dec(v_a_2803_);
                if v___x_2807_ == 0 {
                    crate::leanh::lean_dec(v___x_2786_);
                    v___x_2808_ = crate::leanh::lean_box((v___x_2787_) as usize);
                    if v_isShared_2806_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2805_, 0, v___x_2808_);
                        v___x_2810_ = v___x_2805_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2811_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2808_);
                        v___x_2810_ = v_reuseFailAlloc_2811_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2805_);
                    v___x_2812_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1_once), _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1);
                    v___x_2813_ = l_Nat_reprFast(v___x_2786_);
                    v___x_2814_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2814_, 0, v___x_2813_);
                    v___x_2815_ = l_Lean_MessageData_ofFormat(v___x_2814_);
                    crate::leanh::lean_inc_ref(v___x_2815_);
                    v___x_2816_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2816_, 0, v___x_2812_);
                    crate::leanh::lean_ctor_set(v___x_2816_, 1, v___x_2815_);
                    v___x_2817_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3_once), _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3);
                    v___x_2818_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2818_, 0, v___x_2816_);
                    crate::leanh::lean_ctor_set(v___x_2818_, 1, v___x_2817_);
                    v___x_2819_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2819_, 0, v___x_2818_);
                    crate::leanh::lean_ctor_set(v___x_2819_, 1, v___x_2815_);
                    v___x_2820_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5_once), _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5);
                    v___x_2821_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2821_, 0, v___x_2819_);
                    crate::leanh::lean_ctor_set(v___x_2821_, 1, v___x_2820_);
                    v___x_2822_ = l_Lean_Meta_Sym_reportIssue(
                        v___x_2821_,
                        v_a_2773_,
                        v_a_2774_,
                        v_a_2775_,
                        v_a_2776_,
                        v_a_2777_,
                        v_a_2778_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2822_) == 0 {
                        v_isSharedCheck_2830_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2822_)) as u8;
                        if v_isSharedCheck_2830_ == 0 {
                            v_unused_2831_ = crate::leanh::lean_ctor_get(v___x_2822_, 0);
                            crate::leanh::lean_dec(v_unused_2831_);
                            v___x_2824_ = v___x_2822_;
                            v_isShared_2825_ = v_isSharedCheck_2830_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2822_);
                            v___x_2824_ = crate::leanh::lean_box(0);
                            v_isShared_2825_ = v_isSharedCheck_2830_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_2832_ = crate::leanh::lean_ctor_get(v___x_2822_, 0);
                        v_isSharedCheck_2839_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2822_)) as u8;
                        if v_isSharedCheck_2839_ == 0 {
                            v___x_2834_ = v___x_2822_;
                            v_isShared_2835_ = v_isSharedCheck_2839_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2832_);
                            crate::leanh::lean_dec(v___x_2822_);
                            v___x_2834_ = crate::leanh::lean_box(0);
                            v_isShared_2835_ = v_isSharedCheck_2839_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            5 => {
                return v___x_2810_;
            }
            6 => {
                v___x_2826_ = crate::leanh::lean_box((v___x_2787_) as usize);
                if v_isShared_2825_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2824_, 0, v___x_2826_);
                    v___x_2828_ = v___x_2824_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2829_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2829_, 0, v___x_2826_);
                    v___x_2828_ = v_reuseFailAlloc_2829_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2828_;
            }
            8 => {
                if v_isShared_2835_ == 0 {
                    v___x_2837_ = v___x_2834_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2838_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2832_);
                    v___x_2837_ = v_reuseFailAlloc_2838_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2837_;
            }
            10 => {
                if v_isShared_2844_ == 0 {
                    v___x_2846_ = v___x_2843_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2847_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2841_);
                    v___x_2846_ = v_reuseFailAlloc_2847_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2846_;
            }
            12 => {
                if v_isShared_2852_ == 0 {
                    v___x_2854_ = v___x_2851_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2855_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
                    v___x_2854_ = v_reuseFailAlloc_2855_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2854_;
            }
            14 => {
                return v___x_2859_;
            }
            15 => {
                if v_isShared_2865_ == 0 {
                    v___x_2867_ = v___x_2864_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2868_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2862_);
                    v___x_2867_ = v_reuseFailAlloc_2868_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2867_;
            }
            17 => {
                if v_isShared_2874_ == 0 {
                    v___x_2876_ = v___x_2873_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2877_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
                    v___x_2876_ = v_reuseFailAlloc_2877_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2876_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___boxed(
    mut v_p_2879_: *mut crate::leanh::LeanObject,
    mut v_a_2880_: *mut crate::leanh::LeanObject,
    mut v_a_2881_: *mut crate::leanh::LeanObject,
    mut v_a_2882_: *mut crate::leanh::LeanObject,
    mut v_a_2883_: *mut crate::leanh::LeanObject,
    mut v_a_2884_: *mut crate::leanh::LeanObject,
    mut v_a_2885_: *mut crate::leanh::LeanObject,
    mut v_a_2886_: *mut crate::leanh::LeanObject,
    mut v_a_2887_: *mut crate::leanh::LeanObject,
    mut v_a_2888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2889_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg(
        v_p_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_,
        v_a_2887_,
    );
    crate::leanh::lean_dec(v_a_2887_);
    crate::leanh::lean_dec_ref(v_a_2886_);
    crate::leanh::lean_dec(v_a_2885_);
    crate::leanh::lean_dec_ref(v_a_2884_);
    crate::leanh::lean_dec(v_a_2883_);
    crate::leanh::lean_dec_ref(v_a_2882_);
    crate::leanh::lean_dec_ref(v_a_2881_);
    crate::leanh::lean_dec(v_a_2880_);
    crate::leanh::lean_dec_ref(v_p_2879_);
    return v_res_2889_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree(
    mut v_p_2890_: *mut crate::leanh::LeanObject,
    mut v_a_2891_: *mut crate::leanh::LeanObject,
    mut v_a_2892_: *mut crate::leanh::LeanObject,
    mut v_a_2893_: *mut crate::leanh::LeanObject,
    mut v_a_2894_: *mut crate::leanh::LeanObject,
    mut v_a_2895_: *mut crate::leanh::LeanObject,
    mut v_a_2896_: *mut crate::leanh::LeanObject,
    mut v_a_2897_: *mut crate::leanh::LeanObject,
    mut v_a_2898_: *mut crate::leanh::LeanObject,
    mut v_a_2899_: *mut crate::leanh::LeanObject,
    mut v_a_2900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2902_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg(
        v_p_2890_, v_a_2891_, v_a_2893_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_,
        v_a_2900_,
    );
    return v___x_2902_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___boxed(
    mut v_p_2903_: *mut crate::leanh::LeanObject,
    mut v_a_2904_: *mut crate::leanh::LeanObject,
    mut v_a_2905_: *mut crate::leanh::LeanObject,
    mut v_a_2906_: *mut crate::leanh::LeanObject,
    mut v_a_2907_: *mut crate::leanh::LeanObject,
    mut v_a_2908_: *mut crate::leanh::LeanObject,
    mut v_a_2909_: *mut crate::leanh::LeanObject,
    mut v_a_2910_: *mut crate::leanh::LeanObject,
    mut v_a_2911_: *mut crate::leanh::LeanObject,
    mut v_a_2912_: *mut crate::leanh::LeanObject,
    mut v_a_2913_: *mut crate::leanh::LeanObject,
    mut v_a_2914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2915_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree(
        v_p_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_,
        v_a_2911_, v_a_2912_, v_a_2913_,
    );
    crate::leanh::lean_dec(v_a_2913_);
    crate::leanh::lean_dec_ref(v_a_2912_);
    crate::leanh::lean_dec(v_a_2911_);
    crate::leanh::lean_dec_ref(v_a_2910_);
    crate::leanh::lean_dec(v_a_2909_);
    crate::leanh::lean_dec_ref(v_a_2908_);
    crate::leanh::lean_dec(v_a_2907_);
    crate::leanh::lean_dec_ref(v_a_2906_);
    crate::leanh::lean_dec(v_a_2905_);
    crate::leanh::lean_dec(v_a_2904_);
    crate::leanh::lean_dec_ref(v_p_2903_);
    return v_res_2915_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0(
    mut v_n_2916_: *mut crate::leanh::LeanObject,
    mut v_s_2917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_rings_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_2931_: u8 = 0;
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2934_: u8 = 0;
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2939_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_2918_ = crate::leanh::lean_ctor_get(v_s_2917_, 0);
                v_typeIdOf_2919_ = crate::leanh::lean_ctor_get(v_s_2917_, 1);
                v_exprToRingId_2920_ = crate::leanh::lean_ctor_get(v_s_2917_, 2);
                v_semirings_2921_ = crate::leanh::lean_ctor_get(v_s_2917_, 3);
                v_stypeIdOf_2922_ = crate::leanh::lean_ctor_get(v_s_2917_, 4);
                v_exprToSemiringId_2923_ = crate::leanh::lean_ctor_get(v_s_2917_, 5);
                v_ncRings_2924_ = crate::leanh::lean_ctor_get(v_s_2917_, 6);
                v_exprToNCRingId_2925_ = crate::leanh::lean_ctor_get(v_s_2917_, 7);
                v_nctypeIdOf_2926_ = crate::leanh::lean_ctor_get(v_s_2917_, 8);
                v_ncSemirings_2927_ = crate::leanh::lean_ctor_get(v_s_2917_, 9);
                v_exprToNCSemiringId_2928_ = crate::leanh::lean_ctor_get(v_s_2917_, 10);
                v_ncstypeIdOf_2929_ = crate::leanh::lean_ctor_get(v_s_2917_, 11);
                v_steps_2930_ = crate::leanh::lean_ctor_get(v_s_2917_, 12);
                v_reportedMaxDegreeIssue_2931_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_2917_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                v_isSharedCheck_2939_ = (!crate::leanh::lean_is_exclusive(v_s_2917_)) as u8;
                if v_isSharedCheck_2939_ == 0 {
                    v___x_2933_ = v_s_2917_;
                    v_isShared_2934_ = v_isSharedCheck_2939_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_steps_2930_);
                    crate::leanh::lean_inc(v_ncstypeIdOf_2929_);
                    crate::leanh::lean_inc(v_exprToNCSemiringId_2928_);
                    crate::leanh::lean_inc(v_ncSemirings_2927_);
                    crate::leanh::lean_inc(v_nctypeIdOf_2926_);
                    crate::leanh::lean_inc(v_exprToNCRingId_2925_);
                    crate::leanh::lean_inc(v_ncRings_2924_);
                    crate::leanh::lean_inc(v_exprToSemiringId_2923_);
                    crate::leanh::lean_inc(v_stypeIdOf_2922_);
                    crate::leanh::lean_inc(v_semirings_2921_);
                    crate::leanh::lean_inc(v_exprToRingId_2920_);
                    crate::leanh::lean_inc(v_typeIdOf_2919_);
                    crate::leanh::lean_inc(v_rings_2918_);
                    crate::leanh::lean_dec(v_s_2917_);
                    v___x_2933_ = crate::leanh::lean_box(0);
                    v_isShared_2934_ = v_isSharedCheck_2939_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2935_ = lean_nat_add(v_steps_2930_, v_n_2916_);
                crate::leanh::lean_dec(v_steps_2930_);
                if v_isShared_2934_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2933_, 12, v___x_2935_);
                    v___x_2937_ = v___x_2933_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2938_ = crate::leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_rings_2918_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2938_, 1, v_typeIdOf_2919_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2938_, 2, v_exprToRingId_2920_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2938_, 3, v_semirings_2921_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2938_, 4, v_stypeIdOf_2922_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2938_,
                        5,
                        v_exprToSemiringId_2923_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2938_, 6, v_ncRings_2924_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2938_, 7, v_exprToNCRingId_2925_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2938_, 8, v_nctypeIdOf_2926_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2938_, 9, v_ncSemirings_2927_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2938_,
                        10,
                        v_exprToNCSemiringId_2928_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2938_, 11, v_ncstypeIdOf_2929_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2938_, 12, v___x_2935_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2938_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                        v_reportedMaxDegreeIssue_2931_,
                    );
                    v___x_2937_ = v_reuseFailAlloc_2938_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2937_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0___boxed(
    mut v_n_2940_: *mut crate::leanh::LeanObject,
    mut v_s_2941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2942_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0(v_n_2940_, v_s_2941_);
    crate::leanh::lean_dec(v_n_2940_);
    return v_res_2942_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(
    mut v_n_2943_: *mut crate::leanh::LeanObject,
    mut v_a_2944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2946_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2946_, 0, v_n_2943_);
    v___x_2947_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
    v___x_2948_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2947_, v___f_2946_, v_a_2944_);
    return v___x_2948_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___boxed(
    mut v_n_2949_: *mut crate::leanh::LeanObject,
    mut v_a_2950_: *mut crate::leanh::LeanObject,
    mut v_a_2951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2952_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v_n_2949_, v_a_2950_);
    crate::leanh::lean_dec(v_a_2950_);
    return v_res_2952_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_incSteps(
    mut v_n_2953_: *mut crate::leanh::LeanObject,
    mut v_a_2954_: *mut crate::leanh::LeanObject,
    mut v_a_2955_: *mut crate::leanh::LeanObject,
    mut v_a_2956_: *mut crate::leanh::LeanObject,
    mut v_a_2957_: *mut crate::leanh::LeanObject,
    mut v_a_2958_: *mut crate::leanh::LeanObject,
    mut v_a_2959_: *mut crate::leanh::LeanObject,
    mut v_a_2960_: *mut crate::leanh::LeanObject,
    mut v_a_2961_: *mut crate::leanh::LeanObject,
    mut v_a_2962_: *mut crate::leanh::LeanObject,
    mut v_a_2963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2965_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v_n_2953_, v_a_2954_);
    return v___x_2965_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_incSteps___boxed(
    mut v_n_2966_: *mut crate::leanh::LeanObject,
    mut v_a_2967_: *mut crate::leanh::LeanObject,
    mut v_a_2968_: *mut crate::leanh::LeanObject,
    mut v_a_2969_: *mut crate::leanh::LeanObject,
    mut v_a_2970_: *mut crate::leanh::LeanObject,
    mut v_a_2971_: *mut crate::leanh::LeanObject,
    mut v_a_2972_: *mut crate::leanh::LeanObject,
    mut v_a_2973_: *mut crate::leanh::LeanObject,
    mut v_a_2974_: *mut crate::leanh::LeanObject,
    mut v_a_2975_: *mut crate::leanh::LeanObject,
    mut v_a_2976_: *mut crate::leanh::LeanObject,
    mut v_a_2977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2978_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps(
        v_n_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_,
        v_a_2974_, v_a_2975_, v_a_2976_,
    );
    crate::leanh::lean_dec(v_a_2976_);
    crate::leanh::lean_dec_ref(v_a_2975_);
    crate::leanh::lean_dec(v_a_2974_);
    crate::leanh::lean_dec_ref(v_a_2973_);
    crate::leanh::lean_dec(v_a_2972_);
    crate::leanh::lean_dec_ref(v_a_2971_);
    crate::leanh::lean_dec(v_a_2970_);
    crate::leanh::lean_dec_ref(v_a_2969_);
    crate::leanh::lean_dec(v_a_2968_);
    crate::leanh::lean_dec(v_a_2967_);
    return v_res_2978_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg(
    mut v_ringId_2979_: *mut crate::leanh::LeanObject,
    mut v_x_2980_: *mut crate::leanh::LeanObject,
    mut v_a_2981_: *mut crate::leanh::LeanObject,
    mut v_a_2982_: *mut crate::leanh::LeanObject,
    mut v_a_2983_: *mut crate::leanh::LeanObject,
    mut v_a_2984_: *mut crate::leanh::LeanObject,
    mut v_a_2985_: *mut crate::leanh::LeanObject,
    mut v_a_2986_: *mut crate::leanh::LeanObject,
    mut v_a_2987_: *mut crate::leanh::LeanObject,
    mut v_a_2988_: *mut crate::leanh::LeanObject,
    mut v_a_2989_: *mut crate::leanh::LeanObject,
    mut v_a_2990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2992_: u8 = 0;
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2992_ = 0;
    v___x_2993_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2993_, 0, v_ringId_2979_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2993_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2992_,
    );
    crate::leanh::lean_inc(v_a_2990_);
    crate::leanh::lean_inc_ref(v_a_2989_);
    crate::leanh::lean_inc(v_a_2988_);
    crate::leanh::lean_inc_ref(v_a_2987_);
    crate::leanh::lean_inc(v_a_2986_);
    crate::leanh::lean_inc_ref(v_a_2985_);
    crate::leanh::lean_inc(v_a_2984_);
    crate::leanh::lean_inc_ref(v_a_2983_);
    crate::leanh::lean_inc(v_a_2982_);
    crate::leanh::lean_inc(v_a_2981_);
    v___x_2994_ = crate::leanh::lean_apply_12(
        v_x_2980_,
        v___x_2993_,
        v_a_2981_,
        v_a_2982_,
        v_a_2983_,
        v_a_2984_,
        v_a_2985_,
        v_a_2986_,
        v_a_2987_,
        v_a_2988_,
        v_a_2989_,
        v_a_2990_,
        crate::leanh::lean_box(0),
    );
    return v___x_2994_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg___boxed(
    mut v_ringId_2995_: *mut crate::leanh::LeanObject,
    mut v_x_2996_: *mut crate::leanh::LeanObject,
    mut v_a_2997_: *mut crate::leanh::LeanObject,
    mut v_a_2998_: *mut crate::leanh::LeanObject,
    mut v_a_2999_: *mut crate::leanh::LeanObject,
    mut v_a_3000_: *mut crate::leanh::LeanObject,
    mut v_a_3001_: *mut crate::leanh::LeanObject,
    mut v_a_3002_: *mut crate::leanh::LeanObject,
    mut v_a_3003_: *mut crate::leanh::LeanObject,
    mut v_a_3004_: *mut crate::leanh::LeanObject,
    mut v_a_3005_: *mut crate::leanh::LeanObject,
    mut v_a_3006_: *mut crate::leanh::LeanObject,
    mut v_a_3007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3008_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg(
        v_ringId_2995_,
        v_x_2996_,
        v_a_2997_,
        v_a_2998_,
        v_a_2999_,
        v_a_3000_,
        v_a_3001_,
        v_a_3002_,
        v_a_3003_,
        v_a_3004_,
        v_a_3005_,
        v_a_3006_,
    );
    crate::leanh::lean_dec(v_a_3006_);
    crate::leanh::lean_dec_ref(v_a_3005_);
    crate::leanh::lean_dec(v_a_3004_);
    crate::leanh::lean_dec_ref(v_a_3003_);
    crate::leanh::lean_dec(v_a_3002_);
    crate::leanh::lean_dec_ref(v_a_3001_);
    crate::leanh::lean_dec(v_a_3000_);
    crate::leanh::lean_dec_ref(v_a_2999_);
    crate::leanh::lean_dec(v_a_2998_);
    crate::leanh::lean_dec(v_a_2997_);
    return v_res_3008_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_RingM_run(
    mut v_00_u03b1_3009_: *mut crate::leanh::LeanObject,
    mut v_ringId_3010_: *mut crate::leanh::LeanObject,
    mut v_x_3011_: *mut crate::leanh::LeanObject,
    mut v_a_3012_: *mut crate::leanh::LeanObject,
    mut v_a_3013_: *mut crate::leanh::LeanObject,
    mut v_a_3014_: *mut crate::leanh::LeanObject,
    mut v_a_3015_: *mut crate::leanh::LeanObject,
    mut v_a_3016_: *mut crate::leanh::LeanObject,
    mut v_a_3017_: *mut crate::leanh::LeanObject,
    mut v_a_3018_: *mut crate::leanh::LeanObject,
    mut v_a_3019_: *mut crate::leanh::LeanObject,
    mut v_a_3020_: *mut crate::leanh::LeanObject,
    mut v_a_3021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3023_: u8 = 0;
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3023_ = 0;
    v___x_3024_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3024_, 0, v_ringId_3010_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3024_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3023_,
    );
    crate::leanh::lean_inc(v_a_3021_);
    crate::leanh::lean_inc_ref(v_a_3020_);
    crate::leanh::lean_inc(v_a_3019_);
    crate::leanh::lean_inc_ref(v_a_3018_);
    crate::leanh::lean_inc(v_a_3017_);
    crate::leanh::lean_inc_ref(v_a_3016_);
    crate::leanh::lean_inc(v_a_3015_);
    crate::leanh::lean_inc_ref(v_a_3014_);
    crate::leanh::lean_inc(v_a_3013_);
    crate::leanh::lean_inc(v_a_3012_);
    v___x_3025_ = crate::leanh::lean_apply_12(
        v_x_3011_,
        v___x_3024_,
        v_a_3012_,
        v_a_3013_,
        v_a_3014_,
        v_a_3015_,
        v_a_3016_,
        v_a_3017_,
        v_a_3018_,
        v_a_3019_,
        v_a_3020_,
        v_a_3021_,
        crate::leanh::lean_box(0),
    );
    return v___x_3025_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_RingM_run___boxed(
    mut v_00_u03b1_3026_: *mut crate::leanh::LeanObject,
    mut v_ringId_3027_: *mut crate::leanh::LeanObject,
    mut v_x_3028_: *mut crate::leanh::LeanObject,
    mut v_a_3029_: *mut crate::leanh::LeanObject,
    mut v_a_3030_: *mut crate::leanh::LeanObject,
    mut v_a_3031_: *mut crate::leanh::LeanObject,
    mut v_a_3032_: *mut crate::leanh::LeanObject,
    mut v_a_3033_: *mut crate::leanh::LeanObject,
    mut v_a_3034_: *mut crate::leanh::LeanObject,
    mut v_a_3035_: *mut crate::leanh::LeanObject,
    mut v_a_3036_: *mut crate::leanh::LeanObject,
    mut v_a_3037_: *mut crate::leanh::LeanObject,
    mut v_a_3038_: *mut crate::leanh::LeanObject,
    mut v_a_3039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3040_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_run(
        v_00_u03b1_3026_,
        v_ringId_3027_,
        v_x_3028_,
        v_a_3029_,
        v_a_3030_,
        v_a_3031_,
        v_a_3032_,
        v_a_3033_,
        v_a_3034_,
        v_a_3035_,
        v_a_3036_,
        v_a_3037_,
        v_a_3038_,
    );
    crate::leanh::lean_dec(v_a_3038_);
    crate::leanh::lean_dec_ref(v_a_3037_);
    crate::leanh::lean_dec(v_a_3036_);
    crate::leanh::lean_dec_ref(v_a_3035_);
    crate::leanh::lean_dec(v_a_3034_);
    crate::leanh::lean_dec_ref(v_a_3033_);
    crate::leanh::lean_dec(v_a_3032_);
    crate::leanh::lean_dec_ref(v_a_3031_);
    crate::leanh::lean_dec(v_a_3030_);
    crate::leanh::lean_dec(v_a_3029_);
    return v_res_3040_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg(
    mut v_a_3041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ringId_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ringId_3043_ = crate::leanh::lean_ctor_get(v_a_3041_, 0);
    crate::leanh::lean_inc(v_ringId_3043_);
    v___x_3044_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3044_, 0, v_ringId_3043_);
    return v___x_3044_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg___boxed(
    mut v_a_3045_: *mut crate::leanh::LeanObject,
    mut v_a_3046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3047_ = l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg(v_a_3045_);
    crate::leanh::lean_dec_ref(v_a_3045_);
    return v_res_3047_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getRingId(
    mut v_a_3048_: *mut crate::leanh::LeanObject,
    mut v_a_3049_: *mut crate::leanh::LeanObject,
    mut v_a_3050_: *mut crate::leanh::LeanObject,
    mut v_a_3051_: *mut crate::leanh::LeanObject,
    mut v_a_3052_: *mut crate::leanh::LeanObject,
    mut v_a_3053_: *mut crate::leanh::LeanObject,
    mut v_a_3054_: *mut crate::leanh::LeanObject,
    mut v_a_3055_: *mut crate::leanh::LeanObject,
    mut v_a_3056_: *mut crate::leanh::LeanObject,
    mut v_a_3057_: *mut crate::leanh::LeanObject,
    mut v_a_3058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ringId_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ringId_3060_ = crate::leanh::lean_ctor_get(v_a_3048_, 0);
    crate::leanh::lean_inc(v_ringId_3060_);
    v___x_3061_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3061_, 0, v_ringId_3060_);
    return v___x_3061_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getRingId___boxed(
    mut v_a_3062_: *mut crate::leanh::LeanObject,
    mut v_a_3063_: *mut crate::leanh::LeanObject,
    mut v_a_3064_: *mut crate::leanh::LeanObject,
    mut v_a_3065_: *mut crate::leanh::LeanObject,
    mut v_a_3066_: *mut crate::leanh::LeanObject,
    mut v_a_3067_: *mut crate::leanh::LeanObject,
    mut v_a_3068_: *mut crate::leanh::LeanObject,
    mut v_a_3069_: *mut crate::leanh::LeanObject,
    mut v_a_3070_: *mut crate::leanh::LeanObject,
    mut v_a_3071_: *mut crate::leanh::LeanObject,
    mut v_a_3072_: *mut crate::leanh::LeanObject,
    mut v_a_3073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3074_ = l_Lean_Meta_Grind_Arith_CommRing_getRingId(
        v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_,
        v_a_3070_, v_a_3071_, v_a_3072_,
    );
    crate::leanh::lean_dec(v_a_3072_);
    crate::leanh::lean_dec_ref(v_a_3071_);
    crate::leanh::lean_dec(v_a_3070_);
    crate::leanh::lean_dec_ref(v_a_3069_);
    crate::leanh::lean_dec(v_a_3068_);
    crate::leanh::lean_dec_ref(v_a_3067_);
    crate::leanh::lean_dec(v_a_3066_);
    crate::leanh::lean_dec_ref(v_a_3065_);
    crate::leanh::lean_dec(v_a_3064_);
    crate::leanh::lean_dec(v_a_3063_);
    crate::leanh::lean_dec_ref(v_a_3062_);
    return v_res_3074_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0(
    mut v_e_3075_: *mut crate::leanh::LeanObject,
    mut v___y_3076_: *mut crate::leanh::LeanObject,
    mut v___y_3077_: *mut crate::leanh::LeanObject,
    mut v___y_3078_: *mut crate::leanh::LeanObject,
    mut v___y_3079_: *mut crate::leanh::LeanObject,
    mut v___y_3080_: *mut crate::leanh::LeanObject,
    mut v___y_3081_: *mut crate::leanh::LeanObject,
    mut v___y_3082_: *mut crate::leanh::LeanObject,
    mut v___y_3083_: *mut crate::leanh::LeanObject,
    mut v___y_3084_: *mut crate::leanh::LeanObject,
    mut v___y_3085_: *mut crate::leanh::LeanObject,
    mut v___y_3086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3088_ = l_Lean_Meta_Sym_canon(
        v_e_3075_,
        v___y_3081_,
        v___y_3082_,
        v___y_3083_,
        v___y_3084_,
        v___y_3085_,
        v___y_3086_,
    );
    if crate::leanh::lean_obj_tag(v___x_3088_) == 0 {
        let mut v_a_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_3089_ = crate::leanh::lean_ctor_get(v___x_3088_, 0);
        crate::leanh::lean_inc(v_a_3089_);
        crate::leanh::lean_dec_ref_known(v___x_3088_, 1);
        v___x_3090_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_3089_, v___y_3082_);
        return v___x_3090_;
    } else {
        return v___x_3088_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0___boxed(
    mut v_e_3091_: *mut crate::leanh::LeanObject,
    mut v___y_3092_: *mut crate::leanh::LeanObject,
    mut v___y_3093_: *mut crate::leanh::LeanObject,
    mut v___y_3094_: *mut crate::leanh::LeanObject,
    mut v___y_3095_: *mut crate::leanh::LeanObject,
    mut v___y_3096_: *mut crate::leanh::LeanObject,
    mut v___y_3097_: *mut crate::leanh::LeanObject,
    mut v___y_3098_: *mut crate::leanh::LeanObject,
    mut v___y_3099_: *mut crate::leanh::LeanObject,
    mut v___y_3100_: *mut crate::leanh::LeanObject,
    mut v___y_3101_: *mut crate::leanh::LeanObject,
    mut v___y_3102_: *mut crate::leanh::LeanObject,
    mut v___y_3103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3104_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0(
        v_e_3091_,
        v___y_3092_,
        v___y_3093_,
        v___y_3094_,
        v___y_3095_,
        v___y_3096_,
        v___y_3097_,
        v___y_3098_,
        v___y_3099_,
        v___y_3100_,
        v___y_3101_,
        v___y_3102_,
    );
    crate::leanh::lean_dec(v___y_3102_);
    crate::leanh::lean_dec_ref(v___y_3101_);
    crate::leanh::lean_dec(v___y_3100_);
    crate::leanh::lean_dec_ref(v___y_3099_);
    crate::leanh::lean_dec(v___y_3098_);
    crate::leanh::lean_dec_ref(v___y_3097_);
    crate::leanh::lean_dec(v___y_3096_);
    crate::leanh::lean_dec_ref(v___y_3095_);
    crate::leanh::lean_dec(v___y_3094_);
    crate::leanh::lean_dec(v___y_3093_);
    crate::leanh::lean_dec_ref(v___y_3092_);
    return v_res_3104_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1(
    mut v_e_3105_: *mut crate::leanh::LeanObject,
    mut v___y_3106_: *mut crate::leanh::LeanObject,
    mut v___y_3107_: *mut crate::leanh::LeanObject,
    mut v___y_3108_: *mut crate::leanh::LeanObject,
    mut v___y_3109_: *mut crate::leanh::LeanObject,
    mut v___y_3110_: *mut crate::leanh::LeanObject,
    mut v___y_3111_: *mut crate::leanh::LeanObject,
    mut v___y_3112_: *mut crate::leanh::LeanObject,
    mut v___y_3113_: *mut crate::leanh::LeanObject,
    mut v___y_3114_: *mut crate::leanh::LeanObject,
    mut v___y_3115_: *mut crate::leanh::LeanObject,
    mut v___y_3116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3118_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
        v_e_3105_,
        v___y_3113_,
        v___y_3114_,
        v___y_3115_,
        v___y_3116_,
    );
    return v___x_3118_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1___boxed(
    mut v_e_3119_: *mut crate::leanh::LeanObject,
    mut v___y_3120_: *mut crate::leanh::LeanObject,
    mut v___y_3121_: *mut crate::leanh::LeanObject,
    mut v___y_3122_: *mut crate::leanh::LeanObject,
    mut v___y_3123_: *mut crate::leanh::LeanObject,
    mut v___y_3124_: *mut crate::leanh::LeanObject,
    mut v___y_3125_: *mut crate::leanh::LeanObject,
    mut v___y_3126_: *mut crate::leanh::LeanObject,
    mut v___y_3127_: *mut crate::leanh::LeanObject,
    mut v___y_3128_: *mut crate::leanh::LeanObject,
    mut v___y_3129_: *mut crate::leanh::LeanObject,
    mut v___y_3130_: *mut crate::leanh::LeanObject,
    mut v___y_3131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3132_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1(
        v_e_3119_,
        v___y_3120_,
        v___y_3121_,
        v___y_3122_,
        v___y_3123_,
        v___y_3124_,
        v___y_3125_,
        v___y_3126_,
        v___y_3127_,
        v___y_3128_,
        v___y_3129_,
        v___y_3130_,
    );
    crate::leanh::lean_dec(v___y_3130_);
    crate::leanh::lean_dec_ref(v___y_3129_);
    crate::leanh::lean_dec(v___y_3128_);
    crate::leanh::lean_dec_ref(v___y_3127_);
    crate::leanh::lean_dec(v___y_3126_);
    crate::leanh::lean_dec_ref(v___y_3125_);
    crate::leanh::lean_dec(v___y_3124_);
    crate::leanh::lean_dec_ref(v___y_3123_);
    crate::leanh::lean_dec(v___y_3122_);
    crate::leanh::lean_dec(v___y_3121_);
    crate::leanh::lean_dec_ref(v___y_3120_);
    return v_res_3132_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(
    mut v_msgData_3139_: *mut crate::leanh::LeanObject,
    mut v___y_3140_: *mut crate::leanh::LeanObject,
    mut v___y_3141_: *mut crate::leanh::LeanObject,
    mut v___y_3142_: *mut crate::leanh::LeanObject,
    mut v___y_3143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3145_ = lean_st_ref_get(v___y_3143_);
    v_env_3146_ = crate::leanh::lean_ctor_get(v___x_3145_, 0);
    crate::leanh::lean_inc_ref(v_env_3146_);
    crate::leanh::lean_dec(v___x_3145_);
    v___x_3147_ = lean_st_ref_get(v___y_3141_);
    v_mctx_3148_ = crate::leanh::lean_ctor_get(v___x_3147_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3148_);
    crate::leanh::lean_dec(v___x_3147_);
    v_lctx_3149_ = crate::leanh::lean_ctor_get(v___y_3140_, 2);
    v_options_3150_ = crate::leanh::lean_ctor_get(v___y_3142_, 2);
    crate::leanh::lean_inc_ref(v_options_3150_);
    crate::leanh::lean_inc_ref(v_lctx_3149_);
    v___x_3151_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3151_, 0, v_env_3146_);
    crate::leanh::lean_ctor_set(v___x_3151_, 1, v_mctx_3148_);
    crate::leanh::lean_ctor_set(v___x_3151_, 2, v_lctx_3149_);
    crate::leanh::lean_ctor_set(v___x_3151_, 3, v_options_3150_);
    v___x_3152_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3152_, 0, v___x_3151_);
    crate::leanh::lean_ctor_set(v___x_3152_, 1, v_msgData_3139_);
    v___x_3153_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3153_, 0, v___x_3152_);
    return v___x_3153_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0___boxed(
    mut v_msgData_3154_: *mut crate::leanh::LeanObject,
    mut v___y_3155_: *mut crate::leanh::LeanObject,
    mut v___y_3156_: *mut crate::leanh::LeanObject,
    mut v___y_3157_: *mut crate::leanh::LeanObject,
    mut v___y_3158_: *mut crate::leanh::LeanObject,
    mut v___y_3159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3160_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(v_msgData_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
    crate::leanh::lean_dec(v___y_3158_);
    crate::leanh::lean_dec_ref(v___y_3157_);
    crate::leanh::lean_dec(v___y_3156_);
    crate::leanh::lean_dec_ref(v___y_3155_);
    return v_res_3160_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(
    mut v_msg_3161_: *mut crate::leanh::LeanObject,
    mut v___y_3162_: *mut crate::leanh::LeanObject,
    mut v___y_3163_: *mut crate::leanh::LeanObject,
    mut v___y_3164_: *mut crate::leanh::LeanObject,
    mut v___y_3165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3172_: u8 = 0;
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3177_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3167_ = crate::leanh::lean_ctor_get(v___y_3164_, 5);
                v___x_3168_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(v_msg_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
                v_a_3169_ = crate::leanh::lean_ctor_get(v___x_3168_, 0);
                v_isSharedCheck_3177_ = (!crate::leanh::lean_is_exclusive(v___x_3168_)) as u8;
                if v_isSharedCheck_3177_ == 0 {
                    v___x_3171_ = v___x_3168_;
                    v_isShared_3172_ = v_isSharedCheck_3177_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3169_);
                    crate::leanh::lean_dec(v___x_3168_);
                    v___x_3171_ = crate::leanh::lean_box(0);
                    v_isShared_3172_ = v_isSharedCheck_3177_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_3167_);
                v___x_3173_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3173_, 0, v_ref_3167_);
                crate::leanh::lean_ctor_set(v___x_3173_, 1, v_a_3169_);
                if v_isShared_3172_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3171_, 1);
                    crate::leanh::lean_ctor_set(v___x_3171_, 0, v___x_3173_);
                    v___x_3175_ = v___x_3171_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3176_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3176_, 0, v___x_3173_);
                    v___x_3175_ = v_reuseFailAlloc_3176_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3175_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg___boxed(
    mut v_msg_3178_: *mut crate::leanh::LeanObject,
    mut v___y_3179_: *mut crate::leanh::LeanObject,
    mut v___y_3180_: *mut crate::leanh::LeanObject,
    mut v___y_3181_: *mut crate::leanh::LeanObject,
    mut v___y_3182_: *mut crate::leanh::LeanObject,
    mut v___y_3183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3184_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v_msg_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
    crate::leanh::lean_dec(v___y_3182_);
    crate::leanh::lean_dec_ref(v___y_3181_);
    crate::leanh::lean_dec(v___y_3180_);
    crate::leanh::lean_dec_ref(v___y_3179_);
    return v_res_3184_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3186_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__0;
    v___x_3187_ = l_Lean_stringToMessageData(v___x_3186_);
    return v___x_3187_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
    mut v_a_3188_: *mut crate::leanh::LeanObject,
    mut v_a_3189_: *mut crate::leanh::LeanObject,
    mut v_a_3190_: *mut crate::leanh::LeanObject,
    mut v_a_3191_: *mut crate::leanh::LeanObject,
    mut v_a_3192_: *mut crate::leanh::LeanObject,
    mut v_a_3193_: *mut crate::leanh::LeanObject,
    mut v_a_3194_: *mut crate::leanh::LeanObject,
    mut v_a_3195_: *mut crate::leanh::LeanObject,
    mut v_a_3196_: *mut crate::leanh::LeanObject,
    mut v_a_3197_: *mut crate::leanh::LeanObject,
    mut v_a_3198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3204_: u8 = 0;
    let mut v_ringId_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rings_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: u8 = 0;
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3215_: u8 = 0;
    let mut v_a_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3219_: u8 = 0;
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3223_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3200_ =
                    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_3189_, v_a_3197_);
                if crate::leanh::lean_obj_tag(v___x_3200_) == 0 {
                    v_a_3201_ = crate::leanh::lean_ctor_get(v___x_3200_, 0);
                    v_isSharedCheck_3215_ = (!crate::leanh::lean_is_exclusive(v___x_3200_)) as u8;
                    if v_isSharedCheck_3215_ == 0 {
                        v___x_3203_ = v___x_3200_;
                        v_isShared_3204_ = v_isSharedCheck_3215_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3201_);
                        crate::leanh::lean_dec(v___x_3200_);
                        v___x_3203_ = crate::leanh::lean_box(0);
                        v_isShared_3204_ = v_isSharedCheck_3215_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3216_ = crate::leanh::lean_ctor_get(v___x_3200_, 0);
                    v_isSharedCheck_3223_ = (!crate::leanh::lean_is_exclusive(v___x_3200_)) as u8;
                    if v_isSharedCheck_3223_ == 0 {
                        v___x_3218_ = v___x_3200_;
                        v_isShared_3219_ = v_isSharedCheck_3223_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3216_);
                        crate::leanh::lean_dec(v___x_3200_);
                        v___x_3218_ = crate::leanh::lean_box(0);
                        v_isShared_3219_ = v_isSharedCheck_3223_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_ringId_3205_ = crate::leanh::lean_ctor_get(v_a_3188_, 0);
                v_rings_3206_ = crate::leanh::lean_ctor_get(v_a_3201_, 0);
                crate::leanh::lean_inc_ref(v_rings_3206_);
                crate::leanh::lean_dec(v_a_3201_);
                v___x_3207_ = lean_array_get_size(v_rings_3206_);
                v___x_3208_ = lean_nat_dec_lt(v_ringId_3205_, v___x_3207_);
                if v___x_3208_ == 0 {
                    crate::leanh::lean_dec_ref(v_rings_3206_);
                    crate::leanh::lean_del_object(v___x_3203_);
                    v___x_3209_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1,
                    );
                    v___x_3210_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v___x_3209_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_);
                    return v___x_3210_;
                } else {
                    v___x_3211_ = lean_array_fget(v_rings_3206_, v_ringId_3205_);
                    crate::leanh::lean_dec_ref(v_rings_3206_);
                    if v_isShared_3204_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3203_, 0, v___x_3211_);
                        v___x_3213_ = v___x_3203_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3214_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3211_);
                        v___x_3213_ = v_reuseFailAlloc_3214_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3213_;
            }
            3 => {
                if v_isShared_3219_ == 0 {
                    v___x_3221_ = v___x_3218_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3222_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
                    v___x_3221_ = v_reuseFailAlloc_3222_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3221_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___boxed(
    mut v_a_3224_: *mut crate::leanh::LeanObject,
    mut v_a_3225_: *mut crate::leanh::LeanObject,
    mut v_a_3226_: *mut crate::leanh::LeanObject,
    mut v_a_3227_: *mut crate::leanh::LeanObject,
    mut v_a_3228_: *mut crate::leanh::LeanObject,
    mut v_a_3229_: *mut crate::leanh::LeanObject,
    mut v_a_3230_: *mut crate::leanh::LeanObject,
    mut v_a_3231_: *mut crate::leanh::LeanObject,
    mut v_a_3232_: *mut crate::leanh::LeanObject,
    mut v_a_3233_: *mut crate::leanh::LeanObject,
    mut v_a_3234_: *mut crate::leanh::LeanObject,
    mut v_a_3235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3236_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
        v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_,
        v_a_3232_, v_a_3233_, v_a_3234_,
    );
    crate::leanh::lean_dec(v_a_3234_);
    crate::leanh::lean_dec_ref(v_a_3233_);
    crate::leanh::lean_dec(v_a_3232_);
    crate::leanh::lean_dec_ref(v_a_3231_);
    crate::leanh::lean_dec(v_a_3230_);
    crate::leanh::lean_dec_ref(v_a_3229_);
    crate::leanh::lean_dec(v_a_3228_);
    crate::leanh::lean_dec_ref(v_a_3227_);
    crate::leanh::lean_dec(v_a_3226_);
    crate::leanh::lean_dec(v_a_3225_);
    crate::leanh::lean_dec_ref(v_a_3224_);
    return v_res_3236_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0(
    mut v_00_u03b1_3237_: *mut crate::leanh::LeanObject,
    mut v_msg_3238_: *mut crate::leanh::LeanObject,
    mut v___y_3239_: *mut crate::leanh::LeanObject,
    mut v___y_3240_: *mut crate::leanh::LeanObject,
    mut v___y_3241_: *mut crate::leanh::LeanObject,
    mut v___y_3242_: *mut crate::leanh::LeanObject,
    mut v___y_3243_: *mut crate::leanh::LeanObject,
    mut v___y_3244_: *mut crate::leanh::LeanObject,
    mut v___y_3245_: *mut crate::leanh::LeanObject,
    mut v___y_3246_: *mut crate::leanh::LeanObject,
    mut v___y_3247_: *mut crate::leanh::LeanObject,
    mut v___y_3248_: *mut crate::leanh::LeanObject,
    mut v___y_3249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3251_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v_msg_3238_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
    return v___x_3251_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___boxed(
    mut v_00_u03b1_3252_: *mut crate::leanh::LeanObject,
    mut v_msg_3253_: *mut crate::leanh::LeanObject,
    mut v___y_3254_: *mut crate::leanh::LeanObject,
    mut v___y_3255_: *mut crate::leanh::LeanObject,
    mut v___y_3256_: *mut crate::leanh::LeanObject,
    mut v___y_3257_: *mut crate::leanh::LeanObject,
    mut v___y_3258_: *mut crate::leanh::LeanObject,
    mut v___y_3259_: *mut crate::leanh::LeanObject,
    mut v___y_3260_: *mut crate::leanh::LeanObject,
    mut v___y_3261_: *mut crate::leanh::LeanObject,
    mut v___y_3262_: *mut crate::leanh::LeanObject,
    mut v___y_3263_: *mut crate::leanh::LeanObject,
    mut v___y_3264_: *mut crate::leanh::LeanObject,
    mut v___y_3265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3266_ =
        l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0(
            v_00_u03b1_3252_,
            v_msg_3253_,
            v___y_3254_,
            v___y_3255_,
            v___y_3256_,
            v___y_3257_,
            v___y_3258_,
            v___y_3259_,
            v___y_3260_,
            v___y_3261_,
            v___y_3262_,
            v___y_3263_,
            v___y_3264_,
        );
    crate::leanh::lean_dec(v___y_3264_);
    crate::leanh::lean_dec_ref(v___y_3263_);
    crate::leanh::lean_dec(v___y_3262_);
    crate::leanh::lean_dec_ref(v___y_3261_);
    crate::leanh::lean_dec(v___y_3260_);
    crate::leanh::lean_dec_ref(v___y_3259_);
    crate::leanh::lean_dec(v___y_3258_);
    crate::leanh::lean_dec_ref(v___y_3257_);
    crate::leanh::lean_dec(v___y_3256_);
    crate::leanh::lean_dec(v___y_3255_);
    crate::leanh::lean_dec_ref(v___y_3254_);
    return v_res_3266_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0(
    mut v_ringId_3267_: *mut crate::leanh::LeanObject,
    mut v_f_3268_: *mut crate::leanh::LeanObject,
    mut v_s_3269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_rings_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_3283_: u8 = 0;
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: u8 = 0;
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3288_: u8 = 0;
    let mut v_v_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3297_: u8 = 0;
    let mut v_unused_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_3270_ = crate::leanh::lean_ctor_get(v_s_3269_, 0);
                v_typeIdOf_3271_ = crate::leanh::lean_ctor_get(v_s_3269_, 1);
                v_exprToRingId_3272_ = crate::leanh::lean_ctor_get(v_s_3269_, 2);
                v_semirings_3273_ = crate::leanh::lean_ctor_get(v_s_3269_, 3);
                v_stypeIdOf_3274_ = crate::leanh::lean_ctor_get(v_s_3269_, 4);
                v_exprToSemiringId_3275_ = crate::leanh::lean_ctor_get(v_s_3269_, 5);
                v_ncRings_3276_ = crate::leanh::lean_ctor_get(v_s_3269_, 6);
                v_exprToNCRingId_3277_ = crate::leanh::lean_ctor_get(v_s_3269_, 7);
                v_nctypeIdOf_3278_ = crate::leanh::lean_ctor_get(v_s_3269_, 8);
                v_ncSemirings_3279_ = crate::leanh::lean_ctor_get(v_s_3269_, 9);
                v_exprToNCSemiringId_3280_ = crate::leanh::lean_ctor_get(v_s_3269_, 10);
                v_ncstypeIdOf_3281_ = crate::leanh::lean_ctor_get(v_s_3269_, 11);
                v_steps_3282_ = crate::leanh::lean_ctor_get(v_s_3269_, 12);
                v_reportedMaxDegreeIssue_3283_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_3269_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                v___x_3284_ = lean_array_get_size(v_rings_3270_);
                v___x_3285_ = lean_nat_dec_lt(v_ringId_3267_, v___x_3284_);
                if v___x_3285_ == 0 {
                    crate::leanh::lean_dec_ref(v_f_3268_);
                    return v_s_3269_;
                } else {
                    crate::leanh::lean_inc(v_steps_3282_);
                    crate::leanh::lean_inc_ref(v_ncstypeIdOf_3281_);
                    crate::leanh::lean_inc_ref(v_exprToNCSemiringId_3280_);
                    crate::leanh::lean_inc_ref(v_ncSemirings_3279_);
                    crate::leanh::lean_inc_ref(v_nctypeIdOf_3278_);
                    crate::leanh::lean_inc_ref(v_exprToNCRingId_3277_);
                    crate::leanh::lean_inc_ref(v_ncRings_3276_);
                    crate::leanh::lean_inc_ref(v_exprToSemiringId_3275_);
                    crate::leanh::lean_inc_ref(v_stypeIdOf_3274_);
                    crate::leanh::lean_inc_ref(v_semirings_3273_);
                    crate::leanh::lean_inc_ref(v_exprToRingId_3272_);
                    crate::leanh::lean_inc_ref(v_typeIdOf_3271_);
                    crate::leanh::lean_inc_ref(v_rings_3270_);
                    v_isSharedCheck_3297_ = (!crate::leanh::lean_is_exclusive(v_s_3269_)) as u8;
                    if v_isSharedCheck_3297_ == 0 {
                        v_unused_3298_ = crate::leanh::lean_ctor_get(v_s_3269_, 12);
                        crate::leanh::lean_dec(v_unused_3298_);
                        v_unused_3299_ = crate::leanh::lean_ctor_get(v_s_3269_, 11);
                        crate::leanh::lean_dec(v_unused_3299_);
                        v_unused_3300_ = crate::leanh::lean_ctor_get(v_s_3269_, 10);
                        crate::leanh::lean_dec(v_unused_3300_);
                        v_unused_3301_ = crate::leanh::lean_ctor_get(v_s_3269_, 9);
                        crate::leanh::lean_dec(v_unused_3301_);
                        v_unused_3302_ = crate::leanh::lean_ctor_get(v_s_3269_, 8);
                        crate::leanh::lean_dec(v_unused_3302_);
                        v_unused_3303_ = crate::leanh::lean_ctor_get(v_s_3269_, 7);
                        crate::leanh::lean_dec(v_unused_3303_);
                        v_unused_3304_ = crate::leanh::lean_ctor_get(v_s_3269_, 6);
                        crate::leanh::lean_dec(v_unused_3304_);
                        v_unused_3305_ = crate::leanh::lean_ctor_get(v_s_3269_, 5);
                        crate::leanh::lean_dec(v_unused_3305_);
                        v_unused_3306_ = crate::leanh::lean_ctor_get(v_s_3269_, 4);
                        crate::leanh::lean_dec(v_unused_3306_);
                        v_unused_3307_ = crate::leanh::lean_ctor_get(v_s_3269_, 3);
                        crate::leanh::lean_dec(v_unused_3307_);
                        v_unused_3308_ = crate::leanh::lean_ctor_get(v_s_3269_, 2);
                        crate::leanh::lean_dec(v_unused_3308_);
                        v_unused_3309_ = crate::leanh::lean_ctor_get(v_s_3269_, 1);
                        crate::leanh::lean_dec(v_unused_3309_);
                        v_unused_3310_ = crate::leanh::lean_ctor_get(v_s_3269_, 0);
                        crate::leanh::lean_dec(v_unused_3310_);
                        v___x_3287_ = v_s_3269_;
                        v_isShared_3288_ = v_isSharedCheck_3297_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_s_3269_);
                        v___x_3287_ = crate::leanh::lean_box(0);
                        v_isShared_3288_ = v_isSharedCheck_3297_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3289_ = lean_array_fget(v_rings_3270_, v_ringId_3267_);
                v___x_3290_ = crate::leanh::lean_box(0);
                v_xs_x27_3291_ = lean_array_fset(v_rings_3270_, v_ringId_3267_, v___x_3290_);
                v___x_3292_ = crate::leanh::lean_apply_1(v_f_3268_, v_v_3289_);
                v___x_3293_ = lean_array_fset(v_xs_x27_3291_, v_ringId_3267_, v___x_3292_);
                if v_isShared_3288_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3287_, 0, v___x_3293_);
                    v___x_3295_ = v___x_3287_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3296_ = crate::leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___x_3293_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 1, v_typeIdOf_3271_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 2, v_exprToRingId_3272_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 3, v_semirings_3273_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 4, v_stypeIdOf_3274_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3296_,
                        5,
                        v_exprToSemiringId_3275_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 6, v_ncRings_3276_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 7, v_exprToNCRingId_3277_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 8, v_nctypeIdOf_3278_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 9, v_ncSemirings_3279_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3296_,
                        10,
                        v_exprToNCSemiringId_3280_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 11, v_ncstypeIdOf_3281_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 12, v_steps_3282_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3296_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                        v_reportedMaxDegreeIssue_3283_,
                    );
                    v___x_3295_ = v_reuseFailAlloc_3296_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3295_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0___boxed(
    mut v_ringId_3311_: *mut crate::leanh::LeanObject,
    mut v_f_3312_: *mut crate::leanh::LeanObject,
    mut v_s_3313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3314_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0(
        v_ringId_3311_,
        v_f_3312_,
        v_s_3313_,
    );
    crate::leanh::lean_dec(v_ringId_3311_);
    return v_res_3314_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(
    mut v_f_3315_: *mut crate::leanh::LeanObject,
    mut v_a_3316_: *mut crate::leanh::LeanObject,
    mut v_a_3317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ringId_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ringId_3319_ = crate::leanh::lean_ctor_get(v_a_3316_, 0);
    crate::leanh::lean_inc(v_ringId_3319_);
    v___f_3320_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3320_, 0, v_ringId_3319_);
    crate::leanh::lean_closure_set(v___f_3320_, 1, v_f_3315_);
    v___x_3321_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
    v___x_3322_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3321_, v___f_3320_, v_a_3317_);
    return v___x_3322_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___boxed(
    mut v_f_3323_: *mut crate::leanh::LeanObject,
    mut v_a_3324_: *mut crate::leanh::LeanObject,
    mut v_a_3325_: *mut crate::leanh::LeanObject,
    mut v_a_3326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3327_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(
        v_f_3323_, v_a_3324_, v_a_3325_,
    );
    crate::leanh::lean_dec(v_a_3325_);
    crate::leanh::lean_dec_ref(v_a_3324_);
    return v_res_3327_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing(
    mut v_f_3328_: *mut crate::leanh::LeanObject,
    mut v_a_3329_: *mut crate::leanh::LeanObject,
    mut v_a_3330_: *mut crate::leanh::LeanObject,
    mut v_a_3331_: *mut crate::leanh::LeanObject,
    mut v_a_3332_: *mut crate::leanh::LeanObject,
    mut v_a_3333_: *mut crate::leanh::LeanObject,
    mut v_a_3334_: *mut crate::leanh::LeanObject,
    mut v_a_3335_: *mut crate::leanh::LeanObject,
    mut v_a_3336_: *mut crate::leanh::LeanObject,
    mut v_a_3337_: *mut crate::leanh::LeanObject,
    mut v_a_3338_: *mut crate::leanh::LeanObject,
    mut v_a_3339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3341_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(
        v_f_3328_, v_a_3329_, v_a_3330_,
    );
    return v___x_3341_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___boxed(
    mut v_f_3342_: *mut crate::leanh::LeanObject,
    mut v_a_3343_: *mut crate::leanh::LeanObject,
    mut v_a_3344_: *mut crate::leanh::LeanObject,
    mut v_a_3345_: *mut crate::leanh::LeanObject,
    mut v_a_3346_: *mut crate::leanh::LeanObject,
    mut v_a_3347_: *mut crate::leanh::LeanObject,
    mut v_a_3348_: *mut crate::leanh::LeanObject,
    mut v_a_3349_: *mut crate::leanh::LeanObject,
    mut v_a_3350_: *mut crate::leanh::LeanObject,
    mut v_a_3351_: *mut crate::leanh::LeanObject,
    mut v_a_3352_: *mut crate::leanh::LeanObject,
    mut v_a_3353_: *mut crate::leanh::LeanObject,
    mut v_a_3354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3355_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing(
        v_f_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_,
        v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_,
    );
    crate::leanh::lean_dec(v_a_3353_);
    crate::leanh::lean_dec_ref(v_a_3352_);
    crate::leanh::lean_dec(v_a_3351_);
    crate::leanh::lean_dec_ref(v_a_3350_);
    crate::leanh::lean_dec(v_a_3349_);
    crate::leanh::lean_dec_ref(v_a_3348_);
    crate::leanh::lean_dec(v_a_3347_);
    crate::leanh::lean_dec_ref(v_a_3346_);
    crate::leanh::lean_dec(v_a_3345_);
    crate::leanh::lean_dec(v_a_3344_);
    crate::leanh::lean_dec_ref(v_a_3343_);
    return v_res_3355_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3357_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__0;
    v___x_3358_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___boxed as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_3359_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3359_, 0, v___x_3358_);
    crate::leanh::lean_ctor_set(v___x_3359_, 1, v___x_3357_);
    return v___x_3359_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3360_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1,
    );
    return v___x_3360_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg(
    mut v_x_3361_: *mut crate::leanh::LeanObject,
    mut v_a_3362_: *mut crate::leanh::LeanObject,
    mut v_a_3363_: *mut crate::leanh::LeanObject,
    mut v_a_3364_: *mut crate::leanh::LeanObject,
    mut v_a_3365_: *mut crate::leanh::LeanObject,
    mut v_a_3366_: *mut crate::leanh::LeanObject,
    mut v_a_3367_: *mut crate::leanh::LeanObject,
    mut v_a_3368_: *mut crate::leanh::LeanObject,
    mut v_a_3369_: *mut crate::leanh::LeanObject,
    mut v_a_3370_: *mut crate::leanh::LeanObject,
    mut v_a_3371_: *mut crate::leanh::LeanObject,
    mut v_a_3372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ringId_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: u8 = 0;
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ringId_3374_ = crate::leanh::lean_ctor_get(v_a_3362_, 0);
    v___x_3375_ = 1;
    crate::leanh::lean_inc(v_ringId_3374_);
    v___x_3376_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3376_, 0, v_ringId_3374_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3376_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3375_,
    );
    crate::leanh::lean_inc(v_a_3372_);
    crate::leanh::lean_inc_ref(v_a_3371_);
    crate::leanh::lean_inc(v_a_3370_);
    crate::leanh::lean_inc_ref(v_a_3369_);
    crate::leanh::lean_inc(v_a_3368_);
    crate::leanh::lean_inc_ref(v_a_3367_);
    crate::leanh::lean_inc(v_a_3366_);
    crate::leanh::lean_inc_ref(v_a_3365_);
    crate::leanh::lean_inc(v_a_3364_);
    crate::leanh::lean_inc(v_a_3363_);
    v___x_3377_ = crate::leanh::lean_apply_12(
        v_x_3361_,
        v___x_3376_,
        v_a_3363_,
        v_a_3364_,
        v_a_3365_,
        v_a_3366_,
        v_a_3367_,
        v_a_3368_,
        v_a_3369_,
        v_a_3370_,
        v_a_3371_,
        v_a_3372_,
        crate::leanh::lean_box(0),
    );
    return v___x_3377_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg___boxed(
    mut v_x_3378_: *mut crate::leanh::LeanObject,
    mut v_a_3379_: *mut crate::leanh::LeanObject,
    mut v_a_3380_: *mut crate::leanh::LeanObject,
    mut v_a_3381_: *mut crate::leanh::LeanObject,
    mut v_a_3382_: *mut crate::leanh::LeanObject,
    mut v_a_3383_: *mut crate::leanh::LeanObject,
    mut v_a_3384_: *mut crate::leanh::LeanObject,
    mut v_a_3385_: *mut crate::leanh::LeanObject,
    mut v_a_3386_: *mut crate::leanh::LeanObject,
    mut v_a_3387_: *mut crate::leanh::LeanObject,
    mut v_a_3388_: *mut crate::leanh::LeanObject,
    mut v_a_3389_: *mut crate::leanh::LeanObject,
    mut v_a_3390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3391_ = l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg(
        v_x_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_,
        v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_,
    );
    crate::leanh::lean_dec(v_a_3389_);
    crate::leanh::lean_dec_ref(v_a_3388_);
    crate::leanh::lean_dec(v_a_3387_);
    crate::leanh::lean_dec_ref(v_a_3386_);
    crate::leanh::lean_dec(v_a_3385_);
    crate::leanh::lean_dec_ref(v_a_3384_);
    crate::leanh::lean_dec(v_a_3383_);
    crate::leanh::lean_dec_ref(v_a_3382_);
    crate::leanh::lean_dec(v_a_3381_);
    crate::leanh::lean_dec(v_a_3380_);
    crate::leanh::lean_dec_ref(v_a_3379_);
    return v_res_3391_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd(
    mut v_00_u03b1_3392_: *mut crate::leanh::LeanObject,
    mut v_x_3393_: *mut crate::leanh::LeanObject,
    mut v_a_3394_: *mut crate::leanh::LeanObject,
    mut v_a_3395_: *mut crate::leanh::LeanObject,
    mut v_a_3396_: *mut crate::leanh::LeanObject,
    mut v_a_3397_: *mut crate::leanh::LeanObject,
    mut v_a_3398_: *mut crate::leanh::LeanObject,
    mut v_a_3399_: *mut crate::leanh::LeanObject,
    mut v_a_3400_: *mut crate::leanh::LeanObject,
    mut v_a_3401_: *mut crate::leanh::LeanObject,
    mut v_a_3402_: *mut crate::leanh::LeanObject,
    mut v_a_3403_: *mut crate::leanh::LeanObject,
    mut v_a_3404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ringId_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: u8 = 0;
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ringId_3406_ = crate::leanh::lean_ctor_get(v_a_3394_, 0);
    v___x_3407_ = 1;
    crate::leanh::lean_inc(v_ringId_3406_);
    v___x_3408_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3408_, 0, v_ringId_3406_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3408_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3407_,
    );
    crate::leanh::lean_inc(v_a_3404_);
    crate::leanh::lean_inc_ref(v_a_3403_);
    crate::leanh::lean_inc(v_a_3402_);
    crate::leanh::lean_inc_ref(v_a_3401_);
    crate::leanh::lean_inc(v_a_3400_);
    crate::leanh::lean_inc_ref(v_a_3399_);
    crate::leanh::lean_inc(v_a_3398_);
    crate::leanh::lean_inc_ref(v_a_3397_);
    crate::leanh::lean_inc(v_a_3396_);
    crate::leanh::lean_inc(v_a_3395_);
    v___x_3409_ = crate::leanh::lean_apply_12(
        v_x_3393_,
        v___x_3408_,
        v_a_3395_,
        v_a_3396_,
        v_a_3397_,
        v_a_3398_,
        v_a_3399_,
        v_a_3400_,
        v_a_3401_,
        v_a_3402_,
        v_a_3403_,
        v_a_3404_,
        crate::leanh::lean_box(0),
    );
    return v___x_3409_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___boxed(
    mut v_00_u03b1_3410_: *mut crate::leanh::LeanObject,
    mut v_x_3411_: *mut crate::leanh::LeanObject,
    mut v_a_3412_: *mut crate::leanh::LeanObject,
    mut v_a_3413_: *mut crate::leanh::LeanObject,
    mut v_a_3414_: *mut crate::leanh::LeanObject,
    mut v_a_3415_: *mut crate::leanh::LeanObject,
    mut v_a_3416_: *mut crate::leanh::LeanObject,
    mut v_a_3417_: *mut crate::leanh::LeanObject,
    mut v_a_3418_: *mut crate::leanh::LeanObject,
    mut v_a_3419_: *mut crate::leanh::LeanObject,
    mut v_a_3420_: *mut crate::leanh::LeanObject,
    mut v_a_3421_: *mut crate::leanh::LeanObject,
    mut v_a_3422_: *mut crate::leanh::LeanObject,
    mut v_a_3423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3424_ = l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd(
        v_00_u03b1_3410_,
        v_x_3411_,
        v_a_3412_,
        v_a_3413_,
        v_a_3414_,
        v_a_3415_,
        v_a_3416_,
        v_a_3417_,
        v_a_3418_,
        v_a_3419_,
        v_a_3420_,
        v_a_3421_,
        v_a_3422_,
    );
    crate::leanh::lean_dec(v_a_3422_);
    crate::leanh::lean_dec_ref(v_a_3421_);
    crate::leanh::lean_dec(v_a_3420_);
    crate::leanh::lean_dec_ref(v_a_3419_);
    crate::leanh::lean_dec(v_a_3418_);
    crate::leanh::lean_dec_ref(v_a_3417_);
    crate::leanh::lean_dec(v_a_3416_);
    crate::leanh::lean_dec_ref(v_a_3415_);
    crate::leanh::lean_dec(v_a_3414_);
    crate::leanh::lean_dec(v_a_3413_);
    crate::leanh::lean_dec_ref(v_a_3412_);
    return v_res_3424_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(
    mut v_a_3425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_checkCoeffDvd_3427_: u8 = 0;
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_checkCoeffDvd_3427_ = crate::leanh::lean_ctor_get_uint8(
        v_a_3425_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    v___x_3428_ = crate::leanh::lean_box((v_checkCoeffDvd_3427_) as usize);
    v___x_3429_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3429_, 0, v___x_3428_);
    return v___x_3429_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg___boxed(
    mut v_a_3430_: *mut crate::leanh::LeanObject,
    mut v_a_3431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3432_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(v_a_3430_);
    crate::leanh::lean_dec_ref(v_a_3430_);
    return v_res_3432_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd(
    mut v_a_3433_: *mut crate::leanh::LeanObject,
    mut v_a_3434_: *mut crate::leanh::LeanObject,
    mut v_a_3435_: *mut crate::leanh::LeanObject,
    mut v_a_3436_: *mut crate::leanh::LeanObject,
    mut v_a_3437_: *mut crate::leanh::LeanObject,
    mut v_a_3438_: *mut crate::leanh::LeanObject,
    mut v_a_3439_: *mut crate::leanh::LeanObject,
    mut v_a_3440_: *mut crate::leanh::LeanObject,
    mut v_a_3441_: *mut crate::leanh::LeanObject,
    mut v_a_3442_: *mut crate::leanh::LeanObject,
    mut v_a_3443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3445_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(v_a_3433_);
    return v___x_3445_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___boxed(
    mut v_a_3446_: *mut crate::leanh::LeanObject,
    mut v_a_3447_: *mut crate::leanh::LeanObject,
    mut v_a_3448_: *mut crate::leanh::LeanObject,
    mut v_a_3449_: *mut crate::leanh::LeanObject,
    mut v_a_3450_: *mut crate::leanh::LeanObject,
    mut v_a_3451_: *mut crate::leanh::LeanObject,
    mut v_a_3452_: *mut crate::leanh::LeanObject,
    mut v_a_3453_: *mut crate::leanh::LeanObject,
    mut v_a_3454_: *mut crate::leanh::LeanObject,
    mut v_a_3455_: *mut crate::leanh::LeanObject,
    mut v_a_3456_: *mut crate::leanh::LeanObject,
    mut v_a_3457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3458_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd(
        v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_,
        v_a_3454_, v_a_3455_, v_a_3456_,
    );
    crate::leanh::lean_dec(v_a_3456_);
    crate::leanh::lean_dec_ref(v_a_3455_);
    crate::leanh::lean_dec(v_a_3454_);
    crate::leanh::lean_dec_ref(v_a_3453_);
    crate::leanh::lean_dec(v_a_3452_);
    crate::leanh::lean_dec_ref(v_a_3451_);
    crate::leanh::lean_dec(v_a_3450_);
    crate::leanh::lean_dec_ref(v_a_3449_);
    crate::leanh::lean_dec(v_a_3448_);
    crate::leanh::lean_dec(v_a_3447_);
    crate::leanh::lean_dec_ref(v_a_3446_);
    return v_res_3458_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_keys_3459_: *mut crate::leanh::LeanObject,
    mut v_vals_3460_: *mut crate::leanh::LeanObject,
    mut v_i_3461_: *mut crate::leanh::LeanObject,
    mut v_k_3462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: u8 = 0;
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: u8 = 0;
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3463_ = lean_array_get_size(v_keys_3459_);
                v___x_3464_ = lean_nat_dec_lt(v_i_3461_, v___x_3463_);
                if v___x_3464_ == 0 {
                    crate::leanh::lean_dec(v_i_3461_);
                    v___x_3465_ = crate::leanh::lean_box(0);
                    return v___x_3465_;
                } else {
                    v_k_x27_3466_ = lean_array_fget_borrowed(v_keys_3459_, v_i_3461_);
                    v___x_3467_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_3462_,
                            v_k_x27_3466_,
                        );
                    if v___x_3467_ == 0 {
                        v___x_3468_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3469_ = lean_nat_add(v_i_3461_, v___x_3468_);
                        crate::leanh::lean_dec(v_i_3461_);
                        v_i_3461_ = v___x_3469_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3471_ = lean_array_fget_borrowed(v_vals_3460_, v_i_3461_);
                        crate::leanh::lean_dec(v_i_3461_);
                        crate::leanh::lean_inc(v___x_3471_);
                        v___x_3472_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3472_, 0, v___x_3471_);
                        return v___x_3472_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_3473_: *mut crate::leanh::LeanObject,
    mut v_vals_3474_: *mut crate::leanh::LeanObject,
    mut v_i_3475_: *mut crate::leanh::LeanObject,
    mut v_k_3476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3477_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_3473_, v_vals_3474_, v_i_3475_, v_k_3476_);
    crate::leanh::lean_dec_ref(v_k_3476_);
    crate::leanh::lean_dec_ref(v_vals_3474_);
    crate::leanh::lean_dec_ref(v_keys_3473_);
    return v_res_3477_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_3478_: usize = 0;
    let mut v___x_3479_: usize = 0;
    let mut v___x_3480_: usize = 0;
    v___x_3478_ = 5usize;
    v___x_3479_ = 1usize;
    v___x_3480_ = lean_usize_shift_left(v___x_3479_, v___x_3478_);
    return v___x_3480_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_3481_: usize = 0;
    let mut v___x_3482_: usize = 0;
    let mut v___x_3483_: usize = 0;
    v___x_3481_ = 1usize;
    v___x_3482_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__0);
    v___x_3483_ = lean_usize_sub(v___x_3482_, v___x_3481_);
    return v___x_3483_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(
    mut v_x_3484_: *mut crate::leanh::LeanObject,
    mut v_x_3485_: usize,
    mut v_x_3486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: usize = 0;
    let mut v___x_3490_: usize = 0;
    let mut v___x_3491_: usize = 0;
    let mut v_j_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: u8 = 0;
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: usize = 0;
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3484_) == 0 {
                    v_es_3487_ = crate::leanh::lean_ctor_get(v_x_3484_, 0);
                    v___x_3488_ = crate::leanh::lean_box(2);
                    v___x_3489_ = 5usize;
                    v___x_3490_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_3491_ = lean_usize_land(v_x_3485_, v___x_3490_);
                    v_j_3492_ = lean_usize_to_nat(v___x_3491_);
                    v___x_3493_ = lean_array_get_borrowed(v___x_3488_, v_es_3487_, v_j_3492_);
                    crate::leanh::lean_dec(v_j_3492_);
                    match crate::leanh::lean_obj_tag(v___x_3493_) {
                        0 => {
                            v_key_3494_ = crate::leanh::lean_ctor_get(v___x_3493_, 0);
                            v_val_3495_ = crate::leanh::lean_ctor_get(v___x_3493_, 1);
                            v___x_3496_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_3486_, v_key_3494_);
                            if v___x_3496_ == 0 {
                                v___x_3497_ = crate::leanh::lean_box(0);
                                return v___x_3497_;
                            } else {
                                crate::leanh::lean_inc(v_val_3495_);
                                v___x_3498_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3498_, 0, v_val_3495_);
                                return v___x_3498_;
                            }
                        }
                        1 => {
                            v_node_3499_ = crate::leanh::lean_ctor_get(v___x_3493_, 0);
                            v___x_3500_ = lean_usize_shift_right(v_x_3485_, v___x_3489_);
                            v_x_3484_ = v_node_3499_;
                            v_x_3485_ = v___x_3500_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3502_ = crate::leanh::lean_box(0);
                            return v___x_3502_;
                        }
                    }
                } else {
                    v_ks_3503_ = crate::leanh::lean_ctor_get(v_x_3484_, 0);
                    v_vs_3504_ = crate::leanh::lean_ctor_get(v_x_3484_, 1);
                    v___x_3505_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3506_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_3503_, v_vs_3504_, v___x_3505_, v_x_3486_);
                    return v___x_3506_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_3507_: *mut crate::leanh::LeanObject,
    mut v_x_3508_: *mut crate::leanh::LeanObject,
    mut v_x_3509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_867__boxed_3510_: usize = 0;
    let mut v_res_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_867__boxed_3510_ = crate::leanh::lean_unbox_usize(v_x_3508_);
    crate::leanh::lean_dec(v_x_3508_);
    v_res_3511_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_3507_, v_x_867__boxed_3510_, v_x_3509_);
    crate::leanh::lean_dec_ref(v_x_3509_);
    crate::leanh::lean_dec_ref(v_x_3507_);
    return v_res_3511_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(
    mut v_x_3512_: *mut crate::leanh::LeanObject,
    mut v_x_3513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3514_: u64 = 0;
    let mut v___x_3515_: usize = 0;
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3514_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_3513_);
    v___x_3515_ = lean_uint64_to_usize(v___x_3514_);
    v___x_3516_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_3512_, v___x_3515_, v_x_3513_);
    return v___x_3516_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg___boxed(
    mut v_x_3517_: *mut crate::leanh::LeanObject,
    mut v_x_3518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3519_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_3517_, v_x_3518_);
    crate::leanh::lean_dec_ref(v_x_3518_);
    crate::leanh::lean_dec_ref(v_x_3517_);
    return v_res_3519_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(
    mut v_e_3520_: *mut crate::leanh::LeanObject,
    mut v_a_3521_: *mut crate::leanh::LeanObject,
    mut v_a_3522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3528_: u8 = 0;
    let mut v_exprToRingId_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3534_: u8 = 0;
    let mut v_a_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3538_: u8 = 0;
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3542_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3524_ =
                    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_3521_, v_a_3522_);
                if crate::leanh::lean_obj_tag(v___x_3524_) == 0 {
                    v_a_3525_ = crate::leanh::lean_ctor_get(v___x_3524_, 0);
                    v_isSharedCheck_3534_ = (!crate::leanh::lean_is_exclusive(v___x_3524_)) as u8;
                    if v_isSharedCheck_3534_ == 0 {
                        v___x_3527_ = v___x_3524_;
                        v_isShared_3528_ = v_isSharedCheck_3534_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3525_);
                        crate::leanh::lean_dec(v___x_3524_);
                        v___x_3527_ = crate::leanh::lean_box(0);
                        v_isShared_3528_ = v_isSharedCheck_3534_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3535_ = crate::leanh::lean_ctor_get(v___x_3524_, 0);
                    v_isSharedCheck_3542_ = (!crate::leanh::lean_is_exclusive(v___x_3524_)) as u8;
                    if v_isSharedCheck_3542_ == 0 {
                        v___x_3537_ = v___x_3524_;
                        v_isShared_3538_ = v_isSharedCheck_3542_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3535_);
                        crate::leanh::lean_dec(v___x_3524_);
                        v___x_3537_ = crate::leanh::lean_box(0);
                        v_isShared_3538_ = v_isSharedCheck_3542_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_exprToRingId_3529_ = crate::leanh::lean_ctor_get(v_a_3525_, 2);
                crate::leanh::lean_inc_ref(v_exprToRingId_3529_);
                crate::leanh::lean_dec(v_a_3525_);
                v___x_3530_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_exprToRingId_3529_, v_e_3520_);
                crate::leanh::lean_dec_ref(v_exprToRingId_3529_);
                if v_isShared_3528_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3527_, 0, v___x_3530_);
                    v___x_3532_ = v___x_3527_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3533_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3530_);
                    v___x_3532_ = v_reuseFailAlloc_3533_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3532_;
            }
            3 => {
                if v_isShared_3538_ == 0 {
                    v___x_3540_ = v___x_3537_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3541_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_a_3535_);
                    v___x_3540_ = v_reuseFailAlloc_3541_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3540_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg___boxed(
    mut v_e_3543_: *mut crate::leanh::LeanObject,
    mut v_a_3544_: *mut crate::leanh::LeanObject,
    mut v_a_3545_: *mut crate::leanh::LeanObject,
    mut v_a_3546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3547_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(
        v_e_3543_, v_a_3544_, v_a_3545_,
    );
    crate::leanh::lean_dec_ref(v_a_3545_);
    crate::leanh::lean_dec(v_a_3544_);
    crate::leanh::lean_dec_ref(v_e_3543_);
    return v_res_3547_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(
    mut v_e_3548_: *mut crate::leanh::LeanObject,
    mut v_a_3549_: *mut crate::leanh::LeanObject,
    mut v_a_3550_: *mut crate::leanh::LeanObject,
    mut v_a_3551_: *mut crate::leanh::LeanObject,
    mut v_a_3552_: *mut crate::leanh::LeanObject,
    mut v_a_3553_: *mut crate::leanh::LeanObject,
    mut v_a_3554_: *mut crate::leanh::LeanObject,
    mut v_a_3555_: *mut crate::leanh::LeanObject,
    mut v_a_3556_: *mut crate::leanh::LeanObject,
    mut v_a_3557_: *mut crate::leanh::LeanObject,
    mut v_a_3558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3560_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(
        v_e_3548_, v_a_3549_, v_a_3557_,
    );
    return v___x_3560_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___boxed(
    mut v_e_3561_: *mut crate::leanh::LeanObject,
    mut v_a_3562_: *mut crate::leanh::LeanObject,
    mut v_a_3563_: *mut crate::leanh::LeanObject,
    mut v_a_3564_: *mut crate::leanh::LeanObject,
    mut v_a_3565_: *mut crate::leanh::LeanObject,
    mut v_a_3566_: *mut crate::leanh::LeanObject,
    mut v_a_3567_: *mut crate::leanh::LeanObject,
    mut v_a_3568_: *mut crate::leanh::LeanObject,
    mut v_a_3569_: *mut crate::leanh::LeanObject,
    mut v_a_3570_: *mut crate::leanh::LeanObject,
    mut v_a_3571_: *mut crate::leanh::LeanObject,
    mut v_a_3572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3573_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(
        v_e_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_,
        v_a_3569_, v_a_3570_, v_a_3571_,
    );
    crate::leanh::lean_dec(v_a_3571_);
    crate::leanh::lean_dec_ref(v_a_3570_);
    crate::leanh::lean_dec(v_a_3569_);
    crate::leanh::lean_dec_ref(v_a_3568_);
    crate::leanh::lean_dec(v_a_3567_);
    crate::leanh::lean_dec_ref(v_a_3566_);
    crate::leanh::lean_dec(v_a_3565_);
    crate::leanh::lean_dec_ref(v_a_3564_);
    crate::leanh::lean_dec(v_a_3563_);
    crate::leanh::lean_dec(v_a_3562_);
    crate::leanh::lean_dec_ref(v_e_3561_);
    return v_res_3573_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(
    mut v_00_u03b2_3574_: *mut crate::leanh::LeanObject,
    mut v_x_3575_: *mut crate::leanh::LeanObject,
    mut v_x_3576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3577_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_3575_, v_x_3576_);
    return v___x_3577_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___boxed(
    mut v_00_u03b2_3578_: *mut crate::leanh::LeanObject,
    mut v_x_3579_: *mut crate::leanh::LeanObject,
    mut v_x_3580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3581_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(v_00_u03b2_3578_, v_x_3579_, v_x_3580_);
    crate::leanh::lean_dec_ref(v_x_3580_);
    crate::leanh::lean_dec_ref(v_x_3579_);
    return v_res_3581_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(
    mut v_00_u03b2_3582_: *mut crate::leanh::LeanObject,
    mut v_x_3583_: *mut crate::leanh::LeanObject,
    mut v_x_3584_: usize,
    mut v_x_3585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3586_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_3583_, v_x_3584_, v_x_3585_);
    return v___x_3586_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_3587_: *mut crate::leanh::LeanObject,
    mut v_x_3588_: *mut crate::leanh::LeanObject,
    mut v_x_3589_: *mut crate::leanh::LeanObject,
    mut v_x_3590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_984__boxed_3591_: usize = 0;
    let mut v_res_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_984__boxed_3591_ = crate::leanh::lean_unbox_usize(v_x_3589_);
    crate::leanh::lean_dec(v_x_3589_);
    v_res_3592_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(v_00_u03b2_3587_, v_x_3588_, v_x_984__boxed_3591_, v_x_3590_);
    crate::leanh::lean_dec_ref(v_x_3590_);
    crate::leanh::lean_dec_ref(v_x_3588_);
    return v_res_3592_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3593_: *mut crate::leanh::LeanObject,
    mut v_keys_3594_: *mut crate::leanh::LeanObject,
    mut v_vals_3595_: *mut crate::leanh::LeanObject,
    mut v_heq_3596_: *mut crate::leanh::LeanObject,
    mut v_i_3597_: *mut crate::leanh::LeanObject,
    mut v_k_3598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3599_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_3594_, v_vals_3595_, v_i_3597_, v_k_3598_);
    return v___x_3599_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_3600_: *mut crate::leanh::LeanObject,
    mut v_keys_3601_: *mut crate::leanh::LeanObject,
    mut v_vals_3602_: *mut crate::leanh::LeanObject,
    mut v_heq_3603_: *mut crate::leanh::LeanObject,
    mut v_i_3604_: *mut crate::leanh::LeanObject,
    mut v_k_3605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3606_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_3600_, v_keys_3601_, v_vals_3602_, v_heq_3603_, v_i_3604_, v_k_3605_);
    crate::leanh::lean_dec_ref(v_k_3605_);
    crate::leanh::lean_dec_ref(v_vals_3602_);
    crate::leanh::lean_dec_ref(v_keys_3601_);
    return v_res_3606_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0(
    mut v_toPure_3607_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3616_: u8 = 0;
    let mut v_snd_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: u8 = 0;
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3624_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_charInst_x3f_3612_ = crate::leanh::lean_ctor_get(v_____do__lift_3608_, 5);
                crate::leanh::lean_inc(v_charInst_x3f_3612_);
                crate::leanh::lean_dec_ref(v_____do__lift_3608_);
                if crate::leanh::lean_obj_tag(v_charInst_x3f_3612_) == 1 {
                    v_val_3613_ = crate::leanh::lean_ctor_get(v_charInst_x3f_3612_, 0);
                    v_isSharedCheck_3624_ =
                        (!crate::leanh::lean_is_exclusive(v_charInst_x3f_3612_)) as u8;
                    if v_isSharedCheck_3624_ == 0 {
                        v___x_3615_ = v_charInst_x3f_3612_;
                        v_isShared_3616_ = v_isSharedCheck_3624_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3613_);
                        crate::leanh::lean_dec(v_charInst_x3f_3612_);
                        v___x_3615_ = crate::leanh::lean_box(0);
                        v_isShared_3616_ = v_isSharedCheck_3624_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_charInst_x3f_3612_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3610_ = crate::leanh::lean_box(0);
                v___x_3611_ = crate::leanh::lean_apply_2(
                    v_toPure_3607_,
                    crate::leanh::lean_box(0),
                    v___x_3610_,
                );
                return v___x_3611_;
            }
            2 => {
                v_snd_3617_ = crate::leanh::lean_ctor_get(v_val_3613_, 1);
                crate::leanh::lean_inc(v_snd_3617_);
                crate::leanh::lean_dec(v_val_3613_);
                v___x_3618_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3619_ = lean_nat_dec_eq(v_snd_3617_, v___x_3618_);
                if v___x_3619_ == 0 {
                    if v_isShared_3616_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3615_, 0, v_snd_3617_);
                        v___x_3621_ = v___x_3615_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3623_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_snd_3617_);
                        v___x_3621_ = v_reuseFailAlloc_3623_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_3617_);
                    crate::leanh::lean_del_object(v___x_3615_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3622_ = crate::leanh::lean_apply_2(
                    v_toPure_3607_,
                    crate::leanh::lean_box(0),
                    v___x_3621_,
                );
                return v___x_3622_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(
    mut v_inst_3625_: *mut crate::leanh::LeanObject,
    mut v_inst_3626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3627_ = crate::leanh::lean_ctor_get(v_inst_3625_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3627_);
    v_toBind_3628_ = crate::leanh::lean_ctor_get(v_inst_3625_, 1);
    crate::leanh::lean_inc(v_toBind_3628_);
    crate::leanh::lean_dec_ref(v_inst_3625_);
    v_getRing_3629_ = crate::leanh::lean_ctor_get(v_inst_3626_, 0);
    crate::leanh::lean_inc(v_getRing_3629_);
    crate::leanh::lean_dec_ref(v_inst_3626_);
    v_toPure_3630_ = crate::leanh::lean_ctor_get(v_toApplicative_3627_, 1);
    crate::leanh::lean_inc(v_toPure_3630_);
    crate::leanh::lean_dec_ref(v_toApplicative_3627_);
    v___f_3631_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3631_, 0, v_toPure_3630_);
    v___x_3632_ = crate::leanh::lean_apply_4(
        v_toBind_3628_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRing_3629_,
        v___f_3631_,
    );
    return v___x_3632_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f(
    mut v_m_3633_: *mut crate::leanh::LeanObject,
    mut v_inst_3634_: *mut crate::leanh::LeanObject,
    mut v_inst_3635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3636_ =
        l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(v_inst_3634_, v_inst_3635_);
    return v___x_3636_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0(
    mut v_toPure_3637_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: u8 = 0;
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_charInst_x3f_3642_ = crate::leanh::lean_ctor_get(v_____do__lift_3638_, 5);
                crate::leanh::lean_inc(v_charInst_x3f_3642_);
                crate::leanh::lean_dec_ref(v_____do__lift_3638_);
                if crate::leanh::lean_obj_tag(v_charInst_x3f_3642_) == 1 {
                    v_val_3643_ = crate::leanh::lean_ctor_get(v_charInst_x3f_3642_, 0);
                    v_snd_3644_ = crate::leanh::lean_ctor_get(v_val_3643_, 1);
                    v___x_3645_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3646_ = lean_nat_dec_eq(v_snd_3644_, v___x_3645_);
                    if v___x_3646_ == 0 {
                        v___x_3647_ = crate::leanh::lean_apply_2(
                            v_toPure_3637_,
                            crate::leanh::lean_box(0),
                            v_charInst_x3f_3642_,
                        );
                        return v___x_3647_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_charInst_x3f_3642_, 1);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_charInst_x3f_3642_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3640_ = crate::leanh::lean_box(0);
                v___x_3641_ = crate::leanh::lean_apply_2(
                    v_toPure_3637_,
                    crate::leanh::lean_box(0),
                    v___x_3640_,
                );
                return v___x_3641_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(
    mut v_inst_3648_: *mut crate::leanh::LeanObject,
    mut v_inst_3649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3650_ = crate::leanh::lean_ctor_get(v_inst_3648_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3650_);
    v_toBind_3651_ = crate::leanh::lean_ctor_get(v_inst_3648_, 1);
    crate::leanh::lean_inc(v_toBind_3651_);
    crate::leanh::lean_dec_ref(v_inst_3648_);
    v_getRing_3652_ = crate::leanh::lean_ctor_get(v_inst_3649_, 0);
    crate::leanh::lean_inc(v_getRing_3652_);
    crate::leanh::lean_dec_ref(v_inst_3649_);
    v_toPure_3653_ = crate::leanh::lean_ctor_get(v_toApplicative_3650_, 1);
    crate::leanh::lean_inc(v_toPure_3653_);
    crate::leanh::lean_dec_ref(v_toApplicative_3650_);
    v___f_3654_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3654_, 0, v_toPure_3653_);
    v___x_3655_ = crate::leanh::lean_apply_4(
        v_toBind_3651_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRing_3652_,
        v___f_3654_,
    );
    return v___x_3655_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f(
    mut v_m_3656_: *mut crate::leanh::LeanObject,
    mut v_inst_3657_: *mut crate::leanh::LeanObject,
    mut v_inst_3658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3659_ =
        l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(v_inst_3657_, v_inst_3658_);
    return v___x_3659_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(
    mut v_a_3660_: *mut crate::leanh::LeanObject,
    mut v_a_3661_: *mut crate::leanh::LeanObject,
    mut v_a_3662_: *mut crate::leanh::LeanObject,
    mut v_a_3663_: *mut crate::leanh::LeanObject,
    mut v_a_3664_: *mut crate::leanh::LeanObject,
    mut v_a_3665_: *mut crate::leanh::LeanObject,
    mut v_a_3666_: *mut crate::leanh::LeanObject,
    mut v_a_3667_: *mut crate::leanh::LeanObject,
    mut v_a_3668_: *mut crate::leanh::LeanObject,
    mut v_a_3669_: *mut crate::leanh::LeanObject,
    mut v_a_3670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3676_: u8 = 0;
    let mut v_noZeroDivInst_x3f_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3681_: u8 = 0;
    let mut v_a_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3685_: u8 = 0;
    let mut v___x_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3689_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3672_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                    v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_,
                    v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_,
                );
                if crate::leanh::lean_obj_tag(v___x_3672_) == 0 {
                    v_a_3673_ = crate::leanh::lean_ctor_get(v___x_3672_, 0);
                    v_isSharedCheck_3681_ = (!crate::leanh::lean_is_exclusive(v___x_3672_)) as u8;
                    if v_isSharedCheck_3681_ == 0 {
                        v___x_3675_ = v___x_3672_;
                        v_isShared_3676_ = v_isSharedCheck_3681_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3673_);
                        crate::leanh::lean_dec(v___x_3672_);
                        v___x_3675_ = crate::leanh::lean_box(0);
                        v_isShared_3676_ = v_isSharedCheck_3681_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3682_ = crate::leanh::lean_ctor_get(v___x_3672_, 0);
                    v_isSharedCheck_3689_ = (!crate::leanh::lean_is_exclusive(v___x_3672_)) as u8;
                    if v_isSharedCheck_3689_ == 0 {
                        v___x_3684_ = v___x_3672_;
                        v_isShared_3685_ = v_isSharedCheck_3689_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3682_);
                        crate::leanh::lean_dec(v___x_3672_);
                        v___x_3684_ = crate::leanh::lean_box(0);
                        v_isShared_3685_ = v_isSharedCheck_3689_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_noZeroDivInst_x3f_3677_ = crate::leanh::lean_ctor_get(v_a_3673_, 5);
                crate::leanh::lean_inc(v_noZeroDivInst_x3f_3677_);
                crate::leanh::lean_dec(v_a_3673_);
                if v_isShared_3676_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3675_, 0, v_noZeroDivInst_x3f_3677_);
                    v___x_3679_ = v___x_3675_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3680_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3680_,
                        0,
                        v_noZeroDivInst_x3f_3677_,
                    );
                    v___x_3679_ = v_reuseFailAlloc_3680_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3679_;
            }
            3 => {
                if v_isShared_3685_ == 0 {
                    v___x_3687_ = v___x_3684_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3688_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_a_3682_);
                    v___x_3687_ = v_reuseFailAlloc_3688_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3687_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f___boxed(
    mut v_a_3690_: *mut crate::leanh::LeanObject,
    mut v_a_3691_: *mut crate::leanh::LeanObject,
    mut v_a_3692_: *mut crate::leanh::LeanObject,
    mut v_a_3693_: *mut crate::leanh::LeanObject,
    mut v_a_3694_: *mut crate::leanh::LeanObject,
    mut v_a_3695_: *mut crate::leanh::LeanObject,
    mut v_a_3696_: *mut crate::leanh::LeanObject,
    mut v_a_3697_: *mut crate::leanh::LeanObject,
    mut v_a_3698_: *mut crate::leanh::LeanObject,
    mut v_a_3699_: *mut crate::leanh::LeanObject,
    mut v_a_3700_: *mut crate::leanh::LeanObject,
    mut v_a_3701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3702_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(
        v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_,
        v_a_3698_, v_a_3699_, v_a_3700_,
    );
    crate::leanh::lean_dec(v_a_3700_);
    crate::leanh::lean_dec_ref(v_a_3699_);
    crate::leanh::lean_dec(v_a_3698_);
    crate::leanh::lean_dec_ref(v_a_3697_);
    crate::leanh::lean_dec(v_a_3696_);
    crate::leanh::lean_dec_ref(v_a_3695_);
    crate::leanh::lean_dec(v_a_3694_);
    crate::leanh::lean_dec_ref(v_a_3693_);
    crate::leanh::lean_dec(v_a_3692_);
    crate::leanh::lean_dec(v_a_3691_);
    crate::leanh::lean_dec_ref(v_a_3690_);
    return v_res_3702_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(
    mut v_a_3703_: *mut crate::leanh::LeanObject,
    mut v_a_3704_: *mut crate::leanh::LeanObject,
    mut v_a_3705_: *mut crate::leanh::LeanObject,
    mut v_a_3706_: *mut crate::leanh::LeanObject,
    mut v_a_3707_: *mut crate::leanh::LeanObject,
    mut v_a_3708_: *mut crate::leanh::LeanObject,
    mut v_a_3709_: *mut crate::leanh::LeanObject,
    mut v_a_3710_: *mut crate::leanh::LeanObject,
    mut v_a_3711_: *mut crate::leanh::LeanObject,
    mut v_a_3712_: *mut crate::leanh::LeanObject,
    mut v_a_3713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3719_: u8 = 0;
    let mut v_noZeroDivInst_x3f_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: u8 = 0;
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: u8 = 0;
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3731_: u8 = 0;
    let mut v_a_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3735_: u8 = 0;
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3739_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3715_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                    v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_,
                    v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_,
                );
                if crate::leanh::lean_obj_tag(v___x_3715_) == 0 {
                    v_a_3716_ = crate::leanh::lean_ctor_get(v___x_3715_, 0);
                    v_isSharedCheck_3731_ = (!crate::leanh::lean_is_exclusive(v___x_3715_)) as u8;
                    if v_isSharedCheck_3731_ == 0 {
                        v___x_3718_ = v___x_3715_;
                        v_isShared_3719_ = v_isSharedCheck_3731_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3716_);
                        crate::leanh::lean_dec(v___x_3715_);
                        v___x_3718_ = crate::leanh::lean_box(0);
                        v_isShared_3719_ = v_isSharedCheck_3731_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3732_ = crate::leanh::lean_ctor_get(v___x_3715_, 0);
                    v_isSharedCheck_3739_ = (!crate::leanh::lean_is_exclusive(v___x_3715_)) as u8;
                    if v_isSharedCheck_3739_ == 0 {
                        v___x_3734_ = v___x_3715_;
                        v_isShared_3735_ = v_isSharedCheck_3739_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3732_);
                        crate::leanh::lean_dec(v___x_3715_);
                        v___x_3734_ = crate::leanh::lean_box(0);
                        v_isShared_3735_ = v_isSharedCheck_3739_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_noZeroDivInst_x3f_3720_ = crate::leanh::lean_ctor_get(v_a_3716_, 5);
                crate::leanh::lean_inc(v_noZeroDivInst_x3f_3720_);
                crate::leanh::lean_dec(v_a_3716_);
                if crate::leanh::lean_obj_tag(v_noZeroDivInst_x3f_3720_) == 0 {
                    v___x_3721_ = 0;
                    v___x_3722_ = crate::leanh::lean_box((v___x_3721_) as usize);
                    if v_isShared_3719_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3718_, 0, v___x_3722_);
                        v___x_3724_ = v___x_3718_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3725_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3722_);
                        v___x_3724_ = v_reuseFailAlloc_3725_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_noZeroDivInst_x3f_3720_, 1);
                    v___x_3726_ = 1;
                    v___x_3727_ = crate::leanh::lean_box((v___x_3726_) as usize);
                    if v_isShared_3719_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3718_, 0, v___x_3727_);
                        v___x_3729_ = v___x_3718_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3730_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3727_);
                        v___x_3729_ = v_reuseFailAlloc_3730_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3724_;
            }
            3 => {
                return v___x_3729_;
            }
            4 => {
                if v_isShared_3735_ == 0 {
                    v___x_3737_ = v___x_3734_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3738_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3732_);
                    v___x_3737_ = v_reuseFailAlloc_3738_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3737_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors___boxed(
    mut v_a_3740_: *mut crate::leanh::LeanObject,
    mut v_a_3741_: *mut crate::leanh::LeanObject,
    mut v_a_3742_: *mut crate::leanh::LeanObject,
    mut v_a_3743_: *mut crate::leanh::LeanObject,
    mut v_a_3744_: *mut crate::leanh::LeanObject,
    mut v_a_3745_: *mut crate::leanh::LeanObject,
    mut v_a_3746_: *mut crate::leanh::LeanObject,
    mut v_a_3747_: *mut crate::leanh::LeanObject,
    mut v_a_3748_: *mut crate::leanh::LeanObject,
    mut v_a_3749_: *mut crate::leanh::LeanObject,
    mut v_a_3750_: *mut crate::leanh::LeanObject,
    mut v_a_3751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3752_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(
        v_a_3740_, v_a_3741_, v_a_3742_, v_a_3743_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_,
        v_a_3748_, v_a_3749_, v_a_3750_,
    );
    crate::leanh::lean_dec(v_a_3750_);
    crate::leanh::lean_dec_ref(v_a_3749_);
    crate::leanh::lean_dec(v_a_3748_);
    crate::leanh::lean_dec_ref(v_a_3747_);
    crate::leanh::lean_dec(v_a_3746_);
    crate::leanh::lean_dec_ref(v_a_3745_);
    crate::leanh::lean_dec(v_a_3744_);
    crate::leanh::lean_dec_ref(v_a_3743_);
    crate::leanh::lean_dec(v_a_3742_);
    crate::leanh::lean_dec(v_a_3741_);
    crate::leanh::lean_dec_ref(v_a_3740_);
    return v_res_3752_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_hasChar(
    mut v_a_3753_: *mut crate::leanh::LeanObject,
    mut v_a_3754_: *mut crate::leanh::LeanObject,
    mut v_a_3755_: *mut crate::leanh::LeanObject,
    mut v_a_3756_: *mut crate::leanh::LeanObject,
    mut v_a_3757_: *mut crate::leanh::LeanObject,
    mut v_a_3758_: *mut crate::leanh::LeanObject,
    mut v_a_3759_: *mut crate::leanh::LeanObject,
    mut v_a_3760_: *mut crate::leanh::LeanObject,
    mut v_a_3761_: *mut crate::leanh::LeanObject,
    mut v_a_3762_: *mut crate::leanh::LeanObject,
    mut v_a_3763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3769_: u8 = 0;
    let mut v_toRing_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: u8 = 0;
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: u8 = 0;
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3782_: u8 = 0;
    let mut v_a_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3786_: u8 = 0;
    let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3790_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3765_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                    v_a_3753_, v_a_3754_, v_a_3755_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_,
                    v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_,
                );
                if crate::leanh::lean_obj_tag(v___x_3765_) == 0 {
                    v_a_3766_ = crate::leanh::lean_ctor_get(v___x_3765_, 0);
                    v_isSharedCheck_3782_ = (!crate::leanh::lean_is_exclusive(v___x_3765_)) as u8;
                    if v_isSharedCheck_3782_ == 0 {
                        v___x_3768_ = v___x_3765_;
                        v_isShared_3769_ = v_isSharedCheck_3782_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3766_);
                        crate::leanh::lean_dec(v___x_3765_);
                        v___x_3768_ = crate::leanh::lean_box(0);
                        v_isShared_3769_ = v_isSharedCheck_3782_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3783_ = crate::leanh::lean_ctor_get(v___x_3765_, 0);
                    v_isSharedCheck_3790_ = (!crate::leanh::lean_is_exclusive(v___x_3765_)) as u8;
                    if v_isSharedCheck_3790_ == 0 {
                        v___x_3785_ = v___x_3765_;
                        v_isShared_3786_ = v_isSharedCheck_3790_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3783_);
                        crate::leanh::lean_dec(v___x_3765_);
                        v___x_3785_ = crate::leanh::lean_box(0);
                        v_isShared_3786_ = v_isSharedCheck_3790_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_toRing_3770_ = crate::leanh::lean_ctor_get(v_a_3766_, 0);
                crate::leanh::lean_inc_ref(v_toRing_3770_);
                crate::leanh::lean_dec(v_a_3766_);
                v_charInst_x3f_3771_ = crate::leanh::lean_ctor_get(v_toRing_3770_, 5);
                crate::leanh::lean_inc(v_charInst_x3f_3771_);
                crate::leanh::lean_dec_ref(v_toRing_3770_);
                if crate::leanh::lean_obj_tag(v_charInst_x3f_3771_) == 0 {
                    v___x_3772_ = 0;
                    v___x_3773_ = crate::leanh::lean_box((v___x_3772_) as usize);
                    if v_isShared_3769_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3768_, 0, v___x_3773_);
                        v___x_3775_ = v___x_3768_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3776_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3776_, 0, v___x_3773_);
                        v___x_3775_ = v_reuseFailAlloc_3776_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_charInst_x3f_3771_, 1);
                    v___x_3777_ = 1;
                    v___x_3778_ = crate::leanh::lean_box((v___x_3777_) as usize);
                    if v_isShared_3769_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3768_, 0, v___x_3778_);
                        v___x_3780_ = v___x_3768_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3781_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3778_);
                        v___x_3780_ = v_reuseFailAlloc_3781_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3775_;
            }
            3 => {
                return v___x_3780_;
            }
            4 => {
                if v_isShared_3786_ == 0 {
                    v___x_3788_ = v___x_3785_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3789_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3783_);
                    v___x_3788_ = v_reuseFailAlloc_3789_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3788_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_hasChar___boxed(
    mut v_a_3791_: *mut crate::leanh::LeanObject,
    mut v_a_3792_: *mut crate::leanh::LeanObject,
    mut v_a_3793_: *mut crate::leanh::LeanObject,
    mut v_a_3794_: *mut crate::leanh::LeanObject,
    mut v_a_3795_: *mut crate::leanh::LeanObject,
    mut v_a_3796_: *mut crate::leanh::LeanObject,
    mut v_a_3797_: *mut crate::leanh::LeanObject,
    mut v_a_3798_: *mut crate::leanh::LeanObject,
    mut v_a_3799_: *mut crate::leanh::LeanObject,
    mut v_a_3800_: *mut crate::leanh::LeanObject,
    mut v_a_3801_: *mut crate::leanh::LeanObject,
    mut v_a_3802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3803_ = l_Lean_Meta_Grind_Arith_CommRing_hasChar(
        v_a_3791_, v_a_3792_, v_a_3793_, v_a_3794_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_,
        v_a_3799_, v_a_3800_, v_a_3801_,
    );
    crate::leanh::lean_dec(v_a_3801_);
    crate::leanh::lean_dec_ref(v_a_3800_);
    crate::leanh::lean_dec(v_a_3799_);
    crate::leanh::lean_dec_ref(v_a_3798_);
    crate::leanh::lean_dec(v_a_3797_);
    crate::leanh::lean_dec_ref(v_a_3796_);
    crate::leanh::lean_dec(v_a_3795_);
    crate::leanh::lean_dec_ref(v_a_3794_);
    crate::leanh::lean_dec(v_a_3793_);
    crate::leanh::lean_dec(v_a_3792_);
    crate::leanh::lean_dec_ref(v_a_3791_);
    return v_res_3803_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3805_ = l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0;
    v___x_3806_ = l_Lean_stringToMessageData(v___x_3805_);
    return v___x_3806_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getCharInst(
    mut v_a_3807_: *mut crate::leanh::LeanObject,
    mut v_a_3808_: *mut crate::leanh::LeanObject,
    mut v_a_3809_: *mut crate::leanh::LeanObject,
    mut v_a_3810_: *mut crate::leanh::LeanObject,
    mut v_a_3811_: *mut crate::leanh::LeanObject,
    mut v_a_3812_: *mut crate::leanh::LeanObject,
    mut v_a_3813_: *mut crate::leanh::LeanObject,
    mut v_a_3814_: *mut crate::leanh::LeanObject,
    mut v_a_3815_: *mut crate::leanh::LeanObject,
    mut v_a_3816_: *mut crate::leanh::LeanObject,
    mut v_a_3817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3823_: u8 = 0;
    let mut v_toRing_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3832_: u8 = 0;
    let mut v_a_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3836_: u8 = 0;
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3840_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3819_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                    v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_,
                    v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_,
                );
                if crate::leanh::lean_obj_tag(v___x_3819_) == 0 {
                    v_a_3820_ = crate::leanh::lean_ctor_get(v___x_3819_, 0);
                    v_isSharedCheck_3832_ = (!crate::leanh::lean_is_exclusive(v___x_3819_)) as u8;
                    if v_isSharedCheck_3832_ == 0 {
                        v___x_3822_ = v___x_3819_;
                        v_isShared_3823_ = v_isSharedCheck_3832_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3820_);
                        crate::leanh::lean_dec(v___x_3819_);
                        v___x_3822_ = crate::leanh::lean_box(0);
                        v_isShared_3823_ = v_isSharedCheck_3832_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3833_ = crate::leanh::lean_ctor_get(v___x_3819_, 0);
                    v_isSharedCheck_3840_ = (!crate::leanh::lean_is_exclusive(v___x_3819_)) as u8;
                    if v_isSharedCheck_3840_ == 0 {
                        v___x_3835_ = v___x_3819_;
                        v_isShared_3836_ = v_isSharedCheck_3840_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3833_);
                        crate::leanh::lean_dec(v___x_3819_);
                        v___x_3835_ = crate::leanh::lean_box(0);
                        v_isShared_3836_ = v_isSharedCheck_3840_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_toRing_3824_ = crate::leanh::lean_ctor_get(v_a_3820_, 0);
                crate::leanh::lean_inc_ref(v_toRing_3824_);
                crate::leanh::lean_dec(v_a_3820_);
                v_charInst_x3f_3825_ = crate::leanh::lean_ctor_get(v_toRing_3824_, 5);
                crate::leanh::lean_inc(v_charInst_x3f_3825_);
                crate::leanh::lean_dec_ref(v_toRing_3824_);
                if crate::leanh::lean_obj_tag(v_charInst_x3f_3825_) == 1 {
                    v_val_3826_ = crate::leanh::lean_ctor_get(v_charInst_x3f_3825_, 0);
                    crate::leanh::lean_inc(v_val_3826_);
                    crate::leanh::lean_dec_ref_known(v_charInst_x3f_3825_, 1);
                    if v_isShared_3823_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3822_, 0, v_val_3826_);
                        v___x_3828_ = v___x_3822_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3829_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_val_3826_);
                        v___x_3828_ = v_reuseFailAlloc_3829_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_charInst_x3f_3825_);
                    crate::leanh::lean_del_object(v___x_3822_);
                    v___x_3830_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1,
                    );
                    v___x_3831_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v___x_3830_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
                    return v___x_3831_;
                }
            }
            2 => {
                return v___x_3828_;
            }
            3 => {
                if v_isShared_3836_ == 0 {
                    v___x_3838_ = v___x_3835_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3839_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_a_3833_);
                    v___x_3838_ = v_reuseFailAlloc_3839_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3838_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getCharInst___boxed(
    mut v_a_3841_: *mut crate::leanh::LeanObject,
    mut v_a_3842_: *mut crate::leanh::LeanObject,
    mut v_a_3843_: *mut crate::leanh::LeanObject,
    mut v_a_3844_: *mut crate::leanh::LeanObject,
    mut v_a_3845_: *mut crate::leanh::LeanObject,
    mut v_a_3846_: *mut crate::leanh::LeanObject,
    mut v_a_3847_: *mut crate::leanh::LeanObject,
    mut v_a_3848_: *mut crate::leanh::LeanObject,
    mut v_a_3849_: *mut crate::leanh::LeanObject,
    mut v_a_3850_: *mut crate::leanh::LeanObject,
    mut v_a_3851_: *mut crate::leanh::LeanObject,
    mut v_a_3852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3853_ = l_Lean_Meta_Grind_Arith_CommRing_getCharInst(
        v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_,
        v_a_3849_, v_a_3850_, v_a_3851_,
    );
    crate::leanh::lean_dec(v_a_3851_);
    crate::leanh::lean_dec_ref(v_a_3850_);
    crate::leanh::lean_dec(v_a_3849_);
    crate::leanh::lean_dec_ref(v_a_3848_);
    crate::leanh::lean_dec(v_a_3847_);
    crate::leanh::lean_dec_ref(v_a_3846_);
    crate::leanh::lean_dec(v_a_3845_);
    crate::leanh::lean_dec_ref(v_a_3844_);
    crate::leanh::lean_dec(v_a_3843_);
    crate::leanh::lean_dec(v_a_3842_);
    crate::leanh::lean_dec_ref(v_a_3841_);
    return v_res_3853_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_isField(
    mut v_a_3854_: *mut crate::leanh::LeanObject,
    mut v_a_3855_: *mut crate::leanh::LeanObject,
    mut v_a_3856_: *mut crate::leanh::LeanObject,
    mut v_a_3857_: *mut crate::leanh::LeanObject,
    mut v_a_3858_: *mut crate::leanh::LeanObject,
    mut v_a_3859_: *mut crate::leanh::LeanObject,
    mut v_a_3860_: *mut crate::leanh::LeanObject,
    mut v_a_3861_: *mut crate::leanh::LeanObject,
    mut v_a_3862_: *mut crate::leanh::LeanObject,
    mut v_a_3863_: *mut crate::leanh::LeanObject,
    mut v_a_3864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3870_: u8 = 0;
    let mut v_fieldInst_x3f_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: u8 = 0;
    let mut v___x_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: u8 = 0;
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3882_: u8 = 0;
    let mut v_a_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3886_: u8 = 0;
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3890_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3866_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                    v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_,
                    v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_,
                );
                if crate::leanh::lean_obj_tag(v___x_3866_) == 0 {
                    v_a_3867_ = crate::leanh::lean_ctor_get(v___x_3866_, 0);
                    v_isSharedCheck_3882_ = (!crate::leanh::lean_is_exclusive(v___x_3866_)) as u8;
                    if v_isSharedCheck_3882_ == 0 {
                        v___x_3869_ = v___x_3866_;
                        v_isShared_3870_ = v_isSharedCheck_3882_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3867_);
                        crate::leanh::lean_dec(v___x_3866_);
                        v___x_3869_ = crate::leanh::lean_box(0);
                        v_isShared_3870_ = v_isSharedCheck_3882_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3883_ = crate::leanh::lean_ctor_get(v___x_3866_, 0);
                    v_isSharedCheck_3890_ = (!crate::leanh::lean_is_exclusive(v___x_3866_)) as u8;
                    if v_isSharedCheck_3890_ == 0 {
                        v___x_3885_ = v___x_3866_;
                        v_isShared_3886_ = v_isSharedCheck_3890_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3883_);
                        crate::leanh::lean_dec(v___x_3866_);
                        v___x_3885_ = crate::leanh::lean_box(0);
                        v_isShared_3886_ = v_isSharedCheck_3890_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_fieldInst_x3f_3871_ = crate::leanh::lean_ctor_get(v_a_3867_, 6);
                crate::leanh::lean_inc(v_fieldInst_x3f_3871_);
                crate::leanh::lean_dec(v_a_3867_);
                if crate::leanh::lean_obj_tag(v_fieldInst_x3f_3871_) == 0 {
                    v___x_3872_ = 0;
                    v___x_3873_ = crate::leanh::lean_box((v___x_3872_) as usize);
                    if v_isShared_3870_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3869_, 0, v___x_3873_);
                        v___x_3875_ = v___x_3869_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3876_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3876_, 0, v___x_3873_);
                        v___x_3875_ = v_reuseFailAlloc_3876_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_fieldInst_x3f_3871_, 1);
                    v___x_3877_ = 1;
                    v___x_3878_ = crate::leanh::lean_box((v___x_3877_) as usize);
                    if v_isShared_3870_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3869_, 0, v___x_3878_);
                        v___x_3880_ = v___x_3869_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3881_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3881_, 0, v___x_3878_);
                        v___x_3880_ = v_reuseFailAlloc_3881_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3875_;
            }
            3 => {
                return v___x_3880_;
            }
            4 => {
                if v_isShared_3886_ == 0 {
                    v___x_3888_ = v___x_3885_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3889_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_a_3883_);
                    v___x_3888_ = v_reuseFailAlloc_3889_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3888_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_isField___boxed(
    mut v_a_3891_: *mut crate::leanh::LeanObject,
    mut v_a_3892_: *mut crate::leanh::LeanObject,
    mut v_a_3893_: *mut crate::leanh::LeanObject,
    mut v_a_3894_: *mut crate::leanh::LeanObject,
    mut v_a_3895_: *mut crate::leanh::LeanObject,
    mut v_a_3896_: *mut crate::leanh::LeanObject,
    mut v_a_3897_: *mut crate::leanh::LeanObject,
    mut v_a_3898_: *mut crate::leanh::LeanObject,
    mut v_a_3899_: *mut crate::leanh::LeanObject,
    mut v_a_3900_: *mut crate::leanh::LeanObject,
    mut v_a_3901_: *mut crate::leanh::LeanObject,
    mut v_a_3902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3903_ = l_Lean_Meta_Grind_Arith_CommRing_isField(
        v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_,
        v_a_3899_, v_a_3900_, v_a_3901_,
    );
    crate::leanh::lean_dec(v_a_3901_);
    crate::leanh::lean_dec_ref(v_a_3900_);
    crate::leanh::lean_dec(v_a_3899_);
    crate::leanh::lean_dec_ref(v_a_3898_);
    crate::leanh::lean_dec(v_a_3897_);
    crate::leanh::lean_dec_ref(v_a_3896_);
    crate::leanh::lean_dec(v_a_3895_);
    crate::leanh::lean_dec_ref(v_a_3894_);
    crate::leanh::lean_dec(v_a_3893_);
    crate::leanh::lean_dec(v_a_3892_);
    crate::leanh::lean_dec_ref(v_a_3891_);
    return v_res_3903_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(
    mut v_a_3904_: *mut crate::leanh::LeanObject,
    mut v_a_3905_: *mut crate::leanh::LeanObject,
    mut v_a_3906_: *mut crate::leanh::LeanObject,
    mut v_a_3907_: *mut crate::leanh::LeanObject,
    mut v_a_3908_: *mut crate::leanh::LeanObject,
    mut v_a_3909_: *mut crate::leanh::LeanObject,
    mut v_a_3910_: *mut crate::leanh::LeanObject,
    mut v_a_3911_: *mut crate::leanh::LeanObject,
    mut v_a_3912_: *mut crate::leanh::LeanObject,
    mut v_a_3913_: *mut crate::leanh::LeanObject,
    mut v_a_3914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3920_: u8 = 0;
    let mut v_queue_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: u8 = 0;
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: u8 = 0;
    let mut v___x_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3932_: u8 = 0;
    let mut v_a_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3936_: u8 = 0;
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3940_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3916_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                    v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_, v_a_3910_,
                    v_a_3911_, v_a_3912_, v_a_3913_, v_a_3914_,
                );
                if crate::leanh::lean_obj_tag(v___x_3916_) == 0 {
                    v_a_3917_ = crate::leanh::lean_ctor_get(v___x_3916_, 0);
                    v_isSharedCheck_3932_ = (!crate::leanh::lean_is_exclusive(v___x_3916_)) as u8;
                    if v_isSharedCheck_3932_ == 0 {
                        v___x_3919_ = v___x_3916_;
                        v_isShared_3920_ = v_isSharedCheck_3932_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3917_);
                        crate::leanh::lean_dec(v___x_3916_);
                        v___x_3919_ = crate::leanh::lean_box(0);
                        v_isShared_3920_ = v_isSharedCheck_3932_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3933_ = crate::leanh::lean_ctor_get(v___x_3916_, 0);
                    v_isSharedCheck_3940_ = (!crate::leanh::lean_is_exclusive(v___x_3916_)) as u8;
                    if v_isSharedCheck_3940_ == 0 {
                        v___x_3935_ = v___x_3916_;
                        v_isShared_3936_ = v_isSharedCheck_3940_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3933_);
                        crate::leanh::lean_dec(v___x_3916_);
                        v___x_3935_ = crate::leanh::lean_box(0);
                        v_isShared_3936_ = v_isSharedCheck_3940_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_queue_3921_ = crate::leanh::lean_ctor_get(v_a_3917_, 11);
                crate::leanh::lean_inc(v_queue_3921_);
                crate::leanh::lean_dec(v_a_3917_);
                if crate::leanh::lean_obj_tag(v_queue_3921_) == 0 {
                    crate::leanh::lean_dec_ref_known(v_queue_3921_, 5);
                    v___x_3922_ = 0;
                    v___x_3923_ = crate::leanh::lean_box((v___x_3922_) as usize);
                    if v_isShared_3920_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3919_, 0, v___x_3923_);
                        v___x_3925_ = v___x_3919_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3926_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___x_3923_);
                        v___x_3925_ = v_reuseFailAlloc_3926_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3927_ = 1;
                    v___x_3928_ = crate::leanh::lean_box((v___x_3927_) as usize);
                    if v_isShared_3920_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3919_, 0, v___x_3928_);
                        v___x_3930_ = v___x_3919_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3931_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3931_, 0, v___x_3928_);
                        v___x_3930_ = v_reuseFailAlloc_3931_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3925_;
            }
            3 => {
                return v___x_3930_;
            }
            4 => {
                if v_isShared_3936_ == 0 {
                    v___x_3938_ = v___x_3935_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3939_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_a_3933_);
                    v___x_3938_ = v_reuseFailAlloc_3939_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3938_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___boxed(
    mut v_a_3941_: *mut crate::leanh::LeanObject,
    mut v_a_3942_: *mut crate::leanh::LeanObject,
    mut v_a_3943_: *mut crate::leanh::LeanObject,
    mut v_a_3944_: *mut crate::leanh::LeanObject,
    mut v_a_3945_: *mut crate::leanh::LeanObject,
    mut v_a_3946_: *mut crate::leanh::LeanObject,
    mut v_a_3947_: *mut crate::leanh::LeanObject,
    mut v_a_3948_: *mut crate::leanh::LeanObject,
    mut v_a_3949_: *mut crate::leanh::LeanObject,
    mut v_a_3950_: *mut crate::leanh::LeanObject,
    mut v_a_3951_: *mut crate::leanh::LeanObject,
    mut v_a_3952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3953_ = l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(
        v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_,
        v_a_3949_, v_a_3950_, v_a_3951_,
    );
    crate::leanh::lean_dec(v_a_3951_);
    crate::leanh::lean_dec_ref(v_a_3950_);
    crate::leanh::lean_dec(v_a_3949_);
    crate::leanh::lean_dec_ref(v_a_3948_);
    crate::leanh::lean_dec(v_a_3947_);
    crate::leanh::lean_dec_ref(v_a_3946_);
    crate::leanh::lean_dec(v_a_3945_);
    crate::leanh::lean_dec_ref(v_a_3944_);
    crate::leanh::lean_dec(v_a_3943_);
    crate::leanh::lean_dec(v_a_3942_);
    crate::leanh::lean_dec_ref(v_a_3941_);
    return v_res_3953_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(
    mut v_k_3954_: *mut crate::leanh::LeanObject,
    mut v_t_3955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3962_: u8 = 0;
    let mut v___x_3963_: u8 = 0;
    let mut v_impl_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: u8 = 0;
    let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3982_: u8 = 0;
    let mut v_size_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: u8 = 0;
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3994_: u8 = 0;
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4019_: u8 = 0;
    let mut v_unused_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4032_: u8 = 0;
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4036_: u8 = 0;
    let mut v_unused_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4043_: u8 = 0;
    let mut v_unused_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4061_: u8 = 0;
    let mut v_size_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4071_: u8 = 0;
    let mut v_unused_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4078_: u8 = 0;
    let mut v_k_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4083_: u8 = 0;
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4094_: u8 = 0;
    let mut v_unused_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4098_: u8 = 0;
    let mut v_unused_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4107_: u8 = 0;
    let mut v___x_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4115_: u8 = 0;
    let mut v_unused_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4124_: u8 = 0;
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4132_: u8 = 0;
    let mut v_unused_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: u8 = 0;
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4152_: u8 = 0;
    let mut v___x_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: u8 = 0;
    let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4168_: u8 = 0;
    let mut v_size_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: u8 = 0;
    let mut v___x_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4180_: u8 = 0;
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4205_: u8 = 0;
    let mut v_unused_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4220_: u8 = 0;
    let mut v_unused_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4228_: u8 = 0;
    let mut v_k_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4246_: u8 = 0;
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4257_: u8 = 0;
    let mut v_unused_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4279_: u8 = 0;
    let mut v_unused_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4285_: u8 = 0;
    let mut v_unused_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4293_: u8 = 0;
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: u8 = 0;
    let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4309_: u8 = 0;
    let mut v_size_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: u8 = 0;
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4321_: u8 = 0;
    let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4333_: u8 = 0;
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4337_: u8 = 0;
    let mut v_unused_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4356_: u8 = 0;
    let mut v_unused_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4372_: u8 = 0;
    let mut v_unused_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4380_: u8 = 0;
    let mut v_k_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4401_: u8 = 0;
    let mut v_unused_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4409_: u8 = 0;
    let mut v_k_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4416_: u8 = 0;
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4427_: u8 = 0;
    let mut v_unused_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4431_: u8 = 0;
    let mut v_unused_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4443_: u8 = 0;
    let mut v_unused_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: u8 = 0;
    let mut v___x_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4467_: u8 = 0;
    let mut v_size_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: u8 = 0;
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4479_: u8 = 0;
    let mut v___x_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4505_: u8 = 0;
    let mut v_unused_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4519_: u8 = 0;
    let mut v___x_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4523_: u8 = 0;
    let mut v_unused_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4530_: u8 = 0;
    let mut v_unused_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4548_: u8 = 0;
    let mut v_size_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4558_: u8 = 0;
    let mut v_unused_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4565_: u8 = 0;
    let mut v___x_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4573_: u8 = 0;
    let mut v_unused_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4582_: u8 = 0;
    let mut v_k_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4587_: u8 = 0;
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4598_: u8 = 0;
    let mut v_unused_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4602_: u8 = 0;
    let mut v_unused_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4613_: u8 = 0;
    let mut v_unused_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_3955_) == 0 {
                    v_k_3956_ = crate::leanh::lean_ctor_get(v_t_3955_, 1);
                    v_v_3957_ = crate::leanh::lean_ctor_get(v_t_3955_, 2);
                    v_l_3958_ = crate::leanh::lean_ctor_get(v_t_3955_, 3);
                    v_r_3959_ = crate::leanh::lean_ctor_get(v_t_3955_, 4);
                    v_isSharedCheck_4613_ = (!crate::leanh::lean_is_exclusive(v_t_3955_)) as u8;
                    if v_isSharedCheck_4613_ == 0 {
                        v_unused_4614_ = crate::leanh::lean_ctor_get(v_t_3955_, 0);
                        crate::leanh::lean_dec(v_unused_4614_);
                        v___x_3961_ = v_t_3955_;
                        v_isShared_3962_ = v_isSharedCheck_4613_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_3959_);
                        crate::leanh::lean_inc(v_l_3958_);
                        crate::leanh::lean_inc(v_v_3957_);
                        crate::leanh::lean_inc(v_k_3956_);
                        crate::leanh::lean_dec(v_t_3955_);
                        v___x_3961_ = crate::leanh::lean_box(0);
                        v_isShared_3962_ = v_isSharedCheck_4613_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_t_3955_;
                }
            }
            1 => {
                v___x_3963_ =
                    l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(v_k_3954_, v_k_3956_);
                match v___x_3963_ {
                    0 => {
                        v_impl_3964_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_3954_, v_l_3958_);
                        v___x_3965_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_impl_3964_) == 0 {
                            if crate::leanh::lean_obj_tag(v_r_3959_) == 0 {
                                v_size_3966_ = crate::leanh::lean_ctor_get(v_impl_3964_, 0);
                                crate::leanh::lean_inc(v_size_3966_);
                                v_size_3967_ = crate::leanh::lean_ctor_get(v_r_3959_, 0);
                                v_k_3968_ = crate::leanh::lean_ctor_get(v_r_3959_, 1);
                                v_v_3969_ = crate::leanh::lean_ctor_get(v_r_3959_, 2);
                                v_l_3970_ = crate::leanh::lean_ctor_get(v_r_3959_, 3);
                                crate::leanh::lean_inc(v_l_3970_);
                                v_r_3971_ = crate::leanh::lean_ctor_get(v_r_3959_, 4);
                                v___x_3972_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_3973_ = lean_nat_mul(v___x_3972_, v_size_3966_);
                                v___x_3974_ = lean_nat_dec_lt(v___x_3973_, v_size_3967_);
                                crate::leanh::lean_dec(v___x_3973_);
                                if v___x_3974_ == 0 {
                                    crate::leanh::lean_dec(v_l_3970_);
                                    v___x_3975_ = lean_nat_add(v___x_3965_, v_size_3966_);
                                    crate::leanh::lean_dec(v_size_3966_);
                                    v___x_3976_ = lean_nat_add(v___x_3975_, v_size_3967_);
                                    crate::leanh::lean_dec(v___x_3975_);
                                    if v_isShared_3962_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_3961_, 3, v_impl_3964_);
                                        crate::leanh::lean_ctor_set(v___x_3961_, 0, v___x_3976_);
                                        v___x_3978_ = v___x_3961_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3979_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3979_,
                                            0,
                                            v___x_3976_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3979_,
                                            1,
                                            v_k_3956_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3979_,
                                            2,
                                            v_v_3957_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3979_,
                                            3,
                                            v_impl_3964_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3979_,
                                            4,
                                            v_r_3959_,
                                        );
                                        v___x_3978_ = v_reuseFailAlloc_3979_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc(v_r_3971_);
                                    crate::leanh::lean_inc(v_v_3969_);
                                    crate::leanh::lean_inc(v_k_3968_);
                                    crate::leanh::lean_inc(v_size_3967_);
                                    v_isSharedCheck_4043_ =
                                        (!crate::leanh::lean_is_exclusive(v_r_3959_)) as u8;
                                    if v_isSharedCheck_4043_ == 0 {
                                        v_unused_4044_ = crate::leanh::lean_ctor_get(v_r_3959_, 4);
                                        crate::leanh::lean_dec(v_unused_4044_);
                                        v_unused_4045_ = crate::leanh::lean_ctor_get(v_r_3959_, 3);
                                        crate::leanh::lean_dec(v_unused_4045_);
                                        v_unused_4046_ = crate::leanh::lean_ctor_get(v_r_3959_, 2);
                                        crate::leanh::lean_dec(v_unused_4046_);
                                        v_unused_4047_ = crate::leanh::lean_ctor_get(v_r_3959_, 1);
                                        crate::leanh::lean_dec(v_unused_4047_);
                                        v_unused_4048_ = crate::leanh::lean_ctor_get(v_r_3959_, 0);
                                        crate::leanh::lean_dec(v_unused_4048_);
                                        v___x_3981_ = v_r_3959_;
                                        v_isShared_3982_ = v_isSharedCheck_4043_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_r_3959_);
                                        v___x_3981_ = crate::leanh::lean_box(0);
                                        v_isShared_3982_ = v_isSharedCheck_4043_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_4049_ = crate::leanh::lean_ctor_get(v_impl_3964_, 0);
                                crate::leanh::lean_inc(v_size_4049_);
                                v___x_4050_ = lean_nat_add(v___x_3965_, v_size_4049_);
                                crate::leanh::lean_dec(v_size_4049_);
                                if v_isShared_3962_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3961_, 3, v_impl_3964_);
                                    crate::leanh::lean_ctor_set(v___x_3961_, 0, v___x_4050_);
                                    v___x_4052_ = v___x_3961_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4053_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4053_,
                                        0,
                                        v___x_4050_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4053_,
                                        1,
                                        v_k_3956_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4053_,
                                        2,
                                        v_v_3957_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4053_,
                                        3,
                                        v_impl_3964_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4053_,
                                        4,
                                        v_r_3959_,
                                    );
                                    v___x_4052_ = v_reuseFailAlloc_4053_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v_r_3959_) == 0 {
                                v_l_4054_ = crate::leanh::lean_ctor_get(v_r_3959_, 3);
                                crate::leanh::lean_inc(v_l_4054_);
                                if crate::leanh::lean_obj_tag(v_l_4054_) == 0 {
                                    v_r_4055_ = crate::leanh::lean_ctor_get(v_r_3959_, 4);
                                    crate::leanh::lean_inc(v_r_4055_);
                                    if crate::leanh::lean_obj_tag(v_r_4055_) == 0 {
                                        v_size_4056_ = crate::leanh::lean_ctor_get(v_r_3959_, 0);
                                        v_k_4057_ = crate::leanh::lean_ctor_get(v_r_3959_, 1);
                                        v_v_4058_ = crate::leanh::lean_ctor_get(v_r_3959_, 2);
                                        v_isSharedCheck_4071_ =
                                            (!crate::leanh::lean_is_exclusive(v_r_3959_)) as u8;
                                        if v_isSharedCheck_4071_ == 0 {
                                            v_unused_4072_ =
                                                crate::leanh::lean_ctor_get(v_r_3959_, 4);
                                            crate::leanh::lean_dec(v_unused_4072_);
                                            v_unused_4073_ =
                                                crate::leanh::lean_ctor_get(v_r_3959_, 3);
                                            crate::leanh::lean_dec(v_unused_4073_);
                                            v___x_4060_ = v_r_3959_;
                                            v_isShared_4061_ = v_isSharedCheck_4071_;
                                            state = 14;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_4058_);
                                            crate::leanh::lean_inc(v_k_4057_);
                                            crate::leanh::lean_inc(v_size_4056_);
                                            crate::leanh::lean_dec(v_r_3959_);
                                            v___x_4060_ = crate::leanh::lean_box(0);
                                            v_isShared_4061_ = v_isSharedCheck_4071_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_4074_ = crate::leanh::lean_ctor_get(v_r_3959_, 1);
                                        v_v_4075_ = crate::leanh::lean_ctor_get(v_r_3959_, 2);
                                        v_isSharedCheck_4098_ =
                                            (!crate::leanh::lean_is_exclusive(v_r_3959_)) as u8;
                                        if v_isSharedCheck_4098_ == 0 {
                                            v_unused_4099_ =
                                                crate::leanh::lean_ctor_get(v_r_3959_, 4);
                                            crate::leanh::lean_dec(v_unused_4099_);
                                            v_unused_4100_ =
                                                crate::leanh::lean_ctor_get(v_r_3959_, 3);
                                            crate::leanh::lean_dec(v_unused_4100_);
                                            v_unused_4101_ =
                                                crate::leanh::lean_ctor_get(v_r_3959_, 0);
                                            crate::leanh::lean_dec(v_unused_4101_);
                                            v___x_4077_ = v_r_3959_;
                                            v_isShared_4078_ = v_isSharedCheck_4098_;
                                            state = 17;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_4075_);
                                            crate::leanh::lean_inc(v_k_4074_);
                                            crate::leanh::lean_dec(v_r_3959_);
                                            v___x_4077_ = crate::leanh::lean_box(0);
                                            v_isShared_4078_ = v_isSharedCheck_4098_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_4102_ = crate::leanh::lean_ctor_get(v_r_3959_, 4);
                                    crate::leanh::lean_inc(v_r_4102_);
                                    if crate::leanh::lean_obj_tag(v_r_4102_) == 0 {
                                        v_k_4103_ = crate::leanh::lean_ctor_get(v_r_3959_, 1);
                                        v_v_4104_ = crate::leanh::lean_ctor_get(v_r_3959_, 2);
                                        v_isSharedCheck_4115_ =
                                            (!crate::leanh::lean_is_exclusive(v_r_3959_)) as u8;
                                        if v_isSharedCheck_4115_ == 0 {
                                            v_unused_4116_ =
                                                crate::leanh::lean_ctor_get(v_r_3959_, 4);
                                            crate::leanh::lean_dec(v_unused_4116_);
                                            v_unused_4117_ =
                                                crate::leanh::lean_ctor_get(v_r_3959_, 3);
                                            crate::leanh::lean_dec(v_unused_4117_);
                                            v_unused_4118_ =
                                                crate::leanh::lean_ctor_get(v_r_3959_, 0);
                                            crate::leanh::lean_dec(v_unused_4118_);
                                            v___x_4106_ = v_r_3959_;
                                            v_isShared_4107_ = v_isSharedCheck_4115_;
                                            state = 22;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_4104_);
                                            crate::leanh::lean_inc(v_k_4103_);
                                            crate::leanh::lean_dec(v_r_3959_);
                                            v___x_4106_ = crate::leanh::lean_box(0);
                                            v_isShared_4107_ = v_isSharedCheck_4115_;
                                            state = 22;
                                            continue;
                                        }
                                    } else {
                                        v_size_4119_ = crate::leanh::lean_ctor_get(v_r_3959_, 0);
                                        v_k_4120_ = crate::leanh::lean_ctor_get(v_r_3959_, 1);
                                        v_v_4121_ = crate::leanh::lean_ctor_get(v_r_3959_, 2);
                                        v_isSharedCheck_4132_ =
                                            (!crate::leanh::lean_is_exclusive(v_r_3959_)) as u8;
                                        if v_isSharedCheck_4132_ == 0 {
                                            v_unused_4133_ =
                                                crate::leanh::lean_ctor_get(v_r_3959_, 4);
                                            crate::leanh::lean_dec(v_unused_4133_);
                                            v_unused_4134_ =
                                                crate::leanh::lean_ctor_get(v_r_3959_, 3);
                                            crate::leanh::lean_dec(v_unused_4134_);
                                            v___x_4123_ = v_r_3959_;
                                            v_isShared_4124_ = v_isSharedCheck_4132_;
                                            state = 25;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_4121_);
                                            crate::leanh::lean_inc(v_k_4120_);
                                            crate::leanh::lean_inc(v_size_4119_);
                                            crate::leanh::lean_dec(v_r_3959_);
                                            v___x_4123_ = crate::leanh::lean_box(0);
                                            v_isShared_4124_ = v_isSharedCheck_4132_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                if v_isShared_3962_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3961_, 3, v_r_3959_);
                                    crate::leanh::lean_ctor_set(v___x_3961_, 0, v___x_3965_);
                                    v___x_4136_ = v___x_3961_;
                                    state = 28;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4137_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4137_,
                                        0,
                                        v___x_3965_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4137_,
                                        1,
                                        v_k_3956_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4137_,
                                        2,
                                        v_v_3957_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4137_,
                                        3,
                                        v_r_3959_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4137_,
                                        4,
                                        v_r_3959_,
                                    );
                                    v___x_4136_ = v_reuseFailAlloc_4137_;
                                    state = 28;
                                    continue;
                                }
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_del_object(v___x_3961_);
                        crate::leanh::lean_dec(v_v_3957_);
                        crate::leanh::lean_dec(v_k_3956_);
                        if crate::leanh::lean_obj_tag(v_l_3958_) == 0 {
                            if crate::leanh::lean_obj_tag(v_r_3959_) == 0 {
                                v_size_4138_ = crate::leanh::lean_ctor_get(v_l_3958_, 0);
                                v_k_4139_ = crate::leanh::lean_ctor_get(v_l_3958_, 1);
                                v_v_4140_ = crate::leanh::lean_ctor_get(v_l_3958_, 2);
                                v_l_4141_ = crate::leanh::lean_ctor_get(v_l_3958_, 3);
                                v_r_4142_ = crate::leanh::lean_ctor_get(v_l_3958_, 4);
                                crate::leanh::lean_inc(v_r_4142_);
                                v_size_4143_ = crate::leanh::lean_ctor_get(v_r_3959_, 0);
                                v_k_4144_ = crate::leanh::lean_ctor_get(v_r_3959_, 1);
                                v_v_4145_ = crate::leanh::lean_ctor_get(v_r_3959_, 2);
                                v_l_4146_ = crate::leanh::lean_ctor_get(v_r_3959_, 3);
                                crate::leanh::lean_inc(v_l_4146_);
                                v_r_4147_ = crate::leanh::lean_ctor_get(v_r_3959_, 4);
                                v___x_4148_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_4149_ = lean_nat_dec_lt(v_size_4138_, v_size_4143_);
                                if v___x_4149_ == 0 {
                                    crate::leanh::lean_inc(v_l_4141_);
                                    crate::leanh::lean_inc(v_v_4140_);
                                    crate::leanh::lean_inc(v_k_4139_);
                                    v_isSharedCheck_4285_ =
                                        (!crate::leanh::lean_is_exclusive(v_l_3958_)) as u8;
                                    if v_isSharedCheck_4285_ == 0 {
                                        v_unused_4286_ = crate::leanh::lean_ctor_get(v_l_3958_, 4);
                                        crate::leanh::lean_dec(v_unused_4286_);
                                        v_unused_4287_ = crate::leanh::lean_ctor_get(v_l_3958_, 3);
                                        crate::leanh::lean_dec(v_unused_4287_);
                                        v_unused_4288_ = crate::leanh::lean_ctor_get(v_l_3958_, 2);
                                        crate::leanh::lean_dec(v_unused_4288_);
                                        v_unused_4289_ = crate::leanh::lean_ctor_get(v_l_3958_, 1);
                                        crate::leanh::lean_dec(v_unused_4289_);
                                        v_unused_4290_ = crate::leanh::lean_ctor_get(v_l_3958_, 0);
                                        crate::leanh::lean_dec(v_unused_4290_);
                                        v___x_4151_ = v_l_3958_;
                                        v_isShared_4152_ = v_isSharedCheck_4285_;
                                        state = 29;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_l_3958_);
                                        v___x_4151_ = crate::leanh::lean_box(0);
                                        v_isShared_4152_ = v_isSharedCheck_4285_;
                                        state = 29;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc(v_r_4147_);
                                    crate::leanh::lean_inc(v_v_4145_);
                                    crate::leanh::lean_inc(v_k_4144_);
                                    v_isSharedCheck_4443_ =
                                        (!crate::leanh::lean_is_exclusive(v_r_3959_)) as u8;
                                    if v_isSharedCheck_4443_ == 0 {
                                        v_unused_4444_ = crate::leanh::lean_ctor_get(v_r_3959_, 4);
                                        crate::leanh::lean_dec(v_unused_4444_);
                                        v_unused_4445_ = crate::leanh::lean_ctor_get(v_r_3959_, 3);
                                        crate::leanh::lean_dec(v_unused_4445_);
                                        v_unused_4446_ = crate::leanh::lean_ctor_get(v_r_3959_, 2);
                                        crate::leanh::lean_dec(v_unused_4446_);
                                        v_unused_4447_ = crate::leanh::lean_ctor_get(v_r_3959_, 1);
                                        crate::leanh::lean_dec(v_unused_4447_);
                                        v_unused_4448_ = crate::leanh::lean_ctor_get(v_r_3959_, 0);
                                        crate::leanh::lean_dec(v_unused_4448_);
                                        v___x_4292_ = v_r_3959_;
                                        v_isShared_4293_ = v_isSharedCheck_4443_;
                                        state = 51;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_r_3959_);
                                        v___x_4292_ = crate::leanh::lean_box(0);
                                        v_isShared_4293_ = v_isSharedCheck_4443_;
                                        state = 51;
                                        continue;
                                    }
                                }
                            } else {
                                return v_l_3958_;
                            }
                        } else {
                            return v_r_3959_;
                        }
                    }
                    _ => {
                        v_impl_4449_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_3954_, v_r_3959_);
                        v___x_4450_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_impl_4449_) == 0 {
                            if crate::leanh::lean_obj_tag(v_l_3958_) == 0 {
                                v_size_4451_ = crate::leanh::lean_ctor_get(v_impl_4449_, 0);
                                crate::leanh::lean_inc(v_size_4451_);
                                v_size_4452_ = crate::leanh::lean_ctor_get(v_l_3958_, 0);
                                v_k_4453_ = crate::leanh::lean_ctor_get(v_l_3958_, 1);
                                v_v_4454_ = crate::leanh::lean_ctor_get(v_l_3958_, 2);
                                v_l_4455_ = crate::leanh::lean_ctor_get(v_l_3958_, 3);
                                v_r_4456_ = crate::leanh::lean_ctor_get(v_l_3958_, 4);
                                crate::leanh::lean_inc(v_r_4456_);
                                v___x_4457_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_4458_ = lean_nat_mul(v___x_4457_, v_size_4451_);
                                v___x_4459_ = lean_nat_dec_lt(v___x_4458_, v_size_4452_);
                                crate::leanh::lean_dec(v___x_4458_);
                                if v___x_4459_ == 0 {
                                    crate::leanh::lean_dec(v_r_4456_);
                                    v___x_4460_ = lean_nat_add(v___x_4450_, v_size_4452_);
                                    v___x_4461_ = lean_nat_add(v___x_4460_, v_size_4451_);
                                    crate::leanh::lean_dec(v_size_4451_);
                                    crate::leanh::lean_dec(v___x_4460_);
                                    if v_isShared_3962_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_3961_, 4, v_impl_4449_);
                                        crate::leanh::lean_ctor_set(v___x_3961_, 0, v___x_4461_);
                                        v___x_4463_ = v___x_3961_;
                                        state = 74;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_4464_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4464_,
                                            0,
                                            v___x_4461_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4464_,
                                            1,
                                            v_k_3956_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4464_,
                                            2,
                                            v_v_3957_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4464_,
                                            3,
                                            v_l_3958_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4464_,
                                            4,
                                            v_impl_4449_,
                                        );
                                        v___x_4463_ = v_reuseFailAlloc_4464_;
                                        state = 74;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc(v_l_4455_);
                                    crate::leanh::lean_inc(v_v_4454_);
                                    crate::leanh::lean_inc(v_k_4453_);
                                    crate::leanh::lean_inc(v_size_4452_);
                                    v_isSharedCheck_4530_ =
                                        (!crate::leanh::lean_is_exclusive(v_l_3958_)) as u8;
                                    if v_isSharedCheck_4530_ == 0 {
                                        v_unused_4531_ = crate::leanh::lean_ctor_get(v_l_3958_, 4);
                                        crate::leanh::lean_dec(v_unused_4531_);
                                        v_unused_4532_ = crate::leanh::lean_ctor_get(v_l_3958_, 3);
                                        crate::leanh::lean_dec(v_unused_4532_);
                                        v_unused_4533_ = crate::leanh::lean_ctor_get(v_l_3958_, 2);
                                        crate::leanh::lean_dec(v_unused_4533_);
                                        v_unused_4534_ = crate::leanh::lean_ctor_get(v_l_3958_, 1);
                                        crate::leanh::lean_dec(v_unused_4534_);
                                        v_unused_4535_ = crate::leanh::lean_ctor_get(v_l_3958_, 0);
                                        crate::leanh::lean_dec(v_unused_4535_);
                                        v___x_4466_ = v_l_3958_;
                                        v_isShared_4467_ = v_isSharedCheck_4530_;
                                        state = 75;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_l_3958_);
                                        v___x_4466_ = crate::leanh::lean_box(0);
                                        v_isShared_4467_ = v_isSharedCheck_4530_;
                                        state = 75;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_4536_ = crate::leanh::lean_ctor_get(v_impl_4449_, 0);
                                crate::leanh::lean_inc(v_size_4536_);
                                v___x_4537_ = lean_nat_add(v___x_4450_, v_size_4536_);
                                crate::leanh::lean_dec(v_size_4536_);
                                if v_isShared_3962_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3961_, 4, v_impl_4449_);
                                    crate::leanh::lean_ctor_set(v___x_3961_, 0, v___x_4537_);
                                    v___x_4539_ = v___x_3961_;
                                    state = 85;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4540_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4540_,
                                        0,
                                        v___x_4537_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4540_,
                                        1,
                                        v_k_3956_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4540_,
                                        2,
                                        v_v_3957_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4540_,
                                        3,
                                        v_l_3958_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4540_,
                                        4,
                                        v_impl_4449_,
                                    );
                                    v___x_4539_ = v_reuseFailAlloc_4540_;
                                    state = 85;
                                    continue;
                                }
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v_l_3958_) == 0 {
                                v_l_4541_ = crate::leanh::lean_ctor_get(v_l_3958_, 3);
                                if crate::leanh::lean_obj_tag(v_l_4541_) == 0 {
                                    crate::leanh::lean_inc_ref(v_l_4541_);
                                    v_r_4542_ = crate::leanh::lean_ctor_get(v_l_3958_, 4);
                                    crate::leanh::lean_inc(v_r_4542_);
                                    if crate::leanh::lean_obj_tag(v_r_4542_) == 0 {
                                        v_size_4543_ = crate::leanh::lean_ctor_get(v_l_3958_, 0);
                                        v_k_4544_ = crate::leanh::lean_ctor_get(v_l_3958_, 1);
                                        v_v_4545_ = crate::leanh::lean_ctor_get(v_l_3958_, 2);
                                        v_isSharedCheck_4558_ =
                                            (!crate::leanh::lean_is_exclusive(v_l_3958_)) as u8;
                                        if v_isSharedCheck_4558_ == 0 {
                                            v_unused_4559_ =
                                                crate::leanh::lean_ctor_get(v_l_3958_, 4);
                                            crate::leanh::lean_dec(v_unused_4559_);
                                            v_unused_4560_ =
                                                crate::leanh::lean_ctor_get(v_l_3958_, 3);
                                            crate::leanh::lean_dec(v_unused_4560_);
                                            v___x_4547_ = v_l_3958_;
                                            v_isShared_4548_ = v_isSharedCheck_4558_;
                                            state = 86;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_4545_);
                                            crate::leanh::lean_inc(v_k_4544_);
                                            crate::leanh::lean_inc(v_size_4543_);
                                            crate::leanh::lean_dec(v_l_3958_);
                                            v___x_4547_ = crate::leanh::lean_box(0);
                                            v_isShared_4548_ = v_isSharedCheck_4558_;
                                            state = 86;
                                            continue;
                                        }
                                    } else {
                                        v_k_4561_ = crate::leanh::lean_ctor_get(v_l_3958_, 1);
                                        v_v_4562_ = crate::leanh::lean_ctor_get(v_l_3958_, 2);
                                        v_isSharedCheck_4573_ =
                                            (!crate::leanh::lean_is_exclusive(v_l_3958_)) as u8;
                                        if v_isSharedCheck_4573_ == 0 {
                                            v_unused_4574_ =
                                                crate::leanh::lean_ctor_get(v_l_3958_, 4);
                                            crate::leanh::lean_dec(v_unused_4574_);
                                            v_unused_4575_ =
                                                crate::leanh::lean_ctor_get(v_l_3958_, 3);
                                            crate::leanh::lean_dec(v_unused_4575_);
                                            v_unused_4576_ =
                                                crate::leanh::lean_ctor_get(v_l_3958_, 0);
                                            crate::leanh::lean_dec(v_unused_4576_);
                                            v___x_4564_ = v_l_3958_;
                                            v_isShared_4565_ = v_isSharedCheck_4573_;
                                            state = 89;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_4562_);
                                            crate::leanh::lean_inc(v_k_4561_);
                                            crate::leanh::lean_dec(v_l_3958_);
                                            v___x_4564_ = crate::leanh::lean_box(0);
                                            v_isShared_4565_ = v_isSharedCheck_4573_;
                                            state = 89;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_4577_ = crate::leanh::lean_ctor_get(v_l_3958_, 4);
                                    crate::leanh::lean_inc(v_r_4577_);
                                    if crate::leanh::lean_obj_tag(v_r_4577_) == 0 {
                                        crate::leanh::lean_inc(v_l_4541_);
                                        v_k_4578_ = crate::leanh::lean_ctor_get(v_l_3958_, 1);
                                        v_v_4579_ = crate::leanh::lean_ctor_get(v_l_3958_, 2);
                                        v_isSharedCheck_4602_ =
                                            (!crate::leanh::lean_is_exclusive(v_l_3958_)) as u8;
                                        if v_isSharedCheck_4602_ == 0 {
                                            v_unused_4603_ =
                                                crate::leanh::lean_ctor_get(v_l_3958_, 4);
                                            crate::leanh::lean_dec(v_unused_4603_);
                                            v_unused_4604_ =
                                                crate::leanh::lean_ctor_get(v_l_3958_, 3);
                                            crate::leanh::lean_dec(v_unused_4604_);
                                            v_unused_4605_ =
                                                crate::leanh::lean_ctor_get(v_l_3958_, 0);
                                            crate::leanh::lean_dec(v_unused_4605_);
                                            v___x_4581_ = v_l_3958_;
                                            v_isShared_4582_ = v_isSharedCheck_4602_;
                                            state = 92;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_4579_);
                                            crate::leanh::lean_inc(v_k_4578_);
                                            crate::leanh::lean_dec(v_l_3958_);
                                            v___x_4581_ = crate::leanh::lean_box(0);
                                            v_isShared_4582_ = v_isSharedCheck_4602_;
                                            state = 92;
                                            continue;
                                        }
                                    } else {
                                        v___x_4606_ = crate::leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_3962_ == 0 {
                                            crate::leanh::lean_ctor_set(v___x_3961_, 4, v_r_4577_);
                                            crate::leanh::lean_ctor_set(
                                                v___x_3961_,
                                                0,
                                                v___x_4606_,
                                            );
                                            v___x_4608_ = v___x_3961_;
                                            state = 97;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_4609_ =
                                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_4609_,
                                                0,
                                                v___x_4606_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_4609_,
                                                1,
                                                v_k_3956_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_4609_,
                                                2,
                                                v_v_3957_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_4609_,
                                                3,
                                                v_l_3958_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_4609_,
                                                4,
                                                v_r_4577_,
                                            );
                                            v___x_4608_ = v_reuseFailAlloc_4609_;
                                            state = 97;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                if v_isShared_3962_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3961_, 4, v_l_3958_);
                                    crate::leanh::lean_ctor_set(v___x_3961_, 0, v___x_4450_);
                                    v___x_4611_ = v___x_3961_;
                                    state = 98;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4612_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4612_,
                                        0,
                                        v___x_4450_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4612_,
                                        1,
                                        v_k_3956_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4612_,
                                        2,
                                        v_v_3957_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4612_,
                                        3,
                                        v_l_3958_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4612_,
                                        4,
                                        v_l_3958_,
                                    );
                                    v___x_4611_ = v_reuseFailAlloc_4612_;
                                    state = 98;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_3978_;
            }
            3 => {
                v_size_3983_ = crate::leanh::lean_ctor_get(v_l_3970_, 0);
                v_k_3984_ = crate::leanh::lean_ctor_get(v_l_3970_, 1);
                v_v_3985_ = crate::leanh::lean_ctor_get(v_l_3970_, 2);
                v_l_3986_ = crate::leanh::lean_ctor_get(v_l_3970_, 3);
                v_r_3987_ = crate::leanh::lean_ctor_get(v_l_3970_, 4);
                v_size_3988_ = crate::leanh::lean_ctor_get(v_r_3971_, 0);
                v___x_3989_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_3990_ = lean_nat_mul(v___x_3989_, v_size_3988_);
                v___x_3991_ = lean_nat_dec_lt(v_size_3983_, v___x_3990_);
                crate::leanh::lean_dec(v___x_3990_);
                if v___x_3991_ == 0 {
                    crate::leanh::lean_inc(v_r_3987_);
                    crate::leanh::lean_inc(v_l_3986_);
                    crate::leanh::lean_inc(v_v_3985_);
                    crate::leanh::lean_inc(v_k_3984_);
                    v_isSharedCheck_4019_ = (!crate::leanh::lean_is_exclusive(v_l_3970_)) as u8;
                    if v_isSharedCheck_4019_ == 0 {
                        v_unused_4020_ = crate::leanh::lean_ctor_get(v_l_3970_, 4);
                        crate::leanh::lean_dec(v_unused_4020_);
                        v_unused_4021_ = crate::leanh::lean_ctor_get(v_l_3970_, 3);
                        crate::leanh::lean_dec(v_unused_4021_);
                        v_unused_4022_ = crate::leanh::lean_ctor_get(v_l_3970_, 2);
                        crate::leanh::lean_dec(v_unused_4022_);
                        v_unused_4023_ = crate::leanh::lean_ctor_get(v_l_3970_, 1);
                        crate::leanh::lean_dec(v_unused_4023_);
                        v_unused_4024_ = crate::leanh::lean_ctor_get(v_l_3970_, 0);
                        crate::leanh::lean_dec(v_unused_4024_);
                        v___x_3993_ = v_l_3970_;
                        v_isShared_3994_ = v_isSharedCheck_4019_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_3970_);
                        v___x_3993_ = crate::leanh::lean_box(0);
                        v_isShared_3994_ = v_isSharedCheck_4019_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3961_);
                    v___x_4025_ = lean_nat_add(v___x_3965_, v_size_3966_);
                    crate::leanh::lean_dec(v_size_3966_);
                    v___x_4026_ = lean_nat_add(v___x_4025_, v_size_3967_);
                    crate::leanh::lean_dec(v_size_3967_);
                    v___x_4027_ = lean_nat_add(v___x_4025_, v_size_3983_);
                    crate::leanh::lean_dec(v___x_4025_);
                    crate::leanh::lean_inc_ref(v_impl_3964_);
                    if v_isShared_3982_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3981_, 4, v_l_3970_);
                        crate::leanh::lean_ctor_set(v___x_3981_, 3, v_impl_3964_);
                        crate::leanh::lean_ctor_set(v___x_3981_, 2, v_v_3957_);
                        crate::leanh::lean_ctor_set(v___x_3981_, 1, v_k_3956_);
                        crate::leanh::lean_ctor_set(v___x_3981_, 0, v___x_4027_);
                        v___x_4029_ = v___x_3981_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4042_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4042_, 0, v___x_4027_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4042_, 1, v_k_3956_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4042_, 2, v_v_3957_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4042_, 3, v_impl_3964_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4042_, 4, v_l_3970_);
                        v___x_4029_ = v_reuseFailAlloc_4042_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3995_ = lean_nat_add(v___x_3965_, v_size_3966_);
                crate::leanh::lean_dec(v_size_3966_);
                v___x_3996_ = lean_nat_add(v___x_3995_, v_size_3967_);
                crate::leanh::lean_dec(v_size_3967_);
                if crate::leanh::lean_obj_tag(v_l_3986_) == 0 {
                    v_size_4017_ = crate::leanh::lean_ctor_get(v_l_3986_, 0);
                    crate::leanh::lean_inc(v_size_4017_);
                    v___y_4009_ = v_size_4017_;
                    state = 8;
                    continue;
                } else {
                    v___x_4018_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4009_ = v___x_4018_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_4001_ = lean_nat_add(v___y_3998_, v___y_4000_);
                crate::leanh::lean_dec(v___y_4000_);
                crate::leanh::lean_dec(v___y_3998_);
                if v_isShared_3994_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3993_, 4, v_r_3971_);
                    crate::leanh::lean_ctor_set(v___x_3993_, 3, v_r_3987_);
                    crate::leanh::lean_ctor_set(v___x_3993_, 2, v_v_3969_);
                    crate::leanh::lean_ctor_set(v___x_3993_, 1, v_k_3968_);
                    crate::leanh::lean_ctor_set(v___x_3993_, 0, v___x_4001_);
                    v___x_4003_ = v___x_3993_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4007_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4007_, 0, v___x_4001_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4007_, 1, v_k_3968_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4007_, 2, v_v_3969_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4007_, 3, v_r_3987_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4007_, 4, v_r_3971_);
                    v___x_4003_ = v_reuseFailAlloc_4007_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3982_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3981_, 4, v___x_4003_);
                    crate::leanh::lean_ctor_set(v___x_3981_, 3, v___y_3999_);
                    crate::leanh::lean_ctor_set(v___x_3981_, 2, v_v_3985_);
                    crate::leanh::lean_ctor_set(v___x_3981_, 1, v_k_3984_);
                    crate::leanh::lean_ctor_set(v___x_3981_, 0, v___x_3996_);
                    v___x_4005_ = v___x_3981_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4006_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4006_, 0, v___x_3996_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4006_, 1, v_k_3984_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4006_, 2, v_v_3985_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4006_, 3, v___y_3999_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4006_, 4, v___x_4003_);
                    v___x_4005_ = v_reuseFailAlloc_4006_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4005_;
            }
            8 => {
                v___x_4010_ = lean_nat_add(v___x_3995_, v___y_4009_);
                crate::leanh::lean_dec(v___y_4009_);
                crate::leanh::lean_dec(v___x_3995_);
                if v_isShared_3962_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3961_, 4, v_l_3986_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 3, v_impl_3964_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 0, v___x_4010_);
                    v___x_4012_ = v___x_3961_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4016_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4016_, 0, v___x_4010_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4016_, 1, v_k_3956_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4016_, 2, v_v_3957_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4016_, 3, v_impl_3964_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4016_, 4, v_l_3986_);
                    v___x_4012_ = v_reuseFailAlloc_4016_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_4013_ = lean_nat_add(v___x_3965_, v_size_3988_);
                if crate::leanh::lean_obj_tag(v_r_3987_) == 0 {
                    v_size_4014_ = crate::leanh::lean_ctor_get(v_r_3987_, 0);
                    crate::leanh::lean_inc(v_size_4014_);
                    v___y_3998_ = v___x_4013_;
                    v___y_3999_ = v___x_4012_;
                    v___y_4000_ = v_size_4014_;
                    state = 5;
                    continue;
                } else {
                    v___x_4015_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3998_ = v___x_4013_;
                    v___y_3999_ = v___x_4012_;
                    v___y_4000_ = v___x_4015_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_4036_ = (!crate::leanh::lean_is_exclusive(v_impl_3964_)) as u8;
                if v_isSharedCheck_4036_ == 0 {
                    v_unused_4037_ = crate::leanh::lean_ctor_get(v_impl_3964_, 4);
                    crate::leanh::lean_dec(v_unused_4037_);
                    v_unused_4038_ = crate::leanh::lean_ctor_get(v_impl_3964_, 3);
                    crate::leanh::lean_dec(v_unused_4038_);
                    v_unused_4039_ = crate::leanh::lean_ctor_get(v_impl_3964_, 2);
                    crate::leanh::lean_dec(v_unused_4039_);
                    v_unused_4040_ = crate::leanh::lean_ctor_get(v_impl_3964_, 1);
                    crate::leanh::lean_dec(v_unused_4040_);
                    v_unused_4041_ = crate::leanh::lean_ctor_get(v_impl_3964_, 0);
                    crate::leanh::lean_dec(v_unused_4041_);
                    v___x_4031_ = v_impl_3964_;
                    v_isShared_4032_ = v_isSharedCheck_4036_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_impl_3964_);
                    v___x_4031_ = crate::leanh::lean_box(0);
                    v_isShared_4032_ = v_isSharedCheck_4036_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_4032_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4031_, 4, v_r_3971_);
                    crate::leanh::lean_ctor_set(v___x_4031_, 3, v___x_4029_);
                    crate::leanh::lean_ctor_set(v___x_4031_, 2, v_v_3969_);
                    crate::leanh::lean_ctor_set(v___x_4031_, 1, v_k_3968_);
                    crate::leanh::lean_ctor_set(v___x_4031_, 0, v___x_4026_);
                    v___x_4034_ = v___x_4031_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4035_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4035_, 0, v___x_4026_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4035_, 1, v_k_3968_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4035_, 2, v_v_3969_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4035_, 3, v___x_4029_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4035_, 4, v_r_3971_);
                    v___x_4034_ = v_reuseFailAlloc_4035_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4034_;
            }
            13 => {
                return v___x_4052_;
            }
            14 => {
                v_size_4062_ = crate::leanh::lean_ctor_get(v_l_4054_, 0);
                v___x_4063_ = lean_nat_add(v___x_3965_, v_size_4056_);
                crate::leanh::lean_dec(v_size_4056_);
                v___x_4064_ = lean_nat_add(v___x_3965_, v_size_4062_);
                if v_isShared_4061_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4060_, 4, v_l_4054_);
                    crate::leanh::lean_ctor_set(v___x_4060_, 3, v_impl_3964_);
                    crate::leanh::lean_ctor_set(v___x_4060_, 2, v_v_3957_);
                    crate::leanh::lean_ctor_set(v___x_4060_, 1, v_k_3956_);
                    crate::leanh::lean_ctor_set(v___x_4060_, 0, v___x_4064_);
                    v___x_4066_ = v___x_4060_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4070_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 0, v___x_4064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 1, v_k_3956_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 2, v_v_3957_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 3, v_impl_3964_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 4, v_l_4054_);
                    v___x_4066_ = v_reuseFailAlloc_4070_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_3962_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3961_, 4, v_r_4055_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 3, v___x_4066_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 2, v_v_4058_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 1, v_k_4057_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 0, v___x_4063_);
                    v___x_4068_ = v___x_3961_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4069_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4069_, 0, v___x_4063_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4069_, 1, v_k_4057_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4069_, 2, v_v_4058_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4069_, 3, v___x_4066_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4069_, 4, v_r_4055_);
                    v___x_4068_ = v_reuseFailAlloc_4069_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4068_;
            }
            17 => {
                v_k_4079_ = crate::leanh::lean_ctor_get(v_l_4054_, 1);
                v_v_4080_ = crate::leanh::lean_ctor_get(v_l_4054_, 2);
                v_isSharedCheck_4094_ = (!crate::leanh::lean_is_exclusive(v_l_4054_)) as u8;
                if v_isSharedCheck_4094_ == 0 {
                    v_unused_4095_ = crate::leanh::lean_ctor_get(v_l_4054_, 4);
                    crate::leanh::lean_dec(v_unused_4095_);
                    v_unused_4096_ = crate::leanh::lean_ctor_get(v_l_4054_, 3);
                    crate::leanh::lean_dec(v_unused_4096_);
                    v_unused_4097_ = crate::leanh::lean_ctor_get(v_l_4054_, 0);
                    crate::leanh::lean_dec(v_unused_4097_);
                    v___x_4082_ = v_l_4054_;
                    v_isShared_4083_ = v_isSharedCheck_4094_;
                    state = 18;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_4080_);
                    crate::leanh::lean_inc(v_k_4079_);
                    crate::leanh::lean_dec(v_l_4054_);
                    v___x_4082_ = crate::leanh::lean_box(0);
                    v_isShared_4083_ = v_isSharedCheck_4094_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_4084_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_4083_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4082_, 4, v_r_4055_);
                    crate::leanh::lean_ctor_set(v___x_4082_, 3, v_r_4055_);
                    crate::leanh::lean_ctor_set(v___x_4082_, 2, v_v_3957_);
                    crate::leanh::lean_ctor_set(v___x_4082_, 1, v_k_3956_);
                    crate::leanh::lean_ctor_set(v___x_4082_, 0, v___x_3965_);
                    v___x_4086_ = v___x_4082_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4093_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4093_, 0, v___x_3965_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4093_, 1, v_k_3956_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4093_, 2, v_v_3957_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4093_, 3, v_r_4055_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4093_, 4, v_r_4055_);
                    v___x_4086_ = v_reuseFailAlloc_4093_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_4078_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4077_, 3, v_r_4055_);
                    crate::leanh::lean_ctor_set(v___x_4077_, 0, v___x_3965_);
                    v___x_4088_ = v___x_4077_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4092_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4092_, 0, v___x_3965_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4092_, 1, v_k_4074_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4092_, 2, v_v_4075_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4092_, 3, v_r_4055_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4092_, 4, v_r_4055_);
                    v___x_4088_ = v_reuseFailAlloc_4092_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_3962_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3961_, 4, v___x_4088_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 3, v___x_4086_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 2, v_v_4080_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 1, v_k_4079_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 0, v___x_4084_);
                    v___x_4090_ = v___x_3961_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4091_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4084_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4091_, 1, v_k_4079_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4091_, 2, v_v_4080_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4091_, 3, v___x_4086_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4091_, 4, v___x_4088_);
                    v___x_4090_ = v_reuseFailAlloc_4091_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_4090_;
            }
            22 => {
                v___x_4108_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_4107_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4106_, 4, v_l_4054_);
                    crate::leanh::lean_ctor_set(v___x_4106_, 2, v_v_3957_);
                    crate::leanh::lean_ctor_set(v___x_4106_, 1, v_k_3956_);
                    crate::leanh::lean_ctor_set(v___x_4106_, 0, v___x_3965_);
                    v___x_4110_ = v___x_4106_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_4114_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4114_, 0, v___x_3965_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4114_, 1, v_k_3956_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4114_, 2, v_v_3957_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4114_, 3, v_l_4054_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4114_, 4, v_l_4054_);
                    v___x_4110_ = v_reuseFailAlloc_4114_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_3962_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3961_, 4, v_r_4102_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 3, v___x_4110_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 2, v_v_4104_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 1, v_k_4103_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 0, v___x_4108_);
                    v___x_4112_ = v___x_3961_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4113_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 0, v___x_4108_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 1, v_k_4103_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 2, v_v_4104_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 3, v___x_4110_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 4, v_r_4102_);
                    v___x_4112_ = v_reuseFailAlloc_4113_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_4112_;
            }
            25 => {
                if v_isShared_4124_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4123_, 3, v_r_4102_);
                    v___x_4126_ = v___x_4123_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4131_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_size_4119_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4131_, 1, v_k_4120_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4131_, 2, v_v_4121_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4131_, 3, v_r_4102_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4131_, 4, v_r_4102_);
                    v___x_4126_ = v_reuseFailAlloc_4131_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_4127_ = crate::leanh::lean_unsigned_to_nat(2);
                if v_isShared_3962_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3961_, 4, v___x_4126_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 3, v_r_4102_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 0, v___x_4127_);
                    v___x_4129_ = v___x_3961_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_4130_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 0, v___x_4127_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 1, v_k_3956_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 2, v_v_3957_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 3, v_r_4102_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 4, v___x_4126_);
                    v___x_4129_ = v_reuseFailAlloc_4130_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_4129_;
            }
            28 => {
                return v___x_4136_;
            }
            29 => {
                v___x_4153_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(
                    v_k_4139_, v_v_4140_, v_l_4141_, v_r_4142_,
                );
                v_tree_4154_ = crate::leanh::lean_ctor_get(v___x_4153_, 2);
                crate::leanh::lean_inc(v_tree_4154_);
                if crate::leanh::lean_obj_tag(v_tree_4154_) == 0 {
                    v_k_4155_ = crate::leanh::lean_ctor_get(v___x_4153_, 0);
                    crate::leanh::lean_inc(v_k_4155_);
                    v_v_4156_ = crate::leanh::lean_ctor_get(v___x_4153_, 1);
                    crate::leanh::lean_inc(v_v_4156_);
                    crate::leanh::lean_dec_ref(v___x_4153_);
                    v_size_4157_ = crate::leanh::lean_ctor_get(v_tree_4154_, 0);
                    v___x_4158_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_4159_ = lean_nat_mul(v___x_4158_, v_size_4157_);
                    v___x_4160_ = lean_nat_dec_lt(v___x_4159_, v_size_4143_);
                    crate::leanh::lean_dec(v___x_4159_);
                    if v___x_4160_ == 0 {
                        crate::leanh::lean_dec(v_l_4146_);
                        v___x_4161_ = lean_nat_add(v___x_4148_, v_size_4157_);
                        v___x_4162_ = lean_nat_add(v___x_4161_, v_size_4143_);
                        crate::leanh::lean_dec(v___x_4161_);
                        if v_isShared_4152_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4151_, 4, v_r_3959_);
                            crate::leanh::lean_ctor_set(v___x_4151_, 3, v_tree_4154_);
                            crate::leanh::lean_ctor_set(v___x_4151_, 2, v_v_4156_);
                            crate::leanh::lean_ctor_set(v___x_4151_, 1, v_k_4155_);
                            crate::leanh::lean_ctor_set(v___x_4151_, 0, v___x_4162_);
                            v___x_4164_ = v___x_4151_;
                            state = 30;
                            continue;
                        } else {
                            v_reuseFailAlloc_4165_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4165_, 0, v___x_4162_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4165_, 1, v_k_4155_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4165_, 2, v_v_4156_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4165_, 3, v_tree_4154_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4165_, 4, v_r_3959_);
                            v___x_4164_ = v_reuseFailAlloc_4165_;
                            state = 30;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc(v_r_4147_);
                        crate::leanh::lean_inc(v_v_4145_);
                        crate::leanh::lean_inc(v_k_4144_);
                        crate::leanh::lean_inc(v_size_4143_);
                        v_isSharedCheck_4220_ = (!crate::leanh::lean_is_exclusive(v_r_3959_)) as u8;
                        if v_isSharedCheck_4220_ == 0 {
                            v_unused_4221_ = crate::leanh::lean_ctor_get(v_r_3959_, 4);
                            crate::leanh::lean_dec(v_unused_4221_);
                            v_unused_4222_ = crate::leanh::lean_ctor_get(v_r_3959_, 3);
                            crate::leanh::lean_dec(v_unused_4222_);
                            v_unused_4223_ = crate::leanh::lean_ctor_get(v_r_3959_, 2);
                            crate::leanh::lean_dec(v_unused_4223_);
                            v_unused_4224_ = crate::leanh::lean_ctor_get(v_r_3959_, 1);
                            crate::leanh::lean_dec(v_unused_4224_);
                            v_unused_4225_ = crate::leanh::lean_ctor_get(v_r_3959_, 0);
                            crate::leanh::lean_dec(v_unused_4225_);
                            v___x_4167_ = v_r_3959_;
                            v_isShared_4168_ = v_isSharedCheck_4220_;
                            state = 31;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_r_3959_);
                            v___x_4167_ = crate::leanh::lean_box(0);
                            v_isShared_4168_ = v_isSharedCheck_4220_;
                            state = 31;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_r_4147_);
                    crate::leanh::lean_inc(v_v_4145_);
                    crate::leanh::lean_inc(v_k_4144_);
                    crate::leanh::lean_inc(v_size_4143_);
                    v_isSharedCheck_4279_ = (!crate::leanh::lean_is_exclusive(v_r_3959_)) as u8;
                    if v_isSharedCheck_4279_ == 0 {
                        v_unused_4280_ = crate::leanh::lean_ctor_get(v_r_3959_, 4);
                        crate::leanh::lean_dec(v_unused_4280_);
                        v_unused_4281_ = crate::leanh::lean_ctor_get(v_r_3959_, 3);
                        crate::leanh::lean_dec(v_unused_4281_);
                        v_unused_4282_ = crate::leanh::lean_ctor_get(v_r_3959_, 2);
                        crate::leanh::lean_dec(v_unused_4282_);
                        v_unused_4283_ = crate::leanh::lean_ctor_get(v_r_3959_, 1);
                        crate::leanh::lean_dec(v_unused_4283_);
                        v_unused_4284_ = crate::leanh::lean_ctor_get(v_r_3959_, 0);
                        crate::leanh::lean_dec(v_unused_4284_);
                        v___x_4227_ = v_r_3959_;
                        v_isShared_4228_ = v_isSharedCheck_4279_;
                        state = 40;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_3959_);
                        v___x_4227_ = crate::leanh::lean_box(0);
                        v_isShared_4228_ = v_isSharedCheck_4279_;
                        state = 40;
                        continue;
                    }
                }
            }
            30 => {
                return v___x_4164_;
            }
            31 => {
                v_size_4169_ = crate::leanh::lean_ctor_get(v_l_4146_, 0);
                v_k_4170_ = crate::leanh::lean_ctor_get(v_l_4146_, 1);
                v_v_4171_ = crate::leanh::lean_ctor_get(v_l_4146_, 2);
                v_l_4172_ = crate::leanh::lean_ctor_get(v_l_4146_, 3);
                v_r_4173_ = crate::leanh::lean_ctor_get(v_l_4146_, 4);
                v_size_4174_ = crate::leanh::lean_ctor_get(v_r_4147_, 0);
                v___x_4175_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_4176_ = lean_nat_mul(v___x_4175_, v_size_4174_);
                v___x_4177_ = lean_nat_dec_lt(v_size_4169_, v___x_4176_);
                crate::leanh::lean_dec(v___x_4176_);
                if v___x_4177_ == 0 {
                    crate::leanh::lean_inc(v_r_4173_);
                    crate::leanh::lean_inc(v_l_4172_);
                    crate::leanh::lean_inc(v_v_4171_);
                    crate::leanh::lean_inc(v_k_4170_);
                    v_isSharedCheck_4205_ = (!crate::leanh::lean_is_exclusive(v_l_4146_)) as u8;
                    if v_isSharedCheck_4205_ == 0 {
                        v_unused_4206_ = crate::leanh::lean_ctor_get(v_l_4146_, 4);
                        crate::leanh::lean_dec(v_unused_4206_);
                        v_unused_4207_ = crate::leanh::lean_ctor_get(v_l_4146_, 3);
                        crate::leanh::lean_dec(v_unused_4207_);
                        v_unused_4208_ = crate::leanh::lean_ctor_get(v_l_4146_, 2);
                        crate::leanh::lean_dec(v_unused_4208_);
                        v_unused_4209_ = crate::leanh::lean_ctor_get(v_l_4146_, 1);
                        crate::leanh::lean_dec(v_unused_4209_);
                        v_unused_4210_ = crate::leanh::lean_ctor_get(v_l_4146_, 0);
                        crate::leanh::lean_dec(v_unused_4210_);
                        v___x_4179_ = v_l_4146_;
                        v_isShared_4180_ = v_isSharedCheck_4205_;
                        state = 32;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_4146_);
                        v___x_4179_ = crate::leanh::lean_box(0);
                        v_isShared_4180_ = v_isSharedCheck_4205_;
                        state = 32;
                        continue;
                    }
                } else {
                    v___x_4211_ = lean_nat_add(v___x_4148_, v_size_4157_);
                    v___x_4212_ = lean_nat_add(v___x_4211_, v_size_4143_);
                    crate::leanh::lean_dec(v_size_4143_);
                    v___x_4213_ = lean_nat_add(v___x_4211_, v_size_4169_);
                    crate::leanh::lean_dec(v___x_4211_);
                    if v_isShared_4168_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4167_, 4, v_l_4146_);
                        crate::leanh::lean_ctor_set(v___x_4167_, 3, v_tree_4154_);
                        crate::leanh::lean_ctor_set(v___x_4167_, 2, v_v_4156_);
                        crate::leanh::lean_ctor_set(v___x_4167_, 1, v_k_4155_);
                        crate::leanh::lean_ctor_set(v___x_4167_, 0, v___x_4213_);
                        v___x_4215_ = v___x_4167_;
                        state = 38;
                        continue;
                    } else {
                        v_reuseFailAlloc_4219_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4219_, 0, v___x_4213_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4219_, 1, v_k_4155_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4219_, 2, v_v_4156_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4219_, 3, v_tree_4154_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4219_, 4, v_l_4146_);
                        v___x_4215_ = v_reuseFailAlloc_4219_;
                        state = 38;
                        continue;
                    }
                }
            }
            32 => {
                v___x_4181_ = lean_nat_add(v___x_4148_, v_size_4157_);
                v___x_4182_ = lean_nat_add(v___x_4181_, v_size_4143_);
                crate::leanh::lean_dec(v_size_4143_);
                if crate::leanh::lean_obj_tag(v_l_4172_) == 0 {
                    v_size_4203_ = crate::leanh::lean_ctor_get(v_l_4172_, 0);
                    crate::leanh::lean_inc(v_size_4203_);
                    v___y_4195_ = v_size_4203_;
                    state = 36;
                    continue;
                } else {
                    v___x_4204_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4195_ = v___x_4204_;
                    state = 36;
                    continue;
                }
            }
            33 => {
                v___x_4187_ = lean_nat_add(v___y_4184_, v___y_4186_);
                crate::leanh::lean_dec(v___y_4186_);
                crate::leanh::lean_dec(v___y_4184_);
                if v_isShared_4180_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4179_, 4, v_r_4147_);
                    crate::leanh::lean_ctor_set(v___x_4179_, 3, v_r_4173_);
                    crate::leanh::lean_ctor_set(v___x_4179_, 2, v_v_4145_);
                    crate::leanh::lean_ctor_set(v___x_4179_, 1, v_k_4144_);
                    crate::leanh::lean_ctor_set(v___x_4179_, 0, v___x_4187_);
                    v___x_4189_ = v___x_4179_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_4193_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4193_, 0, v___x_4187_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4193_, 1, v_k_4144_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4193_, 2, v_v_4145_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4193_, 3, v_r_4173_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4193_, 4, v_r_4147_);
                    v___x_4189_ = v_reuseFailAlloc_4193_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                if v_isShared_4168_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4167_, 4, v___x_4189_);
                    crate::leanh::lean_ctor_set(v___x_4167_, 3, v___y_4185_);
                    crate::leanh::lean_ctor_set(v___x_4167_, 2, v_v_4171_);
                    crate::leanh::lean_ctor_set(v___x_4167_, 1, v_k_4170_);
                    crate::leanh::lean_ctor_set(v___x_4167_, 0, v___x_4182_);
                    v___x_4191_ = v___x_4167_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_4192_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4192_, 0, v___x_4182_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4192_, 1, v_k_4170_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4192_, 2, v_v_4171_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4192_, 3, v___y_4185_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4192_, 4, v___x_4189_);
                    v___x_4191_ = v_reuseFailAlloc_4192_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_4191_;
            }
            36 => {
                v___x_4196_ = lean_nat_add(v___x_4181_, v___y_4195_);
                crate::leanh::lean_dec(v___y_4195_);
                crate::leanh::lean_dec(v___x_4181_);
                if v_isShared_4152_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4151_, 4, v_l_4172_);
                    crate::leanh::lean_ctor_set(v___x_4151_, 3, v_tree_4154_);
                    crate::leanh::lean_ctor_set(v___x_4151_, 2, v_v_4156_);
                    crate::leanh::lean_ctor_set(v___x_4151_, 1, v_k_4155_);
                    crate::leanh::lean_ctor_set(v___x_4151_, 0, v___x_4196_);
                    v___x_4198_ = v___x_4151_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_4202_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4202_, 0, v___x_4196_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4202_, 1, v_k_4155_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4202_, 2, v_v_4156_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4202_, 3, v_tree_4154_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4202_, 4, v_l_4172_);
                    v___x_4198_ = v_reuseFailAlloc_4202_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                v___x_4199_ = lean_nat_add(v___x_4148_, v_size_4174_);
                if crate::leanh::lean_obj_tag(v_r_4173_) == 0 {
                    v_size_4200_ = crate::leanh::lean_ctor_get(v_r_4173_, 0);
                    crate::leanh::lean_inc(v_size_4200_);
                    v___y_4184_ = v___x_4199_;
                    v___y_4185_ = v___x_4198_;
                    v___y_4186_ = v_size_4200_;
                    state = 33;
                    continue;
                } else {
                    v___x_4201_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4184_ = v___x_4199_;
                    v___y_4185_ = v___x_4198_;
                    v___y_4186_ = v___x_4201_;
                    state = 33;
                    continue;
                }
            }
            38 => {
                if v_isShared_4152_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4151_, 4, v_r_4147_);
                    crate::leanh::lean_ctor_set(v___x_4151_, 3, v___x_4215_);
                    crate::leanh::lean_ctor_set(v___x_4151_, 2, v_v_4145_);
                    crate::leanh::lean_ctor_set(v___x_4151_, 1, v_k_4144_);
                    crate::leanh::lean_ctor_set(v___x_4151_, 0, v___x_4212_);
                    v___x_4217_ = v___x_4151_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_4218_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 0, v___x_4212_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 1, v_k_4144_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 2, v_v_4145_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 3, v___x_4215_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 4, v_r_4147_);
                    v___x_4217_ = v_reuseFailAlloc_4218_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_4217_;
            }
            40 => {
                if crate::leanh::lean_obj_tag(v_l_4146_) == 0 {
                    if crate::leanh::lean_obj_tag(v_r_4147_) == 0 {
                        v_k_4229_ = crate::leanh::lean_ctor_get(v___x_4153_, 0);
                        crate::leanh::lean_inc(v_k_4229_);
                        v_v_4230_ = crate::leanh::lean_ctor_get(v___x_4153_, 1);
                        crate::leanh::lean_inc(v_v_4230_);
                        crate::leanh::lean_dec_ref(v___x_4153_);
                        v_size_4231_ = crate::leanh::lean_ctor_get(v_l_4146_, 0);
                        v___x_4232_ = lean_nat_add(v___x_4148_, v_size_4143_);
                        crate::leanh::lean_dec(v_size_4143_);
                        v___x_4233_ = lean_nat_add(v___x_4148_, v_size_4231_);
                        if v_isShared_4228_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4227_, 4, v_l_4146_);
                            crate::leanh::lean_ctor_set(v___x_4227_, 3, v_tree_4154_);
                            crate::leanh::lean_ctor_set(v___x_4227_, 2, v_v_4230_);
                            crate::leanh::lean_ctor_set(v___x_4227_, 1, v_k_4229_);
                            crate::leanh::lean_ctor_set(v___x_4227_, 0, v___x_4233_);
                            v___x_4235_ = v___x_4227_;
                            state = 41;
                            continue;
                        } else {
                            v_reuseFailAlloc_4239_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4239_, 0, v___x_4233_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4239_, 1, v_k_4229_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4239_, 2, v_v_4230_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4239_, 3, v_tree_4154_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4239_, 4, v_l_4146_);
                            v___x_4235_ = v_reuseFailAlloc_4239_;
                            state = 41;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_size_4143_);
                        v_k_4240_ = crate::leanh::lean_ctor_get(v___x_4153_, 0);
                        crate::leanh::lean_inc(v_k_4240_);
                        v_v_4241_ = crate::leanh::lean_ctor_get(v___x_4153_, 1);
                        crate::leanh::lean_inc(v_v_4241_);
                        crate::leanh::lean_dec_ref(v___x_4153_);
                        v_k_4242_ = crate::leanh::lean_ctor_get(v_l_4146_, 1);
                        v_v_4243_ = crate::leanh::lean_ctor_get(v_l_4146_, 2);
                        v_isSharedCheck_4257_ = (!crate::leanh::lean_is_exclusive(v_l_4146_)) as u8;
                        if v_isSharedCheck_4257_ == 0 {
                            v_unused_4258_ = crate::leanh::lean_ctor_get(v_l_4146_, 4);
                            crate::leanh::lean_dec(v_unused_4258_);
                            v_unused_4259_ = crate::leanh::lean_ctor_get(v_l_4146_, 3);
                            crate::leanh::lean_dec(v_unused_4259_);
                            v_unused_4260_ = crate::leanh::lean_ctor_get(v_l_4146_, 0);
                            crate::leanh::lean_dec(v_unused_4260_);
                            v___x_4245_ = v_l_4146_;
                            v_isShared_4246_ = v_isSharedCheck_4257_;
                            state = 43;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_v_4243_);
                            crate::leanh::lean_inc(v_k_4242_);
                            crate::leanh::lean_dec(v_l_4146_);
                            v___x_4245_ = crate::leanh::lean_box(0);
                            v_isShared_4246_ = v_isSharedCheck_4257_;
                            state = 43;
                            continue;
                        }
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_r_4147_) == 0 {
                        crate::leanh::lean_dec(v_size_4143_);
                        v_k_4261_ = crate::leanh::lean_ctor_get(v___x_4153_, 0);
                        crate::leanh::lean_inc(v_k_4261_);
                        v_v_4262_ = crate::leanh::lean_ctor_get(v___x_4153_, 1);
                        crate::leanh::lean_inc(v_v_4262_);
                        crate::leanh::lean_dec_ref(v___x_4153_);
                        v___x_4263_ = crate::leanh::lean_unsigned_to_nat(3);
                        if v_isShared_4228_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4227_, 4, v_l_4146_);
                            crate::leanh::lean_ctor_set(v___x_4227_, 2, v_v_4262_);
                            crate::leanh::lean_ctor_set(v___x_4227_, 1, v_k_4261_);
                            crate::leanh::lean_ctor_set(v___x_4227_, 0, v___x_4148_);
                            v___x_4265_ = v___x_4227_;
                            state = 47;
                            continue;
                        } else {
                            v_reuseFailAlloc_4269_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 0, v___x_4148_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 1, v_k_4261_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 2, v_v_4262_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 3, v_l_4146_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 4, v_l_4146_);
                            v___x_4265_ = v_reuseFailAlloc_4269_;
                            state = 47;
                            continue;
                        }
                    } else {
                        v_k_4270_ = crate::leanh::lean_ctor_get(v___x_4153_, 0);
                        crate::leanh::lean_inc(v_k_4270_);
                        v_v_4271_ = crate::leanh::lean_ctor_get(v___x_4153_, 1);
                        crate::leanh::lean_inc(v_v_4271_);
                        crate::leanh::lean_dec_ref(v___x_4153_);
                        if v_isShared_4228_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4227_, 3, v_r_4147_);
                            v___x_4273_ = v___x_4227_;
                            state = 49;
                            continue;
                        } else {
                            v_reuseFailAlloc_4278_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4278_, 0, v_size_4143_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4278_, 1, v_k_4144_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4278_, 2, v_v_4145_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4278_, 3, v_r_4147_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4278_, 4, v_r_4147_);
                            v___x_4273_ = v_reuseFailAlloc_4278_;
                            state = 49;
                            continue;
                        }
                    }
                }
            }
            41 => {
                if v_isShared_4152_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4151_, 4, v_r_4147_);
                    crate::leanh::lean_ctor_set(v___x_4151_, 3, v___x_4235_);
                    crate::leanh::lean_ctor_set(v___x_4151_, 2, v_v_4145_);
                    crate::leanh::lean_ctor_set(v___x_4151_, 1, v_k_4144_);
                    crate::leanh::lean_ctor_set(v___x_4151_, 0, v___x_4232_);
                    v___x_4237_ = v___x_4151_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_4238_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4238_, 0, v___x_4232_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4238_, 1, v_k_4144_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4238_, 2, v_v_4145_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4238_, 3, v___x_4235_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4238_, 4, v_r_4147_);
                    v___x_4237_ = v_reuseFailAlloc_4238_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_4237_;
            }
            43 => {
                v___x_4247_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_4246_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4245_, 4, v_r_4147_);
                    crate::leanh::lean_ctor_set(v___x_4245_, 3, v_r_4147_);
                    crate::leanh::lean_ctor_set(v___x_4245_, 2, v_v_4241_);
                    crate::leanh::lean_ctor_set(v___x_4245_, 1, v_k_4240_);
                    crate::leanh::lean_ctor_set(v___x_4245_, 0, v___x_4148_);
                    v___x_4249_ = v___x_4245_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_4256_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4256_, 0, v___x_4148_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4256_, 1, v_k_4240_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4256_, 2, v_v_4241_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4256_, 3, v_r_4147_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4256_, 4, v_r_4147_);
                    v___x_4249_ = v_reuseFailAlloc_4256_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                if v_isShared_4228_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4227_, 3, v_r_4147_);
                    crate::leanh::lean_ctor_set(v___x_4227_, 0, v___x_4148_);
                    v___x_4251_ = v___x_4227_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_4255_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4255_, 0, v___x_4148_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4255_, 1, v_k_4144_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4255_, 2, v_v_4145_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4255_, 3, v_r_4147_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4255_, 4, v_r_4147_);
                    v___x_4251_ = v_reuseFailAlloc_4255_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_4152_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4151_, 4, v___x_4251_);
                    crate::leanh::lean_ctor_set(v___x_4151_, 3, v___x_4249_);
                    crate::leanh::lean_ctor_set(v___x_4151_, 2, v_v_4243_);
                    crate::leanh::lean_ctor_set(v___x_4151_, 1, v_k_4242_);
                    crate::leanh::lean_ctor_set(v___x_4151_, 0, v___x_4247_);
                    v___x_4253_ = v___x_4151_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_4254_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4254_, 0, v___x_4247_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4254_, 1, v_k_4242_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4254_, 2, v_v_4243_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4254_, 3, v___x_4249_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4254_, 4, v___x_4251_);
                    v___x_4253_ = v_reuseFailAlloc_4254_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_4253_;
            }
            47 => {
                if v_isShared_4152_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4151_, 4, v_r_4147_);
                    crate::leanh::lean_ctor_set(v___x_4151_, 3, v___x_4265_);
                    crate::leanh::lean_ctor_set(v___x_4151_, 2, v_v_4145_);
                    crate::leanh::lean_ctor_set(v___x_4151_, 1, v_k_4144_);
                    crate::leanh::lean_ctor_set(v___x_4151_, 0, v___x_4263_);
                    v___x_4267_ = v___x_4151_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_4268_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4268_, 0, v___x_4263_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4268_, 1, v_k_4144_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4268_, 2, v_v_4145_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4268_, 3, v___x_4265_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4268_, 4, v_r_4147_);
                    v___x_4267_ = v_reuseFailAlloc_4268_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_4267_;
            }
            49 => {
                v___x_4274_ = crate::leanh::lean_unsigned_to_nat(2);
                if v_isShared_4152_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4151_, 4, v___x_4273_);
                    crate::leanh::lean_ctor_set(v___x_4151_, 3, v_r_4147_);
                    crate::leanh::lean_ctor_set(v___x_4151_, 2, v_v_4271_);
                    crate::leanh::lean_ctor_set(v___x_4151_, 1, v_k_4270_);
                    crate::leanh::lean_ctor_set(v___x_4151_, 0, v___x_4274_);
                    v___x_4276_ = v___x_4151_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_4277_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4277_, 0, v___x_4274_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4277_, 1, v_k_4270_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4277_, 2, v_v_4271_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4277_, 3, v_r_4147_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4277_, 4, v___x_4273_);
                    v___x_4276_ = v_reuseFailAlloc_4277_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_4276_;
            }
            51 => {
                v___x_4294_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(
                    v_k_4144_, v_v_4145_, v_l_4146_, v_r_4147_,
                );
                v_tree_4295_ = crate::leanh::lean_ctor_get(v___x_4294_, 2);
                crate::leanh::lean_inc(v_tree_4295_);
                if crate::leanh::lean_obj_tag(v_tree_4295_) == 0 {
                    v_k_4296_ = crate::leanh::lean_ctor_get(v___x_4294_, 0);
                    crate::leanh::lean_inc(v_k_4296_);
                    v_v_4297_ = crate::leanh::lean_ctor_get(v___x_4294_, 1);
                    crate::leanh::lean_inc(v_v_4297_);
                    crate::leanh::lean_dec_ref(v___x_4294_);
                    v_size_4298_ = crate::leanh::lean_ctor_get(v_tree_4295_, 0);
                    v___x_4299_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_4300_ = lean_nat_mul(v___x_4299_, v_size_4298_);
                    v___x_4301_ = lean_nat_dec_lt(v___x_4300_, v_size_4138_);
                    crate::leanh::lean_dec(v___x_4300_);
                    if v___x_4301_ == 0 {
                        crate::leanh::lean_dec(v_r_4142_);
                        v___x_4302_ = lean_nat_add(v___x_4148_, v_size_4138_);
                        v___x_4303_ = lean_nat_add(v___x_4302_, v_size_4298_);
                        crate::leanh::lean_dec(v___x_4302_);
                        if v_isShared_4293_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4292_, 4, v_tree_4295_);
                            crate::leanh::lean_ctor_set(v___x_4292_, 3, v_l_3958_);
                            crate::leanh::lean_ctor_set(v___x_4292_, 2, v_v_4297_);
                            crate::leanh::lean_ctor_set(v___x_4292_, 1, v_k_4296_);
                            crate::leanh::lean_ctor_set(v___x_4292_, 0, v___x_4303_);
                            v___x_4305_ = v___x_4292_;
                            state = 52;
                            continue;
                        } else {
                            v_reuseFailAlloc_4306_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4306_, 0, v___x_4303_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4306_, 1, v_k_4296_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4306_, 2, v_v_4297_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4306_, 3, v_l_3958_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4306_, 4, v_tree_4295_);
                            v___x_4305_ = v_reuseFailAlloc_4306_;
                            state = 52;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc(v_l_4141_);
                        crate::leanh::lean_inc(v_v_4140_);
                        crate::leanh::lean_inc(v_k_4139_);
                        crate::leanh::lean_inc(v_size_4138_);
                        v_isSharedCheck_4372_ = (!crate::leanh::lean_is_exclusive(v_l_3958_)) as u8;
                        if v_isSharedCheck_4372_ == 0 {
                            v_unused_4373_ = crate::leanh::lean_ctor_get(v_l_3958_, 4);
                            crate::leanh::lean_dec(v_unused_4373_);
                            v_unused_4374_ = crate::leanh::lean_ctor_get(v_l_3958_, 3);
                            crate::leanh::lean_dec(v_unused_4374_);
                            v_unused_4375_ = crate::leanh::lean_ctor_get(v_l_3958_, 2);
                            crate::leanh::lean_dec(v_unused_4375_);
                            v_unused_4376_ = crate::leanh::lean_ctor_get(v_l_3958_, 1);
                            crate::leanh::lean_dec(v_unused_4376_);
                            v_unused_4377_ = crate::leanh::lean_ctor_get(v_l_3958_, 0);
                            crate::leanh::lean_dec(v_unused_4377_);
                            v___x_4308_ = v_l_3958_;
                            v_isShared_4309_ = v_isSharedCheck_4372_;
                            state = 53;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_l_3958_);
                            v___x_4308_ = crate::leanh::lean_box(0);
                            v_isShared_4309_ = v_isSharedCheck_4372_;
                            state = 53;
                            continue;
                        }
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_l_4141_) == 0 {
                        crate::leanh::lean_inc_ref(v_l_4141_);
                        crate::leanh::lean_inc(v_v_4140_);
                        crate::leanh::lean_inc(v_k_4139_);
                        crate::leanh::lean_inc(v_size_4138_);
                        v_isSharedCheck_4401_ = (!crate::leanh::lean_is_exclusive(v_l_3958_)) as u8;
                        if v_isSharedCheck_4401_ == 0 {
                            v_unused_4402_ = crate::leanh::lean_ctor_get(v_l_3958_, 4);
                            crate::leanh::lean_dec(v_unused_4402_);
                            v_unused_4403_ = crate::leanh::lean_ctor_get(v_l_3958_, 3);
                            crate::leanh::lean_dec(v_unused_4403_);
                            v_unused_4404_ = crate::leanh::lean_ctor_get(v_l_3958_, 2);
                            crate::leanh::lean_dec(v_unused_4404_);
                            v_unused_4405_ = crate::leanh::lean_ctor_get(v_l_3958_, 1);
                            crate::leanh::lean_dec(v_unused_4405_);
                            v_unused_4406_ = crate::leanh::lean_ctor_get(v_l_3958_, 0);
                            crate::leanh::lean_dec(v_unused_4406_);
                            v___x_4379_ = v_l_3958_;
                            v_isShared_4380_ = v_isSharedCheck_4401_;
                            state = 63;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_l_3958_);
                            v___x_4379_ = crate::leanh::lean_box(0);
                            v_isShared_4380_ = v_isSharedCheck_4401_;
                            state = 63;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v_r_4142_) == 0 {
                            crate::leanh::lean_inc(v_l_4141_);
                            crate::leanh::lean_inc(v_v_4140_);
                            crate::leanh::lean_inc(v_k_4139_);
                            v_isSharedCheck_4431_ =
                                (!crate::leanh::lean_is_exclusive(v_l_3958_)) as u8;
                            if v_isSharedCheck_4431_ == 0 {
                                v_unused_4432_ = crate::leanh::lean_ctor_get(v_l_3958_, 4);
                                crate::leanh::lean_dec(v_unused_4432_);
                                v_unused_4433_ = crate::leanh::lean_ctor_get(v_l_3958_, 3);
                                crate::leanh::lean_dec(v_unused_4433_);
                                v_unused_4434_ = crate::leanh::lean_ctor_get(v_l_3958_, 2);
                                crate::leanh::lean_dec(v_unused_4434_);
                                v_unused_4435_ = crate::leanh::lean_ctor_get(v_l_3958_, 1);
                                crate::leanh::lean_dec(v_unused_4435_);
                                v_unused_4436_ = crate::leanh::lean_ctor_get(v_l_3958_, 0);
                                crate::leanh::lean_dec(v_unused_4436_);
                                v___x_4408_ = v_l_3958_;
                                v_isShared_4409_ = v_isSharedCheck_4431_;
                                state = 68;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_l_3958_);
                                v___x_4408_ = crate::leanh::lean_box(0);
                                v_isShared_4409_ = v_isSharedCheck_4431_;
                                state = 68;
                                continue;
                            }
                        } else {
                            v_k_4437_ = crate::leanh::lean_ctor_get(v___x_4294_, 0);
                            crate::leanh::lean_inc(v_k_4437_);
                            v_v_4438_ = crate::leanh::lean_ctor_get(v___x_4294_, 1);
                            crate::leanh::lean_inc(v_v_4438_);
                            crate::leanh::lean_dec_ref(v___x_4294_);
                            v___x_4439_ = crate::leanh::lean_unsigned_to_nat(2);
                            if v_isShared_4293_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4292_, 4, v_r_4142_);
                                crate::leanh::lean_ctor_set(v___x_4292_, 3, v_l_3958_);
                                crate::leanh::lean_ctor_set(v___x_4292_, 2, v_v_4438_);
                                crate::leanh::lean_ctor_set(v___x_4292_, 1, v_k_4437_);
                                crate::leanh::lean_ctor_set(v___x_4292_, 0, v___x_4439_);
                                v___x_4441_ = v___x_4292_;
                                state = 73;
                                continue;
                            } else {
                                v_reuseFailAlloc_4442_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4442_, 0, v___x_4439_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4442_, 1, v_k_4437_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4442_, 2, v_v_4438_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4442_, 3, v_l_3958_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4442_, 4, v_r_4142_);
                                v___x_4441_ = v_reuseFailAlloc_4442_;
                                state = 73;
                                continue;
                            }
                        }
                    }
                }
            }
            52 => {
                return v___x_4305_;
            }
            53 => {
                v_size_4310_ = crate::leanh::lean_ctor_get(v_l_4141_, 0);
                v_size_4311_ = crate::leanh::lean_ctor_get(v_r_4142_, 0);
                v_k_4312_ = crate::leanh::lean_ctor_get(v_r_4142_, 1);
                v_v_4313_ = crate::leanh::lean_ctor_get(v_r_4142_, 2);
                v_l_4314_ = crate::leanh::lean_ctor_get(v_r_4142_, 3);
                v_r_4315_ = crate::leanh::lean_ctor_get(v_r_4142_, 4);
                v___x_4316_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_4317_ = lean_nat_mul(v___x_4316_, v_size_4310_);
                v___x_4318_ = lean_nat_dec_lt(v_size_4311_, v___x_4317_);
                crate::leanh::lean_dec(v___x_4317_);
                if v___x_4318_ == 0 {
                    crate::leanh::lean_inc(v_r_4315_);
                    crate::leanh::lean_inc(v_l_4314_);
                    crate::leanh::lean_inc(v_v_4313_);
                    crate::leanh::lean_inc(v_k_4312_);
                    crate::leanh::lean_del_object(v___x_4308_);
                    v_isSharedCheck_4356_ = (!crate::leanh::lean_is_exclusive(v_r_4142_)) as u8;
                    if v_isSharedCheck_4356_ == 0 {
                        v_unused_4357_ = crate::leanh::lean_ctor_get(v_r_4142_, 4);
                        crate::leanh::lean_dec(v_unused_4357_);
                        v_unused_4358_ = crate::leanh::lean_ctor_get(v_r_4142_, 3);
                        crate::leanh::lean_dec(v_unused_4358_);
                        v_unused_4359_ = crate::leanh::lean_ctor_get(v_r_4142_, 2);
                        crate::leanh::lean_dec(v_unused_4359_);
                        v_unused_4360_ = crate::leanh::lean_ctor_get(v_r_4142_, 1);
                        crate::leanh::lean_dec(v_unused_4360_);
                        v_unused_4361_ = crate::leanh::lean_ctor_get(v_r_4142_, 0);
                        crate::leanh::lean_dec(v_unused_4361_);
                        v___x_4320_ = v_r_4142_;
                        v_isShared_4321_ = v_isSharedCheck_4356_;
                        state = 54;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_4142_);
                        v___x_4320_ = crate::leanh::lean_box(0);
                        v_isShared_4321_ = v_isSharedCheck_4356_;
                        state = 54;
                        continue;
                    }
                } else {
                    v___x_4362_ = lean_nat_add(v___x_4148_, v_size_4138_);
                    crate::leanh::lean_dec(v_size_4138_);
                    v___x_4363_ = lean_nat_add(v___x_4362_, v_size_4298_);
                    crate::leanh::lean_dec(v___x_4362_);
                    v___x_4364_ = lean_nat_add(v___x_4148_, v_size_4298_);
                    v___x_4365_ = lean_nat_add(v___x_4364_, v_size_4311_);
                    crate::leanh::lean_dec(v___x_4364_);
                    if v_isShared_4293_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4292_, 4, v_tree_4295_);
                        crate::leanh::lean_ctor_set(v___x_4292_, 3, v_r_4142_);
                        crate::leanh::lean_ctor_set(v___x_4292_, 2, v_v_4297_);
                        crate::leanh::lean_ctor_set(v___x_4292_, 1, v_k_4296_);
                        crate::leanh::lean_ctor_set(v___x_4292_, 0, v___x_4365_);
                        v___x_4367_ = v___x_4292_;
                        state = 61;
                        continue;
                    } else {
                        v_reuseFailAlloc_4371_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4371_, 0, v___x_4365_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4371_, 1, v_k_4296_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4371_, 2, v_v_4297_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4371_, 3, v_r_4142_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4371_, 4, v_tree_4295_);
                        v___x_4367_ = v_reuseFailAlloc_4371_;
                        state = 61;
                        continue;
                    }
                }
            }
            54 => {
                v___x_4322_ = lean_nat_add(v___x_4148_, v_size_4138_);
                crate::leanh::lean_dec(v_size_4138_);
                v___x_4323_ = lean_nat_add(v___x_4322_, v_size_4298_);
                crate::leanh::lean_dec(v___x_4322_);
                v___x_4344_ = lean_nat_add(v___x_4148_, v_size_4310_);
                if crate::leanh::lean_obj_tag(v_l_4314_) == 0 {
                    v_size_4354_ = crate::leanh::lean_ctor_get(v_l_4314_, 0);
                    crate::leanh::lean_inc(v_size_4354_);
                    v___y_4346_ = v_size_4354_;
                    state = 59;
                    continue;
                } else {
                    v___x_4355_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4346_ = v___x_4355_;
                    state = 59;
                    continue;
                }
            }
            55 => {
                v___x_4328_ = lean_nat_add(v___y_4326_, v___y_4327_);
                crate::leanh::lean_dec(v___y_4327_);
                crate::leanh::lean_dec(v___y_4326_);
                crate::leanh::lean_inc_ref(v_tree_4295_);
                if v_isShared_4321_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4320_, 4, v_tree_4295_);
                    crate::leanh::lean_ctor_set(v___x_4320_, 3, v_r_4315_);
                    crate::leanh::lean_ctor_set(v___x_4320_, 2, v_v_4297_);
                    crate::leanh::lean_ctor_set(v___x_4320_, 1, v_k_4296_);
                    crate::leanh::lean_ctor_set(v___x_4320_, 0, v___x_4328_);
                    v___x_4330_ = v___x_4320_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_4343_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4343_, 0, v___x_4328_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4343_, 1, v_k_4296_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4343_, 2, v_v_4297_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4343_, 3, v_r_4315_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4343_, 4, v_tree_4295_);
                    v___x_4330_ = v_reuseFailAlloc_4343_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                v_isSharedCheck_4337_ = (!crate::leanh::lean_is_exclusive(v_tree_4295_)) as u8;
                if v_isSharedCheck_4337_ == 0 {
                    v_unused_4338_ = crate::leanh::lean_ctor_get(v_tree_4295_, 4);
                    crate::leanh::lean_dec(v_unused_4338_);
                    v_unused_4339_ = crate::leanh::lean_ctor_get(v_tree_4295_, 3);
                    crate::leanh::lean_dec(v_unused_4339_);
                    v_unused_4340_ = crate::leanh::lean_ctor_get(v_tree_4295_, 2);
                    crate::leanh::lean_dec(v_unused_4340_);
                    v_unused_4341_ = crate::leanh::lean_ctor_get(v_tree_4295_, 1);
                    crate::leanh::lean_dec(v_unused_4341_);
                    v_unused_4342_ = crate::leanh::lean_ctor_get(v_tree_4295_, 0);
                    crate::leanh::lean_dec(v_unused_4342_);
                    v___x_4332_ = v_tree_4295_;
                    v_isShared_4333_ = v_isSharedCheck_4337_;
                    state = 57;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_tree_4295_);
                    v___x_4332_ = crate::leanh::lean_box(0);
                    v_isShared_4333_ = v_isSharedCheck_4337_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                if v_isShared_4333_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4332_, 4, v___x_4330_);
                    crate::leanh::lean_ctor_set(v___x_4332_, 3, v___y_4325_);
                    crate::leanh::lean_ctor_set(v___x_4332_, 2, v_v_4313_);
                    crate::leanh::lean_ctor_set(v___x_4332_, 1, v_k_4312_);
                    crate::leanh::lean_ctor_set(v___x_4332_, 0, v___x_4323_);
                    v___x_4335_ = v___x_4332_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_4336_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4336_, 0, v___x_4323_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4336_, 1, v_k_4312_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4336_, 2, v_v_4313_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4336_, 3, v___y_4325_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4336_, 4, v___x_4330_);
                    v___x_4335_ = v_reuseFailAlloc_4336_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                return v___x_4335_;
            }
            59 => {
                v___x_4347_ = lean_nat_add(v___x_4344_, v___y_4346_);
                crate::leanh::lean_dec(v___y_4346_);
                crate::leanh::lean_dec(v___x_4344_);
                if v_isShared_4293_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4292_, 4, v_l_4314_);
                    crate::leanh::lean_ctor_set(v___x_4292_, 3, v_l_4141_);
                    crate::leanh::lean_ctor_set(v___x_4292_, 2, v_v_4140_);
                    crate::leanh::lean_ctor_set(v___x_4292_, 1, v_k_4139_);
                    crate::leanh::lean_ctor_set(v___x_4292_, 0, v___x_4347_);
                    v___x_4349_ = v___x_4292_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_4353_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4353_, 0, v___x_4347_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4353_, 1, v_k_4139_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4353_, 2, v_v_4140_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4353_, 3, v_l_4141_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4353_, 4, v_l_4314_);
                    v___x_4349_ = v_reuseFailAlloc_4353_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                v___x_4350_ = lean_nat_add(v___x_4148_, v_size_4298_);
                if crate::leanh::lean_obj_tag(v_r_4315_) == 0 {
                    v_size_4351_ = crate::leanh::lean_ctor_get(v_r_4315_, 0);
                    crate::leanh::lean_inc(v_size_4351_);
                    v___y_4325_ = v___x_4349_;
                    v___y_4326_ = v___x_4350_;
                    v___y_4327_ = v_size_4351_;
                    state = 55;
                    continue;
                } else {
                    v___x_4352_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4325_ = v___x_4349_;
                    v___y_4326_ = v___x_4350_;
                    v___y_4327_ = v___x_4352_;
                    state = 55;
                    continue;
                }
            }
            61 => {
                if v_isShared_4309_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4308_, 4, v___x_4367_);
                    crate::leanh::lean_ctor_set(v___x_4308_, 0, v___x_4363_);
                    v___x_4369_ = v___x_4308_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_4370_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4370_, 0, v___x_4363_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4370_, 1, v_k_4139_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4370_, 2, v_v_4140_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4370_, 3, v_l_4141_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4370_, 4, v___x_4367_);
                    v___x_4369_ = v_reuseFailAlloc_4370_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                return v___x_4369_;
            }
            63 => {
                if crate::leanh::lean_obj_tag(v_r_4142_) == 0 {
                    v_k_4381_ = crate::leanh::lean_ctor_get(v___x_4294_, 0);
                    crate::leanh::lean_inc(v_k_4381_);
                    v_v_4382_ = crate::leanh::lean_ctor_get(v___x_4294_, 1);
                    crate::leanh::lean_inc(v_v_4382_);
                    crate::leanh::lean_dec_ref(v___x_4294_);
                    v_size_4383_ = crate::leanh::lean_ctor_get(v_r_4142_, 0);
                    v___x_4384_ = lean_nat_add(v___x_4148_, v_size_4138_);
                    crate::leanh::lean_dec(v_size_4138_);
                    v___x_4385_ = lean_nat_add(v___x_4148_, v_size_4383_);
                    if v_isShared_4293_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4292_, 4, v_tree_4295_);
                        crate::leanh::lean_ctor_set(v___x_4292_, 3, v_r_4142_);
                        crate::leanh::lean_ctor_set(v___x_4292_, 2, v_v_4382_);
                        crate::leanh::lean_ctor_set(v___x_4292_, 1, v_k_4381_);
                        crate::leanh::lean_ctor_set(v___x_4292_, 0, v___x_4385_);
                        v___x_4387_ = v___x_4292_;
                        state = 64;
                        continue;
                    } else {
                        v_reuseFailAlloc_4391_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4391_, 0, v___x_4385_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4391_, 1, v_k_4381_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4391_, 2, v_v_4382_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4391_, 3, v_r_4142_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4391_, 4, v_tree_4295_);
                        v___x_4387_ = v_reuseFailAlloc_4391_;
                        state = 64;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_size_4138_);
                    v_k_4392_ = crate::leanh::lean_ctor_get(v___x_4294_, 0);
                    crate::leanh::lean_inc(v_k_4392_);
                    v_v_4393_ = crate::leanh::lean_ctor_get(v___x_4294_, 1);
                    crate::leanh::lean_inc(v_v_4393_);
                    crate::leanh::lean_dec_ref(v___x_4294_);
                    v___x_4394_ = crate::leanh::lean_unsigned_to_nat(3);
                    if v_isShared_4293_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4292_, 4, v_r_4142_);
                        crate::leanh::lean_ctor_set(v___x_4292_, 3, v_r_4142_);
                        crate::leanh::lean_ctor_set(v___x_4292_, 2, v_v_4393_);
                        crate::leanh::lean_ctor_set(v___x_4292_, 1, v_k_4392_);
                        crate::leanh::lean_ctor_set(v___x_4292_, 0, v___x_4148_);
                        v___x_4396_ = v___x_4292_;
                        state = 66;
                        continue;
                    } else {
                        v_reuseFailAlloc_4400_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4400_, 0, v___x_4148_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4400_, 1, v_k_4392_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4400_, 2, v_v_4393_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4400_, 3, v_r_4142_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4400_, 4, v_r_4142_);
                        v___x_4396_ = v_reuseFailAlloc_4400_;
                        state = 66;
                        continue;
                    }
                }
            }
            64 => {
                if v_isShared_4380_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4379_, 4, v___x_4387_);
                    crate::leanh::lean_ctor_set(v___x_4379_, 0, v___x_4384_);
                    v___x_4389_ = v___x_4379_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_4390_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4390_, 0, v___x_4384_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4390_, 1, v_k_4139_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4390_, 2, v_v_4140_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4390_, 3, v_l_4141_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4390_, 4, v___x_4387_);
                    v___x_4389_ = v_reuseFailAlloc_4390_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_4389_;
            }
            66 => {
                if v_isShared_4380_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4379_, 4, v___x_4396_);
                    crate::leanh::lean_ctor_set(v___x_4379_, 0, v___x_4394_);
                    v___x_4398_ = v___x_4379_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_4399_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4399_, 0, v___x_4394_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4399_, 1, v_k_4139_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4399_, 2, v_v_4140_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4399_, 3, v_l_4141_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4399_, 4, v___x_4396_);
                    v___x_4398_ = v_reuseFailAlloc_4399_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_4398_;
            }
            68 => {
                v_k_4410_ = crate::leanh::lean_ctor_get(v___x_4294_, 0);
                crate::leanh::lean_inc(v_k_4410_);
                v_v_4411_ = crate::leanh::lean_ctor_get(v___x_4294_, 1);
                crate::leanh::lean_inc(v_v_4411_);
                crate::leanh::lean_dec_ref(v___x_4294_);
                v_k_4412_ = crate::leanh::lean_ctor_get(v_r_4142_, 1);
                v_v_4413_ = crate::leanh::lean_ctor_get(v_r_4142_, 2);
                v_isSharedCheck_4427_ = (!crate::leanh::lean_is_exclusive(v_r_4142_)) as u8;
                if v_isSharedCheck_4427_ == 0 {
                    v_unused_4428_ = crate::leanh::lean_ctor_get(v_r_4142_, 4);
                    crate::leanh::lean_dec(v_unused_4428_);
                    v_unused_4429_ = crate::leanh::lean_ctor_get(v_r_4142_, 3);
                    crate::leanh::lean_dec(v_unused_4429_);
                    v_unused_4430_ = crate::leanh::lean_ctor_get(v_r_4142_, 0);
                    crate::leanh::lean_dec(v_unused_4430_);
                    v___x_4415_ = v_r_4142_;
                    v_isShared_4416_ = v_isSharedCheck_4427_;
                    state = 69;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_4413_);
                    crate::leanh::lean_inc(v_k_4412_);
                    crate::leanh::lean_dec(v_r_4142_);
                    v___x_4415_ = crate::leanh::lean_box(0);
                    v_isShared_4416_ = v_isSharedCheck_4427_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                v___x_4417_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_4416_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4415_, 4, v_l_4141_);
                    crate::leanh::lean_ctor_set(v___x_4415_, 3, v_l_4141_);
                    crate::leanh::lean_ctor_set(v___x_4415_, 2, v_v_4140_);
                    crate::leanh::lean_ctor_set(v___x_4415_, 1, v_k_4139_);
                    crate::leanh::lean_ctor_set(v___x_4415_, 0, v___x_4148_);
                    v___x_4419_ = v___x_4415_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_4426_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4426_, 0, v___x_4148_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4426_, 1, v_k_4139_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4426_, 2, v_v_4140_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4426_, 3, v_l_4141_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4426_, 4, v_l_4141_);
                    v___x_4419_ = v_reuseFailAlloc_4426_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                if v_isShared_4293_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4292_, 4, v_l_4141_);
                    crate::leanh::lean_ctor_set(v___x_4292_, 3, v_l_4141_);
                    crate::leanh::lean_ctor_set(v___x_4292_, 2, v_v_4411_);
                    crate::leanh::lean_ctor_set(v___x_4292_, 1, v_k_4410_);
                    crate::leanh::lean_ctor_set(v___x_4292_, 0, v___x_4148_);
                    v___x_4421_ = v___x_4292_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_4425_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4148_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4425_, 1, v_k_4410_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4425_, 2, v_v_4411_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4425_, 3, v_l_4141_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4425_, 4, v_l_4141_);
                    v___x_4421_ = v_reuseFailAlloc_4425_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                if v_isShared_4409_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4408_, 4, v___x_4421_);
                    crate::leanh::lean_ctor_set(v___x_4408_, 3, v___x_4419_);
                    crate::leanh::lean_ctor_set(v___x_4408_, 2, v_v_4413_);
                    crate::leanh::lean_ctor_set(v___x_4408_, 1, v_k_4412_);
                    crate::leanh::lean_ctor_set(v___x_4408_, 0, v___x_4417_);
                    v___x_4423_ = v___x_4408_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_4424_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4424_, 0, v___x_4417_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4424_, 1, v_k_4412_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4424_, 2, v_v_4413_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4424_, 3, v___x_4419_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4424_, 4, v___x_4421_);
                    v___x_4423_ = v_reuseFailAlloc_4424_;
                    state = 72;
                    continue;
                }
            }
            72 => {
                return v___x_4423_;
            }
            73 => {
                return v___x_4441_;
            }
            74 => {
                return v___x_4463_;
            }
            75 => {
                v_size_4468_ = crate::leanh::lean_ctor_get(v_l_4455_, 0);
                v_size_4469_ = crate::leanh::lean_ctor_get(v_r_4456_, 0);
                v_k_4470_ = crate::leanh::lean_ctor_get(v_r_4456_, 1);
                v_v_4471_ = crate::leanh::lean_ctor_get(v_r_4456_, 2);
                v_l_4472_ = crate::leanh::lean_ctor_get(v_r_4456_, 3);
                v_r_4473_ = crate::leanh::lean_ctor_get(v_r_4456_, 4);
                v___x_4474_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_4475_ = lean_nat_mul(v___x_4474_, v_size_4468_);
                v___x_4476_ = lean_nat_dec_lt(v_size_4469_, v___x_4475_);
                crate::leanh::lean_dec(v___x_4475_);
                if v___x_4476_ == 0 {
                    crate::leanh::lean_inc(v_r_4473_);
                    crate::leanh::lean_inc(v_l_4472_);
                    crate::leanh::lean_inc(v_v_4471_);
                    crate::leanh::lean_inc(v_k_4470_);
                    v_isSharedCheck_4505_ = (!crate::leanh::lean_is_exclusive(v_r_4456_)) as u8;
                    if v_isSharedCheck_4505_ == 0 {
                        v_unused_4506_ = crate::leanh::lean_ctor_get(v_r_4456_, 4);
                        crate::leanh::lean_dec(v_unused_4506_);
                        v_unused_4507_ = crate::leanh::lean_ctor_get(v_r_4456_, 3);
                        crate::leanh::lean_dec(v_unused_4507_);
                        v_unused_4508_ = crate::leanh::lean_ctor_get(v_r_4456_, 2);
                        crate::leanh::lean_dec(v_unused_4508_);
                        v_unused_4509_ = crate::leanh::lean_ctor_get(v_r_4456_, 1);
                        crate::leanh::lean_dec(v_unused_4509_);
                        v_unused_4510_ = crate::leanh::lean_ctor_get(v_r_4456_, 0);
                        crate::leanh::lean_dec(v_unused_4510_);
                        v___x_4478_ = v_r_4456_;
                        v_isShared_4479_ = v_isSharedCheck_4505_;
                        state = 76;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_4456_);
                        v___x_4478_ = crate::leanh::lean_box(0);
                        v_isShared_4479_ = v_isSharedCheck_4505_;
                        state = 76;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3961_);
                    v___x_4511_ = lean_nat_add(v___x_4450_, v_size_4452_);
                    crate::leanh::lean_dec(v_size_4452_);
                    v___x_4512_ = lean_nat_add(v___x_4511_, v_size_4451_);
                    crate::leanh::lean_dec(v___x_4511_);
                    v___x_4513_ = lean_nat_add(v___x_4450_, v_size_4451_);
                    crate::leanh::lean_dec(v_size_4451_);
                    v___x_4514_ = lean_nat_add(v___x_4513_, v_size_4469_);
                    crate::leanh::lean_dec(v___x_4513_);
                    crate::leanh::lean_inc_ref(v_impl_4449_);
                    if v_isShared_4467_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4466_, 4, v_impl_4449_);
                        crate::leanh::lean_ctor_set(v___x_4466_, 3, v_r_4456_);
                        crate::leanh::lean_ctor_set(v___x_4466_, 2, v_v_3957_);
                        crate::leanh::lean_ctor_set(v___x_4466_, 1, v_k_3956_);
                        crate::leanh::lean_ctor_set(v___x_4466_, 0, v___x_4514_);
                        v___x_4516_ = v___x_4466_;
                        state = 82;
                        continue;
                    } else {
                        v_reuseFailAlloc_4529_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4529_, 0, v___x_4514_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4529_, 1, v_k_3956_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4529_, 2, v_v_3957_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4529_, 3, v_r_4456_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4529_, 4, v_impl_4449_);
                        v___x_4516_ = v_reuseFailAlloc_4529_;
                        state = 82;
                        continue;
                    }
                }
            }
            76 => {
                v___x_4480_ = lean_nat_add(v___x_4450_, v_size_4452_);
                crate::leanh::lean_dec(v_size_4452_);
                v___x_4481_ = lean_nat_add(v___x_4480_, v_size_4451_);
                crate::leanh::lean_dec(v___x_4480_);
                v___x_4493_ = lean_nat_add(v___x_4450_, v_size_4468_);
                if crate::leanh::lean_obj_tag(v_l_4472_) == 0 {
                    v_size_4503_ = crate::leanh::lean_ctor_get(v_l_4472_, 0);
                    crate::leanh::lean_inc(v_size_4503_);
                    v___y_4495_ = v_size_4503_;
                    state = 80;
                    continue;
                } else {
                    v___x_4504_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4495_ = v___x_4504_;
                    state = 80;
                    continue;
                }
            }
            77 => {
                v___x_4486_ = lean_nat_add(v___y_4484_, v___y_4485_);
                crate::leanh::lean_dec(v___y_4485_);
                crate::leanh::lean_dec(v___y_4484_);
                if v_isShared_4479_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4478_, 4, v_impl_4449_);
                    crate::leanh::lean_ctor_set(v___x_4478_, 3, v_r_4473_);
                    crate::leanh::lean_ctor_set(v___x_4478_, 2, v_v_3957_);
                    crate::leanh::lean_ctor_set(v___x_4478_, 1, v_k_3956_);
                    crate::leanh::lean_ctor_set(v___x_4478_, 0, v___x_4486_);
                    v___x_4488_ = v___x_4478_;
                    state = 78;
                    continue;
                } else {
                    v_reuseFailAlloc_4492_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4492_, 0, v___x_4486_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4492_, 1, v_k_3956_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4492_, 2, v_v_3957_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4492_, 3, v_r_4473_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4492_, 4, v_impl_4449_);
                    v___x_4488_ = v_reuseFailAlloc_4492_;
                    state = 78;
                    continue;
                }
            }
            78 => {
                if v_isShared_4467_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4466_, 4, v___x_4488_);
                    crate::leanh::lean_ctor_set(v___x_4466_, 3, v___y_4483_);
                    crate::leanh::lean_ctor_set(v___x_4466_, 2, v_v_4471_);
                    crate::leanh::lean_ctor_set(v___x_4466_, 1, v_k_4470_);
                    crate::leanh::lean_ctor_set(v___x_4466_, 0, v___x_4481_);
                    v___x_4490_ = v___x_4466_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_4491_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4491_, 0, v___x_4481_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4491_, 1, v_k_4470_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4491_, 2, v_v_4471_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4491_, 3, v___y_4483_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4491_, 4, v___x_4488_);
                    v___x_4490_ = v_reuseFailAlloc_4491_;
                    state = 79;
                    continue;
                }
            }
            79 => {
                return v___x_4490_;
            }
            80 => {
                v___x_4496_ = lean_nat_add(v___x_4493_, v___y_4495_);
                crate::leanh::lean_dec(v___y_4495_);
                crate::leanh::lean_dec(v___x_4493_);
                if v_isShared_3962_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3961_, 4, v_l_4472_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 3, v_l_4455_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 2, v_v_4454_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 1, v_k_4453_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 0, v___x_4496_);
                    v___x_4498_ = v___x_3961_;
                    state = 81;
                    continue;
                } else {
                    v_reuseFailAlloc_4502_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4502_, 0, v___x_4496_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4502_, 1, v_k_4453_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4502_, 2, v_v_4454_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4502_, 3, v_l_4455_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4502_, 4, v_l_4472_);
                    v___x_4498_ = v_reuseFailAlloc_4502_;
                    state = 81;
                    continue;
                }
            }
            81 => {
                v___x_4499_ = lean_nat_add(v___x_4450_, v_size_4451_);
                crate::leanh::lean_dec(v_size_4451_);
                if crate::leanh::lean_obj_tag(v_r_4473_) == 0 {
                    v_size_4500_ = crate::leanh::lean_ctor_get(v_r_4473_, 0);
                    crate::leanh::lean_inc(v_size_4500_);
                    v___y_4483_ = v___x_4498_;
                    v___y_4484_ = v___x_4499_;
                    v___y_4485_ = v_size_4500_;
                    state = 77;
                    continue;
                } else {
                    v___x_4501_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4483_ = v___x_4498_;
                    v___y_4484_ = v___x_4499_;
                    v___y_4485_ = v___x_4501_;
                    state = 77;
                    continue;
                }
            }
            82 => {
                v_isSharedCheck_4523_ = (!crate::leanh::lean_is_exclusive(v_impl_4449_)) as u8;
                if v_isSharedCheck_4523_ == 0 {
                    v_unused_4524_ = crate::leanh::lean_ctor_get(v_impl_4449_, 4);
                    crate::leanh::lean_dec(v_unused_4524_);
                    v_unused_4525_ = crate::leanh::lean_ctor_get(v_impl_4449_, 3);
                    crate::leanh::lean_dec(v_unused_4525_);
                    v_unused_4526_ = crate::leanh::lean_ctor_get(v_impl_4449_, 2);
                    crate::leanh::lean_dec(v_unused_4526_);
                    v_unused_4527_ = crate::leanh::lean_ctor_get(v_impl_4449_, 1);
                    crate::leanh::lean_dec(v_unused_4527_);
                    v_unused_4528_ = crate::leanh::lean_ctor_get(v_impl_4449_, 0);
                    crate::leanh::lean_dec(v_unused_4528_);
                    v___x_4518_ = v_impl_4449_;
                    v_isShared_4519_ = v_isSharedCheck_4523_;
                    state = 83;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_impl_4449_);
                    v___x_4518_ = crate::leanh::lean_box(0);
                    v_isShared_4519_ = v_isSharedCheck_4523_;
                    state = 83;
                    continue;
                }
            }
            83 => {
                if v_isShared_4519_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4518_, 4, v___x_4516_);
                    crate::leanh::lean_ctor_set(v___x_4518_, 3, v_l_4455_);
                    crate::leanh::lean_ctor_set(v___x_4518_, 2, v_v_4454_);
                    crate::leanh::lean_ctor_set(v___x_4518_, 1, v_k_4453_);
                    crate::leanh::lean_ctor_set(v___x_4518_, 0, v___x_4512_);
                    v___x_4521_ = v___x_4518_;
                    state = 84;
                    continue;
                } else {
                    v_reuseFailAlloc_4522_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4522_, 0, v___x_4512_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4522_, 1, v_k_4453_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4522_, 2, v_v_4454_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4522_, 3, v_l_4455_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4522_, 4, v___x_4516_);
                    v___x_4521_ = v_reuseFailAlloc_4522_;
                    state = 84;
                    continue;
                }
            }
            84 => {
                return v___x_4521_;
            }
            85 => {
                return v___x_4539_;
            }
            86 => {
                v_size_4549_ = crate::leanh::lean_ctor_get(v_r_4542_, 0);
                v___x_4550_ = lean_nat_add(v___x_4450_, v_size_4543_);
                crate::leanh::lean_dec(v_size_4543_);
                v___x_4551_ = lean_nat_add(v___x_4450_, v_size_4549_);
                if v_isShared_4548_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4547_, 4, v_impl_4449_);
                    crate::leanh::lean_ctor_set(v___x_4547_, 3, v_r_4542_);
                    crate::leanh::lean_ctor_set(v___x_4547_, 2, v_v_3957_);
                    crate::leanh::lean_ctor_set(v___x_4547_, 1, v_k_3956_);
                    crate::leanh::lean_ctor_set(v___x_4547_, 0, v___x_4551_);
                    v___x_4553_ = v___x_4547_;
                    state = 87;
                    continue;
                } else {
                    v_reuseFailAlloc_4557_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4557_, 0, v___x_4551_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4557_, 1, v_k_3956_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4557_, 2, v_v_3957_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4557_, 3, v_r_4542_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4557_, 4, v_impl_4449_);
                    v___x_4553_ = v_reuseFailAlloc_4557_;
                    state = 87;
                    continue;
                }
            }
            87 => {
                if v_isShared_3962_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3961_, 4, v___x_4553_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 3, v_l_4541_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 2, v_v_4545_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 1, v_k_4544_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 0, v___x_4550_);
                    v___x_4555_ = v___x_3961_;
                    state = 88;
                    continue;
                } else {
                    v_reuseFailAlloc_4556_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4556_, 0, v___x_4550_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4556_, 1, v_k_4544_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4556_, 2, v_v_4545_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4556_, 3, v_l_4541_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4556_, 4, v___x_4553_);
                    v___x_4555_ = v_reuseFailAlloc_4556_;
                    state = 88;
                    continue;
                }
            }
            88 => {
                return v___x_4555_;
            }
            89 => {
                v___x_4566_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_4565_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4564_, 3, v_r_4542_);
                    crate::leanh::lean_ctor_set(v___x_4564_, 2, v_v_3957_);
                    crate::leanh::lean_ctor_set(v___x_4564_, 1, v_k_3956_);
                    crate::leanh::lean_ctor_set(v___x_4564_, 0, v___x_4450_);
                    v___x_4568_ = v___x_4564_;
                    state = 90;
                    continue;
                } else {
                    v_reuseFailAlloc_4572_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4572_, 0, v___x_4450_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4572_, 1, v_k_3956_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4572_, 2, v_v_3957_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4572_, 3, v_r_4542_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4572_, 4, v_r_4542_);
                    v___x_4568_ = v_reuseFailAlloc_4572_;
                    state = 90;
                    continue;
                }
            }
            90 => {
                if v_isShared_3962_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3961_, 4, v___x_4568_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 3, v_l_4541_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 2, v_v_4562_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 1, v_k_4561_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 0, v___x_4566_);
                    v___x_4570_ = v___x_3961_;
                    state = 91;
                    continue;
                } else {
                    v_reuseFailAlloc_4571_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4571_, 0, v___x_4566_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4571_, 1, v_k_4561_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4571_, 2, v_v_4562_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4571_, 3, v_l_4541_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4571_, 4, v___x_4568_);
                    v___x_4570_ = v_reuseFailAlloc_4571_;
                    state = 91;
                    continue;
                }
            }
            91 => {
                return v___x_4570_;
            }
            92 => {
                v_k_4583_ = crate::leanh::lean_ctor_get(v_r_4577_, 1);
                v_v_4584_ = crate::leanh::lean_ctor_get(v_r_4577_, 2);
                v_isSharedCheck_4598_ = (!crate::leanh::lean_is_exclusive(v_r_4577_)) as u8;
                if v_isSharedCheck_4598_ == 0 {
                    v_unused_4599_ = crate::leanh::lean_ctor_get(v_r_4577_, 4);
                    crate::leanh::lean_dec(v_unused_4599_);
                    v_unused_4600_ = crate::leanh::lean_ctor_get(v_r_4577_, 3);
                    crate::leanh::lean_dec(v_unused_4600_);
                    v_unused_4601_ = crate::leanh::lean_ctor_get(v_r_4577_, 0);
                    crate::leanh::lean_dec(v_unused_4601_);
                    v___x_4586_ = v_r_4577_;
                    v_isShared_4587_ = v_isSharedCheck_4598_;
                    state = 93;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_4584_);
                    crate::leanh::lean_inc(v_k_4583_);
                    crate::leanh::lean_dec(v_r_4577_);
                    v___x_4586_ = crate::leanh::lean_box(0);
                    v_isShared_4587_ = v_isSharedCheck_4598_;
                    state = 93;
                    continue;
                }
            }
            93 => {
                v___x_4588_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_4587_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4586_, 4, v_l_4541_);
                    crate::leanh::lean_ctor_set(v___x_4586_, 3, v_l_4541_);
                    crate::leanh::lean_ctor_set(v___x_4586_, 2, v_v_4579_);
                    crate::leanh::lean_ctor_set(v___x_4586_, 1, v_k_4578_);
                    crate::leanh::lean_ctor_set(v___x_4586_, 0, v___x_4450_);
                    v___x_4590_ = v___x_4586_;
                    state = 94;
                    continue;
                } else {
                    v_reuseFailAlloc_4597_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4597_, 0, v___x_4450_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4597_, 1, v_k_4578_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4597_, 2, v_v_4579_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4597_, 3, v_l_4541_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4597_, 4, v_l_4541_);
                    v___x_4590_ = v_reuseFailAlloc_4597_;
                    state = 94;
                    continue;
                }
            }
            94 => {
                if v_isShared_4582_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4581_, 4, v_l_4541_);
                    crate::leanh::lean_ctor_set(v___x_4581_, 2, v_v_3957_);
                    crate::leanh::lean_ctor_set(v___x_4581_, 1, v_k_3956_);
                    crate::leanh::lean_ctor_set(v___x_4581_, 0, v___x_4450_);
                    v___x_4592_ = v___x_4581_;
                    state = 95;
                    continue;
                } else {
                    v_reuseFailAlloc_4596_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4596_, 0, v___x_4450_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4596_, 1, v_k_3956_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4596_, 2, v_v_3957_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4596_, 3, v_l_4541_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4596_, 4, v_l_4541_);
                    v___x_4592_ = v_reuseFailAlloc_4596_;
                    state = 95;
                    continue;
                }
            }
            95 => {
                if v_isShared_3962_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3961_, 4, v___x_4592_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 3, v___x_4590_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 2, v_v_4584_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 1, v_k_4583_);
                    crate::leanh::lean_ctor_set(v___x_3961_, 0, v___x_4588_);
                    v___x_4594_ = v___x_3961_;
                    state = 96;
                    continue;
                } else {
                    v_reuseFailAlloc_4595_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4595_, 0, v___x_4588_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4595_, 1, v_k_4583_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4595_, 2, v_v_4584_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4595_, 3, v___x_4590_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4595_, 4, v___x_4592_);
                    v___x_4594_ = v_reuseFailAlloc_4595_;
                    state = 96;
                    continue;
                }
            }
            96 => {
                return v___x_4594_;
            }
            97 => {
                return v___x_4608_;
            }
            98 => {
                return v___x_4611_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg___boxed(
    mut v_k_4615_: *mut crate::leanh::LeanObject,
    mut v_t_4616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4617_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_4615_, v_t_4616_);
    crate::leanh::lean_dec_ref(v_k_4615_);
    return v_res_4617_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0(
    mut v_val_4618_: *mut crate::leanh::LeanObject,
    mut v_s_4619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toRing_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recheck_4634_: u8 = 0;
    let mut v_invSet_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_4638_: u8 = 0;
    let mut v___x_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4641_: u8 = 0;
    let mut v___x_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4646_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_4620_ = crate::leanh::lean_ctor_get(v_s_4619_, 0);
                v_invFn_x3f_4621_ = crate::leanh::lean_ctor_get(v_s_4619_, 1);
                v_semiringId_x3f_4622_ = crate::leanh::lean_ctor_get(v_s_4619_, 2);
                v_commSemiringInst_4623_ = crate::leanh::lean_ctor_get(v_s_4619_, 3);
                v_commRingInst_4624_ = crate::leanh::lean_ctor_get(v_s_4619_, 4);
                v_noZeroDivInst_x3f_4625_ = crate::leanh::lean_ctor_get(v_s_4619_, 5);
                v_fieldInst_x3f_4626_ = crate::leanh::lean_ctor_get(v_s_4619_, 6);
                v_powIdentityInst_x3f_4627_ = crate::leanh::lean_ctor_get(v_s_4619_, 7);
                v_denoteEntries_4628_ = crate::leanh::lean_ctor_get(v_s_4619_, 8);
                v_nextId_4629_ = crate::leanh::lean_ctor_get(v_s_4619_, 9);
                v_steps_4630_ = crate::leanh::lean_ctor_get(v_s_4619_, 10);
                v_queue_4631_ = crate::leanh::lean_ctor_get(v_s_4619_, 11);
                v_basis_4632_ = crate::leanh::lean_ctor_get(v_s_4619_, 12);
                v_diseqs_4633_ = crate::leanh::lean_ctor_get(v_s_4619_, 13);
                v_recheck_4634_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_4619_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                );
                v_invSet_4635_ = crate::leanh::lean_ctor_get(v_s_4619_, 14);
                v_powIdentityVarCount_4636_ = crate::leanh::lean_ctor_get(v_s_4619_, 15);
                v_numEq0_x3f_4637_ = crate::leanh::lean_ctor_get(v_s_4619_, 16);
                v_numEq0Updated_4638_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_4619_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_4646_ = (!crate::leanh::lean_is_exclusive(v_s_4619_)) as u8;
                if v_isSharedCheck_4646_ == 0 {
                    v___x_4640_ = v_s_4619_;
                    v_isShared_4641_ = v_isSharedCheck_4646_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_numEq0_x3f_4637_);
                    crate::leanh::lean_inc(v_powIdentityVarCount_4636_);
                    crate::leanh::lean_inc(v_invSet_4635_);
                    crate::leanh::lean_inc(v_diseqs_4633_);
                    crate::leanh::lean_inc(v_basis_4632_);
                    crate::leanh::lean_inc(v_queue_4631_);
                    crate::leanh::lean_inc(v_steps_4630_);
                    crate::leanh::lean_inc(v_nextId_4629_);
                    crate::leanh::lean_inc(v_denoteEntries_4628_);
                    crate::leanh::lean_inc(v_powIdentityInst_x3f_4627_);
                    crate::leanh::lean_inc(v_fieldInst_x3f_4626_);
                    crate::leanh::lean_inc(v_noZeroDivInst_x3f_4625_);
                    crate::leanh::lean_inc(v_commRingInst_4624_);
                    crate::leanh::lean_inc(v_commSemiringInst_4623_);
                    crate::leanh::lean_inc(v_semiringId_x3f_4622_);
                    crate::leanh::lean_inc(v_invFn_x3f_4621_);
                    crate::leanh::lean_inc(v_toRing_4620_);
                    crate::leanh::lean_dec(v_s_4619_);
                    v___x_4640_ = crate::leanh::lean_box(0);
                    v_isShared_4641_ = v_isSharedCheck_4646_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4642_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_val_4618_, v_queue_4631_);
                if v_isShared_4641_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4640_, 11, v___x_4642_);
                    v___x_4644_ = v___x_4640_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4645_ = crate::leanh::lean_alloc_ctor(0, 17, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 0, v_toRing_4620_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 1, v_invFn_x3f_4621_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 2, v_semiringId_x3f_4622_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4645_,
                        3,
                        v_commSemiringInst_4623_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 4, v_commRingInst_4624_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4645_,
                        5,
                        v_noZeroDivInst_x3f_4625_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 6, v_fieldInst_x3f_4626_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4645_,
                        7,
                        v_powIdentityInst_x3f_4627_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 8, v_denoteEntries_4628_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 9, v_nextId_4629_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 10, v_steps_4630_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 11, v___x_4642_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 12, v_basis_4632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 13, v_diseqs_4633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 14, v_invSet_4635_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4645_,
                        15,
                        v_powIdentityVarCount_4636_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 16, v_numEq0_x3f_4637_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4645_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                        v_recheck_4634_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4645_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                        v_numEq0Updated_4638_,
                    );
                    v___x_4644_ = v_reuseFailAlloc_4645_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4644_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0___boxed(
    mut v_val_4647_: *mut crate::leanh::LeanObject,
    mut v_s_4648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4649_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0(v_val_4647_, v_s_4648_);
    crate::leanh::lean_dec_ref(v_val_4647_);
    return v_res_4649_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(
    mut v_a_4650_: *mut crate::leanh::LeanObject,
    mut v_a_4651_: *mut crate::leanh::LeanObject,
    mut v_a_4652_: *mut crate::leanh::LeanObject,
    mut v_a_4653_: *mut crate::leanh::LeanObject,
    mut v_a_4654_: *mut crate::leanh::LeanObject,
    mut v_a_4655_: *mut crate::leanh::LeanObject,
    mut v_a_4656_: *mut crate::leanh::LeanObject,
    mut v_a_4657_: *mut crate::leanh::LeanObject,
    mut v_a_4658_: *mut crate::leanh::LeanObject,
    mut v_a_4659_: *mut crate::leanh::LeanObject,
    mut v_a_4660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4666_: u8 = 0;
    let mut v_queue_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4676_: u8 = 0;
    let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4680_: u8 = 0;
    let mut v_unused_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4685_: u8 = 0;
    let mut v___x_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4689_: u8 = 0;
    let mut v_a_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4693_: u8 = 0;
    let mut v___x_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4697_: u8 = 0;
    let mut v___x_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4702_: u8 = 0;
    let mut v_a_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4706_: u8 = 0;
    let mut v___x_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4710_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4662_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                    v_a_4650_, v_a_4651_, v_a_4652_, v_a_4653_, v_a_4654_, v_a_4655_, v_a_4656_,
                    v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_,
                );
                if crate::leanh::lean_obj_tag(v___x_4662_) == 0 {
                    v_a_4663_ = crate::leanh::lean_ctor_get(v___x_4662_, 0);
                    v_isSharedCheck_4702_ = (!crate::leanh::lean_is_exclusive(v___x_4662_)) as u8;
                    if v_isSharedCheck_4702_ == 0 {
                        v___x_4665_ = v___x_4662_;
                        v_isShared_4666_ = v_isSharedCheck_4702_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4663_);
                        crate::leanh::lean_dec(v___x_4662_);
                        v___x_4665_ = crate::leanh::lean_box(0);
                        v_isShared_4666_ = v_isSharedCheck_4702_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4703_ = crate::leanh::lean_ctor_get(v___x_4662_, 0);
                    v_isSharedCheck_4710_ = (!crate::leanh::lean_is_exclusive(v___x_4662_)) as u8;
                    if v_isSharedCheck_4710_ == 0 {
                        v___x_4705_ = v___x_4662_;
                        v_isShared_4706_ = v_isSharedCheck_4710_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4703_);
                        crate::leanh::lean_dec(v___x_4662_);
                        v___x_4705_ = crate::leanh::lean_box(0);
                        v_isShared_4706_ = v_isSharedCheck_4710_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_queue_4667_ = crate::leanh::lean_ctor_get(v_a_4663_, 11);
                crate::leanh::lean_inc(v_queue_4667_);
                crate::leanh::lean_dec(v_a_4663_);
                v___x_4668_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_queue_4667_);
                crate::leanh::lean_dec(v_queue_4667_);
                if crate::leanh::lean_obj_tag(v___x_4668_) == 1 {
                    crate::leanh::lean_del_object(v___x_4665_);
                    v_val_4669_ = crate::leanh::lean_ctor_get(v___x_4668_, 0);
                    crate::leanh::lean_inc(v_val_4669_);
                    v___f_4670_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0___boxed
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_4670_, 0, v_val_4669_);
                    v___x_4671_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(
                        v___f_4670_,
                        v_a_4650_,
                        v_a_4651_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4671_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4671_, 1);
                        v___x_4672_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4673_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(
                            v___x_4672_,
                            v_a_4651_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4673_) == 0 {
                            v_isSharedCheck_4680_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4673_)) as u8;
                            if v_isSharedCheck_4680_ == 0 {
                                v_unused_4681_ = crate::leanh::lean_ctor_get(v___x_4673_, 0);
                                crate::leanh::lean_dec(v_unused_4681_);
                                v___x_4675_ = v___x_4673_;
                                v_isShared_4676_ = v_isSharedCheck_4680_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_4673_);
                                v___x_4675_ = crate::leanh::lean_box(0);
                                v_isShared_4676_ = v_isSharedCheck_4680_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_4668_, 1);
                            v_a_4682_ = crate::leanh::lean_ctor_get(v___x_4673_, 0);
                            v_isSharedCheck_4689_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4673_)) as u8;
                            if v_isSharedCheck_4689_ == 0 {
                                v___x_4684_ = v___x_4673_;
                                v_isShared_4685_ = v_isSharedCheck_4689_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4682_);
                                crate::leanh::lean_dec(v___x_4673_);
                                v___x_4684_ = crate::leanh::lean_box(0);
                                v_isShared_4685_ = v_isSharedCheck_4689_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_4668_, 1);
                        v_a_4690_ = crate::leanh::lean_ctor_get(v___x_4671_, 0);
                        v_isSharedCheck_4697_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4671_)) as u8;
                        if v_isSharedCheck_4697_ == 0 {
                            v___x_4692_ = v___x_4671_;
                            v_isShared_4693_ = v_isSharedCheck_4697_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4690_);
                            crate::leanh::lean_dec(v___x_4671_);
                            v___x_4692_ = crate::leanh::lean_box(0);
                            v_isShared_4693_ = v_isSharedCheck_4697_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4668_);
                    v___x_4698_ = crate::leanh::lean_box(0);
                    if v_isShared_4666_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4665_, 0, v___x_4698_);
                        v___x_4700_ = v___x_4665_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4701_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4701_, 0, v___x_4698_);
                        v___x_4700_ = v_reuseFailAlloc_4701_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4676_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4675_, 0, v___x_4668_);
                    v___x_4678_ = v___x_4675_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4679_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4679_, 0, v___x_4668_);
                    v___x_4678_ = v_reuseFailAlloc_4679_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4678_;
            }
            4 => {
                if v_isShared_4685_ == 0 {
                    v___x_4687_ = v___x_4684_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4688_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4688_, 0, v_a_4682_);
                    v___x_4687_ = v_reuseFailAlloc_4688_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4687_;
            }
            6 => {
                if v_isShared_4693_ == 0 {
                    v___x_4695_ = v___x_4692_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4696_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4696_, 0, v_a_4690_);
                    v___x_4695_ = v_reuseFailAlloc_4696_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4695_;
            }
            8 => {
                return v___x_4700_;
            }
            9 => {
                if v_isShared_4706_ == 0 {
                    v___x_4708_ = v___x_4705_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4709_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4709_, 0, v_a_4703_);
                    v___x_4708_ = v_reuseFailAlloc_4709_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4708_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___boxed(
    mut v_a_4711_: *mut crate::leanh::LeanObject,
    mut v_a_4712_: *mut crate::leanh::LeanObject,
    mut v_a_4713_: *mut crate::leanh::LeanObject,
    mut v_a_4714_: *mut crate::leanh::LeanObject,
    mut v_a_4715_: *mut crate::leanh::LeanObject,
    mut v_a_4716_: *mut crate::leanh::LeanObject,
    mut v_a_4717_: *mut crate::leanh::LeanObject,
    mut v_a_4718_: *mut crate::leanh::LeanObject,
    mut v_a_4719_: *mut crate::leanh::LeanObject,
    mut v_a_4720_: *mut crate::leanh::LeanObject,
    mut v_a_4721_: *mut crate::leanh::LeanObject,
    mut v_a_4722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4723_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(
        v_a_4711_, v_a_4712_, v_a_4713_, v_a_4714_, v_a_4715_, v_a_4716_, v_a_4717_, v_a_4718_,
        v_a_4719_, v_a_4720_, v_a_4721_,
    );
    crate::leanh::lean_dec(v_a_4721_);
    crate::leanh::lean_dec_ref(v_a_4720_);
    crate::leanh::lean_dec(v_a_4719_);
    crate::leanh::lean_dec_ref(v_a_4718_);
    crate::leanh::lean_dec(v_a_4717_);
    crate::leanh::lean_dec_ref(v_a_4716_);
    crate::leanh::lean_dec(v_a_4715_);
    crate::leanh::lean_dec_ref(v_a_4714_);
    crate::leanh::lean_dec(v_a_4713_);
    crate::leanh::lean_dec(v_a_4712_);
    crate::leanh::lean_dec_ref(v_a_4711_);
    return v_res_4723_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(
    mut v_00_u03b2_4724_: *mut crate::leanh::LeanObject,
    mut v_k_4725_: *mut crate::leanh::LeanObject,
    mut v_t_4726_: *mut crate::leanh::LeanObject,
    mut v_h_4727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4728_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_4725_, v_t_4726_);
    return v___x_4728_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___boxed(
    mut v_00_u03b2_4729_: *mut crate::leanh::LeanObject,
    mut v_k_4730_: *mut crate::leanh::LeanObject,
    mut v_t_4731_: *mut crate::leanh::LeanObject,
    mut v_h_4732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4733_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(v_00_u03b2_4729_, v_k_4730_, v_t_4731_, v_h_4732_);
    crate::leanh::lean_dec_ref(v_k_4730_);
    return v_res_4733_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_x_4734_: *mut crate::leanh::LeanObject,
    mut v_x_4735_: *mut crate::leanh::LeanObject,
    mut v_x_4736_: *mut crate::leanh::LeanObject,
    mut v_x_4737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4742_: u8 = 0;
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: u8 = 0;
    let mut v___x_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: u8 = 0;
    let mut v___x_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4763_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4738_ = crate::leanh::lean_ctor_get(v_x_4734_, 0);
                v_vs_4739_ = crate::leanh::lean_ctor_get(v_x_4734_, 1);
                v_isSharedCheck_4763_ = (!crate::leanh::lean_is_exclusive(v_x_4734_)) as u8;
                if v_isSharedCheck_4763_ == 0 {
                    v___x_4741_ = v_x_4734_;
                    v_isShared_4742_ = v_isSharedCheck_4763_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_4739_);
                    crate::leanh::lean_inc(v_ks_4738_);
                    crate::leanh::lean_dec(v_x_4734_);
                    v___x_4741_ = crate::leanh::lean_box(0);
                    v_isShared_4742_ = v_isSharedCheck_4763_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4743_ = lean_array_get_size(v_ks_4738_);
                v___x_4744_ = lean_nat_dec_lt(v_x_4735_, v___x_4743_);
                if v___x_4744_ == 0 {
                    crate::leanh::lean_dec(v_x_4735_);
                    v___x_4745_ = lean_array_push(v_ks_4738_, v_x_4736_);
                    v___x_4746_ = lean_array_push(v_vs_4739_, v_x_4737_);
                    if v_isShared_4742_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4741_, 1, v___x_4746_);
                        crate::leanh::lean_ctor_set(v___x_4741_, 0, v___x_4745_);
                        v___x_4748_ = v___x_4741_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4749_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4749_, 0, v___x_4745_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4749_, 1, v___x_4746_);
                        v___x_4748_ = v_reuseFailAlloc_4749_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_4750_ = lean_array_fget_borrowed(v_ks_4738_, v_x_4735_);
                    v___x_4751_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_x_4736_,
                            v_k_x27_4750_,
                        );
                    if v___x_4751_ == 0 {
                        if v_isShared_4742_ == 0 {
                            v___x_4753_ = v___x_4741_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4757_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4757_, 0, v_ks_4738_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4757_, 1, v_vs_4739_);
                            v___x_4753_ = v_reuseFailAlloc_4757_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4758_ = lean_array_fset(v_ks_4738_, v_x_4735_, v_x_4736_);
                        v___x_4759_ = lean_array_fset(v_vs_4739_, v_x_4735_, v_x_4737_);
                        crate::leanh::lean_dec(v_x_4735_);
                        if v_isShared_4742_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4741_, 1, v___x_4759_);
                            crate::leanh::lean_ctor_set(v___x_4741_, 0, v___x_4758_);
                            v___x_4761_ = v___x_4741_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4762_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4762_, 0, v___x_4758_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4762_, 1, v___x_4759_);
                            v___x_4761_ = v_reuseFailAlloc_4762_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4748_;
            }
            3 => {
                v___x_4754_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4755_ = lean_nat_add(v_x_4735_, v___x_4754_);
                crate::leanh::lean_dec(v_x_4735_);
                v_x_4734_ = v___x_4753_;
                v_x_4735_ = v___x_4755_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_4761_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(
    mut v_n_4764_: *mut crate::leanh::LeanObject,
    mut v_k_4765_: *mut crate::leanh::LeanObject,
    mut v_v_4766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4767_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4768_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_4764_, v___x_4767_, v_k_4765_, v_v_4766_);
    return v___x_4768_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4769_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4769_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(
    mut v_x_4770_: *mut crate::leanh::LeanObject,
    mut v_x_4771_: usize,
    mut v_x_4772_: usize,
    mut v_x_4773_: *mut crate::leanh::LeanObject,
    mut v_x_4774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: usize = 0;
    let mut v___x_4777_: usize = 0;
    let mut v___x_4778_: usize = 0;
    let mut v___x_4779_: usize = 0;
    let mut v_j_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: u8 = 0;
    let mut v___x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4785_: u8 = 0;
    let mut v_v_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4799_: u8 = 0;
    let mut v___x_4800_: u8 = 0;
    let mut v___x_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4806_: u8 = 0;
    let mut v_node_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4810_: u8 = 0;
    let mut v___x_4811_: usize = 0;
    let mut v___x_4812_: usize = 0;
    let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4817_: u8 = 0;
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4819_: u8 = 0;
    let mut v_unused_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4825_: u8 = 0;
    let mut v___x_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4830_: u8 = 0;
    let mut v_ks_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: usize = 0;
    let mut v___x_4837_: u8 = 0;
    let mut v___x_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: u8 = 0;
    let mut v_reuseFailAlloc_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4842_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4770_) == 0 {
                    v_es_4775_ = crate::leanh::lean_ctor_get(v_x_4770_, 0);
                    v___x_4776_ = 5usize;
                    v___x_4777_ = 1usize;
                    v___x_4778_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_4779_ = lean_usize_land(v_x_4771_, v___x_4778_);
                    v_j_4780_ = lean_usize_to_nat(v___x_4779_);
                    v___x_4781_ = lean_array_get_size(v_es_4775_);
                    v___x_4782_ = lean_nat_dec_lt(v_j_4780_, v___x_4781_);
                    if v___x_4782_ == 0 {
                        crate::leanh::lean_dec(v_j_4780_);
                        crate::leanh::lean_dec(v_x_4774_);
                        crate::leanh::lean_dec_ref(v_x_4773_);
                        return v_x_4770_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_4775_);
                        v_isSharedCheck_4819_ = (!crate::leanh::lean_is_exclusive(v_x_4770_)) as u8;
                        if v_isSharedCheck_4819_ == 0 {
                            v_unused_4820_ = crate::leanh::lean_ctor_get(v_x_4770_, 0);
                            crate::leanh::lean_dec(v_unused_4820_);
                            v___x_4784_ = v_x_4770_;
                            v_isShared_4785_ = v_isSharedCheck_4819_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_4770_);
                            v___x_4784_ = crate::leanh::lean_box(0);
                            v_isShared_4785_ = v_isSharedCheck_4819_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4821_ = crate::leanh::lean_ctor_get(v_x_4770_, 0);
                    v_vs_4822_ = crate::leanh::lean_ctor_get(v_x_4770_, 1);
                    v_isSharedCheck_4842_ = (!crate::leanh::lean_is_exclusive(v_x_4770_)) as u8;
                    if v_isSharedCheck_4842_ == 0 {
                        v___x_4824_ = v_x_4770_;
                        v_isShared_4825_ = v_isSharedCheck_4842_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_4822_);
                        crate::leanh::lean_inc(v_ks_4821_);
                        crate::leanh::lean_dec(v_x_4770_);
                        v___x_4824_ = crate::leanh::lean_box(0);
                        v_isShared_4825_ = v_isSharedCheck_4842_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4786_ = lean_array_fget(v_es_4775_, v_j_4780_);
                v___x_4787_ = crate::leanh::lean_box(0);
                v_xs_x27_4788_ = lean_array_fset(v_es_4775_, v_j_4780_, v___x_4787_);
                match crate::leanh::lean_obj_tag(v_v_4786_) {
                    0 => {
                        v_key_4795_ = crate::leanh::lean_ctor_get(v_v_4786_, 0);
                        v_val_4796_ = crate::leanh::lean_ctor_get(v_v_4786_, 1);
                        v_isSharedCheck_4806_ = (!crate::leanh::lean_is_exclusive(v_v_4786_)) as u8;
                        if v_isSharedCheck_4806_ == 0 {
                            v___x_4798_ = v_v_4786_;
                            v_isShared_4799_ = v_isSharedCheck_4806_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4796_);
                            crate::leanh::lean_inc(v_key_4795_);
                            crate::leanh::lean_dec(v_v_4786_);
                            v___x_4798_ = crate::leanh::lean_box(0);
                            v_isShared_4799_ = v_isSharedCheck_4806_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4807_ = crate::leanh::lean_ctor_get(v_v_4786_, 0);
                        v_isSharedCheck_4817_ = (!crate::leanh::lean_is_exclusive(v_v_4786_)) as u8;
                        if v_isSharedCheck_4817_ == 0 {
                            v___x_4809_ = v_v_4786_;
                            v_isShared_4810_ = v_isSharedCheck_4817_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_4807_);
                            crate::leanh::lean_dec(v_v_4786_);
                            v___x_4809_ = crate::leanh::lean_box(0);
                            v_isShared_4810_ = v_isSharedCheck_4817_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4818_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4818_, 0, v_x_4773_);
                        crate::leanh::lean_ctor_set(v___x_4818_, 1, v_x_4774_);
                        v___y_4790_ = v___x_4818_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4791_ = lean_array_fset(v_xs_x27_4788_, v_j_4780_, v___y_4790_);
                crate::leanh::lean_dec(v_j_4780_);
                if v_isShared_4785_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4784_, 0, v___x_4791_);
                    v___x_4793_ = v___x_4784_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4794_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4794_, 0, v___x_4791_);
                    v___x_4793_ = v_reuseFailAlloc_4794_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4793_;
            }
            4 => {
                v___x_4800_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_x_4773_,
                        v_key_4795_,
                    );
                if v___x_4800_ == 0 {
                    crate::leanh::lean_del_object(v___x_4798_);
                    v___x_4801_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4795_,
                        v_val_4796_,
                        v_x_4773_,
                        v_x_4774_,
                    );
                    v___x_4802_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4802_, 0, v___x_4801_);
                    v___y_4790_ = v___x_4802_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_4796_);
                    crate::leanh::lean_dec(v_key_4795_);
                    if v_isShared_4799_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4798_, 1, v_x_4774_);
                        crate::leanh::lean_ctor_set(v___x_4798_, 0, v_x_4773_);
                        v___x_4804_ = v___x_4798_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4805_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4805_, 0, v_x_4773_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4805_, 1, v_x_4774_);
                        v___x_4804_ = v_reuseFailAlloc_4805_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_4790_ = v___x_4804_;
                state = 2;
                continue;
            }
            6 => {
                v___x_4811_ = lean_usize_shift_right(v_x_4771_, v___x_4776_);
                v___x_4812_ = lean_usize_add(v_x_4772_, v___x_4777_);
                v___x_4813_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_node_4807_, v___x_4811_, v___x_4812_, v_x_4773_, v_x_4774_);
                if v_isShared_4810_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4809_, 0, v___x_4813_);
                    v___x_4815_ = v___x_4809_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4816_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4816_, 0, v___x_4813_);
                    v___x_4815_ = v_reuseFailAlloc_4816_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_4790_ = v___x_4815_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_4825_ == 0 {
                    v___x_4827_ = v___x_4824_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4841_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4841_, 0, v_ks_4821_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4841_, 1, v_vs_4822_);
                    v___x_4827_ = v_reuseFailAlloc_4841_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_4828_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v___x_4827_, v_x_4773_, v_x_4774_);
                v___x_4836_ = 7usize;
                v___x_4837_ = lean_usize_dec_le(v___x_4836_, v_x_4772_);
                if v___x_4837_ == 0 {
                    v___x_4838_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4828_);
                    v___x_4839_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_4840_ = lean_nat_dec_lt(v___x_4838_, v___x_4839_);
                    crate::leanh::lean_dec(v___x_4838_);
                    v___y_4830_ = v___x_4840_;
                    state = 10;
                    continue;
                } else {
                    v___y_4830_ = v___x_4837_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_4830_ == 0 {
                    v_ks_4831_ = crate::leanh::lean_ctor_get(v_newNode_4828_, 0);
                    crate::leanh::lean_inc_ref(v_ks_4831_);
                    v_vs_4832_ = crate::leanh::lean_ctor_get(v_newNode_4828_, 1);
                    crate::leanh::lean_inc_ref(v_vs_4832_);
                    crate::leanh::lean_dec_ref(v_newNode_4828_);
                    v___x_4833_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4834_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0);
                    v___x_4835_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_x_4772_, v_ks_4831_, v_vs_4832_, v___x_4833_, v___x_4834_);
                    crate::leanh::lean_dec_ref(v_vs_4832_);
                    crate::leanh::lean_dec_ref(v_ks_4831_);
                    return v___x_4835_;
                } else {
                    return v_newNode_4828_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(
    mut v_depth_4843_: usize,
    mut v_keys_4844_: *mut crate::leanh::LeanObject,
    mut v_vals_4845_: *mut crate::leanh::LeanObject,
    mut v_i_4846_: *mut crate::leanh::LeanObject,
    mut v_entries_4847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: u8 = 0;
    let mut v_k_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: u64 = 0;
    let mut v_h_4853_: usize = 0;
    let mut v___x_4854_: usize = 0;
    let mut v___x_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: usize = 0;
    let mut v___x_4857_: usize = 0;
    let mut v___x_4858_: usize = 0;
    let mut v_h_4859_: usize = 0;
    let mut v___x_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4848_ = lean_array_get_size(v_keys_4844_);
                v___x_4849_ = lean_nat_dec_lt(v_i_4846_, v___x_4848_);
                if v___x_4849_ == 0 {
                    crate::leanh::lean_dec(v_i_4846_);
                    return v_entries_4847_;
                } else {
                    v_k_4850_ = lean_array_fget_borrowed(v_keys_4844_, v_i_4846_);
                    v_v_4851_ = lean_array_fget_borrowed(v_vals_4845_, v_i_4846_);
                    v___x_4852_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_4850_);
                    v_h_4853_ = lean_uint64_to_usize(v___x_4852_);
                    v___x_4854_ = 5usize;
                    v___x_4855_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4856_ = 1usize;
                    v___x_4857_ = lean_usize_sub(v_depth_4843_, v___x_4856_);
                    v___x_4858_ = lean_usize_mul(v___x_4854_, v___x_4857_);
                    v_h_4859_ = lean_usize_shift_right(v_h_4853_, v___x_4858_);
                    v___x_4860_ = lean_nat_add(v_i_4846_, v___x_4855_);
                    crate::leanh::lean_dec(v_i_4846_);
                    crate::leanh::lean_inc(v_v_4851_);
                    crate::leanh::lean_inc(v_k_4850_);
                    v___x_4861_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_entries_4847_, v_h_4859_, v_depth_4843_, v_k_4850_, v_v_4851_);
                    v_i_4846_ = v___x_4860_;
                    v_entries_4847_ = v___x_4861_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_depth_4863_: *mut crate::leanh::LeanObject,
    mut v_keys_4864_: *mut crate::leanh::LeanObject,
    mut v_vals_4865_: *mut crate::leanh::LeanObject,
    mut v_i_4866_: *mut crate::leanh::LeanObject,
    mut v_entries_4867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_4868_: usize = 0;
    let mut v_res_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4868_ = crate::leanh::lean_unbox_usize(v_depth_4863_);
    crate::leanh::lean_dec(v_depth_4863_);
    v_res_4869_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_4868_, v_keys_4864_, v_vals_4865_, v_i_4866_, v_entries_4867_);
    crate::leanh::lean_dec_ref(v_vals_4865_);
    crate::leanh::lean_dec_ref(v_keys_4864_);
    return v_res_4869_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___boxed(
    mut v_x_4870_: *mut crate::leanh::LeanObject,
    mut v_x_4871_: *mut crate::leanh::LeanObject,
    mut v_x_4872_: *mut crate::leanh::LeanObject,
    mut v_x_4873_: *mut crate::leanh::LeanObject,
    mut v_x_4874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_7240__boxed_4875_: usize = 0;
    let mut v_x_7241__boxed_4876_: usize = 0;
    let mut v_res_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_7240__boxed_4875_ = crate::leanh::lean_unbox_usize(v_x_4871_);
    crate::leanh::lean_dec(v_x_4871_);
    v_x_7241__boxed_4876_ = crate::leanh::lean_unbox_usize(v_x_4872_);
    crate::leanh::lean_dec(v_x_4872_);
    v_res_4877_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_4870_, v_x_7240__boxed_4875_, v_x_7241__boxed_4876_, v_x_4873_, v_x_4874_);
    return v_res_4877_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(
    mut v_x_4878_: *mut crate::leanh::LeanObject,
    mut v_x_4879_: *mut crate::leanh::LeanObject,
    mut v_x_4880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4881_: u64 = 0;
    let mut v___x_4882_: usize = 0;
    let mut v___x_4883_: usize = 0;
    let mut v___x_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4881_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_4879_);
    v___x_4882_ = lean_uint64_to_usize(v___x_4881_);
    v___x_4883_ = 1usize;
    v___x_4884_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_4878_, v___x_4882_, v___x_4883_, v_x_4879_, v_x_4880_);
    return v___x_4884_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___lam__0(
    mut v_e_4885_: *mut crate::leanh::LeanObject,
    mut v_ringId_4886_: *mut crate::leanh::LeanObject,
    mut v_s_4887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_rings_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_4901_: u8 = 0;
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4904_: u8 = 0;
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4909_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_4888_ = crate::leanh::lean_ctor_get(v_s_4887_, 0);
                v_typeIdOf_4889_ = crate::leanh::lean_ctor_get(v_s_4887_, 1);
                v_exprToRingId_4890_ = crate::leanh::lean_ctor_get(v_s_4887_, 2);
                v_semirings_4891_ = crate::leanh::lean_ctor_get(v_s_4887_, 3);
                v_stypeIdOf_4892_ = crate::leanh::lean_ctor_get(v_s_4887_, 4);
                v_exprToSemiringId_4893_ = crate::leanh::lean_ctor_get(v_s_4887_, 5);
                v_ncRings_4894_ = crate::leanh::lean_ctor_get(v_s_4887_, 6);
                v_exprToNCRingId_4895_ = crate::leanh::lean_ctor_get(v_s_4887_, 7);
                v_nctypeIdOf_4896_ = crate::leanh::lean_ctor_get(v_s_4887_, 8);
                v_ncSemirings_4897_ = crate::leanh::lean_ctor_get(v_s_4887_, 9);
                v_exprToNCSemiringId_4898_ = crate::leanh::lean_ctor_get(v_s_4887_, 10);
                v_ncstypeIdOf_4899_ = crate::leanh::lean_ctor_get(v_s_4887_, 11);
                v_steps_4900_ = crate::leanh::lean_ctor_get(v_s_4887_, 12);
                v_reportedMaxDegreeIssue_4901_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_4887_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                v_isSharedCheck_4909_ = (!crate::leanh::lean_is_exclusive(v_s_4887_)) as u8;
                if v_isSharedCheck_4909_ == 0 {
                    v___x_4903_ = v_s_4887_;
                    v_isShared_4904_ = v_isSharedCheck_4909_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_steps_4900_);
                    crate::leanh::lean_inc(v_ncstypeIdOf_4899_);
                    crate::leanh::lean_inc(v_exprToNCSemiringId_4898_);
                    crate::leanh::lean_inc(v_ncSemirings_4897_);
                    crate::leanh::lean_inc(v_nctypeIdOf_4896_);
                    crate::leanh::lean_inc(v_exprToNCRingId_4895_);
                    crate::leanh::lean_inc(v_ncRings_4894_);
                    crate::leanh::lean_inc(v_exprToSemiringId_4893_);
                    crate::leanh::lean_inc(v_stypeIdOf_4892_);
                    crate::leanh::lean_inc(v_semirings_4891_);
                    crate::leanh::lean_inc(v_exprToRingId_4890_);
                    crate::leanh::lean_inc(v_typeIdOf_4889_);
                    crate::leanh::lean_inc(v_rings_4888_);
                    crate::leanh::lean_dec(v_s_4887_);
                    v___x_4903_ = crate::leanh::lean_box(0);
                    v_isShared_4904_ = v_isSharedCheck_4909_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4905_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_exprToRingId_4890_, v_e_4885_, v_ringId_4886_);
                if v_isShared_4904_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4903_, 2, v___x_4905_);
                    v___x_4907_ = v___x_4903_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4908_ = crate::leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 0, v_rings_4888_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 1, v_typeIdOf_4889_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 2, v___x_4905_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 3, v_semirings_4891_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 4, v_stypeIdOf_4892_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4908_,
                        5,
                        v_exprToSemiringId_4893_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 6, v_ncRings_4894_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 7, v_exprToNCRingId_4895_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 8, v_nctypeIdOf_4896_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 9, v_ncSemirings_4897_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4908_,
                        10,
                        v_exprToNCSemiringId_4898_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 11, v_ncstypeIdOf_4899_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 12, v_steps_4900_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4908_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                        v_reportedMaxDegreeIssue_4901_,
                    );
                    v___x_4907_ = v_reuseFailAlloc_4908_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4907_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4911_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__0;
    v___x_4912_ = l_Lean_stringToMessageData(v___x_4911_);
    return v___x_4912_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(
    mut v_e_4913_: *mut crate::leanh::LeanObject,
    mut v_a_4914_: *mut crate::leanh::LeanObject,
    mut v_a_4915_: *mut crate::leanh::LeanObject,
    mut v_a_4916_: *mut crate::leanh::LeanObject,
    mut v_a_4917_: *mut crate::leanh::LeanObject,
    mut v_a_4918_: *mut crate::leanh::LeanObject,
    mut v_a_4919_: *mut crate::leanh::LeanObject,
    mut v_a_4920_: *mut crate::leanh::LeanObject,
    mut v_a_4921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringId_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: u8 = 0;
    let mut v___x_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: u8 = 0;
    let mut v___x_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4941_: u8 = 0;
    let mut v___x_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4945_: u8 = 0;
    let mut v_ringId_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4953_: u8 = 0;
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4957_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4926_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(
                    v_e_4913_, v_a_4915_, v_a_4920_,
                );
                if crate::leanh::lean_obj_tag(v___x_4926_) == 0 {
                    v_a_4927_ = crate::leanh::lean_ctor_get(v___x_4926_, 0);
                    crate::leanh::lean_inc(v_a_4927_);
                    crate::leanh::lean_dec_ref_known(v___x_4926_, 1);
                    if crate::leanh::lean_obj_tag(v_a_4927_) == 1 {
                        v_ringId_4928_ = crate::leanh::lean_ctor_get(v_a_4914_, 0);
                        v_val_4929_ = crate::leanh::lean_ctor_get(v_a_4927_, 0);
                        crate::leanh::lean_inc(v_val_4929_);
                        crate::leanh::lean_dec_ref_known(v_a_4927_, 1);
                        v___x_4930_ = lean_nat_dec_eq(v_val_4929_, v_ringId_4928_);
                        crate::leanh::lean_dec(v_val_4929_);
                        if v___x_4930_ == 0 {
                            v___x_4931_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_4916_);
                            if crate::leanh::lean_obj_tag(v___x_4931_) == 0 {
                                v_a_4932_ = crate::leanh::lean_ctor_get(v___x_4931_, 0);
                                crate::leanh::lean_inc(v_a_4932_);
                                crate::leanh::lean_dec_ref_known(v___x_4931_, 1);
                                v___x_4933_ = (crate::leanh::lean_unbox(v_a_4932_) as u8);
                                crate::leanh::lean_dec(v_a_4932_);
                                if v___x_4933_ == 0 {
                                    crate::leanh::lean_dec_ref(v_e_4913_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_4934_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1_once), _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1);
                                    v___x_4935_ = l_Lean_indentExpr(v_e_4913_);
                                    v___x_4936_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4936_, 0, v___x_4934_);
                                    crate::leanh::lean_ctor_set(v___x_4936_, 1, v___x_4935_);
                                    v___x_4937_ = l_Lean_Meta_Sym_reportIssue(
                                        v___x_4936_,
                                        v_a_4916_,
                                        v_a_4917_,
                                        v_a_4918_,
                                        v_a_4919_,
                                        v_a_4920_,
                                        v_a_4921_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_4937_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_4937_, 1);
                                        state = 1;
                                        continue;
                                    } else {
                                        return v___x_4937_;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_e_4913_);
                                v_a_4938_ = crate::leanh::lean_ctor_get(v___x_4931_, 0);
                                v_isSharedCheck_4945_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4931_)) as u8;
                                if v_isSharedCheck_4945_ == 0 {
                                    v___x_4940_ = v___x_4931_;
                                    v_isShared_4941_ = v_isSharedCheck_4945_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4938_);
                                    crate::leanh::lean_dec(v___x_4931_);
                                    v___x_4940_ = crate::leanh::lean_box(0);
                                    v_isShared_4941_ = v_isSharedCheck_4945_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_e_4913_);
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4927_);
                        v_ringId_4946_ = crate::leanh::lean_ctor_get(v_a_4914_, 0);
                        crate::leanh::lean_inc(v_ringId_4946_);
                        v___f_4947_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___lam__0
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___f_4947_, 0, v_e_4913_);
                        crate::leanh::lean_closure_set(v___f_4947_, 1, v_ringId_4946_);
                        v___x_4948_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                        v___x_4949_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4948_, v___f_4947_, v_a_4915_);
                        return v___x_4949_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_4913_);
                    v_a_4950_ = crate::leanh::lean_ctor_get(v___x_4926_, 0);
                    v_isSharedCheck_4957_ = (!crate::leanh::lean_is_exclusive(v___x_4926_)) as u8;
                    if v_isSharedCheck_4957_ == 0 {
                        v___x_4952_ = v___x_4926_;
                        v_isShared_4953_ = v_isSharedCheck_4957_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4950_);
                        crate::leanh::lean_dec(v___x_4926_);
                        v___x_4952_ = crate::leanh::lean_box(0);
                        v_isShared_4953_ = v_isSharedCheck_4957_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4924_ = crate::leanh::lean_box(0);
                v___x_4925_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4925_, 0, v___x_4924_);
                return v___x_4925_;
            }
            2 => {
                if v_isShared_4941_ == 0 {
                    v___x_4943_ = v___x_4940_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4944_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4944_, 0, v_a_4938_);
                    v___x_4943_ = v_reuseFailAlloc_4944_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4943_;
            }
            4 => {
                if v_isShared_4953_ == 0 {
                    v___x_4955_ = v___x_4952_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4956_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4956_, 0, v_a_4950_);
                    v___x_4955_ = v_reuseFailAlloc_4956_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4955_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___boxed(
    mut v_e_4958_: *mut crate::leanh::LeanObject,
    mut v_a_4959_: *mut crate::leanh::LeanObject,
    mut v_a_4960_: *mut crate::leanh::LeanObject,
    mut v_a_4961_: *mut crate::leanh::LeanObject,
    mut v_a_4962_: *mut crate::leanh::LeanObject,
    mut v_a_4963_: *mut crate::leanh::LeanObject,
    mut v_a_4964_: *mut crate::leanh::LeanObject,
    mut v_a_4965_: *mut crate::leanh::LeanObject,
    mut v_a_4966_: *mut crate::leanh::LeanObject,
    mut v_a_4967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4968_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(
        v_e_4958_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_,
        v_a_4966_,
    );
    crate::leanh::lean_dec(v_a_4966_);
    crate::leanh::lean_dec_ref(v_a_4965_);
    crate::leanh::lean_dec(v_a_4964_);
    crate::leanh::lean_dec_ref(v_a_4963_);
    crate::leanh::lean_dec(v_a_4962_);
    crate::leanh::lean_dec_ref(v_a_4961_);
    crate::leanh::lean_dec(v_a_4960_);
    crate::leanh::lean_dec_ref(v_a_4959_);
    return v_res_4968_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(
    mut v_e_4969_: *mut crate::leanh::LeanObject,
    mut v_a_4970_: *mut crate::leanh::LeanObject,
    mut v_a_4971_: *mut crate::leanh::LeanObject,
    mut v_a_4972_: *mut crate::leanh::LeanObject,
    mut v_a_4973_: *mut crate::leanh::LeanObject,
    mut v_a_4974_: *mut crate::leanh::LeanObject,
    mut v_a_4975_: *mut crate::leanh::LeanObject,
    mut v_a_4976_: *mut crate::leanh::LeanObject,
    mut v_a_4977_: *mut crate::leanh::LeanObject,
    mut v_a_4978_: *mut crate::leanh::LeanObject,
    mut v_a_4979_: *mut crate::leanh::LeanObject,
    mut v_a_4980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4982_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(
        v_e_4969_, v_a_4970_, v_a_4971_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_,
        v_a_4980_,
    );
    return v___x_4982_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___boxed(
    mut v_e_4983_: *mut crate::leanh::LeanObject,
    mut v_a_4984_: *mut crate::leanh::LeanObject,
    mut v_a_4985_: *mut crate::leanh::LeanObject,
    mut v_a_4986_: *mut crate::leanh::LeanObject,
    mut v_a_4987_: *mut crate::leanh::LeanObject,
    mut v_a_4988_: *mut crate::leanh::LeanObject,
    mut v_a_4989_: *mut crate::leanh::LeanObject,
    mut v_a_4990_: *mut crate::leanh::LeanObject,
    mut v_a_4991_: *mut crate::leanh::LeanObject,
    mut v_a_4992_: *mut crate::leanh::LeanObject,
    mut v_a_4993_: *mut crate::leanh::LeanObject,
    mut v_a_4994_: *mut crate::leanh::LeanObject,
    mut v_a_4995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4996_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(
        v_e_4983_, v_a_4984_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_,
        v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_,
    );
    crate::leanh::lean_dec(v_a_4994_);
    crate::leanh::lean_dec_ref(v_a_4993_);
    crate::leanh::lean_dec(v_a_4992_);
    crate::leanh::lean_dec_ref(v_a_4991_);
    crate::leanh::lean_dec(v_a_4990_);
    crate::leanh::lean_dec_ref(v_a_4989_);
    crate::leanh::lean_dec(v_a_4988_);
    crate::leanh::lean_dec_ref(v_a_4987_);
    crate::leanh::lean_dec(v_a_4986_);
    crate::leanh::lean_dec(v_a_4985_);
    crate::leanh::lean_dec_ref(v_a_4984_);
    return v_res_4996_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0(
    mut v_00_u03b2_4997_: *mut crate::leanh::LeanObject,
    mut v_x_4998_: *mut crate::leanh::LeanObject,
    mut v_x_4999_: *mut crate::leanh::LeanObject,
    mut v_x_5000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5001_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_x_4998_, v_x_4999_, v_x_5000_);
    return v___x_5001_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(
    mut v_00_u03b2_5002_: *mut crate::leanh::LeanObject,
    mut v_x_5003_: *mut crate::leanh::LeanObject,
    mut v_x_5004_: usize,
    mut v_x_5005_: usize,
    mut v_x_5006_: *mut crate::leanh::LeanObject,
    mut v_x_5007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5008_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_5003_, v_x_5004_, v_x_5005_, v_x_5006_, v_x_5007_);
    return v___x_5008_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___boxed(
    mut v_00_u03b2_5009_: *mut crate::leanh::LeanObject,
    mut v_x_5010_: *mut crate::leanh::LeanObject,
    mut v_x_5011_: *mut crate::leanh::LeanObject,
    mut v_x_5012_: *mut crate::leanh::LeanObject,
    mut v_x_5013_: *mut crate::leanh::LeanObject,
    mut v_x_5014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_7519__boxed_5015_: usize = 0;
    let mut v_x_7520__boxed_5016_: usize = 0;
    let mut v_res_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_7519__boxed_5015_ = crate::leanh::lean_unbox_usize(v_x_5011_);
    crate::leanh::lean_dec(v_x_5011_);
    v_x_7520__boxed_5016_ = crate::leanh::lean_unbox_usize(v_x_5012_);
    crate::leanh::lean_dec(v_x_5012_);
    v_res_5017_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(v_00_u03b2_5009_, v_x_5010_, v_x_7519__boxed_5015_, v_x_7520__boxed_5016_, v_x_5013_, v_x_5014_);
    return v_res_5017_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1(
    mut v_00_u03b2_5018_: *mut crate::leanh::LeanObject,
    mut v_n_5019_: *mut crate::leanh::LeanObject,
    mut v_k_5020_: *mut crate::leanh::LeanObject,
    mut v_v_5021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5022_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v_n_5019_, v_k_5020_, v_v_5021_);
    return v___x_5022_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(
    mut v_00_u03b2_5023_: *mut crate::leanh::LeanObject,
    mut v_depth_5024_: usize,
    mut v_keys_5025_: *mut crate::leanh::LeanObject,
    mut v_vals_5026_: *mut crate::leanh::LeanObject,
    mut v_heq_5027_: *mut crate::leanh::LeanObject,
    mut v_i_5028_: *mut crate::leanh::LeanObject,
    mut v_entries_5029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5030_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_5024_, v_keys_5025_, v_vals_5026_, v_i_5028_, v_entries_5029_);
    return v___x_5030_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_5031_: *mut crate::leanh::LeanObject,
    mut v_depth_5032_: *mut crate::leanh::LeanObject,
    mut v_keys_5033_: *mut crate::leanh::LeanObject,
    mut v_vals_5034_: *mut crate::leanh::LeanObject,
    mut v_heq_5035_: *mut crate::leanh::LeanObject,
    mut v_i_5036_: *mut crate::leanh::LeanObject,
    mut v_entries_5037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_5038_: usize = 0;
    let mut v_res_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5038_ = crate::leanh::lean_unbox_usize(v_depth_5032_);
    crate::leanh::lean_dec(v_depth_5032_);
    v_res_5039_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(v_00_u03b2_5031_, v_depth_boxed_5038_, v_keys_5033_, v_vals_5034_, v_heq_5035_, v_i_5036_, v_entries_5037_);
    crate::leanh::lean_dec_ref(v_vals_5034_);
    crate::leanh::lean_dec_ref(v_keys_5033_);
    return v_res_5039_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_5040_: *mut crate::leanh::LeanObject,
    mut v_x_5041_: *mut crate::leanh::LeanObject,
    mut v_x_5042_: *mut crate::leanh::LeanObject,
    mut v_x_5043_: *mut crate::leanh::LeanObject,
    mut v_x_5044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5045_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_5041_, v_x_5042_, v_x_5043_, v_x_5044_);
    return v___x_5045_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0(
    mut v_e_5046_: *mut crate::leanh::LeanObject,
    mut v___f_5047_: *mut crate::leanh::LeanObject,
    mut v___f_5048_: *mut crate::leanh::LeanObject,
    mut v_size_5049_: *mut crate::leanh::LeanObject,
    mut v_s_5050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5070_: u8 = 0;
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5076_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_5051_ = crate::leanh::lean_ctor_get(v_s_5050_, 0);
                v_type_5052_ = crate::leanh::lean_ctor_get(v_s_5050_, 1);
                v_u_5053_ = crate::leanh::lean_ctor_get(v_s_5050_, 2);
                v_ringInst_5054_ = crate::leanh::lean_ctor_get(v_s_5050_, 3);
                v_semiringInst_5055_ = crate::leanh::lean_ctor_get(v_s_5050_, 4);
                v_charInst_x3f_5056_ = crate::leanh::lean_ctor_get(v_s_5050_, 5);
                v_addFn_x3f_5057_ = crate::leanh::lean_ctor_get(v_s_5050_, 6);
                v_mulFn_x3f_5058_ = crate::leanh::lean_ctor_get(v_s_5050_, 7);
                v_subFn_x3f_5059_ = crate::leanh::lean_ctor_get(v_s_5050_, 8);
                v_negFn_x3f_5060_ = crate::leanh::lean_ctor_get(v_s_5050_, 9);
                v_powFn_x3f_5061_ = crate::leanh::lean_ctor_get(v_s_5050_, 10);
                v_intCastFn_x3f_5062_ = crate::leanh::lean_ctor_get(v_s_5050_, 11);
                v_natCastFn_x3f_5063_ = crate::leanh::lean_ctor_get(v_s_5050_, 12);
                v_one_x3f_5064_ = crate::leanh::lean_ctor_get(v_s_5050_, 13);
                v_vars_5065_ = crate::leanh::lean_ctor_get(v_s_5050_, 14);
                v_varMap_5066_ = crate::leanh::lean_ctor_get(v_s_5050_, 15);
                v_denote_5067_ = crate::leanh::lean_ctor_get(v_s_5050_, 16);
                v_isSharedCheck_5076_ = (!crate::leanh::lean_is_exclusive(v_s_5050_)) as u8;
                if v_isSharedCheck_5076_ == 0 {
                    v___x_5069_ = v_s_5050_;
                    v_isShared_5070_ = v_isSharedCheck_5076_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_denote_5067_);
                    crate::leanh::lean_inc(v_varMap_5066_);
                    crate::leanh::lean_inc(v_vars_5065_);
                    crate::leanh::lean_inc(v_one_x3f_5064_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_5063_);
                    crate::leanh::lean_inc(v_intCastFn_x3f_5062_);
                    crate::leanh::lean_inc(v_powFn_x3f_5061_);
                    crate::leanh::lean_inc(v_negFn_x3f_5060_);
                    crate::leanh::lean_inc(v_subFn_x3f_5059_);
                    crate::leanh::lean_inc(v_mulFn_x3f_5058_);
                    crate::leanh::lean_inc(v_addFn_x3f_5057_);
                    crate::leanh::lean_inc(v_charInst_x3f_5056_);
                    crate::leanh::lean_inc(v_semiringInst_5055_);
                    crate::leanh::lean_inc(v_ringInst_5054_);
                    crate::leanh::lean_inc(v_u_5053_);
                    crate::leanh::lean_inc(v_type_5052_);
                    crate::leanh::lean_inc(v_id_5051_);
                    crate::leanh::lean_dec(v_s_5050_);
                    v___x_5069_ = crate::leanh::lean_box(0);
                    v_isShared_5070_ = v_isSharedCheck_5076_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_e_5046_);
                v___x_5071_ = l_Lean_PersistentArray_push___redArg(v_vars_5065_, v_e_5046_);
                v___x_5072_ = l_Lean_PersistentHashMap_insert___redArg(
                    v___f_5047_,
                    v___f_5048_,
                    v_varMap_5066_,
                    v_e_5046_,
                    v_size_5049_,
                );
                if v_isShared_5070_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5069_, 15, v___x_5072_);
                    crate::leanh::lean_ctor_set(v___x_5069_, 14, v___x_5071_);
                    v___x_5074_ = v___x_5069_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5075_ = crate::leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 0, v_id_5051_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 1, v_type_5052_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 2, v_u_5053_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 3, v_ringInst_5054_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 4, v_semiringInst_5055_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 5, v_charInst_x3f_5056_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 6, v_addFn_x3f_5057_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 7, v_mulFn_x3f_5058_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 8, v_subFn_x3f_5059_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 9, v_negFn_x3f_5060_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 10, v_powFn_x3f_5061_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 11, v_intCastFn_x3f_5062_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 12, v_natCastFn_x3f_5063_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 13, v_one_x3f_5064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 14, v___x_5071_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 15, v___x_5072_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 16, v_denote_5067_);
                    v___x_5074_ = v_reuseFailAlloc_5075_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5074_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1(
    mut v_toPure_5077_: *mut crate::leanh::LeanObject,
    mut v_size_5078_: *mut crate::leanh::LeanObject,
    mut v_____r_5079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5080_ =
        crate::leanh::lean_apply_2(v_toPure_5077_, crate::leanh::lean_box(0), v_size_5078_);
    return v___x_5080_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2(
    mut v_e_5081_: *mut crate::leanh::LeanObject,
    mut v_inst_5082_: *mut crate::leanh::LeanObject,
    mut v_toBind_5083_: *mut crate::leanh::LeanObject,
    mut v___f_5084_: *mut crate::leanh::LeanObject,
    mut v_____r_5085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5086_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
    v___x_5087_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_SolverExtension_markTerm___boxed as *mut core::ffi::c_void,
        14,
        3,
    );
    crate::leanh::lean_closure_set(v___x_5087_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5087_, 1, v___x_5086_);
    crate::leanh::lean_closure_set(v___x_5087_, 2, v_e_5081_);
    v___x_5088_ = crate::leanh::lean_apply_2(v_inst_5082_, crate::leanh::lean_box(0), v___x_5087_);
    v___x_5089_ = crate::leanh::lean_apply_4(
        v_toBind_5083_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5088_,
        v___f_5084_,
    );
    return v___x_5089_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3(
    mut v_inst_5090_: *mut crate::leanh::LeanObject,
    mut v_e_5091_: *mut crate::leanh::LeanObject,
    mut v_toBind_5092_: *mut crate::leanh::LeanObject,
    mut v___f_5093_: *mut crate::leanh::LeanObject,
    mut v_____r_5094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5095_ = crate::leanh::lean_apply_1(v_inst_5090_, v_e_5091_);
    v___x_5096_ = crate::leanh::lean_apply_4(
        v_toBind_5092_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5095_,
        v___f_5093_,
    );
    return v___x_5096_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4(
    mut v___f_5097_: *mut crate::leanh::LeanObject,
    mut v___f_5098_: *mut crate::leanh::LeanObject,
    mut v_e_5099_: *mut crate::leanh::LeanObject,
    mut v_toPure_5100_: *mut crate::leanh::LeanObject,
    mut v_inst_5101_: *mut crate::leanh::LeanObject,
    mut v_toBind_5102_: *mut crate::leanh::LeanObject,
    mut v_inst_5103_: *mut crate::leanh::LeanObject,
    mut v_modifyRing_5104_: *mut crate::leanh::LeanObject,
    mut v_s_5105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vars_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_vars_5106_ = crate::leanh::lean_ctor_get(v_s_5105_, 14);
    crate::leanh::lean_inc_ref(v_vars_5106_);
    v_varMap_5107_ = crate::leanh::lean_ctor_get(v_s_5105_, 15);
    crate::leanh::lean_inc_ref(v_varMap_5107_);
    crate::leanh::lean_dec_ref(v_s_5105_);
    crate::leanh::lean_inc_ref(v_e_5099_);
    crate::leanh::lean_inc_ref(v___f_5098_);
    crate::leanh::lean_inc_ref(v___f_5097_);
    v___x_5108_ = l_Lean_PersistentHashMap_find_x3f___redArg(
        v___f_5097_,
        v___f_5098_,
        v_varMap_5107_,
        v_e_5099_,
    );
    crate::leanh::lean_dec_ref(v_varMap_5107_);
    if crate::leanh::lean_obj_tag(v___x_5108_) == 1 {
        let mut v_val_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_vars_5106_);
        crate::leanh::lean_dec(v_modifyRing_5104_);
        crate::leanh::lean_dec(v_inst_5103_);
        crate::leanh::lean_dec(v_toBind_5102_);
        crate::leanh::lean_dec(v_inst_5101_);
        crate::leanh::lean_dec_ref(v_e_5099_);
        crate::leanh::lean_dec_ref(v___f_5098_);
        crate::leanh::lean_dec_ref(v___f_5097_);
        v_val_5109_ = crate::leanh::lean_ctor_get(v___x_5108_, 0);
        crate::leanh::lean_inc(v_val_5109_);
        crate::leanh::lean_dec_ref_known(v___x_5108_, 1);
        v___x_5110_ =
            crate::leanh::lean_apply_2(v_toPure_5100_, crate::leanh::lean_box(0), v_val_5109_);
        return v___x_5110_;
    } else {
        let mut v_size_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_5108_);
        v_size_5111_ = crate::leanh::lean_ctor_get(v_vars_5106_, 2);
        crate::leanh::lean_inc_n(v_size_5111_, 2);
        crate::leanh::lean_dec_ref(v_vars_5106_);
        crate::leanh::lean_inc_ref_n(v_e_5099_, 2);
        v___f_5112_ = crate::leanh::lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_5112_, 0, v_e_5099_);
        crate::leanh::lean_closure_set(v___f_5112_, 1, v___f_5097_);
        crate::leanh::lean_closure_set(v___f_5112_, 2, v___f_5098_);
        crate::leanh::lean_closure_set(v___f_5112_, 3, v_size_5111_);
        v___f_5113_ = crate::leanh::lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_5113_, 0, v_toPure_5100_);
        crate::leanh::lean_closure_set(v___f_5113_, 1, v_size_5111_);
        crate::leanh::lean_inc_n(v_toBind_5102_, 2);
        v___f_5114_ = crate::leanh::lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_5114_, 0, v_e_5099_);
        crate::leanh::lean_closure_set(v___f_5114_, 1, v_inst_5101_);
        crate::leanh::lean_closure_set(v___f_5114_, 2, v_toBind_5102_);
        crate::leanh::lean_closure_set(v___f_5114_, 3, v___f_5113_);
        v___f_5115_ = crate::leanh::lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_5115_, 0, v_inst_5103_);
        crate::leanh::lean_closure_set(v___f_5115_, 1, v_e_5099_);
        crate::leanh::lean_closure_set(v___f_5115_, 2, v_toBind_5102_);
        crate::leanh::lean_closure_set(v___f_5115_, 3, v___f_5114_);
        v___x_5116_ = crate::leanh::lean_apply_1(v_modifyRing_5104_, v___f_5112_);
        v___x_5117_ = crate::leanh::lean_apply_4(
            v_toBind_5102_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5116_,
            v___f_5115_,
        );
        return v___x_5117_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(
    mut v_inst_5120_: *mut crate::leanh::LeanObject,
    mut v_inst_5121_: *mut crate::leanh::LeanObject,
    mut v_inst_5122_: *mut crate::leanh::LeanObject,
    mut v_inst_5123_: *mut crate::leanh::LeanObject,
    mut v_e_5124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5125_ = crate::leanh::lean_ctor_get(v_inst_5121_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_5125_);
    v_toBind_5126_ = crate::leanh::lean_ctor_get(v_inst_5121_, 1);
    crate::leanh::lean_inc_n(v_toBind_5126_, 2);
    crate::leanh::lean_dec_ref(v_inst_5121_);
    v_getRing_5127_ = crate::leanh::lean_ctor_get(v_inst_5122_, 0);
    crate::leanh::lean_inc(v_getRing_5127_);
    v_modifyRing_5128_ = crate::leanh::lean_ctor_get(v_inst_5122_, 1);
    crate::leanh::lean_inc(v_modifyRing_5128_);
    crate::leanh::lean_dec_ref(v_inst_5122_);
    v_toPure_5129_ = crate::leanh::lean_ctor_get(v_toApplicative_5125_, 1);
    crate::leanh::lean_inc(v_toPure_5129_);
    crate::leanh::lean_dec_ref(v_toApplicative_5125_);
    v___f_5130_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0;
    v___f_5131_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1;
    v___f_5132_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4 as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_5132_, 0, v___f_5130_);
    crate::leanh::lean_closure_set(v___f_5132_, 1, v___f_5131_);
    crate::leanh::lean_closure_set(v___f_5132_, 2, v_e_5124_);
    crate::leanh::lean_closure_set(v___f_5132_, 3, v_toPure_5129_);
    crate::leanh::lean_closure_set(v___f_5132_, 4, v_inst_5120_);
    crate::leanh::lean_closure_set(v___f_5132_, 5, v_toBind_5126_);
    crate::leanh::lean_closure_set(v___f_5132_, 6, v_inst_5123_);
    crate::leanh::lean_closure_set(v___f_5132_, 7, v_modifyRing_5128_);
    v___x_5133_ = crate::leanh::lean_apply_4(
        v_toBind_5126_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getRing_5127_,
        v___f_5132_,
    );
    return v___x_5133_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkVarCore(
    mut v_m_5134_: *mut crate::leanh::LeanObject,
    mut v_inst_5135_: *mut crate::leanh::LeanObject,
    mut v_inst_5136_: *mut crate::leanh::LeanObject,
    mut v_inst_5137_: *mut crate::leanh::LeanObject,
    mut v_inst_5138_: *mut crate::leanh::LeanObject,
    mut v_e_5139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5140_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(
        v_inst_5135_,
        v_inst_5136_,
        v_inst_5137_,
        v_inst_5138_,
        v_e_5139_,
    );
    return v___x_5140_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0(
    mut v_e_5141_: *mut crate::leanh::LeanObject,
    mut v___y_5142_: *mut crate::leanh::LeanObject,
    mut v___y_5143_: *mut crate::leanh::LeanObject,
    mut v___y_5144_: *mut crate::leanh::LeanObject,
    mut v___y_5145_: *mut crate::leanh::LeanObject,
    mut v___y_5146_: *mut crate::leanh::LeanObject,
    mut v___y_5147_: *mut crate::leanh::LeanObject,
    mut v___y_5148_: *mut crate::leanh::LeanObject,
    mut v___y_5149_: *mut crate::leanh::LeanObject,
    mut v___y_5150_: *mut crate::leanh::LeanObject,
    mut v___y_5151_: *mut crate::leanh::LeanObject,
    mut v___y_5152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5154_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(
        v_e_5141_,
        v___y_5142_,
        v___y_5143_,
        v___y_5147_,
        v___y_5148_,
        v___y_5149_,
        v___y_5150_,
        v___y_5151_,
        v___y_5152_,
    );
    return v___x_5154_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0___boxed(
    mut v_e_5155_: *mut crate::leanh::LeanObject,
    mut v___y_5156_: *mut crate::leanh::LeanObject,
    mut v___y_5157_: *mut crate::leanh::LeanObject,
    mut v___y_5158_: *mut crate::leanh::LeanObject,
    mut v___y_5159_: *mut crate::leanh::LeanObject,
    mut v___y_5160_: *mut crate::leanh::LeanObject,
    mut v___y_5161_: *mut crate::leanh::LeanObject,
    mut v___y_5162_: *mut crate::leanh::LeanObject,
    mut v___y_5163_: *mut crate::leanh::LeanObject,
    mut v___y_5164_: *mut crate::leanh::LeanObject,
    mut v___y_5165_: *mut crate::leanh::LeanObject,
    mut v___y_5166_: *mut crate::leanh::LeanObject,
    mut v___y_5167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5168_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0(
        v_e_5155_,
        v___y_5156_,
        v___y_5157_,
        v___y_5158_,
        v___y_5159_,
        v___y_5160_,
        v___y_5161_,
        v___y_5162_,
        v___y_5163_,
        v___y_5164_,
        v___y_5165_,
        v___y_5166_,
    );
    crate::leanh::lean_dec(v___y_5166_);
    crate::leanh::lean_dec_ref(v___y_5165_);
    crate::leanh::lean_dec(v___y_5164_);
    crate::leanh::lean_dec_ref(v___y_5163_);
    crate::leanh::lean_dec(v___y_5162_);
    crate::leanh::lean_dec_ref(v___y_5161_);
    crate::leanh::lean_dec(v___y_5160_);
    crate::leanh::lean_dec_ref(v___y_5159_);
    crate::leanh::lean_dec(v___y_5158_);
    crate::leanh::lean_dec(v___y_5157_);
    crate::leanh::lean_dec_ref(v___y_5156_);
    return v_res_5168_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___lam__0(
    mut v_e_5171_: *mut crate::leanh::LeanObject,
    mut v_size_5172_: *mut crate::leanh::LeanObject,
    mut v_s_5173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toRing_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recheck_5188_: u8 = 0;
    let mut v_invSet_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_5192_: u8 = 0;
    let mut v___x_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5195_: u8 = 0;
    let mut v_id_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5215_: u8 = 0;
    let mut v___x_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5224_: u8 = 0;
    let mut v_isSharedCheck_5225_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_5174_ = crate::leanh::lean_ctor_get(v_s_5173_, 0);
                v_invFn_x3f_5175_ = crate::leanh::lean_ctor_get(v_s_5173_, 1);
                v_semiringId_x3f_5176_ = crate::leanh::lean_ctor_get(v_s_5173_, 2);
                v_commSemiringInst_5177_ = crate::leanh::lean_ctor_get(v_s_5173_, 3);
                v_commRingInst_5178_ = crate::leanh::lean_ctor_get(v_s_5173_, 4);
                v_noZeroDivInst_x3f_5179_ = crate::leanh::lean_ctor_get(v_s_5173_, 5);
                v_fieldInst_x3f_5180_ = crate::leanh::lean_ctor_get(v_s_5173_, 6);
                v_powIdentityInst_x3f_5181_ = crate::leanh::lean_ctor_get(v_s_5173_, 7);
                v_denoteEntries_5182_ = crate::leanh::lean_ctor_get(v_s_5173_, 8);
                v_nextId_5183_ = crate::leanh::lean_ctor_get(v_s_5173_, 9);
                v_steps_5184_ = crate::leanh::lean_ctor_get(v_s_5173_, 10);
                v_queue_5185_ = crate::leanh::lean_ctor_get(v_s_5173_, 11);
                v_basis_5186_ = crate::leanh::lean_ctor_get(v_s_5173_, 12);
                v_diseqs_5187_ = crate::leanh::lean_ctor_get(v_s_5173_, 13);
                v_recheck_5188_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_5173_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                );
                v_invSet_5189_ = crate::leanh::lean_ctor_get(v_s_5173_, 14);
                v_powIdentityVarCount_5190_ = crate::leanh::lean_ctor_get(v_s_5173_, 15);
                v_numEq0_x3f_5191_ = crate::leanh::lean_ctor_get(v_s_5173_, 16);
                v_numEq0Updated_5192_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_5173_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_5225_ = (!crate::leanh::lean_is_exclusive(v_s_5173_)) as u8;
                if v_isSharedCheck_5225_ == 0 {
                    v___x_5194_ = v_s_5173_;
                    v_isShared_5195_ = v_isSharedCheck_5225_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_numEq0_x3f_5191_);
                    crate::leanh::lean_inc(v_powIdentityVarCount_5190_);
                    crate::leanh::lean_inc(v_invSet_5189_);
                    crate::leanh::lean_inc(v_diseqs_5187_);
                    crate::leanh::lean_inc(v_basis_5186_);
                    crate::leanh::lean_inc(v_queue_5185_);
                    crate::leanh::lean_inc(v_steps_5184_);
                    crate::leanh::lean_inc(v_nextId_5183_);
                    crate::leanh::lean_inc(v_denoteEntries_5182_);
                    crate::leanh::lean_inc(v_powIdentityInst_x3f_5181_);
                    crate::leanh::lean_inc(v_fieldInst_x3f_5180_);
                    crate::leanh::lean_inc(v_noZeroDivInst_x3f_5179_);
                    crate::leanh::lean_inc(v_commRingInst_5178_);
                    crate::leanh::lean_inc(v_commSemiringInst_5177_);
                    crate::leanh::lean_inc(v_semiringId_x3f_5176_);
                    crate::leanh::lean_inc(v_invFn_x3f_5175_);
                    crate::leanh::lean_inc(v_toRing_5174_);
                    crate::leanh::lean_dec(v_s_5173_);
                    v___x_5194_ = crate::leanh::lean_box(0);
                    v_isShared_5195_ = v_isSharedCheck_5225_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_id_5196_ = crate::leanh::lean_ctor_get(v_toRing_5174_, 0);
                v_type_5197_ = crate::leanh::lean_ctor_get(v_toRing_5174_, 1);
                v_u_5198_ = crate::leanh::lean_ctor_get(v_toRing_5174_, 2);
                v_ringInst_5199_ = crate::leanh::lean_ctor_get(v_toRing_5174_, 3);
                v_semiringInst_5200_ = crate::leanh::lean_ctor_get(v_toRing_5174_, 4);
                v_charInst_x3f_5201_ = crate::leanh::lean_ctor_get(v_toRing_5174_, 5);
                v_addFn_x3f_5202_ = crate::leanh::lean_ctor_get(v_toRing_5174_, 6);
                v_mulFn_x3f_5203_ = crate::leanh::lean_ctor_get(v_toRing_5174_, 7);
                v_subFn_x3f_5204_ = crate::leanh::lean_ctor_get(v_toRing_5174_, 8);
                v_negFn_x3f_5205_ = crate::leanh::lean_ctor_get(v_toRing_5174_, 9);
                v_powFn_x3f_5206_ = crate::leanh::lean_ctor_get(v_toRing_5174_, 10);
                v_intCastFn_x3f_5207_ = crate::leanh::lean_ctor_get(v_toRing_5174_, 11);
                v_natCastFn_x3f_5208_ = crate::leanh::lean_ctor_get(v_toRing_5174_, 12);
                v_one_x3f_5209_ = crate::leanh::lean_ctor_get(v_toRing_5174_, 13);
                v_vars_5210_ = crate::leanh::lean_ctor_get(v_toRing_5174_, 14);
                v_varMap_5211_ = crate::leanh::lean_ctor_get(v_toRing_5174_, 15);
                v_denote_5212_ = crate::leanh::lean_ctor_get(v_toRing_5174_, 16);
                v_isSharedCheck_5224_ = (!crate::leanh::lean_is_exclusive(v_toRing_5174_)) as u8;
                if v_isSharedCheck_5224_ == 0 {
                    v___x_5214_ = v_toRing_5174_;
                    v_isShared_5215_ = v_isSharedCheck_5224_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_denote_5212_);
                    crate::leanh::lean_inc(v_varMap_5211_);
                    crate::leanh::lean_inc(v_vars_5210_);
                    crate::leanh::lean_inc(v_one_x3f_5209_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_5208_);
                    crate::leanh::lean_inc(v_intCastFn_x3f_5207_);
                    crate::leanh::lean_inc(v_powFn_x3f_5206_);
                    crate::leanh::lean_inc(v_negFn_x3f_5205_);
                    crate::leanh::lean_inc(v_subFn_x3f_5204_);
                    crate::leanh::lean_inc(v_mulFn_x3f_5203_);
                    crate::leanh::lean_inc(v_addFn_x3f_5202_);
                    crate::leanh::lean_inc(v_charInst_x3f_5201_);
                    crate::leanh::lean_inc(v_semiringInst_5200_);
                    crate::leanh::lean_inc(v_ringInst_5199_);
                    crate::leanh::lean_inc(v_u_5198_);
                    crate::leanh::lean_inc(v_type_5197_);
                    crate::leanh::lean_inc(v_id_5196_);
                    crate::leanh::lean_dec(v_toRing_5174_);
                    v___x_5214_ = crate::leanh::lean_box(0);
                    v_isShared_5215_ = v_isSharedCheck_5224_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v_e_5171_);
                v___x_5216_ = l_Lean_PersistentArray_push___redArg(v_vars_5210_, v_e_5171_);
                v___x_5217_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_varMap_5211_, v_e_5171_, v_size_5172_);
                if v_isShared_5215_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5214_, 15, v___x_5217_);
                    crate::leanh::lean_ctor_set(v___x_5214_, 14, v___x_5216_);
                    v___x_5219_ = v___x_5214_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5223_ = crate::leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 0, v_id_5196_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 1, v_type_5197_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 2, v_u_5198_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 3, v_ringInst_5199_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 4, v_semiringInst_5200_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 5, v_charInst_x3f_5201_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 6, v_addFn_x3f_5202_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 7, v_mulFn_x3f_5203_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 8, v_subFn_x3f_5204_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 9, v_negFn_x3f_5205_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 10, v_powFn_x3f_5206_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 11, v_intCastFn_x3f_5207_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 12, v_natCastFn_x3f_5208_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 13, v_one_x3f_5209_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 14, v___x_5216_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 15, v___x_5217_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 16, v_denote_5212_);
                    v___x_5219_ = v_reuseFailAlloc_5223_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5195_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5194_, 0, v___x_5219_);
                    v___x_5221_ = v___x_5194_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5222_ = crate::leanh::lean_alloc_ctor(0, 17, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 0, v___x_5219_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 1, v_invFn_x3f_5175_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 2, v_semiringId_x3f_5176_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5222_,
                        3,
                        v_commSemiringInst_5177_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 4, v_commRingInst_5178_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5222_,
                        5,
                        v_noZeroDivInst_x3f_5179_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 6, v_fieldInst_x3f_5180_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5222_,
                        7,
                        v_powIdentityInst_x3f_5181_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 8, v_denoteEntries_5182_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 9, v_nextId_5183_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 10, v_steps_5184_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 11, v_queue_5185_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 12, v_basis_5186_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 13, v_diseqs_5187_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 14, v_invSet_5189_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5222_,
                        15,
                        v_powIdentityVarCount_5190_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 16, v_numEq0_x3f_5191_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5222_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                        v_recheck_5188_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5222_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                        v_numEq0Updated_5192_,
                    );
                    v___x_5221_ = v_reuseFailAlloc_5222_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5221_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(
    mut v_e_5226_: *mut crate::leanh::LeanObject,
    mut v___y_5227_: *mut crate::leanh::LeanObject,
    mut v___y_5228_: *mut crate::leanh::LeanObject,
    mut v___y_5229_: *mut crate::leanh::LeanObject,
    mut v___y_5230_: *mut crate::leanh::LeanObject,
    mut v___y_5231_: *mut crate::leanh::LeanObject,
    mut v___y_5232_: *mut crate::leanh::LeanObject,
    mut v___y_5233_: *mut crate::leanh::LeanObject,
    mut v___y_5234_: *mut crate::leanh::LeanObject,
    mut v___y_5235_: *mut crate::leanh::LeanObject,
    mut v___y_5236_: *mut crate::leanh::LeanObject,
    mut v___y_5237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5243_: u8 = 0;
    let mut v_toRing_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5260_: u8 = 0;
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5264_: u8 = 0;
    let mut v_unused_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5269_: u8 = 0;
    let mut v___x_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5273_: u8 = 0;
    let mut v_a_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5277_: u8 = 0;
    let mut v___x_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5281_: u8 = 0;
    let mut v_a_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5285_: u8 = 0;
    let mut v___x_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5289_: u8 = 0;
    let mut v_isSharedCheck_5290_: u8 = 0;
    let mut v_a_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5294_: u8 = 0;
    let mut v___x_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5298_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5239_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                    v___y_5227_,
                    v___y_5228_,
                    v___y_5229_,
                    v___y_5230_,
                    v___y_5231_,
                    v___y_5232_,
                    v___y_5233_,
                    v___y_5234_,
                    v___y_5235_,
                    v___y_5236_,
                    v___y_5237_,
                );
                if crate::leanh::lean_obj_tag(v___x_5239_) == 0 {
                    v_a_5240_ = crate::leanh::lean_ctor_get(v___x_5239_, 0);
                    v_isSharedCheck_5290_ = (!crate::leanh::lean_is_exclusive(v___x_5239_)) as u8;
                    if v_isSharedCheck_5290_ == 0 {
                        v___x_5242_ = v___x_5239_;
                        v_isShared_5243_ = v_isSharedCheck_5290_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5240_);
                        crate::leanh::lean_dec(v___x_5239_);
                        v___x_5242_ = crate::leanh::lean_box(0);
                        v_isShared_5243_ = v_isSharedCheck_5290_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_5226_);
                    v_a_5291_ = crate::leanh::lean_ctor_get(v___x_5239_, 0);
                    v_isSharedCheck_5298_ = (!crate::leanh::lean_is_exclusive(v___x_5239_)) as u8;
                    if v_isSharedCheck_5298_ == 0 {
                        v___x_5293_ = v___x_5239_;
                        v_isShared_5294_ = v_isSharedCheck_5298_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5291_);
                        crate::leanh::lean_dec(v___x_5239_);
                        v___x_5293_ = crate::leanh::lean_box(0);
                        v_isShared_5294_ = v_isSharedCheck_5298_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v_toRing_5244_ = crate::leanh::lean_ctor_get(v_a_5240_, 0);
                crate::leanh::lean_inc_ref(v_toRing_5244_);
                crate::leanh::lean_dec(v_a_5240_);
                v_vars_5245_ = crate::leanh::lean_ctor_get(v_toRing_5244_, 14);
                crate::leanh::lean_inc_ref(v_vars_5245_);
                v_varMap_5246_ = crate::leanh::lean_ctor_get(v_toRing_5244_, 15);
                crate::leanh::lean_inc_ref(v_varMap_5246_);
                crate::leanh::lean_dec_ref(v_toRing_5244_);
                v___x_5247_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_varMap_5246_, v_e_5226_);
                crate::leanh::lean_dec_ref(v_varMap_5246_);
                if crate::leanh::lean_obj_tag(v___x_5247_) == 1 {
                    crate::leanh::lean_dec_ref(v_vars_5245_);
                    crate::leanh::lean_dec_ref(v_e_5226_);
                    v_val_5248_ = crate::leanh::lean_ctor_get(v___x_5247_, 0);
                    crate::leanh::lean_inc(v_val_5248_);
                    crate::leanh::lean_dec_ref_known(v___x_5247_, 1);
                    if v_isShared_5243_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5242_, 0, v_val_5248_);
                        v___x_5250_ = v___x_5242_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5251_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5251_, 0, v_val_5248_);
                        v___x_5250_ = v_reuseFailAlloc_5251_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5247_);
                    crate::leanh::lean_del_object(v___x_5242_);
                    v_size_5252_ = crate::leanh::lean_ctor_get(v_vars_5245_, 2);
                    crate::leanh::lean_inc_n(v_size_5252_, 2);
                    crate::leanh::lean_dec_ref(v_vars_5245_);
                    crate::leanh::lean_inc_ref(v_e_5226_);
                    v___f_5253_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___lam__0 as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_5253_, 0, v_e_5226_);
                    crate::leanh::lean_closure_set(v___f_5253_, 1, v_size_5252_);
                    v___x_5254_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(
                        v___f_5253_,
                        v___y_5227_,
                        v___y_5228_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5254_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5254_, 1);
                        crate::leanh::lean_inc_ref(v_e_5226_);
                        v___x_5255_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(
                            v_e_5226_,
                            v___y_5227_,
                            v___y_5228_,
                            v___y_5232_,
                            v___y_5233_,
                            v___y_5234_,
                            v___y_5235_,
                            v___y_5236_,
                            v___y_5237_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5255_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5255_, 1);
                            v___x_5256_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                            v___x_5257_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(
                                v___x_5256_,
                                v_e_5226_,
                                v___y_5228_,
                                v___y_5229_,
                                v___y_5230_,
                                v___y_5231_,
                                v___y_5232_,
                                v___y_5233_,
                                v___y_5234_,
                                v___y_5235_,
                                v___y_5236_,
                                v___y_5237_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5257_) == 0 {
                                v_isSharedCheck_5264_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5257_)) as u8;
                                if v_isSharedCheck_5264_ == 0 {
                                    v_unused_5265_ = crate::leanh::lean_ctor_get(v___x_5257_, 0);
                                    crate::leanh::lean_dec(v_unused_5265_);
                                    v___x_5259_ = v___x_5257_;
                                    v_isShared_5260_ = v_isSharedCheck_5264_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_5257_);
                                    v___x_5259_ = crate::leanh::lean_box(0);
                                    v_isShared_5260_ = v_isSharedCheck_5264_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_size_5252_);
                                v_a_5266_ = crate::leanh::lean_ctor_get(v___x_5257_, 0);
                                v_isSharedCheck_5273_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5257_)) as u8;
                                if v_isSharedCheck_5273_ == 0 {
                                    v___x_5268_ = v___x_5257_;
                                    v_isShared_5269_ = v_isSharedCheck_5273_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5266_);
                                    crate::leanh::lean_dec(v___x_5257_);
                                    v___x_5268_ = crate::leanh::lean_box(0);
                                    v_isShared_5269_ = v_isSharedCheck_5273_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_size_5252_);
                            crate::leanh::lean_dec_ref(v_e_5226_);
                            v_a_5274_ = crate::leanh::lean_ctor_get(v___x_5255_, 0);
                            v_isSharedCheck_5281_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5255_)) as u8;
                            if v_isSharedCheck_5281_ == 0 {
                                v___x_5276_ = v___x_5255_;
                                v_isShared_5277_ = v_isSharedCheck_5281_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5274_);
                                crate::leanh::lean_dec(v___x_5255_);
                                v___x_5276_ = crate::leanh::lean_box(0);
                                v_isShared_5277_ = v_isSharedCheck_5281_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_size_5252_);
                        crate::leanh::lean_dec_ref(v_e_5226_);
                        v_a_5282_ = crate::leanh::lean_ctor_get(v___x_5254_, 0);
                        v_isSharedCheck_5289_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5254_)) as u8;
                        if v_isSharedCheck_5289_ == 0 {
                            v___x_5284_ = v___x_5254_;
                            v_isShared_5285_ = v_isSharedCheck_5289_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5282_);
                            crate::leanh::lean_dec(v___x_5254_);
                            v___x_5284_ = crate::leanh::lean_box(0);
                            v_isShared_5285_ = v_isSharedCheck_5289_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5250_;
            }
            3 => {
                if v_isShared_5260_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5259_, 0, v_size_5252_);
                    v___x_5262_ = v___x_5259_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5263_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5263_, 0, v_size_5252_);
                    v___x_5262_ = v_reuseFailAlloc_5263_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5262_;
            }
            5 => {
                if v_isShared_5269_ == 0 {
                    v___x_5271_ = v___x_5268_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5272_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5272_, 0, v_a_5266_);
                    v___x_5271_ = v_reuseFailAlloc_5272_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5271_;
            }
            7 => {
                if v_isShared_5277_ == 0 {
                    v___x_5279_ = v___x_5276_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5280_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5280_, 0, v_a_5274_);
                    v___x_5279_ = v_reuseFailAlloc_5280_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5279_;
            }
            9 => {
                if v_isShared_5285_ == 0 {
                    v___x_5287_ = v___x_5284_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5288_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5288_, 0, v_a_5282_);
                    v___x_5287_ = v_reuseFailAlloc_5288_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5287_;
            }
            11 => {
                if v_isShared_5294_ == 0 {
                    v___x_5296_ = v___x_5293_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5297_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5297_, 0, v_a_5291_);
                    v___x_5296_ = v_reuseFailAlloc_5297_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5296_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___boxed(
    mut v_e_5299_: *mut crate::leanh::LeanObject,
    mut v___y_5300_: *mut crate::leanh::LeanObject,
    mut v___y_5301_: *mut crate::leanh::LeanObject,
    mut v___y_5302_: *mut crate::leanh::LeanObject,
    mut v___y_5303_: *mut crate::leanh::LeanObject,
    mut v___y_5304_: *mut crate::leanh::LeanObject,
    mut v___y_5305_: *mut crate::leanh::LeanObject,
    mut v___y_5306_: *mut crate::leanh::LeanObject,
    mut v___y_5307_: *mut crate::leanh::LeanObject,
    mut v___y_5308_: *mut crate::leanh::LeanObject,
    mut v___y_5309_: *mut crate::leanh::LeanObject,
    mut v___y_5310_: *mut crate::leanh::LeanObject,
    mut v___y_5311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5312_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(v_e_5299_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_, v___y_5309_, v___y_5310_);
    crate::leanh::lean_dec(v___y_5310_);
    crate::leanh::lean_dec_ref(v___y_5309_);
    crate::leanh::lean_dec(v___y_5308_);
    crate::leanh::lean_dec_ref(v___y_5307_);
    crate::leanh::lean_dec(v___y_5306_);
    crate::leanh::lean_dec_ref(v___y_5305_);
    crate::leanh::lean_dec(v___y_5304_);
    crate::leanh::lean_dec_ref(v___y_5303_);
    crate::leanh::lean_dec(v___y_5302_);
    crate::leanh::lean_dec(v___y_5301_);
    crate::leanh::lean_dec_ref(v___y_5300_);
    return v_res_5312_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkVar(
    mut v_e_5313_: *mut crate::leanh::LeanObject,
    mut v_a_5314_: *mut crate::leanh::LeanObject,
    mut v_a_5315_: *mut crate::leanh::LeanObject,
    mut v_a_5316_: *mut crate::leanh::LeanObject,
    mut v_a_5317_: *mut crate::leanh::LeanObject,
    mut v_a_5318_: *mut crate::leanh::LeanObject,
    mut v_a_5319_: *mut crate::leanh::LeanObject,
    mut v_a_5320_: *mut crate::leanh::LeanObject,
    mut v_a_5321_: *mut crate::leanh::LeanObject,
    mut v_a_5322_: *mut crate::leanh::LeanObject,
    mut v_a_5323_: *mut crate::leanh::LeanObject,
    mut v_a_5324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5326_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(v_e_5313_, v_a_5314_, v_a_5315_, v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_);
    return v___x_5326_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkVar___boxed(
    mut v_e_5327_: *mut crate::leanh::LeanObject,
    mut v_a_5328_: *mut crate::leanh::LeanObject,
    mut v_a_5329_: *mut crate::leanh::LeanObject,
    mut v_a_5330_: *mut crate::leanh::LeanObject,
    mut v_a_5331_: *mut crate::leanh::LeanObject,
    mut v_a_5332_: *mut crate::leanh::LeanObject,
    mut v_a_5333_: *mut crate::leanh::LeanObject,
    mut v_a_5334_: *mut crate::leanh::LeanObject,
    mut v_a_5335_: *mut crate::leanh::LeanObject,
    mut v_a_5336_: *mut crate::leanh::LeanObject,
    mut v_a_5337_: *mut crate::leanh::LeanObject,
    mut v_a_5338_: *mut crate::leanh::LeanObject,
    mut v_a_5339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5340_ = l_Lean_Meta_Grind_Arith_CommRing_mkVar(
        v_e_5327_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5333_, v_a_5334_,
        v_a_5335_, v_a_5336_, v_a_5337_, v_a_5338_,
    );
    crate::leanh::lean_dec(v_a_5338_);
    crate::leanh::lean_dec_ref(v_a_5337_);
    crate::leanh::lean_dec(v_a_5336_);
    crate::leanh::lean_dec_ref(v_a_5335_);
    crate::leanh::lean_dec(v_a_5334_);
    crate::leanh::lean_dec_ref(v_a_5333_);
    crate::leanh::lean_dec(v_a_5332_);
    crate::leanh::lean_dec_ref(v_a_5331_);
    crate::leanh::lean_dec(v_a_5330_);
    crate::leanh::lean_dec(v_a_5329_);
    crate::leanh::lean_dec_ref(v_a_5328_);
    return v_res_5340_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_Poly(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM =
        _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Arith_Poly(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
}
