// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
// Imports: Lean.Meta.Tactic.Grind.SynthInstance Lean.Meta.Tactic.Grind.Arith.CommRing.MonadRing Lean.Meta.Sym.Arith.Poly
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_mul, lean_st_ref_get, lean_uint64_to_usize, lean_usize_add,
    lean_usize_dec_le, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
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
pub static l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__0_value:
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
        114, 105, 110, 103, 32, 112, 111, 108, 121, 110, 111, 109, 105, 97, 108, 32, 100, 101, 103,
        114, 101, 101, 32, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__2_value:
    leanh::LeanStringObject<39> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__4_value:
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
    m_data: [41, 96, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__1_value:
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
    m_fun: l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__2_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__0_value:
    leanh::LeanStringObject<39> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___boxed
        as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1: usize = 0;
pub static l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0_value:
    leanh::LeanStringObject<60> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__0_value:
    leanh::LeanStringObject<34> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0_value:
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
    m_fun: l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1_value:
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
    m_fun: l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(
    mut v_a_2671_: *mut leanh::LeanObject,
    mut v_a_2672_: *mut leanh::LeanObject,
    mut v_a_2673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2681_: u8 = 0;
    let mut v_ringSteps_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: u8 = 0;
    let mut v___x_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2689_: u8 = 0;
    let mut v_a_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2693_: u8 = 0;
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2697_: u8 = 0;
    let mut v_a_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2701_: u8 = 0;
    let mut v___x_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2705_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2675_ =
                    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_2671_, v_a_2673_);
                if leanh::lean_obj_tag(v___x_2675_) == 0 {
                    v_a_2676_ = leanh::lean_ctor_get(v___x_2675_, 0);
                    leanh::lean_inc(v_a_2676_);
                    leanh::lean_dec_ref_known(v___x_2675_, 1);
                    v___x_2677_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2672_);
                    if leanh::lean_obj_tag(v___x_2677_) == 0 {
                        v_a_2678_ = leanh::lean_ctor_get(v___x_2677_, 0);
                        v_isSharedCheck_2689_ =
                            (!leanh::lean_is_exclusive(v___x_2677_)) as u8;
                        if v_isSharedCheck_2689_ == 0 {
                            v___x_2680_ = v___x_2677_;
                            v_isShared_2681_ = v_isSharedCheck_2689_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2678_);
                            leanh::lean_dec(v___x_2677_);
                            v___x_2680_ = leanh::lean_box(0);
                            v_isShared_2681_ = v_isSharedCheck_2689_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_2676_);
                        v_a_2690_ = leanh::lean_ctor_get(v___x_2677_, 0);
                        v_isSharedCheck_2697_ =
                            (!leanh::lean_is_exclusive(v___x_2677_)) as u8;
                        if v_isSharedCheck_2697_ == 0 {
                            v___x_2692_ = v___x_2677_;
                            v_isShared_2693_ = v_isSharedCheck_2697_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2690_);
                            leanh::lean_dec(v___x_2677_);
                            v___x_2692_ = leanh::lean_box(0);
                            v_isShared_2693_ = v_isSharedCheck_2697_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_2698_ = leanh::lean_ctor_get(v___x_2675_, 0);
                    v_isSharedCheck_2705_ = (!leanh::lean_is_exclusive(v___x_2675_)) as u8;
                    if v_isSharedCheck_2705_ == 0 {
                        v___x_2700_ = v___x_2675_;
                        v_isShared_2701_ = v_isSharedCheck_2705_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2698_);
                        leanh::lean_dec(v___x_2675_);
                        v___x_2700_ = leanh::lean_box(0);
                        v_isShared_2701_ = v_isSharedCheck_2705_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_ringSteps_2682_ = leanh::lean_ctor_get(v_a_2678_, 6);
                leanh::lean_inc(v_ringSteps_2682_);
                leanh::lean_dec(v_a_2678_);
                v_steps_2683_ = leanh::lean_ctor_get(v_a_2676_, 12);
                leanh::lean_inc(v_steps_2683_);
                leanh::lean_dec(v_a_2676_);
                v___x_2684_ = lean_nat_dec_le(v_ringSteps_2682_, v_steps_2683_);
                leanh::lean_dec(v_steps_2683_);
                leanh::lean_dec(v_ringSteps_2682_);
                v___x_2685_ = leanh::lean_box((v___x_2684_) as usize);
                if v_isShared_2681_ == 0 {
                    leanh::lean_ctor_set(v___x_2680_, 0, v___x_2685_);
                    v___x_2687_ = v___x_2680_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2688_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___x_2685_);
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
                    v_reuseFailAlloc_2696_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2690_);
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
                    v_reuseFailAlloc_2704_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2698_);
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
    mut v_a_2706_: *mut leanh::LeanObject,
    mut v_a_2707_: *mut leanh::LeanObject,
    mut v_a_2708_: *mut leanh::LeanObject,
    mut v_a_2709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2710_ =
        l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(v_a_2706_, v_a_2707_, v_a_2708_);
    leanh::lean_dec_ref(v_a_2708_);
    leanh::lean_dec_ref(v_a_2707_);
    leanh::lean_dec(v_a_2706_);
    return v_res_2710_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps(
    mut v_a_2711_: *mut leanh::LeanObject,
    mut v_a_2712_: *mut leanh::LeanObject,
    mut v_a_2713_: *mut leanh::LeanObject,
    mut v_a_2714_: *mut leanh::LeanObject,
    mut v_a_2715_: *mut leanh::LeanObject,
    mut v_a_2716_: *mut leanh::LeanObject,
    mut v_a_2717_: *mut leanh::LeanObject,
    mut v_a_2718_: *mut leanh::LeanObject,
    mut v_a_2719_: *mut leanh::LeanObject,
    mut v_a_2720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2722_ =
        l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(v_a_2711_, v_a_2713_, v_a_2719_);
    return v___x_2722_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___boxed(
    mut v_a_2723_: *mut leanh::LeanObject,
    mut v_a_2724_: *mut leanh::LeanObject,
    mut v_a_2725_: *mut leanh::LeanObject,
    mut v_a_2726_: *mut leanh::LeanObject,
    mut v_a_2727_: *mut leanh::LeanObject,
    mut v_a_2728_: *mut leanh::LeanObject,
    mut v_a_2729_: *mut leanh::LeanObject,
    mut v_a_2730_: *mut leanh::LeanObject,
    mut v_a_2731_: *mut leanh::LeanObject,
    mut v_a_2732_: *mut leanh::LeanObject,
    mut v_a_2733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2734_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps(
        v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_,
        v_a_2731_, v_a_2732_,
    );
    leanh::lean_dec(v_a_2732_);
    leanh::lean_dec_ref(v_a_2731_);
    leanh::lean_dec(v_a_2730_);
    leanh::lean_dec_ref(v_a_2729_);
    leanh::lean_dec(v_a_2728_);
    leanh::lean_dec_ref(v_a_2727_);
    leanh::lean_dec(v_a_2726_);
    leanh::lean_dec_ref(v_a_2725_);
    leanh::lean_dec(v_a_2724_);
    leanh::lean_dec(v_a_2723_);
    return v_res_2734_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0(
    mut v___x_2735_: u8,
    mut v_s_2736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_rings_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2752_: u8 = 0;
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2756_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_2737_ = leanh::lean_ctor_get(v_s_2736_, 0);
                v_typeIdOf_2738_ = leanh::lean_ctor_get(v_s_2736_, 1);
                v_exprToRingId_2739_ = leanh::lean_ctor_get(v_s_2736_, 2);
                v_semirings_2740_ = leanh::lean_ctor_get(v_s_2736_, 3);
                v_stypeIdOf_2741_ = leanh::lean_ctor_get(v_s_2736_, 4);
                v_exprToSemiringId_2742_ = leanh::lean_ctor_get(v_s_2736_, 5);
                v_ncRings_2743_ = leanh::lean_ctor_get(v_s_2736_, 6);
                v_exprToNCRingId_2744_ = leanh::lean_ctor_get(v_s_2736_, 7);
                v_nctypeIdOf_2745_ = leanh::lean_ctor_get(v_s_2736_, 8);
                v_ncSemirings_2746_ = leanh::lean_ctor_get(v_s_2736_, 9);
                v_exprToNCSemiringId_2747_ = leanh::lean_ctor_get(v_s_2736_, 10);
                v_ncstypeIdOf_2748_ = leanh::lean_ctor_get(v_s_2736_, 11);
                v_steps_2749_ = leanh::lean_ctor_get(v_s_2736_, 12);
                v_isSharedCheck_2756_ = (!leanh::lean_is_exclusive(v_s_2736_)) as u8;
                if v_isSharedCheck_2756_ == 0 {
                    v___x_2751_ = v_s_2736_;
                    v_isShared_2752_ = v_isSharedCheck_2756_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_steps_2749_);
                    leanh::lean_inc(v_ncstypeIdOf_2748_);
                    leanh::lean_inc(v_exprToNCSemiringId_2747_);
                    leanh::lean_inc(v_ncSemirings_2746_);
                    leanh::lean_inc(v_nctypeIdOf_2745_);
                    leanh::lean_inc(v_exprToNCRingId_2744_);
                    leanh::lean_inc(v_ncRings_2743_);
                    leanh::lean_inc(v_exprToSemiringId_2742_);
                    leanh::lean_inc(v_stypeIdOf_2741_);
                    leanh::lean_inc(v_semirings_2740_);
                    leanh::lean_inc(v_exprToRingId_2739_);
                    leanh::lean_inc(v_typeIdOf_2738_);
                    leanh::lean_inc(v_rings_2737_);
                    leanh::lean_dec(v_s_2736_);
                    v___x_2751_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2755_ = leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_rings_2737_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2755_, 1, v_typeIdOf_2738_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2755_, 2, v_exprToRingId_2739_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2755_, 3, v_semirings_2740_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2755_, 4, v_stypeIdOf_2741_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2755_,
                        5,
                        v_exprToSemiringId_2742_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2755_, 6, v_ncRings_2743_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2755_, 7, v_exprToNCRingId_2744_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2755_, 8, v_nctypeIdOf_2745_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2755_, 9, v_ncSemirings_2746_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2755_,
                        10,
                        v_exprToNCSemiringId_2747_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2755_, 11, v_ncstypeIdOf_2748_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2755_, 12, v_steps_2749_);
                    v___x_2754_ = v_reuseFailAlloc_2755_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2754_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                    v___x_2735_,
                );
                return v___x_2754_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0___boxed(
    mut v___x_2757_: *mut leanh::LeanObject,
    mut v_s_2758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7553__boxed_2759_: u8 = 0;
    let mut v_res_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7553__boxed_2759_ = (leanh::lean_unbox(v___x_2757_) as u8);
    v_res_2760_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0(
        v___x_7553__boxed_2759_,
        v_s_2758_,
    );
    return v_res_2760_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2762_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__0;
    v___x_2763_ = l_Lean_stringToMessageData(v___x_2762_);
    return v___x_2763_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2765_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__2;
    v___x_2766_ = l_Lean_stringToMessageData(v___x_2765_);
    return v___x_2766_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2768_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__4;
    v___x_2769_ = l_Lean_stringToMessageData(v___x_2768_);
    return v___x_2769_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg(
    mut v_p_2770_: *mut leanh::LeanObject,
    mut v_a_2771_: *mut leanh::LeanObject,
    mut v_a_2772_: *mut leanh::LeanObject,
    mut v_a_2773_: *mut leanh::LeanObject,
    mut v_a_2774_: *mut leanh::LeanObject,
    mut v_a_2775_: *mut leanh::LeanObject,
    mut v_a_2776_: *mut leanh::LeanObject,
    mut v_a_2777_: *mut leanh::LeanObject,
    mut v_a_2778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2784_: u8 = 0;
    let mut v_ringMaxDegree_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: u8 = 0;
    let mut v___x_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2796_: u8 = 0;
    let mut v_reportedMaxDegreeIssue_2797_: u8 = 0;
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2806_: u8 = 0;
    let mut v___x_2807_: u8 = 0;
    let mut v___x_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2825_: u8 = 0;
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2830_: u8 = 0;
    let mut v_unused_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2835_: u8 = 0;
    let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2839_: u8 = 0;
    let mut v_isSharedCheck_2840_: u8 = 0;
    let mut v_a_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2844_: u8 = 0;
    let mut v___x_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2848_: u8 = 0;
    let mut v_a_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2852_: u8 = 0;
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2856_: u8 = 0;
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2861_: u8 = 0;
    let mut v_a_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2865_: u8 = 0;
    let mut v___x_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2869_: u8 = 0;
    let mut v_isSharedCheck_2870_: u8 = 0;
    let mut v_a_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2874_: u8 = 0;
    let mut v___x_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2878_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2780_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2772_);
                if leanh::lean_obj_tag(v___x_2780_) == 0 {
                    v_a_2781_ = leanh::lean_ctor_get(v___x_2780_, 0);
                    v_isSharedCheck_2870_ = (!leanh::lean_is_exclusive(v___x_2780_)) as u8;
                    if v_isSharedCheck_2870_ == 0 {
                        v___x_2783_ = v___x_2780_;
                        v_isShared_2784_ = v_isSharedCheck_2870_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2781_);
                        leanh::lean_dec(v___x_2780_);
                        v___x_2783_ = leanh::lean_box(0);
                        v_isShared_2784_ = v_isSharedCheck_2870_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2871_ = leanh::lean_ctor_get(v___x_2780_, 0);
                    v_isSharedCheck_2878_ = (!leanh::lean_is_exclusive(v___x_2780_)) as u8;
                    if v_isSharedCheck_2878_ == 0 {
                        v___x_2873_ = v___x_2780_;
                        v_isShared_2874_ = v_isSharedCheck_2878_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2871_);
                        leanh::lean_dec(v___x_2780_);
                        v___x_2873_ = leanh::lean_box(0);
                        v_isShared_2874_ = v_isSharedCheck_2878_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                v_ringMaxDegree_2785_ = leanh::lean_ctor_get(v_a_2781_, 7);
                leanh::lean_inc(v_ringMaxDegree_2785_);
                leanh::lean_dec(v_a_2781_);
                v___x_2786_ = l_Lean_Grind_CommRing_Poly_degree(v_p_2770_);
                v___x_2787_ = lean_nat_dec_le(v_ringMaxDegree_2785_, v___x_2786_);
                leanh::lean_dec(v_ringMaxDegree_2785_);
                if v___x_2787_ == 0 {
                    leanh::lean_dec(v___x_2786_);
                    v___x_2788_ = leanh::lean_box((v___x_2787_) as usize);
                    if v_isShared_2784_ == 0 {
                        leanh::lean_ctor_set(v___x_2783_, 0, v___x_2788_);
                        v___x_2790_ = v___x_2783_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2791_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2791_, 0, v___x_2788_);
                        v___x_2790_ = v_reuseFailAlloc_2791_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2783_);
                    v___x_2792_ =
                        l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_2771_, v_a_2777_);
                    if leanh::lean_obj_tag(v___x_2792_) == 0 {
                        v_a_2793_ = leanh::lean_ctor_get(v___x_2792_, 0);
                        v_isSharedCheck_2861_ =
                            (!leanh::lean_is_exclusive(v___x_2792_)) as u8;
                        if v_isSharedCheck_2861_ == 0 {
                            v___x_2795_ = v___x_2792_;
                            v_isShared_2796_ = v_isSharedCheck_2861_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2793_);
                            leanh::lean_dec(v___x_2792_);
                            v___x_2795_ = leanh::lean_box(0);
                            v_isShared_2796_ = v_isSharedCheck_2861_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_2786_);
                        v_a_2862_ = leanh::lean_ctor_get(v___x_2792_, 0);
                        v_isSharedCheck_2869_ =
                            (!leanh::lean_is_exclusive(v___x_2792_)) as u8;
                        if v_isSharedCheck_2869_ == 0 {
                            v___x_2864_ = v___x_2792_;
                            v_isShared_2865_ = v_isSharedCheck_2869_;
                            state = 15;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2862_);
                            leanh::lean_dec(v___x_2792_);
                            v___x_2864_ = leanh::lean_box(0);
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
                v_reportedMaxDegreeIssue_2797_ = leanh::lean_ctor_get_uint8(
                    v_a_2793_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                leanh::lean_dec(v_a_2793_);
                if v_reportedMaxDegreeIssue_2797_ == 0 {
                    leanh::lean_del_object(v___x_2795_);
                    v___x_2798_ = leanh::lean_box((v___x_2787_) as usize);
                    v___f_2799_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_2799_, 0, v___x_2798_);
                    v___x_2800_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                    v___x_2801_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2800_, v___f_2799_, v_a_2771_);
                    if leanh::lean_obj_tag(v___x_2801_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2801_, 1);
                        v___x_2802_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2773_);
                        if leanh::lean_obj_tag(v___x_2802_) == 0 {
                            v_a_2803_ = leanh::lean_ctor_get(v___x_2802_, 0);
                            v_isSharedCheck_2840_ =
                                (!leanh::lean_is_exclusive(v___x_2802_)) as u8;
                            if v_isSharedCheck_2840_ == 0 {
                                v___x_2805_ = v___x_2802_;
                                v_isShared_2806_ = v_isSharedCheck_2840_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2803_);
                                leanh::lean_dec(v___x_2802_);
                                v___x_2805_ = leanh::lean_box(0);
                                v_isShared_2806_ = v_isSharedCheck_2840_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_2786_);
                            v_a_2841_ = leanh::lean_ctor_get(v___x_2802_, 0);
                            v_isSharedCheck_2848_ =
                                (!leanh::lean_is_exclusive(v___x_2802_)) as u8;
                            if v_isSharedCheck_2848_ == 0 {
                                v___x_2843_ = v___x_2802_;
                                v_isShared_2844_ = v_isSharedCheck_2848_;
                                state = 10;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2841_);
                                leanh::lean_dec(v___x_2802_);
                                v___x_2843_ = leanh::lean_box(0);
                                v_isShared_2844_ = v_isSharedCheck_2848_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_2786_);
                        v_a_2849_ = leanh::lean_ctor_get(v___x_2801_, 0);
                        v_isSharedCheck_2856_ =
                            (!leanh::lean_is_exclusive(v___x_2801_)) as u8;
                        if v_isSharedCheck_2856_ == 0 {
                            v___x_2851_ = v___x_2801_;
                            v_isShared_2852_ = v_isSharedCheck_2856_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2849_);
                            leanh::lean_dec(v___x_2801_);
                            v___x_2851_ = leanh::lean_box(0);
                            v_isShared_2852_ = v_isSharedCheck_2856_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_2786_);
                    v___x_2857_ = leanh::lean_box((v___x_2787_) as usize);
                    if v_isShared_2796_ == 0 {
                        leanh::lean_ctor_set(v___x_2795_, 0, v___x_2857_);
                        v___x_2859_ = v___x_2795_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_2860_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2857_);
                        v___x_2859_ = v_reuseFailAlloc_2860_;
                        state = 14;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2807_ = (leanh::lean_unbox(v_a_2803_) as u8);
                leanh::lean_dec(v_a_2803_);
                if v___x_2807_ == 0 {
                    leanh::lean_dec(v___x_2786_);
                    v___x_2808_ = leanh::lean_box((v___x_2787_) as usize);
                    if v_isShared_2806_ == 0 {
                        leanh::lean_ctor_set(v___x_2805_, 0, v___x_2808_);
                        v___x_2810_ = v___x_2805_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2811_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2808_);
                        v___x_2810_ = v_reuseFailAlloc_2811_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2805_);
                    v___x_2812_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1_once), _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1);
                    v___x_2813_ = l_Nat_reprFast(v___x_2786_);
                    v___x_2814_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2814_, 0, v___x_2813_);
                    v___x_2815_ = l_Lean_MessageData_ofFormat(v___x_2814_);
                    leanh::lean_inc_ref(v___x_2815_);
                    v___x_2816_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2816_, 0, v___x_2812_);
                    leanh::lean_ctor_set(v___x_2816_, 1, v___x_2815_);
                    v___x_2817_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3_once), _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3);
                    v___x_2818_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2818_, 0, v___x_2816_);
                    leanh::lean_ctor_set(v___x_2818_, 1, v___x_2817_);
                    v___x_2819_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2819_, 0, v___x_2818_);
                    leanh::lean_ctor_set(v___x_2819_, 1, v___x_2815_);
                    v___x_2820_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5_once), _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5);
                    v___x_2821_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2821_, 0, v___x_2819_);
                    leanh::lean_ctor_set(v___x_2821_, 1, v___x_2820_);
                    v___x_2822_ = l_Lean_Meta_Sym_reportIssue(
                        v___x_2821_,
                        v_a_2773_,
                        v_a_2774_,
                        v_a_2775_,
                        v_a_2776_,
                        v_a_2777_,
                        v_a_2778_,
                    );
                    if leanh::lean_obj_tag(v___x_2822_) == 0 {
                        v_isSharedCheck_2830_ =
                            (!leanh::lean_is_exclusive(v___x_2822_)) as u8;
                        if v_isSharedCheck_2830_ == 0 {
                            v_unused_2831_ = leanh::lean_ctor_get(v___x_2822_, 0);
                            leanh::lean_dec(v_unused_2831_);
                            v___x_2824_ = v___x_2822_;
                            v_isShared_2825_ = v_isSharedCheck_2830_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_2822_);
                            v___x_2824_ = leanh::lean_box(0);
                            v_isShared_2825_ = v_isSharedCheck_2830_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_2832_ = leanh::lean_ctor_get(v___x_2822_, 0);
                        v_isSharedCheck_2839_ =
                            (!leanh::lean_is_exclusive(v___x_2822_)) as u8;
                        if v_isSharedCheck_2839_ == 0 {
                            v___x_2834_ = v___x_2822_;
                            v_isShared_2835_ = v_isSharedCheck_2839_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2832_);
                            leanh::lean_dec(v___x_2822_);
                            v___x_2834_ = leanh::lean_box(0);
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
                v___x_2826_ = leanh::lean_box((v___x_2787_) as usize);
                if v_isShared_2825_ == 0 {
                    leanh::lean_ctor_set(v___x_2824_, 0, v___x_2826_);
                    v___x_2828_ = v___x_2824_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2829_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2829_, 0, v___x_2826_);
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
                    v_reuseFailAlloc_2838_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2832_);
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
                    v_reuseFailAlloc_2847_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2841_);
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
                    v_reuseFailAlloc_2855_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
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
                    v_reuseFailAlloc_2868_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2862_);
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
                    v_reuseFailAlloc_2877_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
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
    mut v_p_2879_: *mut leanh::LeanObject,
    mut v_a_2880_: *mut leanh::LeanObject,
    mut v_a_2881_: *mut leanh::LeanObject,
    mut v_a_2882_: *mut leanh::LeanObject,
    mut v_a_2883_: *mut leanh::LeanObject,
    mut v_a_2884_: *mut leanh::LeanObject,
    mut v_a_2885_: *mut leanh::LeanObject,
    mut v_a_2886_: *mut leanh::LeanObject,
    mut v_a_2887_: *mut leanh::LeanObject,
    mut v_a_2888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2889_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg(
        v_p_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_,
        v_a_2887_,
    );
    leanh::lean_dec(v_a_2887_);
    leanh::lean_dec_ref(v_a_2886_);
    leanh::lean_dec(v_a_2885_);
    leanh::lean_dec_ref(v_a_2884_);
    leanh::lean_dec(v_a_2883_);
    leanh::lean_dec_ref(v_a_2882_);
    leanh::lean_dec_ref(v_a_2881_);
    leanh::lean_dec(v_a_2880_);
    leanh::lean_dec_ref(v_p_2879_);
    return v_res_2889_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree(
    mut v_p_2890_: *mut leanh::LeanObject,
    mut v_a_2891_: *mut leanh::LeanObject,
    mut v_a_2892_: *mut leanh::LeanObject,
    mut v_a_2893_: *mut leanh::LeanObject,
    mut v_a_2894_: *mut leanh::LeanObject,
    mut v_a_2895_: *mut leanh::LeanObject,
    mut v_a_2896_: *mut leanh::LeanObject,
    mut v_a_2897_: *mut leanh::LeanObject,
    mut v_a_2898_: *mut leanh::LeanObject,
    mut v_a_2899_: *mut leanh::LeanObject,
    mut v_a_2900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2902_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg(
        v_p_2890_, v_a_2891_, v_a_2893_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_,
        v_a_2900_,
    );
    return v___x_2902_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___boxed(
    mut v_p_2903_: *mut leanh::LeanObject,
    mut v_a_2904_: *mut leanh::LeanObject,
    mut v_a_2905_: *mut leanh::LeanObject,
    mut v_a_2906_: *mut leanh::LeanObject,
    mut v_a_2907_: *mut leanh::LeanObject,
    mut v_a_2908_: *mut leanh::LeanObject,
    mut v_a_2909_: *mut leanh::LeanObject,
    mut v_a_2910_: *mut leanh::LeanObject,
    mut v_a_2911_: *mut leanh::LeanObject,
    mut v_a_2912_: *mut leanh::LeanObject,
    mut v_a_2913_: *mut leanh::LeanObject,
    mut v_a_2914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2915_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree(
        v_p_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_,
        v_a_2911_, v_a_2912_, v_a_2913_,
    );
    leanh::lean_dec(v_a_2913_);
    leanh::lean_dec_ref(v_a_2912_);
    leanh::lean_dec(v_a_2911_);
    leanh::lean_dec_ref(v_a_2910_);
    leanh::lean_dec(v_a_2909_);
    leanh::lean_dec_ref(v_a_2908_);
    leanh::lean_dec(v_a_2907_);
    leanh::lean_dec_ref(v_a_2906_);
    leanh::lean_dec(v_a_2905_);
    leanh::lean_dec(v_a_2904_);
    leanh::lean_dec_ref(v_p_2903_);
    return v_res_2915_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0(
    mut v_n_2916_: *mut leanh::LeanObject,
    mut v_s_2917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_rings_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_2931_: u8 = 0;
    let mut v___x_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2934_: u8 = 0;
    let mut v___x_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2939_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_2918_ = leanh::lean_ctor_get(v_s_2917_, 0);
                v_typeIdOf_2919_ = leanh::lean_ctor_get(v_s_2917_, 1);
                v_exprToRingId_2920_ = leanh::lean_ctor_get(v_s_2917_, 2);
                v_semirings_2921_ = leanh::lean_ctor_get(v_s_2917_, 3);
                v_stypeIdOf_2922_ = leanh::lean_ctor_get(v_s_2917_, 4);
                v_exprToSemiringId_2923_ = leanh::lean_ctor_get(v_s_2917_, 5);
                v_ncRings_2924_ = leanh::lean_ctor_get(v_s_2917_, 6);
                v_exprToNCRingId_2925_ = leanh::lean_ctor_get(v_s_2917_, 7);
                v_nctypeIdOf_2926_ = leanh::lean_ctor_get(v_s_2917_, 8);
                v_ncSemirings_2927_ = leanh::lean_ctor_get(v_s_2917_, 9);
                v_exprToNCSemiringId_2928_ = leanh::lean_ctor_get(v_s_2917_, 10);
                v_ncstypeIdOf_2929_ = leanh::lean_ctor_get(v_s_2917_, 11);
                v_steps_2930_ = leanh::lean_ctor_get(v_s_2917_, 12);
                v_reportedMaxDegreeIssue_2931_ = leanh::lean_ctor_get_uint8(
                    v_s_2917_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_isSharedCheck_2939_ = (!leanh::lean_is_exclusive(v_s_2917_)) as u8;
                if v_isSharedCheck_2939_ == 0 {
                    v___x_2933_ = v_s_2917_;
                    v_isShared_2934_ = v_isSharedCheck_2939_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_steps_2930_);
                    leanh::lean_inc(v_ncstypeIdOf_2929_);
                    leanh::lean_inc(v_exprToNCSemiringId_2928_);
                    leanh::lean_inc(v_ncSemirings_2927_);
                    leanh::lean_inc(v_nctypeIdOf_2926_);
                    leanh::lean_inc(v_exprToNCRingId_2925_);
                    leanh::lean_inc(v_ncRings_2924_);
                    leanh::lean_inc(v_exprToSemiringId_2923_);
                    leanh::lean_inc(v_stypeIdOf_2922_);
                    leanh::lean_inc(v_semirings_2921_);
                    leanh::lean_inc(v_exprToRingId_2920_);
                    leanh::lean_inc(v_typeIdOf_2919_);
                    leanh::lean_inc(v_rings_2918_);
                    leanh::lean_dec(v_s_2917_);
                    v___x_2933_ = leanh::lean_box(0);
                    v_isShared_2934_ = v_isSharedCheck_2939_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2935_ = lean_nat_add(v_steps_2930_, v_n_2916_);
                leanh::lean_dec(v_steps_2930_);
                if v_isShared_2934_ == 0 {
                    leanh::lean_ctor_set(v___x_2933_, 12, v___x_2935_);
                    v___x_2937_ = v___x_2933_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2938_ = leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_rings_2918_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2938_, 1, v_typeIdOf_2919_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2938_, 2, v_exprToRingId_2920_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2938_, 3, v_semirings_2921_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2938_, 4, v_stypeIdOf_2922_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2938_,
                        5,
                        v_exprToSemiringId_2923_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2938_, 6, v_ncRings_2924_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2938_, 7, v_exprToNCRingId_2925_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2938_, 8, v_nctypeIdOf_2926_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2938_, 9, v_ncSemirings_2927_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2938_,
                        10,
                        v_exprToNCSemiringId_2928_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2938_, 11, v_ncstypeIdOf_2929_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2938_, 12, v___x_2935_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2938_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
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
    mut v_n_2940_: *mut leanh::LeanObject,
    mut v_s_2941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2942_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0(v_n_2940_, v_s_2941_);
    leanh::lean_dec(v_n_2940_);
    return v_res_2942_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(
    mut v_n_2943_: *mut leanh::LeanObject,
    mut v_a_2944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2946_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2946_, 0, v_n_2943_);
    v___x_2947_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
    v___x_2948_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2947_, v___f_2946_, v_a_2944_);
    return v___x_2948_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___boxed(
    mut v_n_2949_: *mut leanh::LeanObject,
    mut v_a_2950_: *mut leanh::LeanObject,
    mut v_a_2951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2952_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v_n_2949_, v_a_2950_);
    leanh::lean_dec(v_a_2950_);
    return v_res_2952_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_incSteps(
    mut v_n_2953_: *mut leanh::LeanObject,
    mut v_a_2954_: *mut leanh::LeanObject,
    mut v_a_2955_: *mut leanh::LeanObject,
    mut v_a_2956_: *mut leanh::LeanObject,
    mut v_a_2957_: *mut leanh::LeanObject,
    mut v_a_2958_: *mut leanh::LeanObject,
    mut v_a_2959_: *mut leanh::LeanObject,
    mut v_a_2960_: *mut leanh::LeanObject,
    mut v_a_2961_: *mut leanh::LeanObject,
    mut v_a_2962_: *mut leanh::LeanObject,
    mut v_a_2963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2965_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v_n_2953_, v_a_2954_);
    return v___x_2965_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_incSteps___boxed(
    mut v_n_2966_: *mut leanh::LeanObject,
    mut v_a_2967_: *mut leanh::LeanObject,
    mut v_a_2968_: *mut leanh::LeanObject,
    mut v_a_2969_: *mut leanh::LeanObject,
    mut v_a_2970_: *mut leanh::LeanObject,
    mut v_a_2971_: *mut leanh::LeanObject,
    mut v_a_2972_: *mut leanh::LeanObject,
    mut v_a_2973_: *mut leanh::LeanObject,
    mut v_a_2974_: *mut leanh::LeanObject,
    mut v_a_2975_: *mut leanh::LeanObject,
    mut v_a_2976_: *mut leanh::LeanObject,
    mut v_a_2977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2978_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps(
        v_n_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_,
        v_a_2974_, v_a_2975_, v_a_2976_,
    );
    leanh::lean_dec(v_a_2976_);
    leanh::lean_dec_ref(v_a_2975_);
    leanh::lean_dec(v_a_2974_);
    leanh::lean_dec_ref(v_a_2973_);
    leanh::lean_dec(v_a_2972_);
    leanh::lean_dec_ref(v_a_2971_);
    leanh::lean_dec(v_a_2970_);
    leanh::lean_dec_ref(v_a_2969_);
    leanh::lean_dec(v_a_2968_);
    leanh::lean_dec(v_a_2967_);
    return v_res_2978_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg(
    mut v_ringId_2979_: *mut leanh::LeanObject,
    mut v_x_2980_: *mut leanh::LeanObject,
    mut v_a_2981_: *mut leanh::LeanObject,
    mut v_a_2982_: *mut leanh::LeanObject,
    mut v_a_2983_: *mut leanh::LeanObject,
    mut v_a_2984_: *mut leanh::LeanObject,
    mut v_a_2985_: *mut leanh::LeanObject,
    mut v_a_2986_: *mut leanh::LeanObject,
    mut v_a_2987_: *mut leanh::LeanObject,
    mut v_a_2988_: *mut leanh::LeanObject,
    mut v_a_2989_: *mut leanh::LeanObject,
    mut v_a_2990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2992_: u8 = 0;
    let mut v___x_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2992_ = 0;
    v___x_2993_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2993_, 0, v_ringId_2979_);
    leanh::lean_ctor_set_uint8(
        v___x_2993_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2992_,
    );
    leanh::lean_inc(v_a_2990_);
    leanh::lean_inc_ref(v_a_2989_);
    leanh::lean_inc(v_a_2988_);
    leanh::lean_inc_ref(v_a_2987_);
    leanh::lean_inc(v_a_2986_);
    leanh::lean_inc_ref(v_a_2985_);
    leanh::lean_inc(v_a_2984_);
    leanh::lean_inc_ref(v_a_2983_);
    leanh::lean_inc(v_a_2982_);
    leanh::lean_inc(v_a_2981_);
    v___x_2994_ = leanh::lean_apply_12(
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
        leanh::lean_box(0),
    );
    return v___x_2994_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg___boxed(
    mut v_ringId_2995_: *mut leanh::LeanObject,
    mut v_x_2996_: *mut leanh::LeanObject,
    mut v_a_2997_: *mut leanh::LeanObject,
    mut v_a_2998_: *mut leanh::LeanObject,
    mut v_a_2999_: *mut leanh::LeanObject,
    mut v_a_3000_: *mut leanh::LeanObject,
    mut v_a_3001_: *mut leanh::LeanObject,
    mut v_a_3002_: *mut leanh::LeanObject,
    mut v_a_3003_: *mut leanh::LeanObject,
    mut v_a_3004_: *mut leanh::LeanObject,
    mut v_a_3005_: *mut leanh::LeanObject,
    mut v_a_3006_: *mut leanh::LeanObject,
    mut v_a_3007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_3006_);
    leanh::lean_dec_ref(v_a_3005_);
    leanh::lean_dec(v_a_3004_);
    leanh::lean_dec_ref(v_a_3003_);
    leanh::lean_dec(v_a_3002_);
    leanh::lean_dec_ref(v_a_3001_);
    leanh::lean_dec(v_a_3000_);
    leanh::lean_dec_ref(v_a_2999_);
    leanh::lean_dec(v_a_2998_);
    leanh::lean_dec(v_a_2997_);
    return v_res_3008_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_RingM_run(
    mut v_00_u03b1_3009_: *mut leanh::LeanObject,
    mut v_ringId_3010_: *mut leanh::LeanObject,
    mut v_x_3011_: *mut leanh::LeanObject,
    mut v_a_3012_: *mut leanh::LeanObject,
    mut v_a_3013_: *mut leanh::LeanObject,
    mut v_a_3014_: *mut leanh::LeanObject,
    mut v_a_3015_: *mut leanh::LeanObject,
    mut v_a_3016_: *mut leanh::LeanObject,
    mut v_a_3017_: *mut leanh::LeanObject,
    mut v_a_3018_: *mut leanh::LeanObject,
    mut v_a_3019_: *mut leanh::LeanObject,
    mut v_a_3020_: *mut leanh::LeanObject,
    mut v_a_3021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3023_: u8 = 0;
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3023_ = 0;
    v___x_3024_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3024_, 0, v_ringId_3010_);
    leanh::lean_ctor_set_uint8(
        v___x_3024_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3023_,
    );
    leanh::lean_inc(v_a_3021_);
    leanh::lean_inc_ref(v_a_3020_);
    leanh::lean_inc(v_a_3019_);
    leanh::lean_inc_ref(v_a_3018_);
    leanh::lean_inc(v_a_3017_);
    leanh::lean_inc_ref(v_a_3016_);
    leanh::lean_inc(v_a_3015_);
    leanh::lean_inc_ref(v_a_3014_);
    leanh::lean_inc(v_a_3013_);
    leanh::lean_inc(v_a_3012_);
    v___x_3025_ = leanh::lean_apply_12(
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
        leanh::lean_box(0),
    );
    return v___x_3025_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_RingM_run___boxed(
    mut v_00_u03b1_3026_: *mut leanh::LeanObject,
    mut v_ringId_3027_: *mut leanh::LeanObject,
    mut v_x_3028_: *mut leanh::LeanObject,
    mut v_a_3029_: *mut leanh::LeanObject,
    mut v_a_3030_: *mut leanh::LeanObject,
    mut v_a_3031_: *mut leanh::LeanObject,
    mut v_a_3032_: *mut leanh::LeanObject,
    mut v_a_3033_: *mut leanh::LeanObject,
    mut v_a_3034_: *mut leanh::LeanObject,
    mut v_a_3035_: *mut leanh::LeanObject,
    mut v_a_3036_: *mut leanh::LeanObject,
    mut v_a_3037_: *mut leanh::LeanObject,
    mut v_a_3038_: *mut leanh::LeanObject,
    mut v_a_3039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_3038_);
    leanh::lean_dec_ref(v_a_3037_);
    leanh::lean_dec(v_a_3036_);
    leanh::lean_dec_ref(v_a_3035_);
    leanh::lean_dec(v_a_3034_);
    leanh::lean_dec_ref(v_a_3033_);
    leanh::lean_dec(v_a_3032_);
    leanh::lean_dec_ref(v_a_3031_);
    leanh::lean_dec(v_a_3030_);
    leanh::lean_dec(v_a_3029_);
    return v_res_3040_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg(
    mut v_a_3041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ringId_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ringId_3043_ = leanh::lean_ctor_get(v_a_3041_, 0);
    leanh::lean_inc(v_ringId_3043_);
    v___x_3044_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3044_, 0, v_ringId_3043_);
    return v___x_3044_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg___boxed(
    mut v_a_3045_: *mut leanh::LeanObject,
    mut v_a_3046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3047_ = l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg(v_a_3045_);
    leanh::lean_dec_ref(v_a_3045_);
    return v_res_3047_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getRingId(
    mut v_a_3048_: *mut leanh::LeanObject,
    mut v_a_3049_: *mut leanh::LeanObject,
    mut v_a_3050_: *mut leanh::LeanObject,
    mut v_a_3051_: *mut leanh::LeanObject,
    mut v_a_3052_: *mut leanh::LeanObject,
    mut v_a_3053_: *mut leanh::LeanObject,
    mut v_a_3054_: *mut leanh::LeanObject,
    mut v_a_3055_: *mut leanh::LeanObject,
    mut v_a_3056_: *mut leanh::LeanObject,
    mut v_a_3057_: *mut leanh::LeanObject,
    mut v_a_3058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ringId_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ringId_3060_ = leanh::lean_ctor_get(v_a_3048_, 0);
    leanh::lean_inc(v_ringId_3060_);
    v___x_3061_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3061_, 0, v_ringId_3060_);
    return v___x_3061_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getRingId___boxed(
    mut v_a_3062_: *mut leanh::LeanObject,
    mut v_a_3063_: *mut leanh::LeanObject,
    mut v_a_3064_: *mut leanh::LeanObject,
    mut v_a_3065_: *mut leanh::LeanObject,
    mut v_a_3066_: *mut leanh::LeanObject,
    mut v_a_3067_: *mut leanh::LeanObject,
    mut v_a_3068_: *mut leanh::LeanObject,
    mut v_a_3069_: *mut leanh::LeanObject,
    mut v_a_3070_: *mut leanh::LeanObject,
    mut v_a_3071_: *mut leanh::LeanObject,
    mut v_a_3072_: *mut leanh::LeanObject,
    mut v_a_3073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3074_ = l_Lean_Meta_Grind_Arith_CommRing_getRingId(
        v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_,
        v_a_3070_, v_a_3071_, v_a_3072_,
    );
    leanh::lean_dec(v_a_3072_);
    leanh::lean_dec_ref(v_a_3071_);
    leanh::lean_dec(v_a_3070_);
    leanh::lean_dec_ref(v_a_3069_);
    leanh::lean_dec(v_a_3068_);
    leanh::lean_dec_ref(v_a_3067_);
    leanh::lean_dec(v_a_3066_);
    leanh::lean_dec_ref(v_a_3065_);
    leanh::lean_dec(v_a_3064_);
    leanh::lean_dec(v_a_3063_);
    leanh::lean_dec_ref(v_a_3062_);
    return v_res_3074_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0(
    mut v_e_3075_: *mut leanh::LeanObject,
    mut v___y_3076_: *mut leanh::LeanObject,
    mut v___y_3077_: *mut leanh::LeanObject,
    mut v___y_3078_: *mut leanh::LeanObject,
    mut v___y_3079_: *mut leanh::LeanObject,
    mut v___y_3080_: *mut leanh::LeanObject,
    mut v___y_3081_: *mut leanh::LeanObject,
    mut v___y_3082_: *mut leanh::LeanObject,
    mut v___y_3083_: *mut leanh::LeanObject,
    mut v___y_3084_: *mut leanh::LeanObject,
    mut v___y_3085_: *mut leanh::LeanObject,
    mut v___y_3086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3088_ = l_Lean_Meta_Sym_canon(
        v_e_3075_,
        v___y_3081_,
        v___y_3082_,
        v___y_3083_,
        v___y_3084_,
        v___y_3085_,
        v___y_3086_,
    );
    if leanh::lean_obj_tag(v___x_3088_) == 0 {
        let mut v_a_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_3089_ = leanh::lean_ctor_get(v___x_3088_, 0);
        leanh::lean_inc(v_a_3089_);
        leanh::lean_dec_ref_known(v___x_3088_, 1);
        v___x_3090_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_3089_, v___y_3082_);
        return v___x_3090_;
    } else {
        return v___x_3088_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0___boxed(
    mut v_e_3091_: *mut leanh::LeanObject,
    mut v___y_3092_: *mut leanh::LeanObject,
    mut v___y_3093_: *mut leanh::LeanObject,
    mut v___y_3094_: *mut leanh::LeanObject,
    mut v___y_3095_: *mut leanh::LeanObject,
    mut v___y_3096_: *mut leanh::LeanObject,
    mut v___y_3097_: *mut leanh::LeanObject,
    mut v___y_3098_: *mut leanh::LeanObject,
    mut v___y_3099_: *mut leanh::LeanObject,
    mut v___y_3100_: *mut leanh::LeanObject,
    mut v___y_3101_: *mut leanh::LeanObject,
    mut v___y_3102_: *mut leanh::LeanObject,
    mut v___y_3103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_3102_);
    leanh::lean_dec_ref(v___y_3101_);
    leanh::lean_dec(v___y_3100_);
    leanh::lean_dec_ref(v___y_3099_);
    leanh::lean_dec(v___y_3098_);
    leanh::lean_dec_ref(v___y_3097_);
    leanh::lean_dec(v___y_3096_);
    leanh::lean_dec_ref(v___y_3095_);
    leanh::lean_dec(v___y_3094_);
    leanh::lean_dec(v___y_3093_);
    leanh::lean_dec_ref(v___y_3092_);
    return v_res_3104_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1(
    mut v_e_3105_: *mut leanh::LeanObject,
    mut v___y_3106_: *mut leanh::LeanObject,
    mut v___y_3107_: *mut leanh::LeanObject,
    mut v___y_3108_: *mut leanh::LeanObject,
    mut v___y_3109_: *mut leanh::LeanObject,
    mut v___y_3110_: *mut leanh::LeanObject,
    mut v___y_3111_: *mut leanh::LeanObject,
    mut v___y_3112_: *mut leanh::LeanObject,
    mut v___y_3113_: *mut leanh::LeanObject,
    mut v___y_3114_: *mut leanh::LeanObject,
    mut v___y_3115_: *mut leanh::LeanObject,
    mut v___y_3116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_e_3119_: *mut leanh::LeanObject,
    mut v___y_3120_: *mut leanh::LeanObject,
    mut v___y_3121_: *mut leanh::LeanObject,
    mut v___y_3122_: *mut leanh::LeanObject,
    mut v___y_3123_: *mut leanh::LeanObject,
    mut v___y_3124_: *mut leanh::LeanObject,
    mut v___y_3125_: *mut leanh::LeanObject,
    mut v___y_3126_: *mut leanh::LeanObject,
    mut v___y_3127_: *mut leanh::LeanObject,
    mut v___y_3128_: *mut leanh::LeanObject,
    mut v___y_3129_: *mut leanh::LeanObject,
    mut v___y_3130_: *mut leanh::LeanObject,
    mut v___y_3131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_3130_);
    leanh::lean_dec_ref(v___y_3129_);
    leanh::lean_dec(v___y_3128_);
    leanh::lean_dec_ref(v___y_3127_);
    leanh::lean_dec(v___y_3126_);
    leanh::lean_dec_ref(v___y_3125_);
    leanh::lean_dec(v___y_3124_);
    leanh::lean_dec_ref(v___y_3123_);
    leanh::lean_dec(v___y_3122_);
    leanh::lean_dec(v___y_3121_);
    leanh::lean_dec_ref(v___y_3120_);
    return v_res_3132_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(
    mut v_msgData_3139_: *mut leanh::LeanObject,
    mut v___y_3140_: *mut leanh::LeanObject,
    mut v___y_3141_: *mut leanh::LeanObject,
    mut v___y_3142_: *mut leanh::LeanObject,
    mut v___y_3143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3145_ = lean_st_ref_get(v___y_3143_);
    v_env_3146_ = leanh::lean_ctor_get(v___x_3145_, 0);
    leanh::lean_inc_ref(v_env_3146_);
    leanh::lean_dec(v___x_3145_);
    v___x_3147_ = lean_st_ref_get(v___y_3141_);
    v_mctx_3148_ = leanh::lean_ctor_get(v___x_3147_, 0);
    leanh::lean_inc_ref(v_mctx_3148_);
    leanh::lean_dec(v___x_3147_);
    v_lctx_3149_ = leanh::lean_ctor_get(v___y_3140_, 2);
    v_options_3150_ = leanh::lean_ctor_get(v___y_3142_, 2);
    leanh::lean_inc_ref(v_options_3150_);
    leanh::lean_inc_ref(v_lctx_3149_);
    v___x_3151_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3151_, 0, v_env_3146_);
    leanh::lean_ctor_set(v___x_3151_, 1, v_mctx_3148_);
    leanh::lean_ctor_set(v___x_3151_, 2, v_lctx_3149_);
    leanh::lean_ctor_set(v___x_3151_, 3, v_options_3150_);
    v___x_3152_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3152_, 0, v___x_3151_);
    leanh::lean_ctor_set(v___x_3152_, 1, v_msgData_3139_);
    v___x_3153_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3153_, 0, v___x_3152_);
    return v___x_3153_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0___boxed(
    mut v_msgData_3154_: *mut leanh::LeanObject,
    mut v___y_3155_: *mut leanh::LeanObject,
    mut v___y_3156_: *mut leanh::LeanObject,
    mut v___y_3157_: *mut leanh::LeanObject,
    mut v___y_3158_: *mut leanh::LeanObject,
    mut v___y_3159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3160_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(v_msgData_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
    leanh::lean_dec(v___y_3158_);
    leanh::lean_dec_ref(v___y_3157_);
    leanh::lean_dec(v___y_3156_);
    leanh::lean_dec_ref(v___y_3155_);
    return v_res_3160_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(
    mut v_msg_3161_: *mut leanh::LeanObject,
    mut v___y_3162_: *mut leanh::LeanObject,
    mut v___y_3163_: *mut leanh::LeanObject,
    mut v___y_3164_: *mut leanh::LeanObject,
    mut v___y_3165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3172_: u8 = 0;
    let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3177_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3167_ = leanh::lean_ctor_get(v___y_3164_, 5);
                v___x_3168_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(v_msg_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
                v_a_3169_ = leanh::lean_ctor_get(v___x_3168_, 0);
                v_isSharedCheck_3177_ = (!leanh::lean_is_exclusive(v___x_3168_)) as u8;
                if v_isSharedCheck_3177_ == 0 {
                    v___x_3171_ = v___x_3168_;
                    v_isShared_3172_ = v_isSharedCheck_3177_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3169_);
                    leanh::lean_dec(v___x_3168_);
                    v___x_3171_ = leanh::lean_box(0);
                    v_isShared_3172_ = v_isSharedCheck_3177_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_3167_);
                v___x_3173_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3173_, 0, v_ref_3167_);
                leanh::lean_ctor_set(v___x_3173_, 1, v_a_3169_);
                if v_isShared_3172_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3171_, 1);
                    leanh::lean_ctor_set(v___x_3171_, 0, v___x_3173_);
                    v___x_3175_ = v___x_3171_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3176_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3176_, 0, v___x_3173_);
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
    mut v_msg_3178_: *mut leanh::LeanObject,
    mut v___y_3179_: *mut leanh::LeanObject,
    mut v___y_3180_: *mut leanh::LeanObject,
    mut v___y_3181_: *mut leanh::LeanObject,
    mut v___y_3182_: *mut leanh::LeanObject,
    mut v___y_3183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3184_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v_msg_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
    leanh::lean_dec(v___y_3182_);
    leanh::lean_dec_ref(v___y_3181_);
    leanh::lean_dec(v___y_3180_);
    leanh::lean_dec_ref(v___y_3179_);
    return v_res_3184_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3186_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__0;
    v___x_3187_ = l_Lean_stringToMessageData(v___x_3186_);
    return v___x_3187_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
    mut v_a_3188_: *mut leanh::LeanObject,
    mut v_a_3189_: *mut leanh::LeanObject,
    mut v_a_3190_: *mut leanh::LeanObject,
    mut v_a_3191_: *mut leanh::LeanObject,
    mut v_a_3192_: *mut leanh::LeanObject,
    mut v_a_3193_: *mut leanh::LeanObject,
    mut v_a_3194_: *mut leanh::LeanObject,
    mut v_a_3195_: *mut leanh::LeanObject,
    mut v_a_3196_: *mut leanh::LeanObject,
    mut v_a_3197_: *mut leanh::LeanObject,
    mut v_a_3198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3204_: u8 = 0;
    let mut v_ringId_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rings_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: u8 = 0;
    let mut v___x_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3215_: u8 = 0;
    let mut v_a_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3219_: u8 = 0;
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3223_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3200_ =
                    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_3189_, v_a_3197_);
                if leanh::lean_obj_tag(v___x_3200_) == 0 {
                    v_a_3201_ = leanh::lean_ctor_get(v___x_3200_, 0);
                    v_isSharedCheck_3215_ = (!leanh::lean_is_exclusive(v___x_3200_)) as u8;
                    if v_isSharedCheck_3215_ == 0 {
                        v___x_3203_ = v___x_3200_;
                        v_isShared_3204_ = v_isSharedCheck_3215_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3201_);
                        leanh::lean_dec(v___x_3200_);
                        v___x_3203_ = leanh::lean_box(0);
                        v_isShared_3204_ = v_isSharedCheck_3215_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3216_ = leanh::lean_ctor_get(v___x_3200_, 0);
                    v_isSharedCheck_3223_ = (!leanh::lean_is_exclusive(v___x_3200_)) as u8;
                    if v_isSharedCheck_3223_ == 0 {
                        v___x_3218_ = v___x_3200_;
                        v_isShared_3219_ = v_isSharedCheck_3223_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3216_);
                        leanh::lean_dec(v___x_3200_);
                        v___x_3218_ = leanh::lean_box(0);
                        v_isShared_3219_ = v_isSharedCheck_3223_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_ringId_3205_ = leanh::lean_ctor_get(v_a_3188_, 0);
                v_rings_3206_ = leanh::lean_ctor_get(v_a_3201_, 0);
                leanh::lean_inc_ref(v_rings_3206_);
                leanh::lean_dec(v_a_3201_);
                v___x_3207_ = lean_array_get_size(v_rings_3206_);
                v___x_3208_ = lean_nat_dec_lt(v_ringId_3205_, v___x_3207_);
                if v___x_3208_ == 0 {
                    leanh::lean_dec_ref(v_rings_3206_);
                    leanh::lean_del_object(v___x_3203_);
                    v___x_3209_ = leanh::lean_obj_once(
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
                    leanh::lean_dec_ref(v_rings_3206_);
                    if v_isShared_3204_ == 0 {
                        leanh::lean_ctor_set(v___x_3203_, 0, v___x_3211_);
                        v___x_3213_ = v___x_3203_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3214_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3211_);
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
                    v_reuseFailAlloc_3222_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
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
    mut v_a_3224_: *mut leanh::LeanObject,
    mut v_a_3225_: *mut leanh::LeanObject,
    mut v_a_3226_: *mut leanh::LeanObject,
    mut v_a_3227_: *mut leanh::LeanObject,
    mut v_a_3228_: *mut leanh::LeanObject,
    mut v_a_3229_: *mut leanh::LeanObject,
    mut v_a_3230_: *mut leanh::LeanObject,
    mut v_a_3231_: *mut leanh::LeanObject,
    mut v_a_3232_: *mut leanh::LeanObject,
    mut v_a_3233_: *mut leanh::LeanObject,
    mut v_a_3234_: *mut leanh::LeanObject,
    mut v_a_3235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3236_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
        v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_,
        v_a_3232_, v_a_3233_, v_a_3234_,
    );
    leanh::lean_dec(v_a_3234_);
    leanh::lean_dec_ref(v_a_3233_);
    leanh::lean_dec(v_a_3232_);
    leanh::lean_dec_ref(v_a_3231_);
    leanh::lean_dec(v_a_3230_);
    leanh::lean_dec_ref(v_a_3229_);
    leanh::lean_dec(v_a_3228_);
    leanh::lean_dec_ref(v_a_3227_);
    leanh::lean_dec(v_a_3226_);
    leanh::lean_dec(v_a_3225_);
    leanh::lean_dec_ref(v_a_3224_);
    return v_res_3236_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0(
    mut v_00_u03b1_3237_: *mut leanh::LeanObject,
    mut v_msg_3238_: *mut leanh::LeanObject,
    mut v___y_3239_: *mut leanh::LeanObject,
    mut v___y_3240_: *mut leanh::LeanObject,
    mut v___y_3241_: *mut leanh::LeanObject,
    mut v___y_3242_: *mut leanh::LeanObject,
    mut v___y_3243_: *mut leanh::LeanObject,
    mut v___y_3244_: *mut leanh::LeanObject,
    mut v___y_3245_: *mut leanh::LeanObject,
    mut v___y_3246_: *mut leanh::LeanObject,
    mut v___y_3247_: *mut leanh::LeanObject,
    mut v___y_3248_: *mut leanh::LeanObject,
    mut v___y_3249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3251_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v_msg_3238_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
    return v___x_3251_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___boxed(
    mut v_00_u03b1_3252_: *mut leanh::LeanObject,
    mut v_msg_3253_: *mut leanh::LeanObject,
    mut v___y_3254_: *mut leanh::LeanObject,
    mut v___y_3255_: *mut leanh::LeanObject,
    mut v___y_3256_: *mut leanh::LeanObject,
    mut v___y_3257_: *mut leanh::LeanObject,
    mut v___y_3258_: *mut leanh::LeanObject,
    mut v___y_3259_: *mut leanh::LeanObject,
    mut v___y_3260_: *mut leanh::LeanObject,
    mut v___y_3261_: *mut leanh::LeanObject,
    mut v___y_3262_: *mut leanh::LeanObject,
    mut v___y_3263_: *mut leanh::LeanObject,
    mut v___y_3264_: *mut leanh::LeanObject,
    mut v___y_3265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_3264_);
    leanh::lean_dec_ref(v___y_3263_);
    leanh::lean_dec(v___y_3262_);
    leanh::lean_dec_ref(v___y_3261_);
    leanh::lean_dec(v___y_3260_);
    leanh::lean_dec_ref(v___y_3259_);
    leanh::lean_dec(v___y_3258_);
    leanh::lean_dec_ref(v___y_3257_);
    leanh::lean_dec(v___y_3256_);
    leanh::lean_dec(v___y_3255_);
    leanh::lean_dec_ref(v___y_3254_);
    return v_res_3266_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0(
    mut v_ringId_3267_: *mut leanh::LeanObject,
    mut v_f_3268_: *mut leanh::LeanObject,
    mut v_s_3269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_rings_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_3283_: u8 = 0;
    let mut v___x_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: u8 = 0;
    let mut v___x_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3288_: u8 = 0;
    let mut v_v_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3297_: u8 = 0;
    let mut v_unused_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_3270_ = leanh::lean_ctor_get(v_s_3269_, 0);
                v_typeIdOf_3271_ = leanh::lean_ctor_get(v_s_3269_, 1);
                v_exprToRingId_3272_ = leanh::lean_ctor_get(v_s_3269_, 2);
                v_semirings_3273_ = leanh::lean_ctor_get(v_s_3269_, 3);
                v_stypeIdOf_3274_ = leanh::lean_ctor_get(v_s_3269_, 4);
                v_exprToSemiringId_3275_ = leanh::lean_ctor_get(v_s_3269_, 5);
                v_ncRings_3276_ = leanh::lean_ctor_get(v_s_3269_, 6);
                v_exprToNCRingId_3277_ = leanh::lean_ctor_get(v_s_3269_, 7);
                v_nctypeIdOf_3278_ = leanh::lean_ctor_get(v_s_3269_, 8);
                v_ncSemirings_3279_ = leanh::lean_ctor_get(v_s_3269_, 9);
                v_exprToNCSemiringId_3280_ = leanh::lean_ctor_get(v_s_3269_, 10);
                v_ncstypeIdOf_3281_ = leanh::lean_ctor_get(v_s_3269_, 11);
                v_steps_3282_ = leanh::lean_ctor_get(v_s_3269_, 12);
                v_reportedMaxDegreeIssue_3283_ = leanh::lean_ctor_get_uint8(
                    v_s_3269_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v___x_3284_ = lean_array_get_size(v_rings_3270_);
                v___x_3285_ = lean_nat_dec_lt(v_ringId_3267_, v___x_3284_);
                if v___x_3285_ == 0 {
                    leanh::lean_dec_ref(v_f_3268_);
                    return v_s_3269_;
                } else {
                    leanh::lean_inc(v_steps_3282_);
                    leanh::lean_inc_ref(v_ncstypeIdOf_3281_);
                    leanh::lean_inc_ref(v_exprToNCSemiringId_3280_);
                    leanh::lean_inc_ref(v_ncSemirings_3279_);
                    leanh::lean_inc_ref(v_nctypeIdOf_3278_);
                    leanh::lean_inc_ref(v_exprToNCRingId_3277_);
                    leanh::lean_inc_ref(v_ncRings_3276_);
                    leanh::lean_inc_ref(v_exprToSemiringId_3275_);
                    leanh::lean_inc_ref(v_stypeIdOf_3274_);
                    leanh::lean_inc_ref(v_semirings_3273_);
                    leanh::lean_inc_ref(v_exprToRingId_3272_);
                    leanh::lean_inc_ref(v_typeIdOf_3271_);
                    leanh::lean_inc_ref(v_rings_3270_);
                    v_isSharedCheck_3297_ = (!leanh::lean_is_exclusive(v_s_3269_)) as u8;
                    if v_isSharedCheck_3297_ == 0 {
                        v_unused_3298_ = leanh::lean_ctor_get(v_s_3269_, 12);
                        leanh::lean_dec(v_unused_3298_);
                        v_unused_3299_ = leanh::lean_ctor_get(v_s_3269_, 11);
                        leanh::lean_dec(v_unused_3299_);
                        v_unused_3300_ = leanh::lean_ctor_get(v_s_3269_, 10);
                        leanh::lean_dec(v_unused_3300_);
                        v_unused_3301_ = leanh::lean_ctor_get(v_s_3269_, 9);
                        leanh::lean_dec(v_unused_3301_);
                        v_unused_3302_ = leanh::lean_ctor_get(v_s_3269_, 8);
                        leanh::lean_dec(v_unused_3302_);
                        v_unused_3303_ = leanh::lean_ctor_get(v_s_3269_, 7);
                        leanh::lean_dec(v_unused_3303_);
                        v_unused_3304_ = leanh::lean_ctor_get(v_s_3269_, 6);
                        leanh::lean_dec(v_unused_3304_);
                        v_unused_3305_ = leanh::lean_ctor_get(v_s_3269_, 5);
                        leanh::lean_dec(v_unused_3305_);
                        v_unused_3306_ = leanh::lean_ctor_get(v_s_3269_, 4);
                        leanh::lean_dec(v_unused_3306_);
                        v_unused_3307_ = leanh::lean_ctor_get(v_s_3269_, 3);
                        leanh::lean_dec(v_unused_3307_);
                        v_unused_3308_ = leanh::lean_ctor_get(v_s_3269_, 2);
                        leanh::lean_dec(v_unused_3308_);
                        v_unused_3309_ = leanh::lean_ctor_get(v_s_3269_, 1);
                        leanh::lean_dec(v_unused_3309_);
                        v_unused_3310_ = leanh::lean_ctor_get(v_s_3269_, 0);
                        leanh::lean_dec(v_unused_3310_);
                        v___x_3287_ = v_s_3269_;
                        v_isShared_3288_ = v_isSharedCheck_3297_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_s_3269_);
                        v___x_3287_ = leanh::lean_box(0);
                        v_isShared_3288_ = v_isSharedCheck_3297_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3289_ = lean_array_fget(v_rings_3270_, v_ringId_3267_);
                v___x_3290_ = leanh::lean_box(0);
                v_xs_x27_3291_ = lean_array_fset(v_rings_3270_, v_ringId_3267_, v___x_3290_);
                v___x_3292_ = leanh::lean_apply_1(v_f_3268_, v_v_3289_);
                v___x_3293_ = lean_array_fset(v_xs_x27_3291_, v_ringId_3267_, v___x_3292_);
                if v_isShared_3288_ == 0 {
                    leanh::lean_ctor_set(v___x_3287_, 0, v___x_3293_);
                    v___x_3295_ = v___x_3287_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3296_ = leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___x_3293_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 1, v_typeIdOf_3271_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 2, v_exprToRingId_3272_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 3, v_semirings_3273_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 4, v_stypeIdOf_3274_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3296_,
                        5,
                        v_exprToSemiringId_3275_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 6, v_ncRings_3276_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 7, v_exprToNCRingId_3277_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 8, v_nctypeIdOf_3278_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 9, v_ncSemirings_3279_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3296_,
                        10,
                        v_exprToNCSemiringId_3280_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 11, v_ncstypeIdOf_3281_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 12, v_steps_3282_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3296_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
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
    mut v_ringId_3311_: *mut leanh::LeanObject,
    mut v_f_3312_: *mut leanh::LeanObject,
    mut v_s_3313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3314_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0(
        v_ringId_3311_,
        v_f_3312_,
        v_s_3313_,
    );
    leanh::lean_dec(v_ringId_3311_);
    return v_res_3314_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(
    mut v_f_3315_: *mut leanh::LeanObject,
    mut v_a_3316_: *mut leanh::LeanObject,
    mut v_a_3317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ringId_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ringId_3319_ = leanh::lean_ctor_get(v_a_3316_, 0);
    leanh::lean_inc(v_ringId_3319_);
    v___f_3320_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3320_, 0, v_ringId_3319_);
    leanh::lean_closure_set(v___f_3320_, 1, v_f_3315_);
    v___x_3321_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
    v___x_3322_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3321_, v___f_3320_, v_a_3317_);
    return v___x_3322_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___boxed(
    mut v_f_3323_: *mut leanh::LeanObject,
    mut v_a_3324_: *mut leanh::LeanObject,
    mut v_a_3325_: *mut leanh::LeanObject,
    mut v_a_3326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3327_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(
        v_f_3323_, v_a_3324_, v_a_3325_,
    );
    leanh::lean_dec(v_a_3325_);
    leanh::lean_dec_ref(v_a_3324_);
    return v_res_3327_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing(
    mut v_f_3328_: *mut leanh::LeanObject,
    mut v_a_3329_: *mut leanh::LeanObject,
    mut v_a_3330_: *mut leanh::LeanObject,
    mut v_a_3331_: *mut leanh::LeanObject,
    mut v_a_3332_: *mut leanh::LeanObject,
    mut v_a_3333_: *mut leanh::LeanObject,
    mut v_a_3334_: *mut leanh::LeanObject,
    mut v_a_3335_: *mut leanh::LeanObject,
    mut v_a_3336_: *mut leanh::LeanObject,
    mut v_a_3337_: *mut leanh::LeanObject,
    mut v_a_3338_: *mut leanh::LeanObject,
    mut v_a_3339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3341_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(
        v_f_3328_, v_a_3329_, v_a_3330_,
    );
    return v___x_3341_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___boxed(
    mut v_f_3342_: *mut leanh::LeanObject,
    mut v_a_3343_: *mut leanh::LeanObject,
    mut v_a_3344_: *mut leanh::LeanObject,
    mut v_a_3345_: *mut leanh::LeanObject,
    mut v_a_3346_: *mut leanh::LeanObject,
    mut v_a_3347_: *mut leanh::LeanObject,
    mut v_a_3348_: *mut leanh::LeanObject,
    mut v_a_3349_: *mut leanh::LeanObject,
    mut v_a_3350_: *mut leanh::LeanObject,
    mut v_a_3351_: *mut leanh::LeanObject,
    mut v_a_3352_: *mut leanh::LeanObject,
    mut v_a_3353_: *mut leanh::LeanObject,
    mut v_a_3354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3355_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing(
        v_f_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_,
        v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_,
    );
    leanh::lean_dec(v_a_3353_);
    leanh::lean_dec_ref(v_a_3352_);
    leanh::lean_dec(v_a_3351_);
    leanh::lean_dec_ref(v_a_3350_);
    leanh::lean_dec(v_a_3349_);
    leanh::lean_dec_ref(v_a_3348_);
    leanh::lean_dec(v_a_3347_);
    leanh::lean_dec_ref(v_a_3346_);
    leanh::lean_dec(v_a_3345_);
    leanh::lean_dec(v_a_3344_);
    leanh::lean_dec_ref(v_a_3343_);
    return v_res_3355_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3357_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__0;
    v___x_3358_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___boxed as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_3359_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3359_, 0, v___x_3358_);
    leanh::lean_ctor_set(v___x_3359_, 1, v___x_3357_);
    return v___x_3359_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM()
-> *mut leanh::LeanObject {
    let mut v___x_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3360_ = leanh::lean_obj_once(
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
    mut v_x_3361_: *mut leanh::LeanObject,
    mut v_a_3362_: *mut leanh::LeanObject,
    mut v_a_3363_: *mut leanh::LeanObject,
    mut v_a_3364_: *mut leanh::LeanObject,
    mut v_a_3365_: *mut leanh::LeanObject,
    mut v_a_3366_: *mut leanh::LeanObject,
    mut v_a_3367_: *mut leanh::LeanObject,
    mut v_a_3368_: *mut leanh::LeanObject,
    mut v_a_3369_: *mut leanh::LeanObject,
    mut v_a_3370_: *mut leanh::LeanObject,
    mut v_a_3371_: *mut leanh::LeanObject,
    mut v_a_3372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ringId_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: u8 = 0;
    let mut v___x_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ringId_3374_ = leanh::lean_ctor_get(v_a_3362_, 0);
    v___x_3375_ = 1;
    leanh::lean_inc(v_ringId_3374_);
    v___x_3376_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3376_, 0, v_ringId_3374_);
    leanh::lean_ctor_set_uint8(
        v___x_3376_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3375_,
    );
    leanh::lean_inc(v_a_3372_);
    leanh::lean_inc_ref(v_a_3371_);
    leanh::lean_inc(v_a_3370_);
    leanh::lean_inc_ref(v_a_3369_);
    leanh::lean_inc(v_a_3368_);
    leanh::lean_inc_ref(v_a_3367_);
    leanh::lean_inc(v_a_3366_);
    leanh::lean_inc_ref(v_a_3365_);
    leanh::lean_inc(v_a_3364_);
    leanh::lean_inc(v_a_3363_);
    v___x_3377_ = leanh::lean_apply_12(
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
        leanh::lean_box(0),
    );
    return v___x_3377_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg___boxed(
    mut v_x_3378_: *mut leanh::LeanObject,
    mut v_a_3379_: *mut leanh::LeanObject,
    mut v_a_3380_: *mut leanh::LeanObject,
    mut v_a_3381_: *mut leanh::LeanObject,
    mut v_a_3382_: *mut leanh::LeanObject,
    mut v_a_3383_: *mut leanh::LeanObject,
    mut v_a_3384_: *mut leanh::LeanObject,
    mut v_a_3385_: *mut leanh::LeanObject,
    mut v_a_3386_: *mut leanh::LeanObject,
    mut v_a_3387_: *mut leanh::LeanObject,
    mut v_a_3388_: *mut leanh::LeanObject,
    mut v_a_3389_: *mut leanh::LeanObject,
    mut v_a_3390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3391_ = l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg(
        v_x_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_,
        v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_,
    );
    leanh::lean_dec(v_a_3389_);
    leanh::lean_dec_ref(v_a_3388_);
    leanh::lean_dec(v_a_3387_);
    leanh::lean_dec_ref(v_a_3386_);
    leanh::lean_dec(v_a_3385_);
    leanh::lean_dec_ref(v_a_3384_);
    leanh::lean_dec(v_a_3383_);
    leanh::lean_dec_ref(v_a_3382_);
    leanh::lean_dec(v_a_3381_);
    leanh::lean_dec(v_a_3380_);
    leanh::lean_dec_ref(v_a_3379_);
    return v_res_3391_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd(
    mut v_00_u03b1_3392_: *mut leanh::LeanObject,
    mut v_x_3393_: *mut leanh::LeanObject,
    mut v_a_3394_: *mut leanh::LeanObject,
    mut v_a_3395_: *mut leanh::LeanObject,
    mut v_a_3396_: *mut leanh::LeanObject,
    mut v_a_3397_: *mut leanh::LeanObject,
    mut v_a_3398_: *mut leanh::LeanObject,
    mut v_a_3399_: *mut leanh::LeanObject,
    mut v_a_3400_: *mut leanh::LeanObject,
    mut v_a_3401_: *mut leanh::LeanObject,
    mut v_a_3402_: *mut leanh::LeanObject,
    mut v_a_3403_: *mut leanh::LeanObject,
    mut v_a_3404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ringId_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: u8 = 0;
    let mut v___x_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ringId_3406_ = leanh::lean_ctor_get(v_a_3394_, 0);
    v___x_3407_ = 1;
    leanh::lean_inc(v_ringId_3406_);
    v___x_3408_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_3408_, 0, v_ringId_3406_);
    leanh::lean_ctor_set_uint8(
        v___x_3408_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3407_,
    );
    leanh::lean_inc(v_a_3404_);
    leanh::lean_inc_ref(v_a_3403_);
    leanh::lean_inc(v_a_3402_);
    leanh::lean_inc_ref(v_a_3401_);
    leanh::lean_inc(v_a_3400_);
    leanh::lean_inc_ref(v_a_3399_);
    leanh::lean_inc(v_a_3398_);
    leanh::lean_inc_ref(v_a_3397_);
    leanh::lean_inc(v_a_3396_);
    leanh::lean_inc(v_a_3395_);
    v___x_3409_ = leanh::lean_apply_12(
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
        leanh::lean_box(0),
    );
    return v___x_3409_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___boxed(
    mut v_00_u03b1_3410_: *mut leanh::LeanObject,
    mut v_x_3411_: *mut leanh::LeanObject,
    mut v_a_3412_: *mut leanh::LeanObject,
    mut v_a_3413_: *mut leanh::LeanObject,
    mut v_a_3414_: *mut leanh::LeanObject,
    mut v_a_3415_: *mut leanh::LeanObject,
    mut v_a_3416_: *mut leanh::LeanObject,
    mut v_a_3417_: *mut leanh::LeanObject,
    mut v_a_3418_: *mut leanh::LeanObject,
    mut v_a_3419_: *mut leanh::LeanObject,
    mut v_a_3420_: *mut leanh::LeanObject,
    mut v_a_3421_: *mut leanh::LeanObject,
    mut v_a_3422_: *mut leanh::LeanObject,
    mut v_a_3423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_3422_);
    leanh::lean_dec_ref(v_a_3421_);
    leanh::lean_dec(v_a_3420_);
    leanh::lean_dec_ref(v_a_3419_);
    leanh::lean_dec(v_a_3418_);
    leanh::lean_dec_ref(v_a_3417_);
    leanh::lean_dec(v_a_3416_);
    leanh::lean_dec_ref(v_a_3415_);
    leanh::lean_dec(v_a_3414_);
    leanh::lean_dec(v_a_3413_);
    leanh::lean_dec_ref(v_a_3412_);
    return v_res_3424_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(
    mut v_a_3425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_checkCoeffDvd_3427_: u8 = 0;
    let mut v___x_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_checkCoeffDvd_3427_ = leanh::lean_ctor_get_uint8(
        v_a_3425_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
    );
    v___x_3428_ = leanh::lean_box((v_checkCoeffDvd_3427_) as usize);
    v___x_3429_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3429_, 0, v___x_3428_);
    return v___x_3429_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg___boxed(
    mut v_a_3430_: *mut leanh::LeanObject,
    mut v_a_3431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3432_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(v_a_3430_);
    leanh::lean_dec_ref(v_a_3430_);
    return v_res_3432_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd(
    mut v_a_3433_: *mut leanh::LeanObject,
    mut v_a_3434_: *mut leanh::LeanObject,
    mut v_a_3435_: *mut leanh::LeanObject,
    mut v_a_3436_: *mut leanh::LeanObject,
    mut v_a_3437_: *mut leanh::LeanObject,
    mut v_a_3438_: *mut leanh::LeanObject,
    mut v_a_3439_: *mut leanh::LeanObject,
    mut v_a_3440_: *mut leanh::LeanObject,
    mut v_a_3441_: *mut leanh::LeanObject,
    mut v_a_3442_: *mut leanh::LeanObject,
    mut v_a_3443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3445_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(v_a_3433_);
    return v___x_3445_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___boxed(
    mut v_a_3446_: *mut leanh::LeanObject,
    mut v_a_3447_: *mut leanh::LeanObject,
    mut v_a_3448_: *mut leanh::LeanObject,
    mut v_a_3449_: *mut leanh::LeanObject,
    mut v_a_3450_: *mut leanh::LeanObject,
    mut v_a_3451_: *mut leanh::LeanObject,
    mut v_a_3452_: *mut leanh::LeanObject,
    mut v_a_3453_: *mut leanh::LeanObject,
    mut v_a_3454_: *mut leanh::LeanObject,
    mut v_a_3455_: *mut leanh::LeanObject,
    mut v_a_3456_: *mut leanh::LeanObject,
    mut v_a_3457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3458_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd(
        v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_,
        v_a_3454_, v_a_3455_, v_a_3456_,
    );
    leanh::lean_dec(v_a_3456_);
    leanh::lean_dec_ref(v_a_3455_);
    leanh::lean_dec(v_a_3454_);
    leanh::lean_dec_ref(v_a_3453_);
    leanh::lean_dec(v_a_3452_);
    leanh::lean_dec_ref(v_a_3451_);
    leanh::lean_dec(v_a_3450_);
    leanh::lean_dec_ref(v_a_3449_);
    leanh::lean_dec(v_a_3448_);
    leanh::lean_dec(v_a_3447_);
    leanh::lean_dec_ref(v_a_3446_);
    return v_res_3458_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_keys_3459_: *mut leanh::LeanObject,
    mut v_vals_3460_: *mut leanh::LeanObject,
    mut v_i_3461_: *mut leanh::LeanObject,
    mut v_k_3462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: u8 = 0;
    let mut v___x_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: u8 = 0;
    let mut v___x_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3463_ = lean_array_get_size(v_keys_3459_);
                v___x_3464_ = lean_nat_dec_lt(v_i_3461_, v___x_3463_);
                if v___x_3464_ == 0 {
                    leanh::lean_dec(v_i_3461_);
                    v___x_3465_ = leanh::lean_box(0);
                    return v___x_3465_;
                } else {
                    v_k_x27_3466_ = lean_array_fget_borrowed(v_keys_3459_, v_i_3461_);
                    v___x_3467_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_3462_,
                            v_k_x27_3466_,
                        );
                    if v___x_3467_ == 0 {
                        v___x_3468_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3469_ = lean_nat_add(v_i_3461_, v___x_3468_);
                        leanh::lean_dec(v_i_3461_);
                        v_i_3461_ = v___x_3469_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3471_ = lean_array_fget_borrowed(v_vals_3460_, v_i_3461_);
                        leanh::lean_dec(v_i_3461_);
                        leanh::lean_inc(v___x_3471_);
                        v___x_3472_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3472_, 0, v___x_3471_);
                        return v___x_3472_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_3473_: *mut leanh::LeanObject,
    mut v_vals_3474_: *mut leanh::LeanObject,
    mut v_i_3475_: *mut leanh::LeanObject,
    mut v_k_3476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3477_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_3473_, v_vals_3474_, v_i_3475_, v_k_3476_);
    leanh::lean_dec_ref(v_k_3476_);
    leanh::lean_dec_ref(v_vals_3474_);
    leanh::lean_dec_ref(v_keys_3473_);
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
    v___x_3482_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__0);
    v___x_3483_ = lean_usize_sub(v___x_3482_, v___x_3481_);
    return v___x_3483_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(
    mut v_x_3484_: *mut leanh::LeanObject,
    mut v_x_3485_: usize,
    mut v_x_3486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: usize = 0;
    let mut v___x_3490_: usize = 0;
    let mut v___x_3491_: usize = 0;
    let mut v_j_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: u8 = 0;
    let mut v___x_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: usize = 0;
    let mut v___x_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3484_) == 0 {
                    v_es_3487_ = leanh::lean_ctor_get(v_x_3484_, 0);
                    v___x_3488_ = leanh::lean_box(2);
                    v___x_3489_ = 5usize;
                    v___x_3490_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_3491_ = lean_usize_land(v_x_3485_, v___x_3490_);
                    v_j_3492_ = lean_usize_to_nat(v___x_3491_);
                    v___x_3493_ = lean_array_get_borrowed(v___x_3488_, v_es_3487_, v_j_3492_);
                    leanh::lean_dec(v_j_3492_);
                    match leanh::lean_obj_tag(v___x_3493_) {
                        0 => {
                            v_key_3494_ = leanh::lean_ctor_get(v___x_3493_, 0);
                            v_val_3495_ = leanh::lean_ctor_get(v___x_3493_, 1);
                            v___x_3496_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_3486_, v_key_3494_);
                            if v___x_3496_ == 0 {
                                v___x_3497_ = leanh::lean_box(0);
                                return v___x_3497_;
                            } else {
                                leanh::lean_inc(v_val_3495_);
                                v___x_3498_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3498_, 0, v_val_3495_);
                                return v___x_3498_;
                            }
                        }
                        1 => {
                            v_node_3499_ = leanh::lean_ctor_get(v___x_3493_, 0);
                            v___x_3500_ = lean_usize_shift_right(v_x_3485_, v___x_3489_);
                            v_x_3484_ = v_node_3499_;
                            v_x_3485_ = v___x_3500_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3502_ = leanh::lean_box(0);
                            return v___x_3502_;
                        }
                    }
                } else {
                    v_ks_3503_ = leanh::lean_ctor_get(v_x_3484_, 0);
                    v_vs_3504_ = leanh::lean_ctor_get(v_x_3484_, 1);
                    v___x_3505_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3506_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_3503_, v_vs_3504_, v___x_3505_, v_x_3486_);
                    return v___x_3506_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_3507_: *mut leanh::LeanObject,
    mut v_x_3508_: *mut leanh::LeanObject,
    mut v_x_3509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_867__boxed_3510_: usize = 0;
    let mut v_res_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_867__boxed_3510_ = leanh::lean_unbox_usize(v_x_3508_);
    leanh::lean_dec(v_x_3508_);
    v_res_3511_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_3507_, v_x_867__boxed_3510_, v_x_3509_);
    leanh::lean_dec_ref(v_x_3509_);
    leanh::lean_dec_ref(v_x_3507_);
    return v_res_3511_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(
    mut v_x_3512_: *mut leanh::LeanObject,
    mut v_x_3513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3514_: u64 = 0;
    let mut v___x_3515_: usize = 0;
    let mut v___x_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3514_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_3513_);
    v___x_3515_ = lean_uint64_to_usize(v___x_3514_);
    v___x_3516_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_3512_, v___x_3515_, v_x_3513_);
    return v___x_3516_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg___boxed(
    mut v_x_3517_: *mut leanh::LeanObject,
    mut v_x_3518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3519_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_3517_, v_x_3518_);
    leanh::lean_dec_ref(v_x_3518_);
    leanh::lean_dec_ref(v_x_3517_);
    return v_res_3519_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(
    mut v_e_3520_: *mut leanh::LeanObject,
    mut v_a_3521_: *mut leanh::LeanObject,
    mut v_a_3522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3528_: u8 = 0;
    let mut v_exprToRingId_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3534_: u8 = 0;
    let mut v_a_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3538_: u8 = 0;
    let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3542_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3524_ =
                    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_3521_, v_a_3522_);
                if leanh::lean_obj_tag(v___x_3524_) == 0 {
                    v_a_3525_ = leanh::lean_ctor_get(v___x_3524_, 0);
                    v_isSharedCheck_3534_ = (!leanh::lean_is_exclusive(v___x_3524_)) as u8;
                    if v_isSharedCheck_3534_ == 0 {
                        v___x_3527_ = v___x_3524_;
                        v_isShared_3528_ = v_isSharedCheck_3534_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3525_);
                        leanh::lean_dec(v___x_3524_);
                        v___x_3527_ = leanh::lean_box(0);
                        v_isShared_3528_ = v_isSharedCheck_3534_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3535_ = leanh::lean_ctor_get(v___x_3524_, 0);
                    v_isSharedCheck_3542_ = (!leanh::lean_is_exclusive(v___x_3524_)) as u8;
                    if v_isSharedCheck_3542_ == 0 {
                        v___x_3537_ = v___x_3524_;
                        v_isShared_3538_ = v_isSharedCheck_3542_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3535_);
                        leanh::lean_dec(v___x_3524_);
                        v___x_3537_ = leanh::lean_box(0);
                        v_isShared_3538_ = v_isSharedCheck_3542_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_exprToRingId_3529_ = leanh::lean_ctor_get(v_a_3525_, 2);
                leanh::lean_inc_ref(v_exprToRingId_3529_);
                leanh::lean_dec(v_a_3525_);
                v___x_3530_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_exprToRingId_3529_, v_e_3520_);
                leanh::lean_dec_ref(v_exprToRingId_3529_);
                if v_isShared_3528_ == 0 {
                    leanh::lean_ctor_set(v___x_3527_, 0, v___x_3530_);
                    v___x_3532_ = v___x_3527_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3533_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3530_);
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
                    v_reuseFailAlloc_3541_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_a_3535_);
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
    mut v_e_3543_: *mut leanh::LeanObject,
    mut v_a_3544_: *mut leanh::LeanObject,
    mut v_a_3545_: *mut leanh::LeanObject,
    mut v_a_3546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3547_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(
        v_e_3543_, v_a_3544_, v_a_3545_,
    );
    leanh::lean_dec_ref(v_a_3545_);
    leanh::lean_dec(v_a_3544_);
    leanh::lean_dec_ref(v_e_3543_);
    return v_res_3547_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(
    mut v_e_3548_: *mut leanh::LeanObject,
    mut v_a_3549_: *mut leanh::LeanObject,
    mut v_a_3550_: *mut leanh::LeanObject,
    mut v_a_3551_: *mut leanh::LeanObject,
    mut v_a_3552_: *mut leanh::LeanObject,
    mut v_a_3553_: *mut leanh::LeanObject,
    mut v_a_3554_: *mut leanh::LeanObject,
    mut v_a_3555_: *mut leanh::LeanObject,
    mut v_a_3556_: *mut leanh::LeanObject,
    mut v_a_3557_: *mut leanh::LeanObject,
    mut v_a_3558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3560_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(
        v_e_3548_, v_a_3549_, v_a_3557_,
    );
    return v___x_3560_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___boxed(
    mut v_e_3561_: *mut leanh::LeanObject,
    mut v_a_3562_: *mut leanh::LeanObject,
    mut v_a_3563_: *mut leanh::LeanObject,
    mut v_a_3564_: *mut leanh::LeanObject,
    mut v_a_3565_: *mut leanh::LeanObject,
    mut v_a_3566_: *mut leanh::LeanObject,
    mut v_a_3567_: *mut leanh::LeanObject,
    mut v_a_3568_: *mut leanh::LeanObject,
    mut v_a_3569_: *mut leanh::LeanObject,
    mut v_a_3570_: *mut leanh::LeanObject,
    mut v_a_3571_: *mut leanh::LeanObject,
    mut v_a_3572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3573_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(
        v_e_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_,
        v_a_3569_, v_a_3570_, v_a_3571_,
    );
    leanh::lean_dec(v_a_3571_);
    leanh::lean_dec_ref(v_a_3570_);
    leanh::lean_dec(v_a_3569_);
    leanh::lean_dec_ref(v_a_3568_);
    leanh::lean_dec(v_a_3567_);
    leanh::lean_dec_ref(v_a_3566_);
    leanh::lean_dec(v_a_3565_);
    leanh::lean_dec_ref(v_a_3564_);
    leanh::lean_dec(v_a_3563_);
    leanh::lean_dec(v_a_3562_);
    leanh::lean_dec_ref(v_e_3561_);
    return v_res_3573_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(
    mut v_00_u03b2_3574_: *mut leanh::LeanObject,
    mut v_x_3575_: *mut leanh::LeanObject,
    mut v_x_3576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3577_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_3575_, v_x_3576_);
    return v___x_3577_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___boxed(
    mut v_00_u03b2_3578_: *mut leanh::LeanObject,
    mut v_x_3579_: *mut leanh::LeanObject,
    mut v_x_3580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3581_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(v_00_u03b2_3578_, v_x_3579_, v_x_3580_);
    leanh::lean_dec_ref(v_x_3580_);
    leanh::lean_dec_ref(v_x_3579_);
    return v_res_3581_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(
    mut v_00_u03b2_3582_: *mut leanh::LeanObject,
    mut v_x_3583_: *mut leanh::LeanObject,
    mut v_x_3584_: usize,
    mut v_x_3585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3586_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_3583_, v_x_3584_, v_x_3585_);
    return v___x_3586_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_3587_: *mut leanh::LeanObject,
    mut v_x_3588_: *mut leanh::LeanObject,
    mut v_x_3589_: *mut leanh::LeanObject,
    mut v_x_3590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_984__boxed_3591_: usize = 0;
    let mut v_res_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_984__boxed_3591_ = leanh::lean_unbox_usize(v_x_3589_);
    leanh::lean_dec(v_x_3589_);
    v_res_3592_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(v_00_u03b2_3587_, v_x_3588_, v_x_984__boxed_3591_, v_x_3590_);
    leanh::lean_dec_ref(v_x_3590_);
    leanh::lean_dec_ref(v_x_3588_);
    return v_res_3592_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3593_: *mut leanh::LeanObject,
    mut v_keys_3594_: *mut leanh::LeanObject,
    mut v_vals_3595_: *mut leanh::LeanObject,
    mut v_heq_3596_: *mut leanh::LeanObject,
    mut v_i_3597_: *mut leanh::LeanObject,
    mut v_k_3598_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3599_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_3594_, v_vals_3595_, v_i_3597_, v_k_3598_);
    return v___x_3599_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_3600_: *mut leanh::LeanObject,
    mut v_keys_3601_: *mut leanh::LeanObject,
    mut v_vals_3602_: *mut leanh::LeanObject,
    mut v_heq_3603_: *mut leanh::LeanObject,
    mut v_i_3604_: *mut leanh::LeanObject,
    mut v_k_3605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3606_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_3600_, v_keys_3601_, v_vals_3602_, v_heq_3603_, v_i_3604_, v_k_3605_);
    leanh::lean_dec_ref(v_k_3605_);
    leanh::lean_dec_ref(v_vals_3602_);
    leanh::lean_dec_ref(v_keys_3601_);
    return v_res_3606_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0(
    mut v_toPure_3607_: *mut leanh::LeanObject,
    mut v_____do__lift_3608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3616_: u8 = 0;
    let mut v_snd_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: u8 = 0;
    let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3624_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_charInst_x3f_3612_ = leanh::lean_ctor_get(v_____do__lift_3608_, 5);
                leanh::lean_inc(v_charInst_x3f_3612_);
                leanh::lean_dec_ref(v_____do__lift_3608_);
                if leanh::lean_obj_tag(v_charInst_x3f_3612_) == 1 {
                    v_val_3613_ = leanh::lean_ctor_get(v_charInst_x3f_3612_, 0);
                    v_isSharedCheck_3624_ =
                        (!leanh::lean_is_exclusive(v_charInst_x3f_3612_)) as u8;
                    if v_isSharedCheck_3624_ == 0 {
                        v___x_3615_ = v_charInst_x3f_3612_;
                        v_isShared_3616_ = v_isSharedCheck_3624_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3613_);
                        leanh::lean_dec(v_charInst_x3f_3612_);
                        v___x_3615_ = leanh::lean_box(0);
                        v_isShared_3616_ = v_isSharedCheck_3624_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_charInst_x3f_3612_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3610_ = leanh::lean_box(0);
                v___x_3611_ = leanh::lean_apply_2(
                    v_toPure_3607_,
                    leanh::lean_box(0),
                    v___x_3610_,
                );
                return v___x_3611_;
            }
            2 => {
                v_snd_3617_ = leanh::lean_ctor_get(v_val_3613_, 1);
                leanh::lean_inc(v_snd_3617_);
                leanh::lean_dec(v_val_3613_);
                v___x_3618_ = leanh::lean_unsigned_to_nat(0);
                v___x_3619_ = lean_nat_dec_eq(v_snd_3617_, v___x_3618_);
                if v___x_3619_ == 0 {
                    if v_isShared_3616_ == 0 {
                        leanh::lean_ctor_set(v___x_3615_, 0, v_snd_3617_);
                        v___x_3621_ = v___x_3615_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3623_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_snd_3617_);
                        v___x_3621_ = v_reuseFailAlloc_3623_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_snd_3617_);
                    leanh::lean_del_object(v___x_3615_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3622_ = leanh::lean_apply_2(
                    v_toPure_3607_,
                    leanh::lean_box(0),
                    v___x_3621_,
                );
                return v___x_3622_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(
    mut v_inst_3625_: *mut leanh::LeanObject,
    mut v_inst_3626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3627_ = leanh::lean_ctor_get(v_inst_3625_, 0);
    leanh::lean_inc_ref(v_toApplicative_3627_);
    v_toBind_3628_ = leanh::lean_ctor_get(v_inst_3625_, 1);
    leanh::lean_inc(v_toBind_3628_);
    leanh::lean_dec_ref(v_inst_3625_);
    v_getRing_3629_ = leanh::lean_ctor_get(v_inst_3626_, 0);
    leanh::lean_inc(v_getRing_3629_);
    leanh::lean_dec_ref(v_inst_3626_);
    v_toPure_3630_ = leanh::lean_ctor_get(v_toApplicative_3627_, 1);
    leanh::lean_inc(v_toPure_3630_);
    leanh::lean_dec_ref(v_toApplicative_3627_);
    v___f_3631_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3631_, 0, v_toPure_3630_);
    v___x_3632_ = leanh::lean_apply_4(
        v_toBind_3628_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getRing_3629_,
        v___f_3631_,
    );
    return v___x_3632_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f(
    mut v_m_3633_: *mut leanh::LeanObject,
    mut v_inst_3634_: *mut leanh::LeanObject,
    mut v_inst_3635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3636_ =
        l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(v_inst_3634_, v_inst_3635_);
    return v___x_3636_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0(
    mut v_toPure_3637_: *mut leanh::LeanObject,
    mut v_____do__lift_3638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: u8 = 0;
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_charInst_x3f_3642_ = leanh::lean_ctor_get(v_____do__lift_3638_, 5);
                leanh::lean_inc(v_charInst_x3f_3642_);
                leanh::lean_dec_ref(v_____do__lift_3638_);
                if leanh::lean_obj_tag(v_charInst_x3f_3642_) == 1 {
                    v_val_3643_ = leanh::lean_ctor_get(v_charInst_x3f_3642_, 0);
                    v_snd_3644_ = leanh::lean_ctor_get(v_val_3643_, 1);
                    v___x_3645_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3646_ = lean_nat_dec_eq(v_snd_3644_, v___x_3645_);
                    if v___x_3646_ == 0 {
                        v___x_3647_ = leanh::lean_apply_2(
                            v_toPure_3637_,
                            leanh::lean_box(0),
                            v_charInst_x3f_3642_,
                        );
                        return v___x_3647_;
                    } else {
                        leanh::lean_dec_ref_known(v_charInst_x3f_3642_, 1);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_charInst_x3f_3642_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3640_ = leanh::lean_box(0);
                v___x_3641_ = leanh::lean_apply_2(
                    v_toPure_3637_,
                    leanh::lean_box(0),
                    v___x_3640_,
                );
                return v___x_3641_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(
    mut v_inst_3648_: *mut leanh::LeanObject,
    mut v_inst_3649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3650_ = leanh::lean_ctor_get(v_inst_3648_, 0);
    leanh::lean_inc_ref(v_toApplicative_3650_);
    v_toBind_3651_ = leanh::lean_ctor_get(v_inst_3648_, 1);
    leanh::lean_inc(v_toBind_3651_);
    leanh::lean_dec_ref(v_inst_3648_);
    v_getRing_3652_ = leanh::lean_ctor_get(v_inst_3649_, 0);
    leanh::lean_inc(v_getRing_3652_);
    leanh::lean_dec_ref(v_inst_3649_);
    v_toPure_3653_ = leanh::lean_ctor_get(v_toApplicative_3650_, 1);
    leanh::lean_inc(v_toPure_3653_);
    leanh::lean_dec_ref(v_toApplicative_3650_);
    v___f_3654_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3654_, 0, v_toPure_3653_);
    v___x_3655_ = leanh::lean_apply_4(
        v_toBind_3651_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getRing_3652_,
        v___f_3654_,
    );
    return v___x_3655_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f(
    mut v_m_3656_: *mut leanh::LeanObject,
    mut v_inst_3657_: *mut leanh::LeanObject,
    mut v_inst_3658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3659_ =
        l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(v_inst_3657_, v_inst_3658_);
    return v___x_3659_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(
    mut v_a_3660_: *mut leanh::LeanObject,
    mut v_a_3661_: *mut leanh::LeanObject,
    mut v_a_3662_: *mut leanh::LeanObject,
    mut v_a_3663_: *mut leanh::LeanObject,
    mut v_a_3664_: *mut leanh::LeanObject,
    mut v_a_3665_: *mut leanh::LeanObject,
    mut v_a_3666_: *mut leanh::LeanObject,
    mut v_a_3667_: *mut leanh::LeanObject,
    mut v_a_3668_: *mut leanh::LeanObject,
    mut v_a_3669_: *mut leanh::LeanObject,
    mut v_a_3670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3676_: u8 = 0;
    let mut v_noZeroDivInst_x3f_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3681_: u8 = 0;
    let mut v_a_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3685_: u8 = 0;
    let mut v___x_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3689_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3672_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                    v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_,
                    v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_,
                );
                if leanh::lean_obj_tag(v___x_3672_) == 0 {
                    v_a_3673_ = leanh::lean_ctor_get(v___x_3672_, 0);
                    v_isSharedCheck_3681_ = (!leanh::lean_is_exclusive(v___x_3672_)) as u8;
                    if v_isSharedCheck_3681_ == 0 {
                        v___x_3675_ = v___x_3672_;
                        v_isShared_3676_ = v_isSharedCheck_3681_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3673_);
                        leanh::lean_dec(v___x_3672_);
                        v___x_3675_ = leanh::lean_box(0);
                        v_isShared_3676_ = v_isSharedCheck_3681_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3682_ = leanh::lean_ctor_get(v___x_3672_, 0);
                    v_isSharedCheck_3689_ = (!leanh::lean_is_exclusive(v___x_3672_)) as u8;
                    if v_isSharedCheck_3689_ == 0 {
                        v___x_3684_ = v___x_3672_;
                        v_isShared_3685_ = v_isSharedCheck_3689_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3682_);
                        leanh::lean_dec(v___x_3672_);
                        v___x_3684_ = leanh::lean_box(0);
                        v_isShared_3685_ = v_isSharedCheck_3689_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_noZeroDivInst_x3f_3677_ = leanh::lean_ctor_get(v_a_3673_, 5);
                leanh::lean_inc(v_noZeroDivInst_x3f_3677_);
                leanh::lean_dec(v_a_3673_);
                if v_isShared_3676_ == 0 {
                    leanh::lean_ctor_set(v___x_3675_, 0, v_noZeroDivInst_x3f_3677_);
                    v___x_3679_ = v___x_3675_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3680_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(
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
                    v_reuseFailAlloc_3688_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_a_3682_);
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
    mut v_a_3690_: *mut leanh::LeanObject,
    mut v_a_3691_: *mut leanh::LeanObject,
    mut v_a_3692_: *mut leanh::LeanObject,
    mut v_a_3693_: *mut leanh::LeanObject,
    mut v_a_3694_: *mut leanh::LeanObject,
    mut v_a_3695_: *mut leanh::LeanObject,
    mut v_a_3696_: *mut leanh::LeanObject,
    mut v_a_3697_: *mut leanh::LeanObject,
    mut v_a_3698_: *mut leanh::LeanObject,
    mut v_a_3699_: *mut leanh::LeanObject,
    mut v_a_3700_: *mut leanh::LeanObject,
    mut v_a_3701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3702_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(
        v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_,
        v_a_3698_, v_a_3699_, v_a_3700_,
    );
    leanh::lean_dec(v_a_3700_);
    leanh::lean_dec_ref(v_a_3699_);
    leanh::lean_dec(v_a_3698_);
    leanh::lean_dec_ref(v_a_3697_);
    leanh::lean_dec(v_a_3696_);
    leanh::lean_dec_ref(v_a_3695_);
    leanh::lean_dec(v_a_3694_);
    leanh::lean_dec_ref(v_a_3693_);
    leanh::lean_dec(v_a_3692_);
    leanh::lean_dec(v_a_3691_);
    leanh::lean_dec_ref(v_a_3690_);
    return v_res_3702_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(
    mut v_a_3703_: *mut leanh::LeanObject,
    mut v_a_3704_: *mut leanh::LeanObject,
    mut v_a_3705_: *mut leanh::LeanObject,
    mut v_a_3706_: *mut leanh::LeanObject,
    mut v_a_3707_: *mut leanh::LeanObject,
    mut v_a_3708_: *mut leanh::LeanObject,
    mut v_a_3709_: *mut leanh::LeanObject,
    mut v_a_3710_: *mut leanh::LeanObject,
    mut v_a_3711_: *mut leanh::LeanObject,
    mut v_a_3712_: *mut leanh::LeanObject,
    mut v_a_3713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3719_: u8 = 0;
    let mut v_noZeroDivInst_x3f_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: u8 = 0;
    let mut v___x_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: u8 = 0;
    let mut v___x_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3731_: u8 = 0;
    let mut v_a_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3735_: u8 = 0;
    let mut v___x_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3739_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3715_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                    v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_,
                    v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_,
                );
                if leanh::lean_obj_tag(v___x_3715_) == 0 {
                    v_a_3716_ = leanh::lean_ctor_get(v___x_3715_, 0);
                    v_isSharedCheck_3731_ = (!leanh::lean_is_exclusive(v___x_3715_)) as u8;
                    if v_isSharedCheck_3731_ == 0 {
                        v___x_3718_ = v___x_3715_;
                        v_isShared_3719_ = v_isSharedCheck_3731_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3716_);
                        leanh::lean_dec(v___x_3715_);
                        v___x_3718_ = leanh::lean_box(0);
                        v_isShared_3719_ = v_isSharedCheck_3731_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3732_ = leanh::lean_ctor_get(v___x_3715_, 0);
                    v_isSharedCheck_3739_ = (!leanh::lean_is_exclusive(v___x_3715_)) as u8;
                    if v_isSharedCheck_3739_ == 0 {
                        v___x_3734_ = v___x_3715_;
                        v_isShared_3735_ = v_isSharedCheck_3739_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3732_);
                        leanh::lean_dec(v___x_3715_);
                        v___x_3734_ = leanh::lean_box(0);
                        v_isShared_3735_ = v_isSharedCheck_3739_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_noZeroDivInst_x3f_3720_ = leanh::lean_ctor_get(v_a_3716_, 5);
                leanh::lean_inc(v_noZeroDivInst_x3f_3720_);
                leanh::lean_dec(v_a_3716_);
                if leanh::lean_obj_tag(v_noZeroDivInst_x3f_3720_) == 0 {
                    v___x_3721_ = 0;
                    v___x_3722_ = leanh::lean_box((v___x_3721_) as usize);
                    if v_isShared_3719_ == 0 {
                        leanh::lean_ctor_set(v___x_3718_, 0, v___x_3722_);
                        v___x_3724_ = v___x_3718_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3725_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3722_);
                        v___x_3724_ = v_reuseFailAlloc_3725_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_noZeroDivInst_x3f_3720_, 1);
                    v___x_3726_ = 1;
                    v___x_3727_ = leanh::lean_box((v___x_3726_) as usize);
                    if v_isShared_3719_ == 0 {
                        leanh::lean_ctor_set(v___x_3718_, 0, v___x_3727_);
                        v___x_3729_ = v___x_3718_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3730_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3727_);
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
                    v_reuseFailAlloc_3738_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3732_);
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
    mut v_a_3740_: *mut leanh::LeanObject,
    mut v_a_3741_: *mut leanh::LeanObject,
    mut v_a_3742_: *mut leanh::LeanObject,
    mut v_a_3743_: *mut leanh::LeanObject,
    mut v_a_3744_: *mut leanh::LeanObject,
    mut v_a_3745_: *mut leanh::LeanObject,
    mut v_a_3746_: *mut leanh::LeanObject,
    mut v_a_3747_: *mut leanh::LeanObject,
    mut v_a_3748_: *mut leanh::LeanObject,
    mut v_a_3749_: *mut leanh::LeanObject,
    mut v_a_3750_: *mut leanh::LeanObject,
    mut v_a_3751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3752_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(
        v_a_3740_, v_a_3741_, v_a_3742_, v_a_3743_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_,
        v_a_3748_, v_a_3749_, v_a_3750_,
    );
    leanh::lean_dec(v_a_3750_);
    leanh::lean_dec_ref(v_a_3749_);
    leanh::lean_dec(v_a_3748_);
    leanh::lean_dec_ref(v_a_3747_);
    leanh::lean_dec(v_a_3746_);
    leanh::lean_dec_ref(v_a_3745_);
    leanh::lean_dec(v_a_3744_);
    leanh::lean_dec_ref(v_a_3743_);
    leanh::lean_dec(v_a_3742_);
    leanh::lean_dec(v_a_3741_);
    leanh::lean_dec_ref(v_a_3740_);
    return v_res_3752_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_hasChar(
    mut v_a_3753_: *mut leanh::LeanObject,
    mut v_a_3754_: *mut leanh::LeanObject,
    mut v_a_3755_: *mut leanh::LeanObject,
    mut v_a_3756_: *mut leanh::LeanObject,
    mut v_a_3757_: *mut leanh::LeanObject,
    mut v_a_3758_: *mut leanh::LeanObject,
    mut v_a_3759_: *mut leanh::LeanObject,
    mut v_a_3760_: *mut leanh::LeanObject,
    mut v_a_3761_: *mut leanh::LeanObject,
    mut v_a_3762_: *mut leanh::LeanObject,
    mut v_a_3763_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3769_: u8 = 0;
    let mut v_toRing_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: u8 = 0;
    let mut v___x_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: u8 = 0;
    let mut v___x_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3782_: u8 = 0;
    let mut v_a_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3786_: u8 = 0;
    let mut v___x_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3790_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3765_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                    v_a_3753_, v_a_3754_, v_a_3755_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_,
                    v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_,
                );
                if leanh::lean_obj_tag(v___x_3765_) == 0 {
                    v_a_3766_ = leanh::lean_ctor_get(v___x_3765_, 0);
                    v_isSharedCheck_3782_ = (!leanh::lean_is_exclusive(v___x_3765_)) as u8;
                    if v_isSharedCheck_3782_ == 0 {
                        v___x_3768_ = v___x_3765_;
                        v_isShared_3769_ = v_isSharedCheck_3782_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3766_);
                        leanh::lean_dec(v___x_3765_);
                        v___x_3768_ = leanh::lean_box(0);
                        v_isShared_3769_ = v_isSharedCheck_3782_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3783_ = leanh::lean_ctor_get(v___x_3765_, 0);
                    v_isSharedCheck_3790_ = (!leanh::lean_is_exclusive(v___x_3765_)) as u8;
                    if v_isSharedCheck_3790_ == 0 {
                        v___x_3785_ = v___x_3765_;
                        v_isShared_3786_ = v_isSharedCheck_3790_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3783_);
                        leanh::lean_dec(v___x_3765_);
                        v___x_3785_ = leanh::lean_box(0);
                        v_isShared_3786_ = v_isSharedCheck_3790_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_toRing_3770_ = leanh::lean_ctor_get(v_a_3766_, 0);
                leanh::lean_inc_ref(v_toRing_3770_);
                leanh::lean_dec(v_a_3766_);
                v_charInst_x3f_3771_ = leanh::lean_ctor_get(v_toRing_3770_, 5);
                leanh::lean_inc(v_charInst_x3f_3771_);
                leanh::lean_dec_ref(v_toRing_3770_);
                if leanh::lean_obj_tag(v_charInst_x3f_3771_) == 0 {
                    v___x_3772_ = 0;
                    v___x_3773_ = leanh::lean_box((v___x_3772_) as usize);
                    if v_isShared_3769_ == 0 {
                        leanh::lean_ctor_set(v___x_3768_, 0, v___x_3773_);
                        v___x_3775_ = v___x_3768_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3776_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3776_, 0, v___x_3773_);
                        v___x_3775_ = v_reuseFailAlloc_3776_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_charInst_x3f_3771_, 1);
                    v___x_3777_ = 1;
                    v___x_3778_ = leanh::lean_box((v___x_3777_) as usize);
                    if v_isShared_3769_ == 0 {
                        leanh::lean_ctor_set(v___x_3768_, 0, v___x_3778_);
                        v___x_3780_ = v___x_3768_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3781_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3778_);
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
                    v_reuseFailAlloc_3789_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3783_);
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
    mut v_a_3791_: *mut leanh::LeanObject,
    mut v_a_3792_: *mut leanh::LeanObject,
    mut v_a_3793_: *mut leanh::LeanObject,
    mut v_a_3794_: *mut leanh::LeanObject,
    mut v_a_3795_: *mut leanh::LeanObject,
    mut v_a_3796_: *mut leanh::LeanObject,
    mut v_a_3797_: *mut leanh::LeanObject,
    mut v_a_3798_: *mut leanh::LeanObject,
    mut v_a_3799_: *mut leanh::LeanObject,
    mut v_a_3800_: *mut leanh::LeanObject,
    mut v_a_3801_: *mut leanh::LeanObject,
    mut v_a_3802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3803_ = l_Lean_Meta_Grind_Arith_CommRing_hasChar(
        v_a_3791_, v_a_3792_, v_a_3793_, v_a_3794_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_,
        v_a_3799_, v_a_3800_, v_a_3801_,
    );
    leanh::lean_dec(v_a_3801_);
    leanh::lean_dec_ref(v_a_3800_);
    leanh::lean_dec(v_a_3799_);
    leanh::lean_dec_ref(v_a_3798_);
    leanh::lean_dec(v_a_3797_);
    leanh::lean_dec_ref(v_a_3796_);
    leanh::lean_dec(v_a_3795_);
    leanh::lean_dec_ref(v_a_3794_);
    leanh::lean_dec(v_a_3793_);
    leanh::lean_dec(v_a_3792_);
    leanh::lean_dec_ref(v_a_3791_);
    return v_res_3803_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3805_ = l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0;
    v___x_3806_ = l_Lean_stringToMessageData(v___x_3805_);
    return v___x_3806_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getCharInst(
    mut v_a_3807_: *mut leanh::LeanObject,
    mut v_a_3808_: *mut leanh::LeanObject,
    mut v_a_3809_: *mut leanh::LeanObject,
    mut v_a_3810_: *mut leanh::LeanObject,
    mut v_a_3811_: *mut leanh::LeanObject,
    mut v_a_3812_: *mut leanh::LeanObject,
    mut v_a_3813_: *mut leanh::LeanObject,
    mut v_a_3814_: *mut leanh::LeanObject,
    mut v_a_3815_: *mut leanh::LeanObject,
    mut v_a_3816_: *mut leanh::LeanObject,
    mut v_a_3817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3823_: u8 = 0;
    let mut v_toRing_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3832_: u8 = 0;
    let mut v_a_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3836_: u8 = 0;
    let mut v___x_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3840_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3819_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                    v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_,
                    v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_,
                );
                if leanh::lean_obj_tag(v___x_3819_) == 0 {
                    v_a_3820_ = leanh::lean_ctor_get(v___x_3819_, 0);
                    v_isSharedCheck_3832_ = (!leanh::lean_is_exclusive(v___x_3819_)) as u8;
                    if v_isSharedCheck_3832_ == 0 {
                        v___x_3822_ = v___x_3819_;
                        v_isShared_3823_ = v_isSharedCheck_3832_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3820_);
                        leanh::lean_dec(v___x_3819_);
                        v___x_3822_ = leanh::lean_box(0);
                        v_isShared_3823_ = v_isSharedCheck_3832_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3833_ = leanh::lean_ctor_get(v___x_3819_, 0);
                    v_isSharedCheck_3840_ = (!leanh::lean_is_exclusive(v___x_3819_)) as u8;
                    if v_isSharedCheck_3840_ == 0 {
                        v___x_3835_ = v___x_3819_;
                        v_isShared_3836_ = v_isSharedCheck_3840_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3833_);
                        leanh::lean_dec(v___x_3819_);
                        v___x_3835_ = leanh::lean_box(0);
                        v_isShared_3836_ = v_isSharedCheck_3840_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_toRing_3824_ = leanh::lean_ctor_get(v_a_3820_, 0);
                leanh::lean_inc_ref(v_toRing_3824_);
                leanh::lean_dec(v_a_3820_);
                v_charInst_x3f_3825_ = leanh::lean_ctor_get(v_toRing_3824_, 5);
                leanh::lean_inc(v_charInst_x3f_3825_);
                leanh::lean_dec_ref(v_toRing_3824_);
                if leanh::lean_obj_tag(v_charInst_x3f_3825_) == 1 {
                    v_val_3826_ = leanh::lean_ctor_get(v_charInst_x3f_3825_, 0);
                    leanh::lean_inc(v_val_3826_);
                    leanh::lean_dec_ref_known(v_charInst_x3f_3825_, 1);
                    if v_isShared_3823_ == 0 {
                        leanh::lean_ctor_set(v___x_3822_, 0, v_val_3826_);
                        v___x_3828_ = v___x_3822_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3829_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_val_3826_);
                        v___x_3828_ = v_reuseFailAlloc_3829_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_charInst_x3f_3825_);
                    leanh::lean_del_object(v___x_3822_);
                    v___x_3830_ = leanh::lean_obj_once(
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
                    v_reuseFailAlloc_3839_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_a_3833_);
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
    mut v_a_3841_: *mut leanh::LeanObject,
    mut v_a_3842_: *mut leanh::LeanObject,
    mut v_a_3843_: *mut leanh::LeanObject,
    mut v_a_3844_: *mut leanh::LeanObject,
    mut v_a_3845_: *mut leanh::LeanObject,
    mut v_a_3846_: *mut leanh::LeanObject,
    mut v_a_3847_: *mut leanh::LeanObject,
    mut v_a_3848_: *mut leanh::LeanObject,
    mut v_a_3849_: *mut leanh::LeanObject,
    mut v_a_3850_: *mut leanh::LeanObject,
    mut v_a_3851_: *mut leanh::LeanObject,
    mut v_a_3852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3853_ = l_Lean_Meta_Grind_Arith_CommRing_getCharInst(
        v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_,
        v_a_3849_, v_a_3850_, v_a_3851_,
    );
    leanh::lean_dec(v_a_3851_);
    leanh::lean_dec_ref(v_a_3850_);
    leanh::lean_dec(v_a_3849_);
    leanh::lean_dec_ref(v_a_3848_);
    leanh::lean_dec(v_a_3847_);
    leanh::lean_dec_ref(v_a_3846_);
    leanh::lean_dec(v_a_3845_);
    leanh::lean_dec_ref(v_a_3844_);
    leanh::lean_dec(v_a_3843_);
    leanh::lean_dec(v_a_3842_);
    leanh::lean_dec_ref(v_a_3841_);
    return v_res_3853_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_isField(
    mut v_a_3854_: *mut leanh::LeanObject,
    mut v_a_3855_: *mut leanh::LeanObject,
    mut v_a_3856_: *mut leanh::LeanObject,
    mut v_a_3857_: *mut leanh::LeanObject,
    mut v_a_3858_: *mut leanh::LeanObject,
    mut v_a_3859_: *mut leanh::LeanObject,
    mut v_a_3860_: *mut leanh::LeanObject,
    mut v_a_3861_: *mut leanh::LeanObject,
    mut v_a_3862_: *mut leanh::LeanObject,
    mut v_a_3863_: *mut leanh::LeanObject,
    mut v_a_3864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3870_: u8 = 0;
    let mut v_fieldInst_x3f_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: u8 = 0;
    let mut v___x_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: u8 = 0;
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3882_: u8 = 0;
    let mut v_a_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3886_: u8 = 0;
    let mut v___x_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3890_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3866_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                    v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_,
                    v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_,
                );
                if leanh::lean_obj_tag(v___x_3866_) == 0 {
                    v_a_3867_ = leanh::lean_ctor_get(v___x_3866_, 0);
                    v_isSharedCheck_3882_ = (!leanh::lean_is_exclusive(v___x_3866_)) as u8;
                    if v_isSharedCheck_3882_ == 0 {
                        v___x_3869_ = v___x_3866_;
                        v_isShared_3870_ = v_isSharedCheck_3882_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3867_);
                        leanh::lean_dec(v___x_3866_);
                        v___x_3869_ = leanh::lean_box(0);
                        v_isShared_3870_ = v_isSharedCheck_3882_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3883_ = leanh::lean_ctor_get(v___x_3866_, 0);
                    v_isSharedCheck_3890_ = (!leanh::lean_is_exclusive(v___x_3866_)) as u8;
                    if v_isSharedCheck_3890_ == 0 {
                        v___x_3885_ = v___x_3866_;
                        v_isShared_3886_ = v_isSharedCheck_3890_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3883_);
                        leanh::lean_dec(v___x_3866_);
                        v___x_3885_ = leanh::lean_box(0);
                        v_isShared_3886_ = v_isSharedCheck_3890_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_fieldInst_x3f_3871_ = leanh::lean_ctor_get(v_a_3867_, 6);
                leanh::lean_inc(v_fieldInst_x3f_3871_);
                leanh::lean_dec(v_a_3867_);
                if leanh::lean_obj_tag(v_fieldInst_x3f_3871_) == 0 {
                    v___x_3872_ = 0;
                    v___x_3873_ = leanh::lean_box((v___x_3872_) as usize);
                    if v_isShared_3870_ == 0 {
                        leanh::lean_ctor_set(v___x_3869_, 0, v___x_3873_);
                        v___x_3875_ = v___x_3869_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3876_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3876_, 0, v___x_3873_);
                        v___x_3875_ = v_reuseFailAlloc_3876_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_fieldInst_x3f_3871_, 1);
                    v___x_3877_ = 1;
                    v___x_3878_ = leanh::lean_box((v___x_3877_) as usize);
                    if v_isShared_3870_ == 0 {
                        leanh::lean_ctor_set(v___x_3869_, 0, v___x_3878_);
                        v___x_3880_ = v___x_3869_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3881_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3881_, 0, v___x_3878_);
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
                    v_reuseFailAlloc_3889_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_a_3883_);
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
    mut v_a_3891_: *mut leanh::LeanObject,
    mut v_a_3892_: *mut leanh::LeanObject,
    mut v_a_3893_: *mut leanh::LeanObject,
    mut v_a_3894_: *mut leanh::LeanObject,
    mut v_a_3895_: *mut leanh::LeanObject,
    mut v_a_3896_: *mut leanh::LeanObject,
    mut v_a_3897_: *mut leanh::LeanObject,
    mut v_a_3898_: *mut leanh::LeanObject,
    mut v_a_3899_: *mut leanh::LeanObject,
    mut v_a_3900_: *mut leanh::LeanObject,
    mut v_a_3901_: *mut leanh::LeanObject,
    mut v_a_3902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3903_ = l_Lean_Meta_Grind_Arith_CommRing_isField(
        v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_,
        v_a_3899_, v_a_3900_, v_a_3901_,
    );
    leanh::lean_dec(v_a_3901_);
    leanh::lean_dec_ref(v_a_3900_);
    leanh::lean_dec(v_a_3899_);
    leanh::lean_dec_ref(v_a_3898_);
    leanh::lean_dec(v_a_3897_);
    leanh::lean_dec_ref(v_a_3896_);
    leanh::lean_dec(v_a_3895_);
    leanh::lean_dec_ref(v_a_3894_);
    leanh::lean_dec(v_a_3893_);
    leanh::lean_dec(v_a_3892_);
    leanh::lean_dec_ref(v_a_3891_);
    return v_res_3903_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(
    mut v_a_3904_: *mut leanh::LeanObject,
    mut v_a_3905_: *mut leanh::LeanObject,
    mut v_a_3906_: *mut leanh::LeanObject,
    mut v_a_3907_: *mut leanh::LeanObject,
    mut v_a_3908_: *mut leanh::LeanObject,
    mut v_a_3909_: *mut leanh::LeanObject,
    mut v_a_3910_: *mut leanh::LeanObject,
    mut v_a_3911_: *mut leanh::LeanObject,
    mut v_a_3912_: *mut leanh::LeanObject,
    mut v_a_3913_: *mut leanh::LeanObject,
    mut v_a_3914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3920_: u8 = 0;
    let mut v_queue_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: u8 = 0;
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: u8 = 0;
    let mut v___x_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3932_: u8 = 0;
    let mut v_a_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3936_: u8 = 0;
    let mut v___x_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3940_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3916_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                    v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_, v_a_3910_,
                    v_a_3911_, v_a_3912_, v_a_3913_, v_a_3914_,
                );
                if leanh::lean_obj_tag(v___x_3916_) == 0 {
                    v_a_3917_ = leanh::lean_ctor_get(v___x_3916_, 0);
                    v_isSharedCheck_3932_ = (!leanh::lean_is_exclusive(v___x_3916_)) as u8;
                    if v_isSharedCheck_3932_ == 0 {
                        v___x_3919_ = v___x_3916_;
                        v_isShared_3920_ = v_isSharedCheck_3932_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3917_);
                        leanh::lean_dec(v___x_3916_);
                        v___x_3919_ = leanh::lean_box(0);
                        v_isShared_3920_ = v_isSharedCheck_3932_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3933_ = leanh::lean_ctor_get(v___x_3916_, 0);
                    v_isSharedCheck_3940_ = (!leanh::lean_is_exclusive(v___x_3916_)) as u8;
                    if v_isSharedCheck_3940_ == 0 {
                        v___x_3935_ = v___x_3916_;
                        v_isShared_3936_ = v_isSharedCheck_3940_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3933_);
                        leanh::lean_dec(v___x_3916_);
                        v___x_3935_ = leanh::lean_box(0);
                        v_isShared_3936_ = v_isSharedCheck_3940_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_queue_3921_ = leanh::lean_ctor_get(v_a_3917_, 11);
                leanh::lean_inc(v_queue_3921_);
                leanh::lean_dec(v_a_3917_);
                if leanh::lean_obj_tag(v_queue_3921_) == 0 {
                    leanh::lean_dec_ref_known(v_queue_3921_, 5);
                    v___x_3922_ = 0;
                    v___x_3923_ = leanh::lean_box((v___x_3922_) as usize);
                    if v_isShared_3920_ == 0 {
                        leanh::lean_ctor_set(v___x_3919_, 0, v___x_3923_);
                        v___x_3925_ = v___x_3919_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3926_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___x_3923_);
                        v___x_3925_ = v_reuseFailAlloc_3926_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3927_ = 1;
                    v___x_3928_ = leanh::lean_box((v___x_3927_) as usize);
                    if v_isShared_3920_ == 0 {
                        leanh::lean_ctor_set(v___x_3919_, 0, v___x_3928_);
                        v___x_3930_ = v___x_3919_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3931_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3931_, 0, v___x_3928_);
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
                    v_reuseFailAlloc_3939_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_a_3933_);
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
    mut v_a_3941_: *mut leanh::LeanObject,
    mut v_a_3942_: *mut leanh::LeanObject,
    mut v_a_3943_: *mut leanh::LeanObject,
    mut v_a_3944_: *mut leanh::LeanObject,
    mut v_a_3945_: *mut leanh::LeanObject,
    mut v_a_3946_: *mut leanh::LeanObject,
    mut v_a_3947_: *mut leanh::LeanObject,
    mut v_a_3948_: *mut leanh::LeanObject,
    mut v_a_3949_: *mut leanh::LeanObject,
    mut v_a_3950_: *mut leanh::LeanObject,
    mut v_a_3951_: *mut leanh::LeanObject,
    mut v_a_3952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3953_ = l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(
        v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_,
        v_a_3949_, v_a_3950_, v_a_3951_,
    );
    leanh::lean_dec(v_a_3951_);
    leanh::lean_dec_ref(v_a_3950_);
    leanh::lean_dec(v_a_3949_);
    leanh::lean_dec_ref(v_a_3948_);
    leanh::lean_dec(v_a_3947_);
    leanh::lean_dec_ref(v_a_3946_);
    leanh::lean_dec(v_a_3945_);
    leanh::lean_dec_ref(v_a_3944_);
    leanh::lean_dec(v_a_3943_);
    leanh::lean_dec(v_a_3942_);
    leanh::lean_dec_ref(v_a_3941_);
    return v_res_3953_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(
    mut v_k_3954_: *mut leanh::LeanObject,
    mut v_t_3955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3962_: u8 = 0;
    let mut v___x_3963_: u8 = 0;
    let mut v_impl_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: u8 = 0;
    let mut v___x_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3982_: u8 = 0;
    let mut v_size_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: u8 = 0;
    let mut v___x_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3994_: u8 = 0;
    let mut v___x_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4019_: u8 = 0;
    let mut v_unused_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4032_: u8 = 0;
    let mut v___x_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4036_: u8 = 0;
    let mut v_unused_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4043_: u8 = 0;
    let mut v_unused_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4061_: u8 = 0;
    let mut v_size_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4071_: u8 = 0;
    let mut v_unused_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4078_: u8 = 0;
    let mut v_k_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4083_: u8 = 0;
    let mut v___x_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4094_: u8 = 0;
    let mut v_unused_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4098_: u8 = 0;
    let mut v_unused_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4107_: u8 = 0;
    let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4115_: u8 = 0;
    let mut v_unused_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4124_: u8 = 0;
    let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4132_: u8 = 0;
    let mut v_unused_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: u8 = 0;
    let mut v___x_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4152_: u8 = 0;
    let mut v___x_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: u8 = 0;
    let mut v___x_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4168_: u8 = 0;
    let mut v_size_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: u8 = 0;
    let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4180_: u8 = 0;
    let mut v___x_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4205_: u8 = 0;
    let mut v_unused_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4220_: u8 = 0;
    let mut v_unused_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4228_: u8 = 0;
    let mut v_k_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4246_: u8 = 0;
    let mut v___x_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4257_: u8 = 0;
    let mut v_unused_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4279_: u8 = 0;
    let mut v_unused_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4285_: u8 = 0;
    let mut v_unused_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4293_: u8 = 0;
    let mut v___x_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: u8 = 0;
    let mut v___x_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4309_: u8 = 0;
    let mut v_size_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: u8 = 0;
    let mut v___x_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4321_: u8 = 0;
    let mut v___x_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4333_: u8 = 0;
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4337_: u8 = 0;
    let mut v_unused_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4356_: u8 = 0;
    let mut v_unused_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4372_: u8 = 0;
    let mut v_unused_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4380_: u8 = 0;
    let mut v_k_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4401_: u8 = 0;
    let mut v_unused_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4409_: u8 = 0;
    let mut v_k_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4416_: u8 = 0;
    let mut v___x_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4427_: u8 = 0;
    let mut v_unused_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4431_: u8 = 0;
    let mut v_unused_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4443_: u8 = 0;
    let mut v_unused_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: u8 = 0;
    let mut v___x_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4467_: u8 = 0;
    let mut v_size_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: u8 = 0;
    let mut v___x_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4479_: u8 = 0;
    let mut v___x_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4505_: u8 = 0;
    let mut v_unused_4506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4519_: u8 = 0;
    let mut v___x_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4523_: u8 = 0;
    let mut v_unused_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4530_: u8 = 0;
    let mut v_unused_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4548_: u8 = 0;
    let mut v_size_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4558_: u8 = 0;
    let mut v_unused_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4565_: u8 = 0;
    let mut v___x_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4573_: u8 = 0;
    let mut v_unused_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4582_: u8 = 0;
    let mut v_k_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4587_: u8 = 0;
    let mut v___x_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4598_: u8 = 0;
    let mut v_unused_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4602_: u8 = 0;
    let mut v_unused_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4613_: u8 = 0;
    let mut v_unused_4614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_3955_) == 0 {
                    v_k_3956_ = leanh::lean_ctor_get(v_t_3955_, 1);
                    v_v_3957_ = leanh::lean_ctor_get(v_t_3955_, 2);
                    v_l_3958_ = leanh::lean_ctor_get(v_t_3955_, 3);
                    v_r_3959_ = leanh::lean_ctor_get(v_t_3955_, 4);
                    v_isSharedCheck_4613_ = (!leanh::lean_is_exclusive(v_t_3955_)) as u8;
                    if v_isSharedCheck_4613_ == 0 {
                        v_unused_4614_ = leanh::lean_ctor_get(v_t_3955_, 0);
                        leanh::lean_dec(v_unused_4614_);
                        v___x_3961_ = v_t_3955_;
                        v_isShared_3962_ = v_isSharedCheck_4613_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_3959_);
                        leanh::lean_inc(v_l_3958_);
                        leanh::lean_inc(v_v_3957_);
                        leanh::lean_inc(v_k_3956_);
                        leanh::lean_dec(v_t_3955_);
                        v___x_3961_ = leanh::lean_box(0);
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
                        v___x_3965_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_impl_3964_) == 0 {
                            if leanh::lean_obj_tag(v_r_3959_) == 0 {
                                v_size_3966_ = leanh::lean_ctor_get(v_impl_3964_, 0);
                                leanh::lean_inc(v_size_3966_);
                                v_size_3967_ = leanh::lean_ctor_get(v_r_3959_, 0);
                                v_k_3968_ = leanh::lean_ctor_get(v_r_3959_, 1);
                                v_v_3969_ = leanh::lean_ctor_get(v_r_3959_, 2);
                                v_l_3970_ = leanh::lean_ctor_get(v_r_3959_, 3);
                                leanh::lean_inc(v_l_3970_);
                                v_r_3971_ = leanh::lean_ctor_get(v_r_3959_, 4);
                                v___x_3972_ = leanh::lean_unsigned_to_nat(3);
                                v___x_3973_ = lean_nat_mul(v___x_3972_, v_size_3966_);
                                v___x_3974_ = lean_nat_dec_lt(v___x_3973_, v_size_3967_);
                                leanh::lean_dec(v___x_3973_);
                                if v___x_3974_ == 0 {
                                    leanh::lean_dec(v_l_3970_);
                                    v___x_3975_ = lean_nat_add(v___x_3965_, v_size_3966_);
                                    leanh::lean_dec(v_size_3966_);
                                    v___x_3976_ = lean_nat_add(v___x_3975_, v_size_3967_);
                                    leanh::lean_dec(v___x_3975_);
                                    if v_isShared_3962_ == 0 {
                                        leanh::lean_ctor_set(v___x_3961_, 3, v_impl_3964_);
                                        leanh::lean_ctor_set(v___x_3961_, 0, v___x_3976_);
                                        v___x_3978_ = v___x_3961_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3979_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3979_,
                                            0,
                                            v___x_3976_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3979_,
                                            1,
                                            v_k_3956_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3979_,
                                            2,
                                            v_v_3957_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3979_,
                                            3,
                                            v_impl_3964_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3979_,
                                            4,
                                            v_r_3959_,
                                        );
                                        v___x_3978_ = v_reuseFailAlloc_3979_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_inc(v_r_3971_);
                                    leanh::lean_inc(v_v_3969_);
                                    leanh::lean_inc(v_k_3968_);
                                    leanh::lean_inc(v_size_3967_);
                                    v_isSharedCheck_4043_ =
                                        (!leanh::lean_is_exclusive(v_r_3959_)) as u8;
                                    if v_isSharedCheck_4043_ == 0 {
                                        v_unused_4044_ = leanh::lean_ctor_get(v_r_3959_, 4);
                                        leanh::lean_dec(v_unused_4044_);
                                        v_unused_4045_ = leanh::lean_ctor_get(v_r_3959_, 3);
                                        leanh::lean_dec(v_unused_4045_);
                                        v_unused_4046_ = leanh::lean_ctor_get(v_r_3959_, 2);
                                        leanh::lean_dec(v_unused_4046_);
                                        v_unused_4047_ = leanh::lean_ctor_get(v_r_3959_, 1);
                                        leanh::lean_dec(v_unused_4047_);
                                        v_unused_4048_ = leanh::lean_ctor_get(v_r_3959_, 0);
                                        leanh::lean_dec(v_unused_4048_);
                                        v___x_3981_ = v_r_3959_;
                                        v_isShared_3982_ = v_isSharedCheck_4043_;
                                        state = 3;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_r_3959_);
                                        v___x_3981_ = leanh::lean_box(0);
                                        v_isShared_3982_ = v_isSharedCheck_4043_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_4049_ = leanh::lean_ctor_get(v_impl_3964_, 0);
                                leanh::lean_inc(v_size_4049_);
                                v___x_4050_ = lean_nat_add(v___x_3965_, v_size_4049_);
                                leanh::lean_dec(v_size_4049_);
                                if v_isShared_3962_ == 0 {
                                    leanh::lean_ctor_set(v___x_3961_, 3, v_impl_3964_);
                                    leanh::lean_ctor_set(v___x_3961_, 0, v___x_4050_);
                                    v___x_4052_ = v___x_3961_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4053_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4053_,
                                        0,
                                        v___x_4050_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4053_,
                                        1,
                                        v_k_3956_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4053_,
                                        2,
                                        v_v_3957_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4053_,
                                        3,
                                        v_impl_3964_,
                                    );
                                    leanh::lean_ctor_set(
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
                            if leanh::lean_obj_tag(v_r_3959_) == 0 {
                                v_l_4054_ = leanh::lean_ctor_get(v_r_3959_, 3);
                                leanh::lean_inc(v_l_4054_);
                                if leanh::lean_obj_tag(v_l_4054_) == 0 {
                                    v_r_4055_ = leanh::lean_ctor_get(v_r_3959_, 4);
                                    leanh::lean_inc(v_r_4055_);
                                    if leanh::lean_obj_tag(v_r_4055_) == 0 {
                                        v_size_4056_ = leanh::lean_ctor_get(v_r_3959_, 0);
                                        v_k_4057_ = leanh::lean_ctor_get(v_r_3959_, 1);
                                        v_v_4058_ = leanh::lean_ctor_get(v_r_3959_, 2);
                                        v_isSharedCheck_4071_ =
                                            (!leanh::lean_is_exclusive(v_r_3959_)) as u8;
                                        if v_isSharedCheck_4071_ == 0 {
                                            v_unused_4072_ =
                                                leanh::lean_ctor_get(v_r_3959_, 4);
                                            leanh::lean_dec(v_unused_4072_);
                                            v_unused_4073_ =
                                                leanh::lean_ctor_get(v_r_3959_, 3);
                                            leanh::lean_dec(v_unused_4073_);
                                            v___x_4060_ = v_r_3959_;
                                            v_isShared_4061_ = v_isSharedCheck_4071_;
                                            state = 14;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_4058_);
                                            leanh::lean_inc(v_k_4057_);
                                            leanh::lean_inc(v_size_4056_);
                                            leanh::lean_dec(v_r_3959_);
                                            v___x_4060_ = leanh::lean_box(0);
                                            v_isShared_4061_ = v_isSharedCheck_4071_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_4074_ = leanh::lean_ctor_get(v_r_3959_, 1);
                                        v_v_4075_ = leanh::lean_ctor_get(v_r_3959_, 2);
                                        v_isSharedCheck_4098_ =
                                            (!leanh::lean_is_exclusive(v_r_3959_)) as u8;
                                        if v_isSharedCheck_4098_ == 0 {
                                            v_unused_4099_ =
                                                leanh::lean_ctor_get(v_r_3959_, 4);
                                            leanh::lean_dec(v_unused_4099_);
                                            v_unused_4100_ =
                                                leanh::lean_ctor_get(v_r_3959_, 3);
                                            leanh::lean_dec(v_unused_4100_);
                                            v_unused_4101_ =
                                                leanh::lean_ctor_get(v_r_3959_, 0);
                                            leanh::lean_dec(v_unused_4101_);
                                            v___x_4077_ = v_r_3959_;
                                            v_isShared_4078_ = v_isSharedCheck_4098_;
                                            state = 17;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_4075_);
                                            leanh::lean_inc(v_k_4074_);
                                            leanh::lean_dec(v_r_3959_);
                                            v___x_4077_ = leanh::lean_box(0);
                                            v_isShared_4078_ = v_isSharedCheck_4098_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_4102_ = leanh::lean_ctor_get(v_r_3959_, 4);
                                    leanh::lean_inc(v_r_4102_);
                                    if leanh::lean_obj_tag(v_r_4102_) == 0 {
                                        v_k_4103_ = leanh::lean_ctor_get(v_r_3959_, 1);
                                        v_v_4104_ = leanh::lean_ctor_get(v_r_3959_, 2);
                                        v_isSharedCheck_4115_ =
                                            (!leanh::lean_is_exclusive(v_r_3959_)) as u8;
                                        if v_isSharedCheck_4115_ == 0 {
                                            v_unused_4116_ =
                                                leanh::lean_ctor_get(v_r_3959_, 4);
                                            leanh::lean_dec(v_unused_4116_);
                                            v_unused_4117_ =
                                                leanh::lean_ctor_get(v_r_3959_, 3);
                                            leanh::lean_dec(v_unused_4117_);
                                            v_unused_4118_ =
                                                leanh::lean_ctor_get(v_r_3959_, 0);
                                            leanh::lean_dec(v_unused_4118_);
                                            v___x_4106_ = v_r_3959_;
                                            v_isShared_4107_ = v_isSharedCheck_4115_;
                                            state = 22;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_4104_);
                                            leanh::lean_inc(v_k_4103_);
                                            leanh::lean_dec(v_r_3959_);
                                            v___x_4106_ = leanh::lean_box(0);
                                            v_isShared_4107_ = v_isSharedCheck_4115_;
                                            state = 22;
                                            continue;
                                        }
                                    } else {
                                        v_size_4119_ = leanh::lean_ctor_get(v_r_3959_, 0);
                                        v_k_4120_ = leanh::lean_ctor_get(v_r_3959_, 1);
                                        v_v_4121_ = leanh::lean_ctor_get(v_r_3959_, 2);
                                        v_isSharedCheck_4132_ =
                                            (!leanh::lean_is_exclusive(v_r_3959_)) as u8;
                                        if v_isSharedCheck_4132_ == 0 {
                                            v_unused_4133_ =
                                                leanh::lean_ctor_get(v_r_3959_, 4);
                                            leanh::lean_dec(v_unused_4133_);
                                            v_unused_4134_ =
                                                leanh::lean_ctor_get(v_r_3959_, 3);
                                            leanh::lean_dec(v_unused_4134_);
                                            v___x_4123_ = v_r_3959_;
                                            v_isShared_4124_ = v_isSharedCheck_4132_;
                                            state = 25;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_4121_);
                                            leanh::lean_inc(v_k_4120_);
                                            leanh::lean_inc(v_size_4119_);
                                            leanh::lean_dec(v_r_3959_);
                                            v___x_4123_ = leanh::lean_box(0);
                                            v_isShared_4124_ = v_isSharedCheck_4132_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                if v_isShared_3962_ == 0 {
                                    leanh::lean_ctor_set(v___x_3961_, 3, v_r_3959_);
                                    leanh::lean_ctor_set(v___x_3961_, 0, v___x_3965_);
                                    v___x_4136_ = v___x_3961_;
                                    state = 28;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4137_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4137_,
                                        0,
                                        v___x_3965_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4137_,
                                        1,
                                        v_k_3956_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4137_,
                                        2,
                                        v_v_3957_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4137_,
                                        3,
                                        v_r_3959_,
                                    );
                                    leanh::lean_ctor_set(
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
                        leanh::lean_del_object(v___x_3961_);
                        leanh::lean_dec(v_v_3957_);
                        leanh::lean_dec(v_k_3956_);
                        if leanh::lean_obj_tag(v_l_3958_) == 0 {
                            if leanh::lean_obj_tag(v_r_3959_) == 0 {
                                v_size_4138_ = leanh::lean_ctor_get(v_l_3958_, 0);
                                v_k_4139_ = leanh::lean_ctor_get(v_l_3958_, 1);
                                v_v_4140_ = leanh::lean_ctor_get(v_l_3958_, 2);
                                v_l_4141_ = leanh::lean_ctor_get(v_l_3958_, 3);
                                v_r_4142_ = leanh::lean_ctor_get(v_l_3958_, 4);
                                leanh::lean_inc(v_r_4142_);
                                v_size_4143_ = leanh::lean_ctor_get(v_r_3959_, 0);
                                v_k_4144_ = leanh::lean_ctor_get(v_r_3959_, 1);
                                v_v_4145_ = leanh::lean_ctor_get(v_r_3959_, 2);
                                v_l_4146_ = leanh::lean_ctor_get(v_r_3959_, 3);
                                leanh::lean_inc(v_l_4146_);
                                v_r_4147_ = leanh::lean_ctor_get(v_r_3959_, 4);
                                v___x_4148_ = leanh::lean_unsigned_to_nat(1);
                                v___x_4149_ = lean_nat_dec_lt(v_size_4138_, v_size_4143_);
                                if v___x_4149_ == 0 {
                                    leanh::lean_inc(v_l_4141_);
                                    leanh::lean_inc(v_v_4140_);
                                    leanh::lean_inc(v_k_4139_);
                                    v_isSharedCheck_4285_ =
                                        (!leanh::lean_is_exclusive(v_l_3958_)) as u8;
                                    if v_isSharedCheck_4285_ == 0 {
                                        v_unused_4286_ = leanh::lean_ctor_get(v_l_3958_, 4);
                                        leanh::lean_dec(v_unused_4286_);
                                        v_unused_4287_ = leanh::lean_ctor_get(v_l_3958_, 3);
                                        leanh::lean_dec(v_unused_4287_);
                                        v_unused_4288_ = leanh::lean_ctor_get(v_l_3958_, 2);
                                        leanh::lean_dec(v_unused_4288_);
                                        v_unused_4289_ = leanh::lean_ctor_get(v_l_3958_, 1);
                                        leanh::lean_dec(v_unused_4289_);
                                        v_unused_4290_ = leanh::lean_ctor_get(v_l_3958_, 0);
                                        leanh::lean_dec(v_unused_4290_);
                                        v___x_4151_ = v_l_3958_;
                                        v_isShared_4152_ = v_isSharedCheck_4285_;
                                        state = 29;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_l_3958_);
                                        v___x_4151_ = leanh::lean_box(0);
                                        v_isShared_4152_ = v_isSharedCheck_4285_;
                                        state = 29;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_inc(v_r_4147_);
                                    leanh::lean_inc(v_v_4145_);
                                    leanh::lean_inc(v_k_4144_);
                                    v_isSharedCheck_4443_ =
                                        (!leanh::lean_is_exclusive(v_r_3959_)) as u8;
                                    if v_isSharedCheck_4443_ == 0 {
                                        v_unused_4444_ = leanh::lean_ctor_get(v_r_3959_, 4);
                                        leanh::lean_dec(v_unused_4444_);
                                        v_unused_4445_ = leanh::lean_ctor_get(v_r_3959_, 3);
                                        leanh::lean_dec(v_unused_4445_);
                                        v_unused_4446_ = leanh::lean_ctor_get(v_r_3959_, 2);
                                        leanh::lean_dec(v_unused_4446_);
                                        v_unused_4447_ = leanh::lean_ctor_get(v_r_3959_, 1);
                                        leanh::lean_dec(v_unused_4447_);
                                        v_unused_4448_ = leanh::lean_ctor_get(v_r_3959_, 0);
                                        leanh::lean_dec(v_unused_4448_);
                                        v___x_4292_ = v_r_3959_;
                                        v_isShared_4293_ = v_isSharedCheck_4443_;
                                        state = 51;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_r_3959_);
                                        v___x_4292_ = leanh::lean_box(0);
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
                        v___x_4450_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_impl_4449_) == 0 {
                            if leanh::lean_obj_tag(v_l_3958_) == 0 {
                                v_size_4451_ = leanh::lean_ctor_get(v_impl_4449_, 0);
                                leanh::lean_inc(v_size_4451_);
                                v_size_4452_ = leanh::lean_ctor_get(v_l_3958_, 0);
                                v_k_4453_ = leanh::lean_ctor_get(v_l_3958_, 1);
                                v_v_4454_ = leanh::lean_ctor_get(v_l_3958_, 2);
                                v_l_4455_ = leanh::lean_ctor_get(v_l_3958_, 3);
                                v_r_4456_ = leanh::lean_ctor_get(v_l_3958_, 4);
                                leanh::lean_inc(v_r_4456_);
                                v___x_4457_ = leanh::lean_unsigned_to_nat(3);
                                v___x_4458_ = lean_nat_mul(v___x_4457_, v_size_4451_);
                                v___x_4459_ = lean_nat_dec_lt(v___x_4458_, v_size_4452_);
                                leanh::lean_dec(v___x_4458_);
                                if v___x_4459_ == 0 {
                                    leanh::lean_dec(v_r_4456_);
                                    v___x_4460_ = lean_nat_add(v___x_4450_, v_size_4452_);
                                    v___x_4461_ = lean_nat_add(v___x_4460_, v_size_4451_);
                                    leanh::lean_dec(v_size_4451_);
                                    leanh::lean_dec(v___x_4460_);
                                    if v_isShared_3962_ == 0 {
                                        leanh::lean_ctor_set(v___x_3961_, 4, v_impl_4449_);
                                        leanh::lean_ctor_set(v___x_3961_, 0, v___x_4461_);
                                        v___x_4463_ = v___x_3961_;
                                        state = 74;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_4464_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4464_,
                                            0,
                                            v___x_4461_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4464_,
                                            1,
                                            v_k_3956_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4464_,
                                            2,
                                            v_v_3957_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4464_,
                                            3,
                                            v_l_3958_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4464_,
                                            4,
                                            v_impl_4449_,
                                        );
                                        v___x_4463_ = v_reuseFailAlloc_4464_;
                                        state = 74;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_inc(v_l_4455_);
                                    leanh::lean_inc(v_v_4454_);
                                    leanh::lean_inc(v_k_4453_);
                                    leanh::lean_inc(v_size_4452_);
                                    v_isSharedCheck_4530_ =
                                        (!leanh::lean_is_exclusive(v_l_3958_)) as u8;
                                    if v_isSharedCheck_4530_ == 0 {
                                        v_unused_4531_ = leanh::lean_ctor_get(v_l_3958_, 4);
                                        leanh::lean_dec(v_unused_4531_);
                                        v_unused_4532_ = leanh::lean_ctor_get(v_l_3958_, 3);
                                        leanh::lean_dec(v_unused_4532_);
                                        v_unused_4533_ = leanh::lean_ctor_get(v_l_3958_, 2);
                                        leanh::lean_dec(v_unused_4533_);
                                        v_unused_4534_ = leanh::lean_ctor_get(v_l_3958_, 1);
                                        leanh::lean_dec(v_unused_4534_);
                                        v_unused_4535_ = leanh::lean_ctor_get(v_l_3958_, 0);
                                        leanh::lean_dec(v_unused_4535_);
                                        v___x_4466_ = v_l_3958_;
                                        v_isShared_4467_ = v_isSharedCheck_4530_;
                                        state = 75;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_l_3958_);
                                        v___x_4466_ = leanh::lean_box(0);
                                        v_isShared_4467_ = v_isSharedCheck_4530_;
                                        state = 75;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_4536_ = leanh::lean_ctor_get(v_impl_4449_, 0);
                                leanh::lean_inc(v_size_4536_);
                                v___x_4537_ = lean_nat_add(v___x_4450_, v_size_4536_);
                                leanh::lean_dec(v_size_4536_);
                                if v_isShared_3962_ == 0 {
                                    leanh::lean_ctor_set(v___x_3961_, 4, v_impl_4449_);
                                    leanh::lean_ctor_set(v___x_3961_, 0, v___x_4537_);
                                    v___x_4539_ = v___x_3961_;
                                    state = 85;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4540_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4540_,
                                        0,
                                        v___x_4537_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4540_,
                                        1,
                                        v_k_3956_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4540_,
                                        2,
                                        v_v_3957_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4540_,
                                        3,
                                        v_l_3958_,
                                    );
                                    leanh::lean_ctor_set(
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
                            if leanh::lean_obj_tag(v_l_3958_) == 0 {
                                v_l_4541_ = leanh::lean_ctor_get(v_l_3958_, 3);
                                if leanh::lean_obj_tag(v_l_4541_) == 0 {
                                    leanh::lean_inc_ref(v_l_4541_);
                                    v_r_4542_ = leanh::lean_ctor_get(v_l_3958_, 4);
                                    leanh::lean_inc(v_r_4542_);
                                    if leanh::lean_obj_tag(v_r_4542_) == 0 {
                                        v_size_4543_ = leanh::lean_ctor_get(v_l_3958_, 0);
                                        v_k_4544_ = leanh::lean_ctor_get(v_l_3958_, 1);
                                        v_v_4545_ = leanh::lean_ctor_get(v_l_3958_, 2);
                                        v_isSharedCheck_4558_ =
                                            (!leanh::lean_is_exclusive(v_l_3958_)) as u8;
                                        if v_isSharedCheck_4558_ == 0 {
                                            v_unused_4559_ =
                                                leanh::lean_ctor_get(v_l_3958_, 4);
                                            leanh::lean_dec(v_unused_4559_);
                                            v_unused_4560_ =
                                                leanh::lean_ctor_get(v_l_3958_, 3);
                                            leanh::lean_dec(v_unused_4560_);
                                            v___x_4547_ = v_l_3958_;
                                            v_isShared_4548_ = v_isSharedCheck_4558_;
                                            state = 86;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_4545_);
                                            leanh::lean_inc(v_k_4544_);
                                            leanh::lean_inc(v_size_4543_);
                                            leanh::lean_dec(v_l_3958_);
                                            v___x_4547_ = leanh::lean_box(0);
                                            v_isShared_4548_ = v_isSharedCheck_4558_;
                                            state = 86;
                                            continue;
                                        }
                                    } else {
                                        v_k_4561_ = leanh::lean_ctor_get(v_l_3958_, 1);
                                        v_v_4562_ = leanh::lean_ctor_get(v_l_3958_, 2);
                                        v_isSharedCheck_4573_ =
                                            (!leanh::lean_is_exclusive(v_l_3958_)) as u8;
                                        if v_isSharedCheck_4573_ == 0 {
                                            v_unused_4574_ =
                                                leanh::lean_ctor_get(v_l_3958_, 4);
                                            leanh::lean_dec(v_unused_4574_);
                                            v_unused_4575_ =
                                                leanh::lean_ctor_get(v_l_3958_, 3);
                                            leanh::lean_dec(v_unused_4575_);
                                            v_unused_4576_ =
                                                leanh::lean_ctor_get(v_l_3958_, 0);
                                            leanh::lean_dec(v_unused_4576_);
                                            v___x_4564_ = v_l_3958_;
                                            v_isShared_4565_ = v_isSharedCheck_4573_;
                                            state = 89;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_4562_);
                                            leanh::lean_inc(v_k_4561_);
                                            leanh::lean_dec(v_l_3958_);
                                            v___x_4564_ = leanh::lean_box(0);
                                            v_isShared_4565_ = v_isSharedCheck_4573_;
                                            state = 89;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_4577_ = leanh::lean_ctor_get(v_l_3958_, 4);
                                    leanh::lean_inc(v_r_4577_);
                                    if leanh::lean_obj_tag(v_r_4577_) == 0 {
                                        leanh::lean_inc(v_l_4541_);
                                        v_k_4578_ = leanh::lean_ctor_get(v_l_3958_, 1);
                                        v_v_4579_ = leanh::lean_ctor_get(v_l_3958_, 2);
                                        v_isSharedCheck_4602_ =
                                            (!leanh::lean_is_exclusive(v_l_3958_)) as u8;
                                        if v_isSharedCheck_4602_ == 0 {
                                            v_unused_4603_ =
                                                leanh::lean_ctor_get(v_l_3958_, 4);
                                            leanh::lean_dec(v_unused_4603_);
                                            v_unused_4604_ =
                                                leanh::lean_ctor_get(v_l_3958_, 3);
                                            leanh::lean_dec(v_unused_4604_);
                                            v_unused_4605_ =
                                                leanh::lean_ctor_get(v_l_3958_, 0);
                                            leanh::lean_dec(v_unused_4605_);
                                            v___x_4581_ = v_l_3958_;
                                            v_isShared_4582_ = v_isSharedCheck_4602_;
                                            state = 92;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_4579_);
                                            leanh::lean_inc(v_k_4578_);
                                            leanh::lean_dec(v_l_3958_);
                                            v___x_4581_ = leanh::lean_box(0);
                                            v_isShared_4582_ = v_isSharedCheck_4602_;
                                            state = 92;
                                            continue;
                                        }
                                    } else {
                                        v___x_4606_ = leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_3962_ == 0 {
                                            leanh::lean_ctor_set(v___x_3961_, 4, v_r_4577_);
                                            leanh::lean_ctor_set(
                                                v___x_3961_,
                                                0,
                                                v___x_4606_,
                                            );
                                            v___x_4608_ = v___x_3961_;
                                            state = 97;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_4609_ =
                                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_4609_,
                                                0,
                                                v___x_4606_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_4609_,
                                                1,
                                                v_k_3956_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_4609_,
                                                2,
                                                v_v_3957_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_4609_,
                                                3,
                                                v_l_3958_,
                                            );
                                            leanh::lean_ctor_set(
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
                                    leanh::lean_ctor_set(v___x_3961_, 4, v_l_3958_);
                                    leanh::lean_ctor_set(v___x_3961_, 0, v___x_4450_);
                                    v___x_4611_ = v___x_3961_;
                                    state = 98;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4612_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4612_,
                                        0,
                                        v___x_4450_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4612_,
                                        1,
                                        v_k_3956_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4612_,
                                        2,
                                        v_v_3957_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4612_,
                                        3,
                                        v_l_3958_,
                                    );
                                    leanh::lean_ctor_set(
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
                v_size_3983_ = leanh::lean_ctor_get(v_l_3970_, 0);
                v_k_3984_ = leanh::lean_ctor_get(v_l_3970_, 1);
                v_v_3985_ = leanh::lean_ctor_get(v_l_3970_, 2);
                v_l_3986_ = leanh::lean_ctor_get(v_l_3970_, 3);
                v_r_3987_ = leanh::lean_ctor_get(v_l_3970_, 4);
                v_size_3988_ = leanh::lean_ctor_get(v_r_3971_, 0);
                v___x_3989_ = leanh::lean_unsigned_to_nat(2);
                v___x_3990_ = lean_nat_mul(v___x_3989_, v_size_3988_);
                v___x_3991_ = lean_nat_dec_lt(v_size_3983_, v___x_3990_);
                leanh::lean_dec(v___x_3990_);
                if v___x_3991_ == 0 {
                    leanh::lean_inc(v_r_3987_);
                    leanh::lean_inc(v_l_3986_);
                    leanh::lean_inc(v_v_3985_);
                    leanh::lean_inc(v_k_3984_);
                    v_isSharedCheck_4019_ = (!leanh::lean_is_exclusive(v_l_3970_)) as u8;
                    if v_isSharedCheck_4019_ == 0 {
                        v_unused_4020_ = leanh::lean_ctor_get(v_l_3970_, 4);
                        leanh::lean_dec(v_unused_4020_);
                        v_unused_4021_ = leanh::lean_ctor_get(v_l_3970_, 3);
                        leanh::lean_dec(v_unused_4021_);
                        v_unused_4022_ = leanh::lean_ctor_get(v_l_3970_, 2);
                        leanh::lean_dec(v_unused_4022_);
                        v_unused_4023_ = leanh::lean_ctor_get(v_l_3970_, 1);
                        leanh::lean_dec(v_unused_4023_);
                        v_unused_4024_ = leanh::lean_ctor_get(v_l_3970_, 0);
                        leanh::lean_dec(v_unused_4024_);
                        v___x_3993_ = v_l_3970_;
                        v_isShared_3994_ = v_isSharedCheck_4019_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_l_3970_);
                        v___x_3993_ = leanh::lean_box(0);
                        v_isShared_3994_ = v_isSharedCheck_4019_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3961_);
                    v___x_4025_ = lean_nat_add(v___x_3965_, v_size_3966_);
                    leanh::lean_dec(v_size_3966_);
                    v___x_4026_ = lean_nat_add(v___x_4025_, v_size_3967_);
                    leanh::lean_dec(v_size_3967_);
                    v___x_4027_ = lean_nat_add(v___x_4025_, v_size_3983_);
                    leanh::lean_dec(v___x_4025_);
                    leanh::lean_inc_ref(v_impl_3964_);
                    if v_isShared_3982_ == 0 {
                        leanh::lean_ctor_set(v___x_3981_, 4, v_l_3970_);
                        leanh::lean_ctor_set(v___x_3981_, 3, v_impl_3964_);
                        leanh::lean_ctor_set(v___x_3981_, 2, v_v_3957_);
                        leanh::lean_ctor_set(v___x_3981_, 1, v_k_3956_);
                        leanh::lean_ctor_set(v___x_3981_, 0, v___x_4027_);
                        v___x_4029_ = v___x_3981_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4042_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4042_, 0, v___x_4027_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4042_, 1, v_k_3956_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4042_, 2, v_v_3957_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4042_, 3, v_impl_3964_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4042_, 4, v_l_3970_);
                        v___x_4029_ = v_reuseFailAlloc_4042_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3995_ = lean_nat_add(v___x_3965_, v_size_3966_);
                leanh::lean_dec(v_size_3966_);
                v___x_3996_ = lean_nat_add(v___x_3995_, v_size_3967_);
                leanh::lean_dec(v_size_3967_);
                if leanh::lean_obj_tag(v_l_3986_) == 0 {
                    v_size_4017_ = leanh::lean_ctor_get(v_l_3986_, 0);
                    leanh::lean_inc(v_size_4017_);
                    v___y_4009_ = v_size_4017_;
                    state = 8;
                    continue;
                } else {
                    v___x_4018_ = leanh::lean_unsigned_to_nat(0);
                    v___y_4009_ = v___x_4018_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_4001_ = lean_nat_add(v___y_3998_, v___y_4000_);
                leanh::lean_dec(v___y_4000_);
                leanh::lean_dec(v___y_3998_);
                if v_isShared_3994_ == 0 {
                    leanh::lean_ctor_set(v___x_3993_, 4, v_r_3971_);
                    leanh::lean_ctor_set(v___x_3993_, 3, v_r_3987_);
                    leanh::lean_ctor_set(v___x_3993_, 2, v_v_3969_);
                    leanh::lean_ctor_set(v___x_3993_, 1, v_k_3968_);
                    leanh::lean_ctor_set(v___x_3993_, 0, v___x_4001_);
                    v___x_4003_ = v___x_3993_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4007_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4007_, 0, v___x_4001_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4007_, 1, v_k_3968_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4007_, 2, v_v_3969_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4007_, 3, v_r_3987_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4007_, 4, v_r_3971_);
                    v___x_4003_ = v_reuseFailAlloc_4007_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3982_ == 0 {
                    leanh::lean_ctor_set(v___x_3981_, 4, v___x_4003_);
                    leanh::lean_ctor_set(v___x_3981_, 3, v___y_3999_);
                    leanh::lean_ctor_set(v___x_3981_, 2, v_v_3985_);
                    leanh::lean_ctor_set(v___x_3981_, 1, v_k_3984_);
                    leanh::lean_ctor_set(v___x_3981_, 0, v___x_3996_);
                    v___x_4005_ = v___x_3981_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4006_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4006_, 0, v___x_3996_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4006_, 1, v_k_3984_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4006_, 2, v_v_3985_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4006_, 3, v___y_3999_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4006_, 4, v___x_4003_);
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
                leanh::lean_dec(v___y_4009_);
                leanh::lean_dec(v___x_3995_);
                if v_isShared_3962_ == 0 {
                    leanh::lean_ctor_set(v___x_3961_, 4, v_l_3986_);
                    leanh::lean_ctor_set(v___x_3961_, 3, v_impl_3964_);
                    leanh::lean_ctor_set(v___x_3961_, 0, v___x_4010_);
                    v___x_4012_ = v___x_3961_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4016_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4016_, 0, v___x_4010_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4016_, 1, v_k_3956_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4016_, 2, v_v_3957_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4016_, 3, v_impl_3964_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4016_, 4, v_l_3986_);
                    v___x_4012_ = v_reuseFailAlloc_4016_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_4013_ = lean_nat_add(v___x_3965_, v_size_3988_);
                if leanh::lean_obj_tag(v_r_3987_) == 0 {
                    v_size_4014_ = leanh::lean_ctor_get(v_r_3987_, 0);
                    leanh::lean_inc(v_size_4014_);
                    v___y_3998_ = v___x_4013_;
                    v___y_3999_ = v___x_4012_;
                    v___y_4000_ = v_size_4014_;
                    state = 5;
                    continue;
                } else {
                    v___x_4015_ = leanh::lean_unsigned_to_nat(0);
                    v___y_3998_ = v___x_4013_;
                    v___y_3999_ = v___x_4012_;
                    v___y_4000_ = v___x_4015_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_4036_ = (!leanh::lean_is_exclusive(v_impl_3964_)) as u8;
                if v_isSharedCheck_4036_ == 0 {
                    v_unused_4037_ = leanh::lean_ctor_get(v_impl_3964_, 4);
                    leanh::lean_dec(v_unused_4037_);
                    v_unused_4038_ = leanh::lean_ctor_get(v_impl_3964_, 3);
                    leanh::lean_dec(v_unused_4038_);
                    v_unused_4039_ = leanh::lean_ctor_get(v_impl_3964_, 2);
                    leanh::lean_dec(v_unused_4039_);
                    v_unused_4040_ = leanh::lean_ctor_get(v_impl_3964_, 1);
                    leanh::lean_dec(v_unused_4040_);
                    v_unused_4041_ = leanh::lean_ctor_get(v_impl_3964_, 0);
                    leanh::lean_dec(v_unused_4041_);
                    v___x_4031_ = v_impl_3964_;
                    v_isShared_4032_ = v_isSharedCheck_4036_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_dec(v_impl_3964_);
                    v___x_4031_ = leanh::lean_box(0);
                    v_isShared_4032_ = v_isSharedCheck_4036_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_4032_ == 0 {
                    leanh::lean_ctor_set(v___x_4031_, 4, v_r_3971_);
                    leanh::lean_ctor_set(v___x_4031_, 3, v___x_4029_);
                    leanh::lean_ctor_set(v___x_4031_, 2, v_v_3969_);
                    leanh::lean_ctor_set(v___x_4031_, 1, v_k_3968_);
                    leanh::lean_ctor_set(v___x_4031_, 0, v___x_4026_);
                    v___x_4034_ = v___x_4031_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4035_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4035_, 0, v___x_4026_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4035_, 1, v_k_3968_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4035_, 2, v_v_3969_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4035_, 3, v___x_4029_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4035_, 4, v_r_3971_);
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
                v_size_4062_ = leanh::lean_ctor_get(v_l_4054_, 0);
                v___x_4063_ = lean_nat_add(v___x_3965_, v_size_4056_);
                leanh::lean_dec(v_size_4056_);
                v___x_4064_ = lean_nat_add(v___x_3965_, v_size_4062_);
                if v_isShared_4061_ == 0 {
                    leanh::lean_ctor_set(v___x_4060_, 4, v_l_4054_);
                    leanh::lean_ctor_set(v___x_4060_, 3, v_impl_3964_);
                    leanh::lean_ctor_set(v___x_4060_, 2, v_v_3957_);
                    leanh::lean_ctor_set(v___x_4060_, 1, v_k_3956_);
                    leanh::lean_ctor_set(v___x_4060_, 0, v___x_4064_);
                    v___x_4066_ = v___x_4060_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4070_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 0, v___x_4064_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 1, v_k_3956_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 2, v_v_3957_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 3, v_impl_3964_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 4, v_l_4054_);
                    v___x_4066_ = v_reuseFailAlloc_4070_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_3962_ == 0 {
                    leanh::lean_ctor_set(v___x_3961_, 4, v_r_4055_);
                    leanh::lean_ctor_set(v___x_3961_, 3, v___x_4066_);
                    leanh::lean_ctor_set(v___x_3961_, 2, v_v_4058_);
                    leanh::lean_ctor_set(v___x_3961_, 1, v_k_4057_);
                    leanh::lean_ctor_set(v___x_3961_, 0, v___x_4063_);
                    v___x_4068_ = v___x_3961_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4069_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4069_, 0, v___x_4063_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4069_, 1, v_k_4057_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4069_, 2, v_v_4058_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4069_, 3, v___x_4066_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4069_, 4, v_r_4055_);
                    v___x_4068_ = v_reuseFailAlloc_4069_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4068_;
            }
            17 => {
                v_k_4079_ = leanh::lean_ctor_get(v_l_4054_, 1);
                v_v_4080_ = leanh::lean_ctor_get(v_l_4054_, 2);
                v_isSharedCheck_4094_ = (!leanh::lean_is_exclusive(v_l_4054_)) as u8;
                if v_isSharedCheck_4094_ == 0 {
                    v_unused_4095_ = leanh::lean_ctor_get(v_l_4054_, 4);
                    leanh::lean_dec(v_unused_4095_);
                    v_unused_4096_ = leanh::lean_ctor_get(v_l_4054_, 3);
                    leanh::lean_dec(v_unused_4096_);
                    v_unused_4097_ = leanh::lean_ctor_get(v_l_4054_, 0);
                    leanh::lean_dec(v_unused_4097_);
                    v___x_4082_ = v_l_4054_;
                    v_isShared_4083_ = v_isSharedCheck_4094_;
                    state = 18;
                    continue;
                } else {
                    leanh::lean_inc(v_v_4080_);
                    leanh::lean_inc(v_k_4079_);
                    leanh::lean_dec(v_l_4054_);
                    v___x_4082_ = leanh::lean_box(0);
                    v_isShared_4083_ = v_isSharedCheck_4094_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_4084_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_4083_ == 0 {
                    leanh::lean_ctor_set(v___x_4082_, 4, v_r_4055_);
                    leanh::lean_ctor_set(v___x_4082_, 3, v_r_4055_);
                    leanh::lean_ctor_set(v___x_4082_, 2, v_v_3957_);
                    leanh::lean_ctor_set(v___x_4082_, 1, v_k_3956_);
                    leanh::lean_ctor_set(v___x_4082_, 0, v___x_3965_);
                    v___x_4086_ = v___x_4082_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4093_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4093_, 0, v___x_3965_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4093_, 1, v_k_3956_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4093_, 2, v_v_3957_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4093_, 3, v_r_4055_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4093_, 4, v_r_4055_);
                    v___x_4086_ = v_reuseFailAlloc_4093_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_4078_ == 0 {
                    leanh::lean_ctor_set(v___x_4077_, 3, v_r_4055_);
                    leanh::lean_ctor_set(v___x_4077_, 0, v___x_3965_);
                    v___x_4088_ = v___x_4077_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4092_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4092_, 0, v___x_3965_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4092_, 1, v_k_4074_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4092_, 2, v_v_4075_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4092_, 3, v_r_4055_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4092_, 4, v_r_4055_);
                    v___x_4088_ = v_reuseFailAlloc_4092_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_3962_ == 0 {
                    leanh::lean_ctor_set(v___x_3961_, 4, v___x_4088_);
                    leanh::lean_ctor_set(v___x_3961_, 3, v___x_4086_);
                    leanh::lean_ctor_set(v___x_3961_, 2, v_v_4080_);
                    leanh::lean_ctor_set(v___x_3961_, 1, v_k_4079_);
                    leanh::lean_ctor_set(v___x_3961_, 0, v___x_4084_);
                    v___x_4090_ = v___x_3961_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4091_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4084_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4091_, 1, v_k_4079_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4091_, 2, v_v_4080_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4091_, 3, v___x_4086_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4091_, 4, v___x_4088_);
                    v___x_4090_ = v_reuseFailAlloc_4091_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_4090_;
            }
            22 => {
                v___x_4108_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_4107_ == 0 {
                    leanh::lean_ctor_set(v___x_4106_, 4, v_l_4054_);
                    leanh::lean_ctor_set(v___x_4106_, 2, v_v_3957_);
                    leanh::lean_ctor_set(v___x_4106_, 1, v_k_3956_);
                    leanh::lean_ctor_set(v___x_4106_, 0, v___x_3965_);
                    v___x_4110_ = v___x_4106_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_4114_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4114_, 0, v___x_3965_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4114_, 1, v_k_3956_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4114_, 2, v_v_3957_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4114_, 3, v_l_4054_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4114_, 4, v_l_4054_);
                    v___x_4110_ = v_reuseFailAlloc_4114_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_3962_ == 0 {
                    leanh::lean_ctor_set(v___x_3961_, 4, v_r_4102_);
                    leanh::lean_ctor_set(v___x_3961_, 3, v___x_4110_);
                    leanh::lean_ctor_set(v___x_3961_, 2, v_v_4104_);
                    leanh::lean_ctor_set(v___x_3961_, 1, v_k_4103_);
                    leanh::lean_ctor_set(v___x_3961_, 0, v___x_4108_);
                    v___x_4112_ = v___x_3961_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4113_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 0, v___x_4108_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 1, v_k_4103_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 2, v_v_4104_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 3, v___x_4110_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 4, v_r_4102_);
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
                    leanh::lean_ctor_set(v___x_4123_, 3, v_r_4102_);
                    v___x_4126_ = v___x_4123_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4131_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_size_4119_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4131_, 1, v_k_4120_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4131_, 2, v_v_4121_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4131_, 3, v_r_4102_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4131_, 4, v_r_4102_);
                    v___x_4126_ = v_reuseFailAlloc_4131_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_4127_ = leanh::lean_unsigned_to_nat(2);
                if v_isShared_3962_ == 0 {
                    leanh::lean_ctor_set(v___x_3961_, 4, v___x_4126_);
                    leanh::lean_ctor_set(v___x_3961_, 3, v_r_4102_);
                    leanh::lean_ctor_set(v___x_3961_, 0, v___x_4127_);
                    v___x_4129_ = v___x_3961_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_4130_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 0, v___x_4127_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 1, v_k_3956_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 2, v_v_3957_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 3, v_r_4102_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 4, v___x_4126_);
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
                v_tree_4154_ = leanh::lean_ctor_get(v___x_4153_, 2);
                leanh::lean_inc(v_tree_4154_);
                if leanh::lean_obj_tag(v_tree_4154_) == 0 {
                    v_k_4155_ = leanh::lean_ctor_get(v___x_4153_, 0);
                    leanh::lean_inc(v_k_4155_);
                    v_v_4156_ = leanh::lean_ctor_get(v___x_4153_, 1);
                    leanh::lean_inc(v_v_4156_);
                    leanh::lean_dec_ref(v___x_4153_);
                    v_size_4157_ = leanh::lean_ctor_get(v_tree_4154_, 0);
                    v___x_4158_ = leanh::lean_unsigned_to_nat(3);
                    v___x_4159_ = lean_nat_mul(v___x_4158_, v_size_4157_);
                    v___x_4160_ = lean_nat_dec_lt(v___x_4159_, v_size_4143_);
                    leanh::lean_dec(v___x_4159_);
                    if v___x_4160_ == 0 {
                        leanh::lean_dec(v_l_4146_);
                        v___x_4161_ = lean_nat_add(v___x_4148_, v_size_4157_);
                        v___x_4162_ = lean_nat_add(v___x_4161_, v_size_4143_);
                        leanh::lean_dec(v___x_4161_);
                        if v_isShared_4152_ == 0 {
                            leanh::lean_ctor_set(v___x_4151_, 4, v_r_3959_);
                            leanh::lean_ctor_set(v___x_4151_, 3, v_tree_4154_);
                            leanh::lean_ctor_set(v___x_4151_, 2, v_v_4156_);
                            leanh::lean_ctor_set(v___x_4151_, 1, v_k_4155_);
                            leanh::lean_ctor_set(v___x_4151_, 0, v___x_4162_);
                            v___x_4164_ = v___x_4151_;
                            state = 30;
                            continue;
                        } else {
                            v_reuseFailAlloc_4165_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4165_, 0, v___x_4162_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4165_, 1, v_k_4155_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4165_, 2, v_v_4156_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4165_, 3, v_tree_4154_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4165_, 4, v_r_3959_);
                            v___x_4164_ = v_reuseFailAlloc_4165_;
                            state = 30;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_r_4147_);
                        leanh::lean_inc(v_v_4145_);
                        leanh::lean_inc(v_k_4144_);
                        leanh::lean_inc(v_size_4143_);
                        v_isSharedCheck_4220_ = (!leanh::lean_is_exclusive(v_r_3959_)) as u8;
                        if v_isSharedCheck_4220_ == 0 {
                            v_unused_4221_ = leanh::lean_ctor_get(v_r_3959_, 4);
                            leanh::lean_dec(v_unused_4221_);
                            v_unused_4222_ = leanh::lean_ctor_get(v_r_3959_, 3);
                            leanh::lean_dec(v_unused_4222_);
                            v_unused_4223_ = leanh::lean_ctor_get(v_r_3959_, 2);
                            leanh::lean_dec(v_unused_4223_);
                            v_unused_4224_ = leanh::lean_ctor_get(v_r_3959_, 1);
                            leanh::lean_dec(v_unused_4224_);
                            v_unused_4225_ = leanh::lean_ctor_get(v_r_3959_, 0);
                            leanh::lean_dec(v_unused_4225_);
                            v___x_4167_ = v_r_3959_;
                            v_isShared_4168_ = v_isSharedCheck_4220_;
                            state = 31;
                            continue;
                        } else {
                            leanh::lean_dec(v_r_3959_);
                            v___x_4167_ = leanh::lean_box(0);
                            v_isShared_4168_ = v_isSharedCheck_4220_;
                            state = 31;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_r_4147_);
                    leanh::lean_inc(v_v_4145_);
                    leanh::lean_inc(v_k_4144_);
                    leanh::lean_inc(v_size_4143_);
                    v_isSharedCheck_4279_ = (!leanh::lean_is_exclusive(v_r_3959_)) as u8;
                    if v_isSharedCheck_4279_ == 0 {
                        v_unused_4280_ = leanh::lean_ctor_get(v_r_3959_, 4);
                        leanh::lean_dec(v_unused_4280_);
                        v_unused_4281_ = leanh::lean_ctor_get(v_r_3959_, 3);
                        leanh::lean_dec(v_unused_4281_);
                        v_unused_4282_ = leanh::lean_ctor_get(v_r_3959_, 2);
                        leanh::lean_dec(v_unused_4282_);
                        v_unused_4283_ = leanh::lean_ctor_get(v_r_3959_, 1);
                        leanh::lean_dec(v_unused_4283_);
                        v_unused_4284_ = leanh::lean_ctor_get(v_r_3959_, 0);
                        leanh::lean_dec(v_unused_4284_);
                        v___x_4227_ = v_r_3959_;
                        v_isShared_4228_ = v_isSharedCheck_4279_;
                        state = 40;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_3959_);
                        v___x_4227_ = leanh::lean_box(0);
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
                v_size_4169_ = leanh::lean_ctor_get(v_l_4146_, 0);
                v_k_4170_ = leanh::lean_ctor_get(v_l_4146_, 1);
                v_v_4171_ = leanh::lean_ctor_get(v_l_4146_, 2);
                v_l_4172_ = leanh::lean_ctor_get(v_l_4146_, 3);
                v_r_4173_ = leanh::lean_ctor_get(v_l_4146_, 4);
                v_size_4174_ = leanh::lean_ctor_get(v_r_4147_, 0);
                v___x_4175_ = leanh::lean_unsigned_to_nat(2);
                v___x_4176_ = lean_nat_mul(v___x_4175_, v_size_4174_);
                v___x_4177_ = lean_nat_dec_lt(v_size_4169_, v___x_4176_);
                leanh::lean_dec(v___x_4176_);
                if v___x_4177_ == 0 {
                    leanh::lean_inc(v_r_4173_);
                    leanh::lean_inc(v_l_4172_);
                    leanh::lean_inc(v_v_4171_);
                    leanh::lean_inc(v_k_4170_);
                    v_isSharedCheck_4205_ = (!leanh::lean_is_exclusive(v_l_4146_)) as u8;
                    if v_isSharedCheck_4205_ == 0 {
                        v_unused_4206_ = leanh::lean_ctor_get(v_l_4146_, 4);
                        leanh::lean_dec(v_unused_4206_);
                        v_unused_4207_ = leanh::lean_ctor_get(v_l_4146_, 3);
                        leanh::lean_dec(v_unused_4207_);
                        v_unused_4208_ = leanh::lean_ctor_get(v_l_4146_, 2);
                        leanh::lean_dec(v_unused_4208_);
                        v_unused_4209_ = leanh::lean_ctor_get(v_l_4146_, 1);
                        leanh::lean_dec(v_unused_4209_);
                        v_unused_4210_ = leanh::lean_ctor_get(v_l_4146_, 0);
                        leanh::lean_dec(v_unused_4210_);
                        v___x_4179_ = v_l_4146_;
                        v_isShared_4180_ = v_isSharedCheck_4205_;
                        state = 32;
                        continue;
                    } else {
                        leanh::lean_dec(v_l_4146_);
                        v___x_4179_ = leanh::lean_box(0);
                        v_isShared_4180_ = v_isSharedCheck_4205_;
                        state = 32;
                        continue;
                    }
                } else {
                    v___x_4211_ = lean_nat_add(v___x_4148_, v_size_4157_);
                    v___x_4212_ = lean_nat_add(v___x_4211_, v_size_4143_);
                    leanh::lean_dec(v_size_4143_);
                    v___x_4213_ = lean_nat_add(v___x_4211_, v_size_4169_);
                    leanh::lean_dec(v___x_4211_);
                    if v_isShared_4168_ == 0 {
                        leanh::lean_ctor_set(v___x_4167_, 4, v_l_4146_);
                        leanh::lean_ctor_set(v___x_4167_, 3, v_tree_4154_);
                        leanh::lean_ctor_set(v___x_4167_, 2, v_v_4156_);
                        leanh::lean_ctor_set(v___x_4167_, 1, v_k_4155_);
                        leanh::lean_ctor_set(v___x_4167_, 0, v___x_4213_);
                        v___x_4215_ = v___x_4167_;
                        state = 38;
                        continue;
                    } else {
                        v_reuseFailAlloc_4219_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4219_, 0, v___x_4213_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4219_, 1, v_k_4155_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4219_, 2, v_v_4156_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4219_, 3, v_tree_4154_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4219_, 4, v_l_4146_);
                        v___x_4215_ = v_reuseFailAlloc_4219_;
                        state = 38;
                        continue;
                    }
                }
            }
            32 => {
                v___x_4181_ = lean_nat_add(v___x_4148_, v_size_4157_);
                v___x_4182_ = lean_nat_add(v___x_4181_, v_size_4143_);
                leanh::lean_dec(v_size_4143_);
                if leanh::lean_obj_tag(v_l_4172_) == 0 {
                    v_size_4203_ = leanh::lean_ctor_get(v_l_4172_, 0);
                    leanh::lean_inc(v_size_4203_);
                    v___y_4195_ = v_size_4203_;
                    state = 36;
                    continue;
                } else {
                    v___x_4204_ = leanh::lean_unsigned_to_nat(0);
                    v___y_4195_ = v___x_4204_;
                    state = 36;
                    continue;
                }
            }
            33 => {
                v___x_4187_ = lean_nat_add(v___y_4184_, v___y_4186_);
                leanh::lean_dec(v___y_4186_);
                leanh::lean_dec(v___y_4184_);
                if v_isShared_4180_ == 0 {
                    leanh::lean_ctor_set(v___x_4179_, 4, v_r_4147_);
                    leanh::lean_ctor_set(v___x_4179_, 3, v_r_4173_);
                    leanh::lean_ctor_set(v___x_4179_, 2, v_v_4145_);
                    leanh::lean_ctor_set(v___x_4179_, 1, v_k_4144_);
                    leanh::lean_ctor_set(v___x_4179_, 0, v___x_4187_);
                    v___x_4189_ = v___x_4179_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_4193_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4193_, 0, v___x_4187_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4193_, 1, v_k_4144_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4193_, 2, v_v_4145_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4193_, 3, v_r_4173_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4193_, 4, v_r_4147_);
                    v___x_4189_ = v_reuseFailAlloc_4193_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                if v_isShared_4168_ == 0 {
                    leanh::lean_ctor_set(v___x_4167_, 4, v___x_4189_);
                    leanh::lean_ctor_set(v___x_4167_, 3, v___y_4185_);
                    leanh::lean_ctor_set(v___x_4167_, 2, v_v_4171_);
                    leanh::lean_ctor_set(v___x_4167_, 1, v_k_4170_);
                    leanh::lean_ctor_set(v___x_4167_, 0, v___x_4182_);
                    v___x_4191_ = v___x_4167_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_4192_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4192_, 0, v___x_4182_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4192_, 1, v_k_4170_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4192_, 2, v_v_4171_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4192_, 3, v___y_4185_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4192_, 4, v___x_4189_);
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
                leanh::lean_dec(v___y_4195_);
                leanh::lean_dec(v___x_4181_);
                if v_isShared_4152_ == 0 {
                    leanh::lean_ctor_set(v___x_4151_, 4, v_l_4172_);
                    leanh::lean_ctor_set(v___x_4151_, 3, v_tree_4154_);
                    leanh::lean_ctor_set(v___x_4151_, 2, v_v_4156_);
                    leanh::lean_ctor_set(v___x_4151_, 1, v_k_4155_);
                    leanh::lean_ctor_set(v___x_4151_, 0, v___x_4196_);
                    v___x_4198_ = v___x_4151_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_4202_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4202_, 0, v___x_4196_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4202_, 1, v_k_4155_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4202_, 2, v_v_4156_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4202_, 3, v_tree_4154_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4202_, 4, v_l_4172_);
                    v___x_4198_ = v_reuseFailAlloc_4202_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                v___x_4199_ = lean_nat_add(v___x_4148_, v_size_4174_);
                if leanh::lean_obj_tag(v_r_4173_) == 0 {
                    v_size_4200_ = leanh::lean_ctor_get(v_r_4173_, 0);
                    leanh::lean_inc(v_size_4200_);
                    v___y_4184_ = v___x_4199_;
                    v___y_4185_ = v___x_4198_;
                    v___y_4186_ = v_size_4200_;
                    state = 33;
                    continue;
                } else {
                    v___x_4201_ = leanh::lean_unsigned_to_nat(0);
                    v___y_4184_ = v___x_4199_;
                    v___y_4185_ = v___x_4198_;
                    v___y_4186_ = v___x_4201_;
                    state = 33;
                    continue;
                }
            }
            38 => {
                if v_isShared_4152_ == 0 {
                    leanh::lean_ctor_set(v___x_4151_, 4, v_r_4147_);
                    leanh::lean_ctor_set(v___x_4151_, 3, v___x_4215_);
                    leanh::lean_ctor_set(v___x_4151_, 2, v_v_4145_);
                    leanh::lean_ctor_set(v___x_4151_, 1, v_k_4144_);
                    leanh::lean_ctor_set(v___x_4151_, 0, v___x_4212_);
                    v___x_4217_ = v___x_4151_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_4218_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 0, v___x_4212_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 1, v_k_4144_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 2, v_v_4145_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 3, v___x_4215_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 4, v_r_4147_);
                    v___x_4217_ = v_reuseFailAlloc_4218_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_4217_;
            }
            40 => {
                if leanh::lean_obj_tag(v_l_4146_) == 0 {
                    if leanh::lean_obj_tag(v_r_4147_) == 0 {
                        v_k_4229_ = leanh::lean_ctor_get(v___x_4153_, 0);
                        leanh::lean_inc(v_k_4229_);
                        v_v_4230_ = leanh::lean_ctor_get(v___x_4153_, 1);
                        leanh::lean_inc(v_v_4230_);
                        leanh::lean_dec_ref(v___x_4153_);
                        v_size_4231_ = leanh::lean_ctor_get(v_l_4146_, 0);
                        v___x_4232_ = lean_nat_add(v___x_4148_, v_size_4143_);
                        leanh::lean_dec(v_size_4143_);
                        v___x_4233_ = lean_nat_add(v___x_4148_, v_size_4231_);
                        if v_isShared_4228_ == 0 {
                            leanh::lean_ctor_set(v___x_4227_, 4, v_l_4146_);
                            leanh::lean_ctor_set(v___x_4227_, 3, v_tree_4154_);
                            leanh::lean_ctor_set(v___x_4227_, 2, v_v_4230_);
                            leanh::lean_ctor_set(v___x_4227_, 1, v_k_4229_);
                            leanh::lean_ctor_set(v___x_4227_, 0, v___x_4233_);
                            v___x_4235_ = v___x_4227_;
                            state = 41;
                            continue;
                        } else {
                            v_reuseFailAlloc_4239_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4239_, 0, v___x_4233_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4239_, 1, v_k_4229_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4239_, 2, v_v_4230_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4239_, 3, v_tree_4154_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4239_, 4, v_l_4146_);
                            v___x_4235_ = v_reuseFailAlloc_4239_;
                            state = 41;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_size_4143_);
                        v_k_4240_ = leanh::lean_ctor_get(v___x_4153_, 0);
                        leanh::lean_inc(v_k_4240_);
                        v_v_4241_ = leanh::lean_ctor_get(v___x_4153_, 1);
                        leanh::lean_inc(v_v_4241_);
                        leanh::lean_dec_ref(v___x_4153_);
                        v_k_4242_ = leanh::lean_ctor_get(v_l_4146_, 1);
                        v_v_4243_ = leanh::lean_ctor_get(v_l_4146_, 2);
                        v_isSharedCheck_4257_ = (!leanh::lean_is_exclusive(v_l_4146_)) as u8;
                        if v_isSharedCheck_4257_ == 0 {
                            v_unused_4258_ = leanh::lean_ctor_get(v_l_4146_, 4);
                            leanh::lean_dec(v_unused_4258_);
                            v_unused_4259_ = leanh::lean_ctor_get(v_l_4146_, 3);
                            leanh::lean_dec(v_unused_4259_);
                            v_unused_4260_ = leanh::lean_ctor_get(v_l_4146_, 0);
                            leanh::lean_dec(v_unused_4260_);
                            v___x_4245_ = v_l_4146_;
                            v_isShared_4246_ = v_isSharedCheck_4257_;
                            state = 43;
                            continue;
                        } else {
                            leanh::lean_inc(v_v_4243_);
                            leanh::lean_inc(v_k_4242_);
                            leanh::lean_dec(v_l_4146_);
                            v___x_4245_ = leanh::lean_box(0);
                            v_isShared_4246_ = v_isSharedCheck_4257_;
                            state = 43;
                            continue;
                        }
                    }
                } else {
                    if leanh::lean_obj_tag(v_r_4147_) == 0 {
                        leanh::lean_dec(v_size_4143_);
                        v_k_4261_ = leanh::lean_ctor_get(v___x_4153_, 0);
                        leanh::lean_inc(v_k_4261_);
                        v_v_4262_ = leanh::lean_ctor_get(v___x_4153_, 1);
                        leanh::lean_inc(v_v_4262_);
                        leanh::lean_dec_ref(v___x_4153_);
                        v___x_4263_ = leanh::lean_unsigned_to_nat(3);
                        if v_isShared_4228_ == 0 {
                            leanh::lean_ctor_set(v___x_4227_, 4, v_l_4146_);
                            leanh::lean_ctor_set(v___x_4227_, 2, v_v_4262_);
                            leanh::lean_ctor_set(v___x_4227_, 1, v_k_4261_);
                            leanh::lean_ctor_set(v___x_4227_, 0, v___x_4148_);
                            v___x_4265_ = v___x_4227_;
                            state = 47;
                            continue;
                        } else {
                            v_reuseFailAlloc_4269_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 0, v___x_4148_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 1, v_k_4261_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 2, v_v_4262_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 3, v_l_4146_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 4, v_l_4146_);
                            v___x_4265_ = v_reuseFailAlloc_4269_;
                            state = 47;
                            continue;
                        }
                    } else {
                        v_k_4270_ = leanh::lean_ctor_get(v___x_4153_, 0);
                        leanh::lean_inc(v_k_4270_);
                        v_v_4271_ = leanh::lean_ctor_get(v___x_4153_, 1);
                        leanh::lean_inc(v_v_4271_);
                        leanh::lean_dec_ref(v___x_4153_);
                        if v_isShared_4228_ == 0 {
                            leanh::lean_ctor_set(v___x_4227_, 3, v_r_4147_);
                            v___x_4273_ = v___x_4227_;
                            state = 49;
                            continue;
                        } else {
                            v_reuseFailAlloc_4278_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4278_, 0, v_size_4143_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4278_, 1, v_k_4144_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4278_, 2, v_v_4145_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4278_, 3, v_r_4147_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4278_, 4, v_r_4147_);
                            v___x_4273_ = v_reuseFailAlloc_4278_;
                            state = 49;
                            continue;
                        }
                    }
                }
            }
            41 => {
                if v_isShared_4152_ == 0 {
                    leanh::lean_ctor_set(v___x_4151_, 4, v_r_4147_);
                    leanh::lean_ctor_set(v___x_4151_, 3, v___x_4235_);
                    leanh::lean_ctor_set(v___x_4151_, 2, v_v_4145_);
                    leanh::lean_ctor_set(v___x_4151_, 1, v_k_4144_);
                    leanh::lean_ctor_set(v___x_4151_, 0, v___x_4232_);
                    v___x_4237_ = v___x_4151_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_4238_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4238_, 0, v___x_4232_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4238_, 1, v_k_4144_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4238_, 2, v_v_4145_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4238_, 3, v___x_4235_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4238_, 4, v_r_4147_);
                    v___x_4237_ = v_reuseFailAlloc_4238_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_4237_;
            }
            43 => {
                v___x_4247_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_4246_ == 0 {
                    leanh::lean_ctor_set(v___x_4245_, 4, v_r_4147_);
                    leanh::lean_ctor_set(v___x_4245_, 3, v_r_4147_);
                    leanh::lean_ctor_set(v___x_4245_, 2, v_v_4241_);
                    leanh::lean_ctor_set(v___x_4245_, 1, v_k_4240_);
                    leanh::lean_ctor_set(v___x_4245_, 0, v___x_4148_);
                    v___x_4249_ = v___x_4245_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_4256_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4256_, 0, v___x_4148_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4256_, 1, v_k_4240_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4256_, 2, v_v_4241_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4256_, 3, v_r_4147_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4256_, 4, v_r_4147_);
                    v___x_4249_ = v_reuseFailAlloc_4256_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                if v_isShared_4228_ == 0 {
                    leanh::lean_ctor_set(v___x_4227_, 3, v_r_4147_);
                    leanh::lean_ctor_set(v___x_4227_, 0, v___x_4148_);
                    v___x_4251_ = v___x_4227_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_4255_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4255_, 0, v___x_4148_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4255_, 1, v_k_4144_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4255_, 2, v_v_4145_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4255_, 3, v_r_4147_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4255_, 4, v_r_4147_);
                    v___x_4251_ = v_reuseFailAlloc_4255_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_4152_ == 0 {
                    leanh::lean_ctor_set(v___x_4151_, 4, v___x_4251_);
                    leanh::lean_ctor_set(v___x_4151_, 3, v___x_4249_);
                    leanh::lean_ctor_set(v___x_4151_, 2, v_v_4243_);
                    leanh::lean_ctor_set(v___x_4151_, 1, v_k_4242_);
                    leanh::lean_ctor_set(v___x_4151_, 0, v___x_4247_);
                    v___x_4253_ = v___x_4151_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_4254_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4254_, 0, v___x_4247_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4254_, 1, v_k_4242_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4254_, 2, v_v_4243_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4254_, 3, v___x_4249_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4254_, 4, v___x_4251_);
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
                    leanh::lean_ctor_set(v___x_4151_, 4, v_r_4147_);
                    leanh::lean_ctor_set(v___x_4151_, 3, v___x_4265_);
                    leanh::lean_ctor_set(v___x_4151_, 2, v_v_4145_);
                    leanh::lean_ctor_set(v___x_4151_, 1, v_k_4144_);
                    leanh::lean_ctor_set(v___x_4151_, 0, v___x_4263_);
                    v___x_4267_ = v___x_4151_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_4268_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4268_, 0, v___x_4263_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4268_, 1, v_k_4144_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4268_, 2, v_v_4145_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4268_, 3, v___x_4265_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4268_, 4, v_r_4147_);
                    v___x_4267_ = v_reuseFailAlloc_4268_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_4267_;
            }
            49 => {
                v___x_4274_ = leanh::lean_unsigned_to_nat(2);
                if v_isShared_4152_ == 0 {
                    leanh::lean_ctor_set(v___x_4151_, 4, v___x_4273_);
                    leanh::lean_ctor_set(v___x_4151_, 3, v_r_4147_);
                    leanh::lean_ctor_set(v___x_4151_, 2, v_v_4271_);
                    leanh::lean_ctor_set(v___x_4151_, 1, v_k_4270_);
                    leanh::lean_ctor_set(v___x_4151_, 0, v___x_4274_);
                    v___x_4276_ = v___x_4151_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_4277_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4277_, 0, v___x_4274_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4277_, 1, v_k_4270_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4277_, 2, v_v_4271_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4277_, 3, v_r_4147_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4277_, 4, v___x_4273_);
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
                v_tree_4295_ = leanh::lean_ctor_get(v___x_4294_, 2);
                leanh::lean_inc(v_tree_4295_);
                if leanh::lean_obj_tag(v_tree_4295_) == 0 {
                    v_k_4296_ = leanh::lean_ctor_get(v___x_4294_, 0);
                    leanh::lean_inc(v_k_4296_);
                    v_v_4297_ = leanh::lean_ctor_get(v___x_4294_, 1);
                    leanh::lean_inc(v_v_4297_);
                    leanh::lean_dec_ref(v___x_4294_);
                    v_size_4298_ = leanh::lean_ctor_get(v_tree_4295_, 0);
                    v___x_4299_ = leanh::lean_unsigned_to_nat(3);
                    v___x_4300_ = lean_nat_mul(v___x_4299_, v_size_4298_);
                    v___x_4301_ = lean_nat_dec_lt(v___x_4300_, v_size_4138_);
                    leanh::lean_dec(v___x_4300_);
                    if v___x_4301_ == 0 {
                        leanh::lean_dec(v_r_4142_);
                        v___x_4302_ = lean_nat_add(v___x_4148_, v_size_4138_);
                        v___x_4303_ = lean_nat_add(v___x_4302_, v_size_4298_);
                        leanh::lean_dec(v___x_4302_);
                        if v_isShared_4293_ == 0 {
                            leanh::lean_ctor_set(v___x_4292_, 4, v_tree_4295_);
                            leanh::lean_ctor_set(v___x_4292_, 3, v_l_3958_);
                            leanh::lean_ctor_set(v___x_4292_, 2, v_v_4297_);
                            leanh::lean_ctor_set(v___x_4292_, 1, v_k_4296_);
                            leanh::lean_ctor_set(v___x_4292_, 0, v___x_4303_);
                            v___x_4305_ = v___x_4292_;
                            state = 52;
                            continue;
                        } else {
                            v_reuseFailAlloc_4306_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4306_, 0, v___x_4303_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4306_, 1, v_k_4296_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4306_, 2, v_v_4297_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4306_, 3, v_l_3958_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4306_, 4, v_tree_4295_);
                            v___x_4305_ = v_reuseFailAlloc_4306_;
                            state = 52;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_l_4141_);
                        leanh::lean_inc(v_v_4140_);
                        leanh::lean_inc(v_k_4139_);
                        leanh::lean_inc(v_size_4138_);
                        v_isSharedCheck_4372_ = (!leanh::lean_is_exclusive(v_l_3958_)) as u8;
                        if v_isSharedCheck_4372_ == 0 {
                            v_unused_4373_ = leanh::lean_ctor_get(v_l_3958_, 4);
                            leanh::lean_dec(v_unused_4373_);
                            v_unused_4374_ = leanh::lean_ctor_get(v_l_3958_, 3);
                            leanh::lean_dec(v_unused_4374_);
                            v_unused_4375_ = leanh::lean_ctor_get(v_l_3958_, 2);
                            leanh::lean_dec(v_unused_4375_);
                            v_unused_4376_ = leanh::lean_ctor_get(v_l_3958_, 1);
                            leanh::lean_dec(v_unused_4376_);
                            v_unused_4377_ = leanh::lean_ctor_get(v_l_3958_, 0);
                            leanh::lean_dec(v_unused_4377_);
                            v___x_4308_ = v_l_3958_;
                            v_isShared_4309_ = v_isSharedCheck_4372_;
                            state = 53;
                            continue;
                        } else {
                            leanh::lean_dec(v_l_3958_);
                            v___x_4308_ = leanh::lean_box(0);
                            v_isShared_4309_ = v_isSharedCheck_4372_;
                            state = 53;
                            continue;
                        }
                    }
                } else {
                    if leanh::lean_obj_tag(v_l_4141_) == 0 {
                        leanh::lean_inc_ref(v_l_4141_);
                        leanh::lean_inc(v_v_4140_);
                        leanh::lean_inc(v_k_4139_);
                        leanh::lean_inc(v_size_4138_);
                        v_isSharedCheck_4401_ = (!leanh::lean_is_exclusive(v_l_3958_)) as u8;
                        if v_isSharedCheck_4401_ == 0 {
                            v_unused_4402_ = leanh::lean_ctor_get(v_l_3958_, 4);
                            leanh::lean_dec(v_unused_4402_);
                            v_unused_4403_ = leanh::lean_ctor_get(v_l_3958_, 3);
                            leanh::lean_dec(v_unused_4403_);
                            v_unused_4404_ = leanh::lean_ctor_get(v_l_3958_, 2);
                            leanh::lean_dec(v_unused_4404_);
                            v_unused_4405_ = leanh::lean_ctor_get(v_l_3958_, 1);
                            leanh::lean_dec(v_unused_4405_);
                            v_unused_4406_ = leanh::lean_ctor_get(v_l_3958_, 0);
                            leanh::lean_dec(v_unused_4406_);
                            v___x_4379_ = v_l_3958_;
                            v_isShared_4380_ = v_isSharedCheck_4401_;
                            state = 63;
                            continue;
                        } else {
                            leanh::lean_dec(v_l_3958_);
                            v___x_4379_ = leanh::lean_box(0);
                            v_isShared_4380_ = v_isSharedCheck_4401_;
                            state = 63;
                            continue;
                        }
                    } else {
                        if leanh::lean_obj_tag(v_r_4142_) == 0 {
                            leanh::lean_inc(v_l_4141_);
                            leanh::lean_inc(v_v_4140_);
                            leanh::lean_inc(v_k_4139_);
                            v_isSharedCheck_4431_ =
                                (!leanh::lean_is_exclusive(v_l_3958_)) as u8;
                            if v_isSharedCheck_4431_ == 0 {
                                v_unused_4432_ = leanh::lean_ctor_get(v_l_3958_, 4);
                                leanh::lean_dec(v_unused_4432_);
                                v_unused_4433_ = leanh::lean_ctor_get(v_l_3958_, 3);
                                leanh::lean_dec(v_unused_4433_);
                                v_unused_4434_ = leanh::lean_ctor_get(v_l_3958_, 2);
                                leanh::lean_dec(v_unused_4434_);
                                v_unused_4435_ = leanh::lean_ctor_get(v_l_3958_, 1);
                                leanh::lean_dec(v_unused_4435_);
                                v_unused_4436_ = leanh::lean_ctor_get(v_l_3958_, 0);
                                leanh::lean_dec(v_unused_4436_);
                                v___x_4408_ = v_l_3958_;
                                v_isShared_4409_ = v_isSharedCheck_4431_;
                                state = 68;
                                continue;
                            } else {
                                leanh::lean_dec(v_l_3958_);
                                v___x_4408_ = leanh::lean_box(0);
                                v_isShared_4409_ = v_isSharedCheck_4431_;
                                state = 68;
                                continue;
                            }
                        } else {
                            v_k_4437_ = leanh::lean_ctor_get(v___x_4294_, 0);
                            leanh::lean_inc(v_k_4437_);
                            v_v_4438_ = leanh::lean_ctor_get(v___x_4294_, 1);
                            leanh::lean_inc(v_v_4438_);
                            leanh::lean_dec_ref(v___x_4294_);
                            v___x_4439_ = leanh::lean_unsigned_to_nat(2);
                            if v_isShared_4293_ == 0 {
                                leanh::lean_ctor_set(v___x_4292_, 4, v_r_4142_);
                                leanh::lean_ctor_set(v___x_4292_, 3, v_l_3958_);
                                leanh::lean_ctor_set(v___x_4292_, 2, v_v_4438_);
                                leanh::lean_ctor_set(v___x_4292_, 1, v_k_4437_);
                                leanh::lean_ctor_set(v___x_4292_, 0, v___x_4439_);
                                v___x_4441_ = v___x_4292_;
                                state = 73;
                                continue;
                            } else {
                                v_reuseFailAlloc_4442_ =
                                    leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_4442_, 0, v___x_4439_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_4442_, 1, v_k_4437_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_4442_, 2, v_v_4438_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_4442_, 3, v_l_3958_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_4442_, 4, v_r_4142_);
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
                v_size_4310_ = leanh::lean_ctor_get(v_l_4141_, 0);
                v_size_4311_ = leanh::lean_ctor_get(v_r_4142_, 0);
                v_k_4312_ = leanh::lean_ctor_get(v_r_4142_, 1);
                v_v_4313_ = leanh::lean_ctor_get(v_r_4142_, 2);
                v_l_4314_ = leanh::lean_ctor_get(v_r_4142_, 3);
                v_r_4315_ = leanh::lean_ctor_get(v_r_4142_, 4);
                v___x_4316_ = leanh::lean_unsigned_to_nat(2);
                v___x_4317_ = lean_nat_mul(v___x_4316_, v_size_4310_);
                v___x_4318_ = lean_nat_dec_lt(v_size_4311_, v___x_4317_);
                leanh::lean_dec(v___x_4317_);
                if v___x_4318_ == 0 {
                    leanh::lean_inc(v_r_4315_);
                    leanh::lean_inc(v_l_4314_);
                    leanh::lean_inc(v_v_4313_);
                    leanh::lean_inc(v_k_4312_);
                    leanh::lean_del_object(v___x_4308_);
                    v_isSharedCheck_4356_ = (!leanh::lean_is_exclusive(v_r_4142_)) as u8;
                    if v_isSharedCheck_4356_ == 0 {
                        v_unused_4357_ = leanh::lean_ctor_get(v_r_4142_, 4);
                        leanh::lean_dec(v_unused_4357_);
                        v_unused_4358_ = leanh::lean_ctor_get(v_r_4142_, 3);
                        leanh::lean_dec(v_unused_4358_);
                        v_unused_4359_ = leanh::lean_ctor_get(v_r_4142_, 2);
                        leanh::lean_dec(v_unused_4359_);
                        v_unused_4360_ = leanh::lean_ctor_get(v_r_4142_, 1);
                        leanh::lean_dec(v_unused_4360_);
                        v_unused_4361_ = leanh::lean_ctor_get(v_r_4142_, 0);
                        leanh::lean_dec(v_unused_4361_);
                        v___x_4320_ = v_r_4142_;
                        v_isShared_4321_ = v_isSharedCheck_4356_;
                        state = 54;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_4142_);
                        v___x_4320_ = leanh::lean_box(0);
                        v_isShared_4321_ = v_isSharedCheck_4356_;
                        state = 54;
                        continue;
                    }
                } else {
                    v___x_4362_ = lean_nat_add(v___x_4148_, v_size_4138_);
                    leanh::lean_dec(v_size_4138_);
                    v___x_4363_ = lean_nat_add(v___x_4362_, v_size_4298_);
                    leanh::lean_dec(v___x_4362_);
                    v___x_4364_ = lean_nat_add(v___x_4148_, v_size_4298_);
                    v___x_4365_ = lean_nat_add(v___x_4364_, v_size_4311_);
                    leanh::lean_dec(v___x_4364_);
                    if v_isShared_4293_ == 0 {
                        leanh::lean_ctor_set(v___x_4292_, 4, v_tree_4295_);
                        leanh::lean_ctor_set(v___x_4292_, 3, v_r_4142_);
                        leanh::lean_ctor_set(v___x_4292_, 2, v_v_4297_);
                        leanh::lean_ctor_set(v___x_4292_, 1, v_k_4296_);
                        leanh::lean_ctor_set(v___x_4292_, 0, v___x_4365_);
                        v___x_4367_ = v___x_4292_;
                        state = 61;
                        continue;
                    } else {
                        v_reuseFailAlloc_4371_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4371_, 0, v___x_4365_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4371_, 1, v_k_4296_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4371_, 2, v_v_4297_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4371_, 3, v_r_4142_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4371_, 4, v_tree_4295_);
                        v___x_4367_ = v_reuseFailAlloc_4371_;
                        state = 61;
                        continue;
                    }
                }
            }
            54 => {
                v___x_4322_ = lean_nat_add(v___x_4148_, v_size_4138_);
                leanh::lean_dec(v_size_4138_);
                v___x_4323_ = lean_nat_add(v___x_4322_, v_size_4298_);
                leanh::lean_dec(v___x_4322_);
                v___x_4344_ = lean_nat_add(v___x_4148_, v_size_4310_);
                if leanh::lean_obj_tag(v_l_4314_) == 0 {
                    v_size_4354_ = leanh::lean_ctor_get(v_l_4314_, 0);
                    leanh::lean_inc(v_size_4354_);
                    v___y_4346_ = v_size_4354_;
                    state = 59;
                    continue;
                } else {
                    v___x_4355_ = leanh::lean_unsigned_to_nat(0);
                    v___y_4346_ = v___x_4355_;
                    state = 59;
                    continue;
                }
            }
            55 => {
                v___x_4328_ = lean_nat_add(v___y_4326_, v___y_4327_);
                leanh::lean_dec(v___y_4327_);
                leanh::lean_dec(v___y_4326_);
                leanh::lean_inc_ref(v_tree_4295_);
                if v_isShared_4321_ == 0 {
                    leanh::lean_ctor_set(v___x_4320_, 4, v_tree_4295_);
                    leanh::lean_ctor_set(v___x_4320_, 3, v_r_4315_);
                    leanh::lean_ctor_set(v___x_4320_, 2, v_v_4297_);
                    leanh::lean_ctor_set(v___x_4320_, 1, v_k_4296_);
                    leanh::lean_ctor_set(v___x_4320_, 0, v___x_4328_);
                    v___x_4330_ = v___x_4320_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_4343_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4343_, 0, v___x_4328_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4343_, 1, v_k_4296_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4343_, 2, v_v_4297_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4343_, 3, v_r_4315_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4343_, 4, v_tree_4295_);
                    v___x_4330_ = v_reuseFailAlloc_4343_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                v_isSharedCheck_4337_ = (!leanh::lean_is_exclusive(v_tree_4295_)) as u8;
                if v_isSharedCheck_4337_ == 0 {
                    v_unused_4338_ = leanh::lean_ctor_get(v_tree_4295_, 4);
                    leanh::lean_dec(v_unused_4338_);
                    v_unused_4339_ = leanh::lean_ctor_get(v_tree_4295_, 3);
                    leanh::lean_dec(v_unused_4339_);
                    v_unused_4340_ = leanh::lean_ctor_get(v_tree_4295_, 2);
                    leanh::lean_dec(v_unused_4340_);
                    v_unused_4341_ = leanh::lean_ctor_get(v_tree_4295_, 1);
                    leanh::lean_dec(v_unused_4341_);
                    v_unused_4342_ = leanh::lean_ctor_get(v_tree_4295_, 0);
                    leanh::lean_dec(v_unused_4342_);
                    v___x_4332_ = v_tree_4295_;
                    v_isShared_4333_ = v_isSharedCheck_4337_;
                    state = 57;
                    continue;
                } else {
                    leanh::lean_dec(v_tree_4295_);
                    v___x_4332_ = leanh::lean_box(0);
                    v_isShared_4333_ = v_isSharedCheck_4337_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                if v_isShared_4333_ == 0 {
                    leanh::lean_ctor_set(v___x_4332_, 4, v___x_4330_);
                    leanh::lean_ctor_set(v___x_4332_, 3, v___y_4325_);
                    leanh::lean_ctor_set(v___x_4332_, 2, v_v_4313_);
                    leanh::lean_ctor_set(v___x_4332_, 1, v_k_4312_);
                    leanh::lean_ctor_set(v___x_4332_, 0, v___x_4323_);
                    v___x_4335_ = v___x_4332_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_4336_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4336_, 0, v___x_4323_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4336_, 1, v_k_4312_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4336_, 2, v_v_4313_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4336_, 3, v___y_4325_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4336_, 4, v___x_4330_);
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
                leanh::lean_dec(v___y_4346_);
                leanh::lean_dec(v___x_4344_);
                if v_isShared_4293_ == 0 {
                    leanh::lean_ctor_set(v___x_4292_, 4, v_l_4314_);
                    leanh::lean_ctor_set(v___x_4292_, 3, v_l_4141_);
                    leanh::lean_ctor_set(v___x_4292_, 2, v_v_4140_);
                    leanh::lean_ctor_set(v___x_4292_, 1, v_k_4139_);
                    leanh::lean_ctor_set(v___x_4292_, 0, v___x_4347_);
                    v___x_4349_ = v___x_4292_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_4353_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4353_, 0, v___x_4347_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4353_, 1, v_k_4139_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4353_, 2, v_v_4140_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4353_, 3, v_l_4141_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4353_, 4, v_l_4314_);
                    v___x_4349_ = v_reuseFailAlloc_4353_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                v___x_4350_ = lean_nat_add(v___x_4148_, v_size_4298_);
                if leanh::lean_obj_tag(v_r_4315_) == 0 {
                    v_size_4351_ = leanh::lean_ctor_get(v_r_4315_, 0);
                    leanh::lean_inc(v_size_4351_);
                    v___y_4325_ = v___x_4349_;
                    v___y_4326_ = v___x_4350_;
                    v___y_4327_ = v_size_4351_;
                    state = 55;
                    continue;
                } else {
                    v___x_4352_ = leanh::lean_unsigned_to_nat(0);
                    v___y_4325_ = v___x_4349_;
                    v___y_4326_ = v___x_4350_;
                    v___y_4327_ = v___x_4352_;
                    state = 55;
                    continue;
                }
            }
            61 => {
                if v_isShared_4309_ == 0 {
                    leanh::lean_ctor_set(v___x_4308_, 4, v___x_4367_);
                    leanh::lean_ctor_set(v___x_4308_, 0, v___x_4363_);
                    v___x_4369_ = v___x_4308_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_4370_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4370_, 0, v___x_4363_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4370_, 1, v_k_4139_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4370_, 2, v_v_4140_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4370_, 3, v_l_4141_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4370_, 4, v___x_4367_);
                    v___x_4369_ = v_reuseFailAlloc_4370_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                return v___x_4369_;
            }
            63 => {
                if leanh::lean_obj_tag(v_r_4142_) == 0 {
                    v_k_4381_ = leanh::lean_ctor_get(v___x_4294_, 0);
                    leanh::lean_inc(v_k_4381_);
                    v_v_4382_ = leanh::lean_ctor_get(v___x_4294_, 1);
                    leanh::lean_inc(v_v_4382_);
                    leanh::lean_dec_ref(v___x_4294_);
                    v_size_4383_ = leanh::lean_ctor_get(v_r_4142_, 0);
                    v___x_4384_ = lean_nat_add(v___x_4148_, v_size_4138_);
                    leanh::lean_dec(v_size_4138_);
                    v___x_4385_ = lean_nat_add(v___x_4148_, v_size_4383_);
                    if v_isShared_4293_ == 0 {
                        leanh::lean_ctor_set(v___x_4292_, 4, v_tree_4295_);
                        leanh::lean_ctor_set(v___x_4292_, 3, v_r_4142_);
                        leanh::lean_ctor_set(v___x_4292_, 2, v_v_4382_);
                        leanh::lean_ctor_set(v___x_4292_, 1, v_k_4381_);
                        leanh::lean_ctor_set(v___x_4292_, 0, v___x_4385_);
                        v___x_4387_ = v___x_4292_;
                        state = 64;
                        continue;
                    } else {
                        v_reuseFailAlloc_4391_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4391_, 0, v___x_4385_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4391_, 1, v_k_4381_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4391_, 2, v_v_4382_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4391_, 3, v_r_4142_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4391_, 4, v_tree_4295_);
                        v___x_4387_ = v_reuseFailAlloc_4391_;
                        state = 64;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_size_4138_);
                    v_k_4392_ = leanh::lean_ctor_get(v___x_4294_, 0);
                    leanh::lean_inc(v_k_4392_);
                    v_v_4393_ = leanh::lean_ctor_get(v___x_4294_, 1);
                    leanh::lean_inc(v_v_4393_);
                    leanh::lean_dec_ref(v___x_4294_);
                    v___x_4394_ = leanh::lean_unsigned_to_nat(3);
                    if v_isShared_4293_ == 0 {
                        leanh::lean_ctor_set(v___x_4292_, 4, v_r_4142_);
                        leanh::lean_ctor_set(v___x_4292_, 3, v_r_4142_);
                        leanh::lean_ctor_set(v___x_4292_, 2, v_v_4393_);
                        leanh::lean_ctor_set(v___x_4292_, 1, v_k_4392_);
                        leanh::lean_ctor_set(v___x_4292_, 0, v___x_4148_);
                        v___x_4396_ = v___x_4292_;
                        state = 66;
                        continue;
                    } else {
                        v_reuseFailAlloc_4400_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4400_, 0, v___x_4148_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4400_, 1, v_k_4392_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4400_, 2, v_v_4393_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4400_, 3, v_r_4142_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4400_, 4, v_r_4142_);
                        v___x_4396_ = v_reuseFailAlloc_4400_;
                        state = 66;
                        continue;
                    }
                }
            }
            64 => {
                if v_isShared_4380_ == 0 {
                    leanh::lean_ctor_set(v___x_4379_, 4, v___x_4387_);
                    leanh::lean_ctor_set(v___x_4379_, 0, v___x_4384_);
                    v___x_4389_ = v___x_4379_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_4390_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4390_, 0, v___x_4384_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4390_, 1, v_k_4139_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4390_, 2, v_v_4140_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4390_, 3, v_l_4141_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4390_, 4, v___x_4387_);
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
                    leanh::lean_ctor_set(v___x_4379_, 4, v___x_4396_);
                    leanh::lean_ctor_set(v___x_4379_, 0, v___x_4394_);
                    v___x_4398_ = v___x_4379_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_4399_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4399_, 0, v___x_4394_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4399_, 1, v_k_4139_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4399_, 2, v_v_4140_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4399_, 3, v_l_4141_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4399_, 4, v___x_4396_);
                    v___x_4398_ = v_reuseFailAlloc_4399_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_4398_;
            }
            68 => {
                v_k_4410_ = leanh::lean_ctor_get(v___x_4294_, 0);
                leanh::lean_inc(v_k_4410_);
                v_v_4411_ = leanh::lean_ctor_get(v___x_4294_, 1);
                leanh::lean_inc(v_v_4411_);
                leanh::lean_dec_ref(v___x_4294_);
                v_k_4412_ = leanh::lean_ctor_get(v_r_4142_, 1);
                v_v_4413_ = leanh::lean_ctor_get(v_r_4142_, 2);
                v_isSharedCheck_4427_ = (!leanh::lean_is_exclusive(v_r_4142_)) as u8;
                if v_isSharedCheck_4427_ == 0 {
                    v_unused_4428_ = leanh::lean_ctor_get(v_r_4142_, 4);
                    leanh::lean_dec(v_unused_4428_);
                    v_unused_4429_ = leanh::lean_ctor_get(v_r_4142_, 3);
                    leanh::lean_dec(v_unused_4429_);
                    v_unused_4430_ = leanh::lean_ctor_get(v_r_4142_, 0);
                    leanh::lean_dec(v_unused_4430_);
                    v___x_4415_ = v_r_4142_;
                    v_isShared_4416_ = v_isSharedCheck_4427_;
                    state = 69;
                    continue;
                } else {
                    leanh::lean_inc(v_v_4413_);
                    leanh::lean_inc(v_k_4412_);
                    leanh::lean_dec(v_r_4142_);
                    v___x_4415_ = leanh::lean_box(0);
                    v_isShared_4416_ = v_isSharedCheck_4427_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                v___x_4417_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_4416_ == 0 {
                    leanh::lean_ctor_set(v___x_4415_, 4, v_l_4141_);
                    leanh::lean_ctor_set(v___x_4415_, 3, v_l_4141_);
                    leanh::lean_ctor_set(v___x_4415_, 2, v_v_4140_);
                    leanh::lean_ctor_set(v___x_4415_, 1, v_k_4139_);
                    leanh::lean_ctor_set(v___x_4415_, 0, v___x_4148_);
                    v___x_4419_ = v___x_4415_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_4426_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4426_, 0, v___x_4148_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4426_, 1, v_k_4139_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4426_, 2, v_v_4140_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4426_, 3, v_l_4141_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4426_, 4, v_l_4141_);
                    v___x_4419_ = v_reuseFailAlloc_4426_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                if v_isShared_4293_ == 0 {
                    leanh::lean_ctor_set(v___x_4292_, 4, v_l_4141_);
                    leanh::lean_ctor_set(v___x_4292_, 3, v_l_4141_);
                    leanh::lean_ctor_set(v___x_4292_, 2, v_v_4411_);
                    leanh::lean_ctor_set(v___x_4292_, 1, v_k_4410_);
                    leanh::lean_ctor_set(v___x_4292_, 0, v___x_4148_);
                    v___x_4421_ = v___x_4292_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_4425_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4148_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4425_, 1, v_k_4410_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4425_, 2, v_v_4411_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4425_, 3, v_l_4141_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4425_, 4, v_l_4141_);
                    v___x_4421_ = v_reuseFailAlloc_4425_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                if v_isShared_4409_ == 0 {
                    leanh::lean_ctor_set(v___x_4408_, 4, v___x_4421_);
                    leanh::lean_ctor_set(v___x_4408_, 3, v___x_4419_);
                    leanh::lean_ctor_set(v___x_4408_, 2, v_v_4413_);
                    leanh::lean_ctor_set(v___x_4408_, 1, v_k_4412_);
                    leanh::lean_ctor_set(v___x_4408_, 0, v___x_4417_);
                    v___x_4423_ = v___x_4408_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_4424_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4424_, 0, v___x_4417_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4424_, 1, v_k_4412_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4424_, 2, v_v_4413_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4424_, 3, v___x_4419_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4424_, 4, v___x_4421_);
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
                v_size_4468_ = leanh::lean_ctor_get(v_l_4455_, 0);
                v_size_4469_ = leanh::lean_ctor_get(v_r_4456_, 0);
                v_k_4470_ = leanh::lean_ctor_get(v_r_4456_, 1);
                v_v_4471_ = leanh::lean_ctor_get(v_r_4456_, 2);
                v_l_4472_ = leanh::lean_ctor_get(v_r_4456_, 3);
                v_r_4473_ = leanh::lean_ctor_get(v_r_4456_, 4);
                v___x_4474_ = leanh::lean_unsigned_to_nat(2);
                v___x_4475_ = lean_nat_mul(v___x_4474_, v_size_4468_);
                v___x_4476_ = lean_nat_dec_lt(v_size_4469_, v___x_4475_);
                leanh::lean_dec(v___x_4475_);
                if v___x_4476_ == 0 {
                    leanh::lean_inc(v_r_4473_);
                    leanh::lean_inc(v_l_4472_);
                    leanh::lean_inc(v_v_4471_);
                    leanh::lean_inc(v_k_4470_);
                    v_isSharedCheck_4505_ = (!leanh::lean_is_exclusive(v_r_4456_)) as u8;
                    if v_isSharedCheck_4505_ == 0 {
                        v_unused_4506_ = leanh::lean_ctor_get(v_r_4456_, 4);
                        leanh::lean_dec(v_unused_4506_);
                        v_unused_4507_ = leanh::lean_ctor_get(v_r_4456_, 3);
                        leanh::lean_dec(v_unused_4507_);
                        v_unused_4508_ = leanh::lean_ctor_get(v_r_4456_, 2);
                        leanh::lean_dec(v_unused_4508_);
                        v_unused_4509_ = leanh::lean_ctor_get(v_r_4456_, 1);
                        leanh::lean_dec(v_unused_4509_);
                        v_unused_4510_ = leanh::lean_ctor_get(v_r_4456_, 0);
                        leanh::lean_dec(v_unused_4510_);
                        v___x_4478_ = v_r_4456_;
                        v_isShared_4479_ = v_isSharedCheck_4505_;
                        state = 76;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_4456_);
                        v___x_4478_ = leanh::lean_box(0);
                        v_isShared_4479_ = v_isSharedCheck_4505_;
                        state = 76;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3961_);
                    v___x_4511_ = lean_nat_add(v___x_4450_, v_size_4452_);
                    leanh::lean_dec(v_size_4452_);
                    v___x_4512_ = lean_nat_add(v___x_4511_, v_size_4451_);
                    leanh::lean_dec(v___x_4511_);
                    v___x_4513_ = lean_nat_add(v___x_4450_, v_size_4451_);
                    leanh::lean_dec(v_size_4451_);
                    v___x_4514_ = lean_nat_add(v___x_4513_, v_size_4469_);
                    leanh::lean_dec(v___x_4513_);
                    leanh::lean_inc_ref(v_impl_4449_);
                    if v_isShared_4467_ == 0 {
                        leanh::lean_ctor_set(v___x_4466_, 4, v_impl_4449_);
                        leanh::lean_ctor_set(v___x_4466_, 3, v_r_4456_);
                        leanh::lean_ctor_set(v___x_4466_, 2, v_v_3957_);
                        leanh::lean_ctor_set(v___x_4466_, 1, v_k_3956_);
                        leanh::lean_ctor_set(v___x_4466_, 0, v___x_4514_);
                        v___x_4516_ = v___x_4466_;
                        state = 82;
                        continue;
                    } else {
                        v_reuseFailAlloc_4529_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4529_, 0, v___x_4514_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4529_, 1, v_k_3956_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4529_, 2, v_v_3957_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4529_, 3, v_r_4456_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4529_, 4, v_impl_4449_);
                        v___x_4516_ = v_reuseFailAlloc_4529_;
                        state = 82;
                        continue;
                    }
                }
            }
            76 => {
                v___x_4480_ = lean_nat_add(v___x_4450_, v_size_4452_);
                leanh::lean_dec(v_size_4452_);
                v___x_4481_ = lean_nat_add(v___x_4480_, v_size_4451_);
                leanh::lean_dec(v___x_4480_);
                v___x_4493_ = lean_nat_add(v___x_4450_, v_size_4468_);
                if leanh::lean_obj_tag(v_l_4472_) == 0 {
                    v_size_4503_ = leanh::lean_ctor_get(v_l_4472_, 0);
                    leanh::lean_inc(v_size_4503_);
                    v___y_4495_ = v_size_4503_;
                    state = 80;
                    continue;
                } else {
                    v___x_4504_ = leanh::lean_unsigned_to_nat(0);
                    v___y_4495_ = v___x_4504_;
                    state = 80;
                    continue;
                }
            }
            77 => {
                v___x_4486_ = lean_nat_add(v___y_4484_, v___y_4485_);
                leanh::lean_dec(v___y_4485_);
                leanh::lean_dec(v___y_4484_);
                if v_isShared_4479_ == 0 {
                    leanh::lean_ctor_set(v___x_4478_, 4, v_impl_4449_);
                    leanh::lean_ctor_set(v___x_4478_, 3, v_r_4473_);
                    leanh::lean_ctor_set(v___x_4478_, 2, v_v_3957_);
                    leanh::lean_ctor_set(v___x_4478_, 1, v_k_3956_);
                    leanh::lean_ctor_set(v___x_4478_, 0, v___x_4486_);
                    v___x_4488_ = v___x_4478_;
                    state = 78;
                    continue;
                } else {
                    v_reuseFailAlloc_4492_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4492_, 0, v___x_4486_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4492_, 1, v_k_3956_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4492_, 2, v_v_3957_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4492_, 3, v_r_4473_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4492_, 4, v_impl_4449_);
                    v___x_4488_ = v_reuseFailAlloc_4492_;
                    state = 78;
                    continue;
                }
            }
            78 => {
                if v_isShared_4467_ == 0 {
                    leanh::lean_ctor_set(v___x_4466_, 4, v___x_4488_);
                    leanh::lean_ctor_set(v___x_4466_, 3, v___y_4483_);
                    leanh::lean_ctor_set(v___x_4466_, 2, v_v_4471_);
                    leanh::lean_ctor_set(v___x_4466_, 1, v_k_4470_);
                    leanh::lean_ctor_set(v___x_4466_, 0, v___x_4481_);
                    v___x_4490_ = v___x_4466_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_4491_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4491_, 0, v___x_4481_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4491_, 1, v_k_4470_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4491_, 2, v_v_4471_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4491_, 3, v___y_4483_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4491_, 4, v___x_4488_);
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
                leanh::lean_dec(v___y_4495_);
                leanh::lean_dec(v___x_4493_);
                if v_isShared_3962_ == 0 {
                    leanh::lean_ctor_set(v___x_3961_, 4, v_l_4472_);
                    leanh::lean_ctor_set(v___x_3961_, 3, v_l_4455_);
                    leanh::lean_ctor_set(v___x_3961_, 2, v_v_4454_);
                    leanh::lean_ctor_set(v___x_3961_, 1, v_k_4453_);
                    leanh::lean_ctor_set(v___x_3961_, 0, v___x_4496_);
                    v___x_4498_ = v___x_3961_;
                    state = 81;
                    continue;
                } else {
                    v_reuseFailAlloc_4502_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4502_, 0, v___x_4496_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4502_, 1, v_k_4453_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4502_, 2, v_v_4454_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4502_, 3, v_l_4455_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4502_, 4, v_l_4472_);
                    v___x_4498_ = v_reuseFailAlloc_4502_;
                    state = 81;
                    continue;
                }
            }
            81 => {
                v___x_4499_ = lean_nat_add(v___x_4450_, v_size_4451_);
                leanh::lean_dec(v_size_4451_);
                if leanh::lean_obj_tag(v_r_4473_) == 0 {
                    v_size_4500_ = leanh::lean_ctor_get(v_r_4473_, 0);
                    leanh::lean_inc(v_size_4500_);
                    v___y_4483_ = v___x_4498_;
                    v___y_4484_ = v___x_4499_;
                    v___y_4485_ = v_size_4500_;
                    state = 77;
                    continue;
                } else {
                    v___x_4501_ = leanh::lean_unsigned_to_nat(0);
                    v___y_4483_ = v___x_4498_;
                    v___y_4484_ = v___x_4499_;
                    v___y_4485_ = v___x_4501_;
                    state = 77;
                    continue;
                }
            }
            82 => {
                v_isSharedCheck_4523_ = (!leanh::lean_is_exclusive(v_impl_4449_)) as u8;
                if v_isSharedCheck_4523_ == 0 {
                    v_unused_4524_ = leanh::lean_ctor_get(v_impl_4449_, 4);
                    leanh::lean_dec(v_unused_4524_);
                    v_unused_4525_ = leanh::lean_ctor_get(v_impl_4449_, 3);
                    leanh::lean_dec(v_unused_4525_);
                    v_unused_4526_ = leanh::lean_ctor_get(v_impl_4449_, 2);
                    leanh::lean_dec(v_unused_4526_);
                    v_unused_4527_ = leanh::lean_ctor_get(v_impl_4449_, 1);
                    leanh::lean_dec(v_unused_4527_);
                    v_unused_4528_ = leanh::lean_ctor_get(v_impl_4449_, 0);
                    leanh::lean_dec(v_unused_4528_);
                    v___x_4518_ = v_impl_4449_;
                    v_isShared_4519_ = v_isSharedCheck_4523_;
                    state = 83;
                    continue;
                } else {
                    leanh::lean_dec(v_impl_4449_);
                    v___x_4518_ = leanh::lean_box(0);
                    v_isShared_4519_ = v_isSharedCheck_4523_;
                    state = 83;
                    continue;
                }
            }
            83 => {
                if v_isShared_4519_ == 0 {
                    leanh::lean_ctor_set(v___x_4518_, 4, v___x_4516_);
                    leanh::lean_ctor_set(v___x_4518_, 3, v_l_4455_);
                    leanh::lean_ctor_set(v___x_4518_, 2, v_v_4454_);
                    leanh::lean_ctor_set(v___x_4518_, 1, v_k_4453_);
                    leanh::lean_ctor_set(v___x_4518_, 0, v___x_4512_);
                    v___x_4521_ = v___x_4518_;
                    state = 84;
                    continue;
                } else {
                    v_reuseFailAlloc_4522_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4522_, 0, v___x_4512_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4522_, 1, v_k_4453_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4522_, 2, v_v_4454_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4522_, 3, v_l_4455_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4522_, 4, v___x_4516_);
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
                v_size_4549_ = leanh::lean_ctor_get(v_r_4542_, 0);
                v___x_4550_ = lean_nat_add(v___x_4450_, v_size_4543_);
                leanh::lean_dec(v_size_4543_);
                v___x_4551_ = lean_nat_add(v___x_4450_, v_size_4549_);
                if v_isShared_4548_ == 0 {
                    leanh::lean_ctor_set(v___x_4547_, 4, v_impl_4449_);
                    leanh::lean_ctor_set(v___x_4547_, 3, v_r_4542_);
                    leanh::lean_ctor_set(v___x_4547_, 2, v_v_3957_);
                    leanh::lean_ctor_set(v___x_4547_, 1, v_k_3956_);
                    leanh::lean_ctor_set(v___x_4547_, 0, v___x_4551_);
                    v___x_4553_ = v___x_4547_;
                    state = 87;
                    continue;
                } else {
                    v_reuseFailAlloc_4557_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4557_, 0, v___x_4551_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4557_, 1, v_k_3956_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4557_, 2, v_v_3957_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4557_, 3, v_r_4542_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4557_, 4, v_impl_4449_);
                    v___x_4553_ = v_reuseFailAlloc_4557_;
                    state = 87;
                    continue;
                }
            }
            87 => {
                if v_isShared_3962_ == 0 {
                    leanh::lean_ctor_set(v___x_3961_, 4, v___x_4553_);
                    leanh::lean_ctor_set(v___x_3961_, 3, v_l_4541_);
                    leanh::lean_ctor_set(v___x_3961_, 2, v_v_4545_);
                    leanh::lean_ctor_set(v___x_3961_, 1, v_k_4544_);
                    leanh::lean_ctor_set(v___x_3961_, 0, v___x_4550_);
                    v___x_4555_ = v___x_3961_;
                    state = 88;
                    continue;
                } else {
                    v_reuseFailAlloc_4556_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4556_, 0, v___x_4550_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4556_, 1, v_k_4544_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4556_, 2, v_v_4545_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4556_, 3, v_l_4541_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4556_, 4, v___x_4553_);
                    v___x_4555_ = v_reuseFailAlloc_4556_;
                    state = 88;
                    continue;
                }
            }
            88 => {
                return v___x_4555_;
            }
            89 => {
                v___x_4566_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_4565_ == 0 {
                    leanh::lean_ctor_set(v___x_4564_, 3, v_r_4542_);
                    leanh::lean_ctor_set(v___x_4564_, 2, v_v_3957_);
                    leanh::lean_ctor_set(v___x_4564_, 1, v_k_3956_);
                    leanh::lean_ctor_set(v___x_4564_, 0, v___x_4450_);
                    v___x_4568_ = v___x_4564_;
                    state = 90;
                    continue;
                } else {
                    v_reuseFailAlloc_4572_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4572_, 0, v___x_4450_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4572_, 1, v_k_3956_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4572_, 2, v_v_3957_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4572_, 3, v_r_4542_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4572_, 4, v_r_4542_);
                    v___x_4568_ = v_reuseFailAlloc_4572_;
                    state = 90;
                    continue;
                }
            }
            90 => {
                if v_isShared_3962_ == 0 {
                    leanh::lean_ctor_set(v___x_3961_, 4, v___x_4568_);
                    leanh::lean_ctor_set(v___x_3961_, 3, v_l_4541_);
                    leanh::lean_ctor_set(v___x_3961_, 2, v_v_4562_);
                    leanh::lean_ctor_set(v___x_3961_, 1, v_k_4561_);
                    leanh::lean_ctor_set(v___x_3961_, 0, v___x_4566_);
                    v___x_4570_ = v___x_3961_;
                    state = 91;
                    continue;
                } else {
                    v_reuseFailAlloc_4571_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4571_, 0, v___x_4566_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4571_, 1, v_k_4561_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4571_, 2, v_v_4562_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4571_, 3, v_l_4541_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4571_, 4, v___x_4568_);
                    v___x_4570_ = v_reuseFailAlloc_4571_;
                    state = 91;
                    continue;
                }
            }
            91 => {
                return v___x_4570_;
            }
            92 => {
                v_k_4583_ = leanh::lean_ctor_get(v_r_4577_, 1);
                v_v_4584_ = leanh::lean_ctor_get(v_r_4577_, 2);
                v_isSharedCheck_4598_ = (!leanh::lean_is_exclusive(v_r_4577_)) as u8;
                if v_isSharedCheck_4598_ == 0 {
                    v_unused_4599_ = leanh::lean_ctor_get(v_r_4577_, 4);
                    leanh::lean_dec(v_unused_4599_);
                    v_unused_4600_ = leanh::lean_ctor_get(v_r_4577_, 3);
                    leanh::lean_dec(v_unused_4600_);
                    v_unused_4601_ = leanh::lean_ctor_get(v_r_4577_, 0);
                    leanh::lean_dec(v_unused_4601_);
                    v___x_4586_ = v_r_4577_;
                    v_isShared_4587_ = v_isSharedCheck_4598_;
                    state = 93;
                    continue;
                } else {
                    leanh::lean_inc(v_v_4584_);
                    leanh::lean_inc(v_k_4583_);
                    leanh::lean_dec(v_r_4577_);
                    v___x_4586_ = leanh::lean_box(0);
                    v_isShared_4587_ = v_isSharedCheck_4598_;
                    state = 93;
                    continue;
                }
            }
            93 => {
                v___x_4588_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_4587_ == 0 {
                    leanh::lean_ctor_set(v___x_4586_, 4, v_l_4541_);
                    leanh::lean_ctor_set(v___x_4586_, 3, v_l_4541_);
                    leanh::lean_ctor_set(v___x_4586_, 2, v_v_4579_);
                    leanh::lean_ctor_set(v___x_4586_, 1, v_k_4578_);
                    leanh::lean_ctor_set(v___x_4586_, 0, v___x_4450_);
                    v___x_4590_ = v___x_4586_;
                    state = 94;
                    continue;
                } else {
                    v_reuseFailAlloc_4597_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4597_, 0, v___x_4450_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4597_, 1, v_k_4578_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4597_, 2, v_v_4579_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4597_, 3, v_l_4541_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4597_, 4, v_l_4541_);
                    v___x_4590_ = v_reuseFailAlloc_4597_;
                    state = 94;
                    continue;
                }
            }
            94 => {
                if v_isShared_4582_ == 0 {
                    leanh::lean_ctor_set(v___x_4581_, 4, v_l_4541_);
                    leanh::lean_ctor_set(v___x_4581_, 2, v_v_3957_);
                    leanh::lean_ctor_set(v___x_4581_, 1, v_k_3956_);
                    leanh::lean_ctor_set(v___x_4581_, 0, v___x_4450_);
                    v___x_4592_ = v___x_4581_;
                    state = 95;
                    continue;
                } else {
                    v_reuseFailAlloc_4596_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4596_, 0, v___x_4450_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4596_, 1, v_k_3956_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4596_, 2, v_v_3957_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4596_, 3, v_l_4541_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4596_, 4, v_l_4541_);
                    v___x_4592_ = v_reuseFailAlloc_4596_;
                    state = 95;
                    continue;
                }
            }
            95 => {
                if v_isShared_3962_ == 0 {
                    leanh::lean_ctor_set(v___x_3961_, 4, v___x_4592_);
                    leanh::lean_ctor_set(v___x_3961_, 3, v___x_4590_);
                    leanh::lean_ctor_set(v___x_3961_, 2, v_v_4584_);
                    leanh::lean_ctor_set(v___x_3961_, 1, v_k_4583_);
                    leanh::lean_ctor_set(v___x_3961_, 0, v___x_4588_);
                    v___x_4594_ = v___x_3961_;
                    state = 96;
                    continue;
                } else {
                    v_reuseFailAlloc_4595_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4595_, 0, v___x_4588_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4595_, 1, v_k_4583_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4595_, 2, v_v_4584_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4595_, 3, v___x_4590_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4595_, 4, v___x_4592_);
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
    mut v_k_4615_: *mut leanh::LeanObject,
    mut v_t_4616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4617_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_4615_, v_t_4616_);
    leanh::lean_dec_ref(v_k_4615_);
    return v_res_4617_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0(
    mut v_val_4618_: *mut leanh::LeanObject,
    mut v_s_4619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toRing_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_4629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_4631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_4633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recheck_4634_: u8 = 0;
    let mut v_invSet_4635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_4638_: u8 = 0;
    let mut v___x_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4641_: u8 = 0;
    let mut v___x_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4646_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_4620_ = leanh::lean_ctor_get(v_s_4619_, 0);
                v_invFn_x3f_4621_ = leanh::lean_ctor_get(v_s_4619_, 1);
                v_semiringId_x3f_4622_ = leanh::lean_ctor_get(v_s_4619_, 2);
                v_commSemiringInst_4623_ = leanh::lean_ctor_get(v_s_4619_, 3);
                v_commRingInst_4624_ = leanh::lean_ctor_get(v_s_4619_, 4);
                v_noZeroDivInst_x3f_4625_ = leanh::lean_ctor_get(v_s_4619_, 5);
                v_fieldInst_x3f_4626_ = leanh::lean_ctor_get(v_s_4619_, 6);
                v_powIdentityInst_x3f_4627_ = leanh::lean_ctor_get(v_s_4619_, 7);
                v_denoteEntries_4628_ = leanh::lean_ctor_get(v_s_4619_, 8);
                v_nextId_4629_ = leanh::lean_ctor_get(v_s_4619_, 9);
                v_steps_4630_ = leanh::lean_ctor_get(v_s_4619_, 10);
                v_queue_4631_ = leanh::lean_ctor_get(v_s_4619_, 11);
                v_basis_4632_ = leanh::lean_ctor_get(v_s_4619_, 12);
                v_diseqs_4633_ = leanh::lean_ctor_get(v_s_4619_, 13);
                v_recheck_4634_ = leanh::lean_ctor_get_uint8(
                    v_s_4619_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                );
                v_invSet_4635_ = leanh::lean_ctor_get(v_s_4619_, 14);
                v_powIdentityVarCount_4636_ = leanh::lean_ctor_get(v_s_4619_, 15);
                v_numEq0_x3f_4637_ = leanh::lean_ctor_get(v_s_4619_, 16);
                v_numEq0Updated_4638_ = leanh::lean_ctor_get_uint8(
                    v_s_4619_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_4646_ = (!leanh::lean_is_exclusive(v_s_4619_)) as u8;
                if v_isSharedCheck_4646_ == 0 {
                    v___x_4640_ = v_s_4619_;
                    v_isShared_4641_ = v_isSharedCheck_4646_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_numEq0_x3f_4637_);
                    leanh::lean_inc(v_powIdentityVarCount_4636_);
                    leanh::lean_inc(v_invSet_4635_);
                    leanh::lean_inc(v_diseqs_4633_);
                    leanh::lean_inc(v_basis_4632_);
                    leanh::lean_inc(v_queue_4631_);
                    leanh::lean_inc(v_steps_4630_);
                    leanh::lean_inc(v_nextId_4629_);
                    leanh::lean_inc(v_denoteEntries_4628_);
                    leanh::lean_inc(v_powIdentityInst_x3f_4627_);
                    leanh::lean_inc(v_fieldInst_x3f_4626_);
                    leanh::lean_inc(v_noZeroDivInst_x3f_4625_);
                    leanh::lean_inc(v_commRingInst_4624_);
                    leanh::lean_inc(v_commSemiringInst_4623_);
                    leanh::lean_inc(v_semiringId_x3f_4622_);
                    leanh::lean_inc(v_invFn_x3f_4621_);
                    leanh::lean_inc(v_toRing_4620_);
                    leanh::lean_dec(v_s_4619_);
                    v___x_4640_ = leanh::lean_box(0);
                    v_isShared_4641_ = v_isSharedCheck_4646_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4642_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_val_4618_, v_queue_4631_);
                if v_isShared_4641_ == 0 {
                    leanh::lean_ctor_set(v___x_4640_, 11, v___x_4642_);
                    v___x_4644_ = v___x_4640_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4645_ = leanh::lean_alloc_ctor(0, 17, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 0, v_toRing_4620_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 1, v_invFn_x3f_4621_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 2, v_semiringId_x3f_4622_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4645_,
                        3,
                        v_commSemiringInst_4623_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 4, v_commRingInst_4624_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4645_,
                        5,
                        v_noZeroDivInst_x3f_4625_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 6, v_fieldInst_x3f_4626_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4645_,
                        7,
                        v_powIdentityInst_x3f_4627_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 8, v_denoteEntries_4628_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 9, v_nextId_4629_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 10, v_steps_4630_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 11, v___x_4642_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 12, v_basis_4632_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 13, v_diseqs_4633_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 14, v_invSet_4635_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4645_,
                        15,
                        v_powIdentityVarCount_4636_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 16, v_numEq0_x3f_4637_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4645_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                        v_recheck_4634_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4645_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 17 + 1) as u32,
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
    mut v_val_4647_: *mut leanh::LeanObject,
    mut v_s_4648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4649_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0(v_val_4647_, v_s_4648_);
    leanh::lean_dec_ref(v_val_4647_);
    return v_res_4649_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(
    mut v_a_4650_: *mut leanh::LeanObject,
    mut v_a_4651_: *mut leanh::LeanObject,
    mut v_a_4652_: *mut leanh::LeanObject,
    mut v_a_4653_: *mut leanh::LeanObject,
    mut v_a_4654_: *mut leanh::LeanObject,
    mut v_a_4655_: *mut leanh::LeanObject,
    mut v_a_4656_: *mut leanh::LeanObject,
    mut v_a_4657_: *mut leanh::LeanObject,
    mut v_a_4658_: *mut leanh::LeanObject,
    mut v_a_4659_: *mut leanh::LeanObject,
    mut v_a_4660_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4666_: u8 = 0;
    let mut v_queue_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4676_: u8 = 0;
    let mut v___x_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4680_: u8 = 0;
    let mut v_unused_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4685_: u8 = 0;
    let mut v___x_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4689_: u8 = 0;
    let mut v_a_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4693_: u8 = 0;
    let mut v___x_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4697_: u8 = 0;
    let mut v___x_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4702_: u8 = 0;
    let mut v_a_4703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4706_: u8 = 0;
    let mut v___x_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4710_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4662_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                    v_a_4650_, v_a_4651_, v_a_4652_, v_a_4653_, v_a_4654_, v_a_4655_, v_a_4656_,
                    v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_,
                );
                if leanh::lean_obj_tag(v___x_4662_) == 0 {
                    v_a_4663_ = leanh::lean_ctor_get(v___x_4662_, 0);
                    v_isSharedCheck_4702_ = (!leanh::lean_is_exclusive(v___x_4662_)) as u8;
                    if v_isSharedCheck_4702_ == 0 {
                        v___x_4665_ = v___x_4662_;
                        v_isShared_4666_ = v_isSharedCheck_4702_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4663_);
                        leanh::lean_dec(v___x_4662_);
                        v___x_4665_ = leanh::lean_box(0);
                        v_isShared_4666_ = v_isSharedCheck_4702_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4703_ = leanh::lean_ctor_get(v___x_4662_, 0);
                    v_isSharedCheck_4710_ = (!leanh::lean_is_exclusive(v___x_4662_)) as u8;
                    if v_isSharedCheck_4710_ == 0 {
                        v___x_4705_ = v___x_4662_;
                        v_isShared_4706_ = v_isSharedCheck_4710_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4703_);
                        leanh::lean_dec(v___x_4662_);
                        v___x_4705_ = leanh::lean_box(0);
                        v_isShared_4706_ = v_isSharedCheck_4710_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_queue_4667_ = leanh::lean_ctor_get(v_a_4663_, 11);
                leanh::lean_inc(v_queue_4667_);
                leanh::lean_dec(v_a_4663_);
                v___x_4668_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_queue_4667_);
                leanh::lean_dec(v_queue_4667_);
                if leanh::lean_obj_tag(v___x_4668_) == 1 {
                    leanh::lean_del_object(v___x_4665_);
                    v_val_4669_ = leanh::lean_ctor_get(v___x_4668_, 0);
                    leanh::lean_inc(v_val_4669_);
                    v___f_4670_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0___boxed
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_4670_, 0, v_val_4669_);
                    v___x_4671_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(
                        v___f_4670_,
                        v_a_4650_,
                        v_a_4651_,
                    );
                    if leanh::lean_obj_tag(v___x_4671_) == 0 {
                        leanh::lean_dec_ref_known(v___x_4671_, 1);
                        v___x_4672_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4673_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(
                            v___x_4672_,
                            v_a_4651_,
                        );
                        if leanh::lean_obj_tag(v___x_4673_) == 0 {
                            v_isSharedCheck_4680_ =
                                (!leanh::lean_is_exclusive(v___x_4673_)) as u8;
                            if v_isSharedCheck_4680_ == 0 {
                                v_unused_4681_ = leanh::lean_ctor_get(v___x_4673_, 0);
                                leanh::lean_dec(v_unused_4681_);
                                v___x_4675_ = v___x_4673_;
                                v_isShared_4676_ = v_isSharedCheck_4680_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_4673_);
                                v___x_4675_ = leanh::lean_box(0);
                                v_isShared_4676_ = v_isSharedCheck_4680_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v___x_4668_, 1);
                            v_a_4682_ = leanh::lean_ctor_get(v___x_4673_, 0);
                            v_isSharedCheck_4689_ =
                                (!leanh::lean_is_exclusive(v___x_4673_)) as u8;
                            if v_isSharedCheck_4689_ == 0 {
                                v___x_4684_ = v___x_4673_;
                                v_isShared_4685_ = v_isSharedCheck_4689_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4682_);
                                leanh::lean_dec(v___x_4673_);
                                v___x_4684_ = leanh::lean_box(0);
                                v_isShared_4685_ = v_isSharedCheck_4689_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___x_4668_, 1);
                        v_a_4690_ = leanh::lean_ctor_get(v___x_4671_, 0);
                        v_isSharedCheck_4697_ =
                            (!leanh::lean_is_exclusive(v___x_4671_)) as u8;
                        if v_isSharedCheck_4697_ == 0 {
                            v___x_4692_ = v___x_4671_;
                            v_isShared_4693_ = v_isSharedCheck_4697_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4690_);
                            leanh::lean_dec(v___x_4671_);
                            v___x_4692_ = leanh::lean_box(0);
                            v_isShared_4693_ = v_isSharedCheck_4697_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_4668_);
                    v___x_4698_ = leanh::lean_box(0);
                    if v_isShared_4666_ == 0 {
                        leanh::lean_ctor_set(v___x_4665_, 0, v___x_4698_);
                        v___x_4700_ = v___x_4665_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4701_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4701_, 0, v___x_4698_);
                        v___x_4700_ = v_reuseFailAlloc_4701_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4676_ == 0 {
                    leanh::lean_ctor_set(v___x_4675_, 0, v___x_4668_);
                    v___x_4678_ = v___x_4675_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4679_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4679_, 0, v___x_4668_);
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
                    v_reuseFailAlloc_4688_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4688_, 0, v_a_4682_);
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
                    v_reuseFailAlloc_4696_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4696_, 0, v_a_4690_);
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
                    v_reuseFailAlloc_4709_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4709_, 0, v_a_4703_);
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
    mut v_a_4711_: *mut leanh::LeanObject,
    mut v_a_4712_: *mut leanh::LeanObject,
    mut v_a_4713_: *mut leanh::LeanObject,
    mut v_a_4714_: *mut leanh::LeanObject,
    mut v_a_4715_: *mut leanh::LeanObject,
    mut v_a_4716_: *mut leanh::LeanObject,
    mut v_a_4717_: *mut leanh::LeanObject,
    mut v_a_4718_: *mut leanh::LeanObject,
    mut v_a_4719_: *mut leanh::LeanObject,
    mut v_a_4720_: *mut leanh::LeanObject,
    mut v_a_4721_: *mut leanh::LeanObject,
    mut v_a_4722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4723_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(
        v_a_4711_, v_a_4712_, v_a_4713_, v_a_4714_, v_a_4715_, v_a_4716_, v_a_4717_, v_a_4718_,
        v_a_4719_, v_a_4720_, v_a_4721_,
    );
    leanh::lean_dec(v_a_4721_);
    leanh::lean_dec_ref(v_a_4720_);
    leanh::lean_dec(v_a_4719_);
    leanh::lean_dec_ref(v_a_4718_);
    leanh::lean_dec(v_a_4717_);
    leanh::lean_dec_ref(v_a_4716_);
    leanh::lean_dec(v_a_4715_);
    leanh::lean_dec_ref(v_a_4714_);
    leanh::lean_dec(v_a_4713_);
    leanh::lean_dec(v_a_4712_);
    leanh::lean_dec_ref(v_a_4711_);
    return v_res_4723_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(
    mut v_00_u03b2_4724_: *mut leanh::LeanObject,
    mut v_k_4725_: *mut leanh::LeanObject,
    mut v_t_4726_: *mut leanh::LeanObject,
    mut v_h_4727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4728_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_4725_, v_t_4726_);
    return v___x_4728_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___boxed(
    mut v_00_u03b2_4729_: *mut leanh::LeanObject,
    mut v_k_4730_: *mut leanh::LeanObject,
    mut v_t_4731_: *mut leanh::LeanObject,
    mut v_h_4732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4733_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(v_00_u03b2_4729_, v_k_4730_, v_t_4731_, v_h_4732_);
    leanh::lean_dec_ref(v_k_4730_);
    return v_res_4733_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_x_4734_: *mut leanh::LeanObject,
    mut v_x_4735_: *mut leanh::LeanObject,
    mut v_x_4736_: *mut leanh::LeanObject,
    mut v_x_4737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4742_: u8 = 0;
    let mut v___x_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: u8 = 0;
    let mut v___x_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: u8 = 0;
    let mut v___x_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4763_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4738_ = leanh::lean_ctor_get(v_x_4734_, 0);
                v_vs_4739_ = leanh::lean_ctor_get(v_x_4734_, 1);
                v_isSharedCheck_4763_ = (!leanh::lean_is_exclusive(v_x_4734_)) as u8;
                if v_isSharedCheck_4763_ == 0 {
                    v___x_4741_ = v_x_4734_;
                    v_isShared_4742_ = v_isSharedCheck_4763_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_4739_);
                    leanh::lean_inc(v_ks_4738_);
                    leanh::lean_dec(v_x_4734_);
                    v___x_4741_ = leanh::lean_box(0);
                    v_isShared_4742_ = v_isSharedCheck_4763_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4743_ = lean_array_get_size(v_ks_4738_);
                v___x_4744_ = lean_nat_dec_lt(v_x_4735_, v___x_4743_);
                if v___x_4744_ == 0 {
                    leanh::lean_dec(v_x_4735_);
                    v___x_4745_ = lean_array_push(v_ks_4738_, v_x_4736_);
                    v___x_4746_ = lean_array_push(v_vs_4739_, v_x_4737_);
                    if v_isShared_4742_ == 0 {
                        leanh::lean_ctor_set(v___x_4741_, 1, v___x_4746_);
                        leanh::lean_ctor_set(v___x_4741_, 0, v___x_4745_);
                        v___x_4748_ = v___x_4741_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4749_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4749_, 0, v___x_4745_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4749_, 1, v___x_4746_);
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
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4757_, 0, v_ks_4738_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4757_, 1, v_vs_4739_);
                            v___x_4753_ = v_reuseFailAlloc_4757_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4758_ = lean_array_fset(v_ks_4738_, v_x_4735_, v_x_4736_);
                        v___x_4759_ = lean_array_fset(v_vs_4739_, v_x_4735_, v_x_4737_);
                        leanh::lean_dec(v_x_4735_);
                        if v_isShared_4742_ == 0 {
                            leanh::lean_ctor_set(v___x_4741_, 1, v___x_4759_);
                            leanh::lean_ctor_set(v___x_4741_, 0, v___x_4758_);
                            v___x_4761_ = v___x_4741_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4762_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4762_, 0, v___x_4758_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4762_, 1, v___x_4759_);
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
                v___x_4754_ = leanh::lean_unsigned_to_nat(1);
                v___x_4755_ = lean_nat_add(v_x_4735_, v___x_4754_);
                leanh::lean_dec(v_x_4735_);
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
    mut v_n_4764_: *mut leanh::LeanObject,
    mut v_k_4765_: *mut leanh::LeanObject,
    mut v_v_4766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4767_ = leanh::lean_unsigned_to_nat(0);
    v___x_4768_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_4764_, v___x_4767_, v_k_4765_, v_v_4766_);
    return v___x_4768_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4769_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4769_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4769_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(
    mut v_x_4770_: *mut leanh::LeanObject,
    mut v_x_4771_: usize,
    mut v_x_4772_: usize,
    mut v_x_4773_: *mut leanh::LeanObject,
    mut v_x_4774_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_4775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: usize = 0;
    let mut v___x_4777_: usize = 0;
    let mut v___x_4778_: usize = 0;
    let mut v___x_4779_: usize = 0;
    let mut v_j_4780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: u8 = 0;
    let mut v___x_4784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4785_: u8 = 0;
    let mut v_v_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4799_: u8 = 0;
    let mut v___x_4800_: u8 = 0;
    let mut v___x_4801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4806_: u8 = 0;
    let mut v_node_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4810_: u8 = 0;
    let mut v___x_4811_: usize = 0;
    let mut v___x_4812_: usize = 0;
    let mut v___x_4813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4817_: u8 = 0;
    let mut v___x_4818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4819_: u8 = 0;
    let mut v_unused_4820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4825_: u8 = 0;
    let mut v___x_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_4828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4830_: u8 = 0;
    let mut v_ks_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: usize = 0;
    let mut v___x_4837_: u8 = 0;
    let mut v___x_4838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: u8 = 0;
    let mut v_reuseFailAlloc_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4842_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4770_) == 0 {
                    v_es_4775_ = leanh::lean_ctor_get(v_x_4770_, 0);
                    v___x_4776_ = 5usize;
                    v___x_4777_ = 1usize;
                    v___x_4778_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_4779_ = lean_usize_land(v_x_4771_, v___x_4778_);
                    v_j_4780_ = lean_usize_to_nat(v___x_4779_);
                    v___x_4781_ = lean_array_get_size(v_es_4775_);
                    v___x_4782_ = lean_nat_dec_lt(v_j_4780_, v___x_4781_);
                    if v___x_4782_ == 0 {
                        leanh::lean_dec(v_j_4780_);
                        leanh::lean_dec(v_x_4774_);
                        leanh::lean_dec_ref(v_x_4773_);
                        return v_x_4770_;
                    } else {
                        leanh::lean_inc_ref(v_es_4775_);
                        v_isSharedCheck_4819_ = (!leanh::lean_is_exclusive(v_x_4770_)) as u8;
                        if v_isSharedCheck_4819_ == 0 {
                            v_unused_4820_ = leanh::lean_ctor_get(v_x_4770_, 0);
                            leanh::lean_dec(v_unused_4820_);
                            v___x_4784_ = v_x_4770_;
                            v_isShared_4785_ = v_isSharedCheck_4819_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_4770_);
                            v___x_4784_ = leanh::lean_box(0);
                            v_isShared_4785_ = v_isSharedCheck_4819_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4821_ = leanh::lean_ctor_get(v_x_4770_, 0);
                    v_vs_4822_ = leanh::lean_ctor_get(v_x_4770_, 1);
                    v_isSharedCheck_4842_ = (!leanh::lean_is_exclusive(v_x_4770_)) as u8;
                    if v_isSharedCheck_4842_ == 0 {
                        v___x_4824_ = v_x_4770_;
                        v_isShared_4825_ = v_isSharedCheck_4842_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_4822_);
                        leanh::lean_inc(v_ks_4821_);
                        leanh::lean_dec(v_x_4770_);
                        v___x_4824_ = leanh::lean_box(0);
                        v_isShared_4825_ = v_isSharedCheck_4842_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4786_ = lean_array_fget(v_es_4775_, v_j_4780_);
                v___x_4787_ = leanh::lean_box(0);
                v_xs_x27_4788_ = lean_array_fset(v_es_4775_, v_j_4780_, v___x_4787_);
                match leanh::lean_obj_tag(v_v_4786_) {
                    0 => {
                        v_key_4795_ = leanh::lean_ctor_get(v_v_4786_, 0);
                        v_val_4796_ = leanh::lean_ctor_get(v_v_4786_, 1);
                        v_isSharedCheck_4806_ = (!leanh::lean_is_exclusive(v_v_4786_)) as u8;
                        if v_isSharedCheck_4806_ == 0 {
                            v___x_4798_ = v_v_4786_;
                            v_isShared_4799_ = v_isSharedCheck_4806_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_4796_);
                            leanh::lean_inc(v_key_4795_);
                            leanh::lean_dec(v_v_4786_);
                            v___x_4798_ = leanh::lean_box(0);
                            v_isShared_4799_ = v_isSharedCheck_4806_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4807_ = leanh::lean_ctor_get(v_v_4786_, 0);
                        v_isSharedCheck_4817_ = (!leanh::lean_is_exclusive(v_v_4786_)) as u8;
                        if v_isSharedCheck_4817_ == 0 {
                            v___x_4809_ = v_v_4786_;
                            v_isShared_4810_ = v_isSharedCheck_4817_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_4807_);
                            leanh::lean_dec(v_v_4786_);
                            v___x_4809_ = leanh::lean_box(0);
                            v_isShared_4810_ = v_isSharedCheck_4817_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4818_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4818_, 0, v_x_4773_);
                        leanh::lean_ctor_set(v___x_4818_, 1, v_x_4774_);
                        v___y_4790_ = v___x_4818_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4791_ = lean_array_fset(v_xs_x27_4788_, v_j_4780_, v___y_4790_);
                leanh::lean_dec(v_j_4780_);
                if v_isShared_4785_ == 0 {
                    leanh::lean_ctor_set(v___x_4784_, 0, v___x_4791_);
                    v___x_4793_ = v___x_4784_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4794_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4794_, 0, v___x_4791_);
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
                    leanh::lean_del_object(v___x_4798_);
                    v___x_4801_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4795_,
                        v_val_4796_,
                        v_x_4773_,
                        v_x_4774_,
                    );
                    v___x_4802_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4802_, 0, v___x_4801_);
                    v___y_4790_ = v___x_4802_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_4796_);
                    leanh::lean_dec(v_key_4795_);
                    if v_isShared_4799_ == 0 {
                        leanh::lean_ctor_set(v___x_4798_, 1, v_x_4774_);
                        leanh::lean_ctor_set(v___x_4798_, 0, v_x_4773_);
                        v___x_4804_ = v___x_4798_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4805_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4805_, 0, v_x_4773_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4805_, 1, v_x_4774_);
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
                    leanh::lean_ctor_set(v___x_4809_, 0, v___x_4813_);
                    v___x_4815_ = v___x_4809_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4816_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4816_, 0, v___x_4813_);
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
                    v_reuseFailAlloc_4841_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4841_, 0, v_ks_4821_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4841_, 1, v_vs_4822_);
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
                    v___x_4839_ = leanh::lean_unsigned_to_nat(4);
                    v___x_4840_ = lean_nat_dec_lt(v___x_4838_, v___x_4839_);
                    leanh::lean_dec(v___x_4838_);
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
                    v_ks_4831_ = leanh::lean_ctor_get(v_newNode_4828_, 0);
                    leanh::lean_inc_ref(v_ks_4831_);
                    v_vs_4832_ = leanh::lean_ctor_get(v_newNode_4828_, 1);
                    leanh::lean_inc_ref(v_vs_4832_);
                    leanh::lean_dec_ref(v_newNode_4828_);
                    v___x_4833_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4834_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0);
                    v___x_4835_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_x_4772_, v_ks_4831_, v_vs_4832_, v___x_4833_, v___x_4834_);
                    leanh::lean_dec_ref(v_vs_4832_);
                    leanh::lean_dec_ref(v_ks_4831_);
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
    mut v_keys_4844_: *mut leanh::LeanObject,
    mut v_vals_4845_: *mut leanh::LeanObject,
    mut v_i_4846_: *mut leanh::LeanObject,
    mut v_entries_4847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: u8 = 0;
    let mut v_k_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: u64 = 0;
    let mut v_h_4853_: usize = 0;
    let mut v___x_4854_: usize = 0;
    let mut v___x_4855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: usize = 0;
    let mut v___x_4857_: usize = 0;
    let mut v___x_4858_: usize = 0;
    let mut v_h_4859_: usize = 0;
    let mut v___x_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4848_ = lean_array_get_size(v_keys_4844_);
                v___x_4849_ = lean_nat_dec_lt(v_i_4846_, v___x_4848_);
                if v___x_4849_ == 0 {
                    leanh::lean_dec(v_i_4846_);
                    return v_entries_4847_;
                } else {
                    v_k_4850_ = lean_array_fget_borrowed(v_keys_4844_, v_i_4846_);
                    v_v_4851_ = lean_array_fget_borrowed(v_vals_4845_, v_i_4846_);
                    v___x_4852_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_4850_);
                    v_h_4853_ = lean_uint64_to_usize(v___x_4852_);
                    v___x_4854_ = 5usize;
                    v___x_4855_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4856_ = 1usize;
                    v___x_4857_ = lean_usize_sub(v_depth_4843_, v___x_4856_);
                    v___x_4858_ = lean_usize_mul(v___x_4854_, v___x_4857_);
                    v_h_4859_ = lean_usize_shift_right(v_h_4853_, v___x_4858_);
                    v___x_4860_ = lean_nat_add(v_i_4846_, v___x_4855_);
                    leanh::lean_dec(v_i_4846_);
                    leanh::lean_inc(v_v_4851_);
                    leanh::lean_inc(v_k_4850_);
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
    mut v_depth_4863_: *mut leanh::LeanObject,
    mut v_keys_4864_: *mut leanh::LeanObject,
    mut v_vals_4865_: *mut leanh::LeanObject,
    mut v_i_4866_: *mut leanh::LeanObject,
    mut v_entries_4867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_4868_: usize = 0;
    let mut v_res_4869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4868_ = leanh::lean_unbox_usize(v_depth_4863_);
    leanh::lean_dec(v_depth_4863_);
    v_res_4869_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_4868_, v_keys_4864_, v_vals_4865_, v_i_4866_, v_entries_4867_);
    leanh::lean_dec_ref(v_vals_4865_);
    leanh::lean_dec_ref(v_keys_4864_);
    return v_res_4869_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___boxed(
    mut v_x_4870_: *mut leanh::LeanObject,
    mut v_x_4871_: *mut leanh::LeanObject,
    mut v_x_4872_: *mut leanh::LeanObject,
    mut v_x_4873_: *mut leanh::LeanObject,
    mut v_x_4874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_7240__boxed_4875_: usize = 0;
    let mut v_x_7241__boxed_4876_: usize = 0;
    let mut v_res_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_7240__boxed_4875_ = leanh::lean_unbox_usize(v_x_4871_);
    leanh::lean_dec(v_x_4871_);
    v_x_7241__boxed_4876_ = leanh::lean_unbox_usize(v_x_4872_);
    leanh::lean_dec(v_x_4872_);
    v_res_4877_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_4870_, v_x_7240__boxed_4875_, v_x_7241__boxed_4876_, v_x_4873_, v_x_4874_);
    return v_res_4877_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(
    mut v_x_4878_: *mut leanh::LeanObject,
    mut v_x_4879_: *mut leanh::LeanObject,
    mut v_x_4880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4881_: u64 = 0;
    let mut v___x_4882_: usize = 0;
    let mut v___x_4883_: usize = 0;
    let mut v___x_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4881_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_4879_);
    v___x_4882_ = lean_uint64_to_usize(v___x_4881_);
    v___x_4883_ = 1usize;
    v___x_4884_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_4878_, v___x_4882_, v___x_4883_, v_x_4879_, v_x_4880_);
    return v___x_4884_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___lam__0(
    mut v_e_4885_: *mut leanh::LeanObject,
    mut v_ringId_4886_: *mut leanh::LeanObject,
    mut v_s_4887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_rings_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_4889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_4891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_4892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_4893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_4898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_4899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_4900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_4901_: u8 = 0;
    let mut v___x_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4904_: u8 = 0;
    let mut v___x_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4909_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_4888_ = leanh::lean_ctor_get(v_s_4887_, 0);
                v_typeIdOf_4889_ = leanh::lean_ctor_get(v_s_4887_, 1);
                v_exprToRingId_4890_ = leanh::lean_ctor_get(v_s_4887_, 2);
                v_semirings_4891_ = leanh::lean_ctor_get(v_s_4887_, 3);
                v_stypeIdOf_4892_ = leanh::lean_ctor_get(v_s_4887_, 4);
                v_exprToSemiringId_4893_ = leanh::lean_ctor_get(v_s_4887_, 5);
                v_ncRings_4894_ = leanh::lean_ctor_get(v_s_4887_, 6);
                v_exprToNCRingId_4895_ = leanh::lean_ctor_get(v_s_4887_, 7);
                v_nctypeIdOf_4896_ = leanh::lean_ctor_get(v_s_4887_, 8);
                v_ncSemirings_4897_ = leanh::lean_ctor_get(v_s_4887_, 9);
                v_exprToNCSemiringId_4898_ = leanh::lean_ctor_get(v_s_4887_, 10);
                v_ncstypeIdOf_4899_ = leanh::lean_ctor_get(v_s_4887_, 11);
                v_steps_4900_ = leanh::lean_ctor_get(v_s_4887_, 12);
                v_reportedMaxDegreeIssue_4901_ = leanh::lean_ctor_get_uint8(
                    v_s_4887_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_isSharedCheck_4909_ = (!leanh::lean_is_exclusive(v_s_4887_)) as u8;
                if v_isSharedCheck_4909_ == 0 {
                    v___x_4903_ = v_s_4887_;
                    v_isShared_4904_ = v_isSharedCheck_4909_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_steps_4900_);
                    leanh::lean_inc(v_ncstypeIdOf_4899_);
                    leanh::lean_inc(v_exprToNCSemiringId_4898_);
                    leanh::lean_inc(v_ncSemirings_4897_);
                    leanh::lean_inc(v_nctypeIdOf_4896_);
                    leanh::lean_inc(v_exprToNCRingId_4895_);
                    leanh::lean_inc(v_ncRings_4894_);
                    leanh::lean_inc(v_exprToSemiringId_4893_);
                    leanh::lean_inc(v_stypeIdOf_4892_);
                    leanh::lean_inc(v_semirings_4891_);
                    leanh::lean_inc(v_exprToRingId_4890_);
                    leanh::lean_inc(v_typeIdOf_4889_);
                    leanh::lean_inc(v_rings_4888_);
                    leanh::lean_dec(v_s_4887_);
                    v___x_4903_ = leanh::lean_box(0);
                    v_isShared_4904_ = v_isSharedCheck_4909_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4905_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_exprToRingId_4890_, v_e_4885_, v_ringId_4886_);
                if v_isShared_4904_ == 0 {
                    leanh::lean_ctor_set(v___x_4903_, 2, v___x_4905_);
                    v___x_4907_ = v___x_4903_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4908_ = leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 0, v_rings_4888_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 1, v_typeIdOf_4889_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 2, v___x_4905_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 3, v_semirings_4891_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 4, v_stypeIdOf_4892_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4908_,
                        5,
                        v_exprToSemiringId_4893_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 6, v_ncRings_4894_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 7, v_exprToNCRingId_4895_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 8, v_nctypeIdOf_4896_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 9, v_ncSemirings_4897_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4908_,
                        10,
                        v_exprToNCSemiringId_4898_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 11, v_ncstypeIdOf_4899_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4908_, 12, v_steps_4900_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4908_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
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
-> *mut leanh::LeanObject {
    let mut v___x_4911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4911_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__0;
    v___x_4912_ = l_Lean_stringToMessageData(v___x_4911_);
    return v___x_4912_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(
    mut v_e_4913_: *mut leanh::LeanObject,
    mut v_a_4914_: *mut leanh::LeanObject,
    mut v_a_4915_: *mut leanh::LeanObject,
    mut v_a_4916_: *mut leanh::LeanObject,
    mut v_a_4917_: *mut leanh::LeanObject,
    mut v_a_4918_: *mut leanh::LeanObject,
    mut v_a_4919_: *mut leanh::LeanObject,
    mut v_a_4920_: *mut leanh::LeanObject,
    mut v_a_4921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringId_4928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: u8 = 0;
    let mut v___x_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: u8 = 0;
    let mut v___x_4934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4941_: u8 = 0;
    let mut v___x_4943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4945_: u8 = 0;
    let mut v_ringId_4946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4953_: u8 = 0;
    let mut v___x_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4957_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4926_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(
                    v_e_4913_, v_a_4915_, v_a_4920_,
                );
                if leanh::lean_obj_tag(v___x_4926_) == 0 {
                    v_a_4927_ = leanh::lean_ctor_get(v___x_4926_, 0);
                    leanh::lean_inc(v_a_4927_);
                    leanh::lean_dec_ref_known(v___x_4926_, 1);
                    if leanh::lean_obj_tag(v_a_4927_) == 1 {
                        v_ringId_4928_ = leanh::lean_ctor_get(v_a_4914_, 0);
                        v_val_4929_ = leanh::lean_ctor_get(v_a_4927_, 0);
                        leanh::lean_inc(v_val_4929_);
                        leanh::lean_dec_ref_known(v_a_4927_, 1);
                        v___x_4930_ = lean_nat_dec_eq(v_val_4929_, v_ringId_4928_);
                        leanh::lean_dec(v_val_4929_);
                        if v___x_4930_ == 0 {
                            v___x_4931_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_4916_);
                            if leanh::lean_obj_tag(v___x_4931_) == 0 {
                                v_a_4932_ = leanh::lean_ctor_get(v___x_4931_, 0);
                                leanh::lean_inc(v_a_4932_);
                                leanh::lean_dec_ref_known(v___x_4931_, 1);
                                v___x_4933_ = (leanh::lean_unbox(v_a_4932_) as u8);
                                leanh::lean_dec(v_a_4932_);
                                if v___x_4933_ == 0 {
                                    leanh::lean_dec_ref(v_e_4913_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_4934_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1_once), _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1);
                                    v___x_4935_ = l_Lean_indentExpr(v_e_4913_);
                                    v___x_4936_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4936_, 0, v___x_4934_);
                                    leanh::lean_ctor_set(v___x_4936_, 1, v___x_4935_);
                                    v___x_4937_ = l_Lean_Meta_Sym_reportIssue(
                                        v___x_4936_,
                                        v_a_4916_,
                                        v_a_4917_,
                                        v_a_4918_,
                                        v_a_4919_,
                                        v_a_4920_,
                                        v_a_4921_,
                                    );
                                    if leanh::lean_obj_tag(v___x_4937_) == 0 {
                                        leanh::lean_dec_ref_known(v___x_4937_, 1);
                                        state = 1;
                                        continue;
                                    } else {
                                        return v___x_4937_;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_e_4913_);
                                v_a_4938_ = leanh::lean_ctor_get(v___x_4931_, 0);
                                v_isSharedCheck_4945_ =
                                    (!leanh::lean_is_exclusive(v___x_4931_)) as u8;
                                if v_isSharedCheck_4945_ == 0 {
                                    v___x_4940_ = v___x_4931_;
                                    v_isShared_4941_ = v_isSharedCheck_4945_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4938_);
                                    leanh::lean_dec(v___x_4931_);
                                    v___x_4940_ = leanh::lean_box(0);
                                    v_isShared_4941_ = v_isSharedCheck_4945_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_e_4913_);
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_4927_);
                        v_ringId_4946_ = leanh::lean_ctor_get(v_a_4914_, 0);
                        leanh::lean_inc(v_ringId_4946_);
                        v___f_4947_ = leanh::lean_alloc_closure(
                            l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___lam__0
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        leanh::lean_closure_set(v___f_4947_, 0, v_e_4913_);
                        leanh::lean_closure_set(v___f_4947_, 1, v_ringId_4946_);
                        v___x_4948_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                        v___x_4949_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4948_, v___f_4947_, v_a_4915_);
                        return v___x_4949_;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_4913_);
                    v_a_4950_ = leanh::lean_ctor_get(v___x_4926_, 0);
                    v_isSharedCheck_4957_ = (!leanh::lean_is_exclusive(v___x_4926_)) as u8;
                    if v_isSharedCheck_4957_ == 0 {
                        v___x_4952_ = v___x_4926_;
                        v_isShared_4953_ = v_isSharedCheck_4957_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4950_);
                        leanh::lean_dec(v___x_4926_);
                        v___x_4952_ = leanh::lean_box(0);
                        v_isShared_4953_ = v_isSharedCheck_4957_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4924_ = leanh::lean_box(0);
                v___x_4925_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4925_, 0, v___x_4924_);
                return v___x_4925_;
            }
            2 => {
                if v_isShared_4941_ == 0 {
                    v___x_4943_ = v___x_4940_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4944_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4944_, 0, v_a_4938_);
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
                    v_reuseFailAlloc_4956_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4956_, 0, v_a_4950_);
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
    mut v_e_4958_: *mut leanh::LeanObject,
    mut v_a_4959_: *mut leanh::LeanObject,
    mut v_a_4960_: *mut leanh::LeanObject,
    mut v_a_4961_: *mut leanh::LeanObject,
    mut v_a_4962_: *mut leanh::LeanObject,
    mut v_a_4963_: *mut leanh::LeanObject,
    mut v_a_4964_: *mut leanh::LeanObject,
    mut v_a_4965_: *mut leanh::LeanObject,
    mut v_a_4966_: *mut leanh::LeanObject,
    mut v_a_4967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4968_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(
        v_e_4958_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_,
        v_a_4966_,
    );
    leanh::lean_dec(v_a_4966_);
    leanh::lean_dec_ref(v_a_4965_);
    leanh::lean_dec(v_a_4964_);
    leanh::lean_dec_ref(v_a_4963_);
    leanh::lean_dec(v_a_4962_);
    leanh::lean_dec_ref(v_a_4961_);
    leanh::lean_dec(v_a_4960_);
    leanh::lean_dec_ref(v_a_4959_);
    return v_res_4968_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(
    mut v_e_4969_: *mut leanh::LeanObject,
    mut v_a_4970_: *mut leanh::LeanObject,
    mut v_a_4971_: *mut leanh::LeanObject,
    mut v_a_4972_: *mut leanh::LeanObject,
    mut v_a_4973_: *mut leanh::LeanObject,
    mut v_a_4974_: *mut leanh::LeanObject,
    mut v_a_4975_: *mut leanh::LeanObject,
    mut v_a_4976_: *mut leanh::LeanObject,
    mut v_a_4977_: *mut leanh::LeanObject,
    mut v_a_4978_: *mut leanh::LeanObject,
    mut v_a_4979_: *mut leanh::LeanObject,
    mut v_a_4980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4982_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(
        v_e_4969_, v_a_4970_, v_a_4971_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_,
        v_a_4980_,
    );
    return v___x_4982_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___boxed(
    mut v_e_4983_: *mut leanh::LeanObject,
    mut v_a_4984_: *mut leanh::LeanObject,
    mut v_a_4985_: *mut leanh::LeanObject,
    mut v_a_4986_: *mut leanh::LeanObject,
    mut v_a_4987_: *mut leanh::LeanObject,
    mut v_a_4988_: *mut leanh::LeanObject,
    mut v_a_4989_: *mut leanh::LeanObject,
    mut v_a_4990_: *mut leanh::LeanObject,
    mut v_a_4991_: *mut leanh::LeanObject,
    mut v_a_4992_: *mut leanh::LeanObject,
    mut v_a_4993_: *mut leanh::LeanObject,
    mut v_a_4994_: *mut leanh::LeanObject,
    mut v_a_4995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4996_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(
        v_e_4983_, v_a_4984_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_,
        v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_,
    );
    leanh::lean_dec(v_a_4994_);
    leanh::lean_dec_ref(v_a_4993_);
    leanh::lean_dec(v_a_4992_);
    leanh::lean_dec_ref(v_a_4991_);
    leanh::lean_dec(v_a_4990_);
    leanh::lean_dec_ref(v_a_4989_);
    leanh::lean_dec(v_a_4988_);
    leanh::lean_dec_ref(v_a_4987_);
    leanh::lean_dec(v_a_4986_);
    leanh::lean_dec(v_a_4985_);
    leanh::lean_dec_ref(v_a_4984_);
    return v_res_4996_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0(
    mut v_00_u03b2_4997_: *mut leanh::LeanObject,
    mut v_x_4998_: *mut leanh::LeanObject,
    mut v_x_4999_: *mut leanh::LeanObject,
    mut v_x_5000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5001_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_x_4998_, v_x_4999_, v_x_5000_);
    return v___x_5001_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(
    mut v_00_u03b2_5002_: *mut leanh::LeanObject,
    mut v_x_5003_: *mut leanh::LeanObject,
    mut v_x_5004_: usize,
    mut v_x_5005_: usize,
    mut v_x_5006_: *mut leanh::LeanObject,
    mut v_x_5007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5008_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_5003_, v_x_5004_, v_x_5005_, v_x_5006_, v_x_5007_);
    return v___x_5008_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___boxed(
    mut v_00_u03b2_5009_: *mut leanh::LeanObject,
    mut v_x_5010_: *mut leanh::LeanObject,
    mut v_x_5011_: *mut leanh::LeanObject,
    mut v_x_5012_: *mut leanh::LeanObject,
    mut v_x_5013_: *mut leanh::LeanObject,
    mut v_x_5014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_7519__boxed_5015_: usize = 0;
    let mut v_x_7520__boxed_5016_: usize = 0;
    let mut v_res_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_7519__boxed_5015_ = leanh::lean_unbox_usize(v_x_5011_);
    leanh::lean_dec(v_x_5011_);
    v_x_7520__boxed_5016_ = leanh::lean_unbox_usize(v_x_5012_);
    leanh::lean_dec(v_x_5012_);
    v_res_5017_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(v_00_u03b2_5009_, v_x_5010_, v_x_7519__boxed_5015_, v_x_7520__boxed_5016_, v_x_5013_, v_x_5014_);
    return v_res_5017_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1(
    mut v_00_u03b2_5018_: *mut leanh::LeanObject,
    mut v_n_5019_: *mut leanh::LeanObject,
    mut v_k_5020_: *mut leanh::LeanObject,
    mut v_v_5021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5022_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v_n_5019_, v_k_5020_, v_v_5021_);
    return v___x_5022_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(
    mut v_00_u03b2_5023_: *mut leanh::LeanObject,
    mut v_depth_5024_: usize,
    mut v_keys_5025_: *mut leanh::LeanObject,
    mut v_vals_5026_: *mut leanh::LeanObject,
    mut v_heq_5027_: *mut leanh::LeanObject,
    mut v_i_5028_: *mut leanh::LeanObject,
    mut v_entries_5029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5030_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_5024_, v_keys_5025_, v_vals_5026_, v_i_5028_, v_entries_5029_);
    return v___x_5030_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_5031_: *mut leanh::LeanObject,
    mut v_depth_5032_: *mut leanh::LeanObject,
    mut v_keys_5033_: *mut leanh::LeanObject,
    mut v_vals_5034_: *mut leanh::LeanObject,
    mut v_heq_5035_: *mut leanh::LeanObject,
    mut v_i_5036_: *mut leanh::LeanObject,
    mut v_entries_5037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_5038_: usize = 0;
    let mut v_res_5039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5038_ = leanh::lean_unbox_usize(v_depth_5032_);
    leanh::lean_dec(v_depth_5032_);
    v_res_5039_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(v_00_u03b2_5031_, v_depth_boxed_5038_, v_keys_5033_, v_vals_5034_, v_heq_5035_, v_i_5036_, v_entries_5037_);
    leanh::lean_dec_ref(v_vals_5034_);
    leanh::lean_dec_ref(v_keys_5033_);
    return v_res_5039_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_5040_: *mut leanh::LeanObject,
    mut v_x_5041_: *mut leanh::LeanObject,
    mut v_x_5042_: *mut leanh::LeanObject,
    mut v_x_5043_: *mut leanh::LeanObject,
    mut v_x_5044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5045_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_5041_, v_x_5042_, v_x_5043_, v_x_5044_);
    return v___x_5045_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0(
    mut v_e_5046_: *mut leanh::LeanObject,
    mut v___f_5047_: *mut leanh::LeanObject,
    mut v___f_5048_: *mut leanh::LeanObject,
    mut v_size_5049_: *mut leanh::LeanObject,
    mut v_s_5050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_id_5051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_5055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_5056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_5058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_5059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_5060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_5061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_5062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_5063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_5064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_5065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_5066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_5067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5070_: u8 = 0;
    let mut v___x_5071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5076_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_5051_ = leanh::lean_ctor_get(v_s_5050_, 0);
                v_type_5052_ = leanh::lean_ctor_get(v_s_5050_, 1);
                v_u_5053_ = leanh::lean_ctor_get(v_s_5050_, 2);
                v_ringInst_5054_ = leanh::lean_ctor_get(v_s_5050_, 3);
                v_semiringInst_5055_ = leanh::lean_ctor_get(v_s_5050_, 4);
                v_charInst_x3f_5056_ = leanh::lean_ctor_get(v_s_5050_, 5);
                v_addFn_x3f_5057_ = leanh::lean_ctor_get(v_s_5050_, 6);
                v_mulFn_x3f_5058_ = leanh::lean_ctor_get(v_s_5050_, 7);
                v_subFn_x3f_5059_ = leanh::lean_ctor_get(v_s_5050_, 8);
                v_negFn_x3f_5060_ = leanh::lean_ctor_get(v_s_5050_, 9);
                v_powFn_x3f_5061_ = leanh::lean_ctor_get(v_s_5050_, 10);
                v_intCastFn_x3f_5062_ = leanh::lean_ctor_get(v_s_5050_, 11);
                v_natCastFn_x3f_5063_ = leanh::lean_ctor_get(v_s_5050_, 12);
                v_one_x3f_5064_ = leanh::lean_ctor_get(v_s_5050_, 13);
                v_vars_5065_ = leanh::lean_ctor_get(v_s_5050_, 14);
                v_varMap_5066_ = leanh::lean_ctor_get(v_s_5050_, 15);
                v_denote_5067_ = leanh::lean_ctor_get(v_s_5050_, 16);
                v_isSharedCheck_5076_ = (!leanh::lean_is_exclusive(v_s_5050_)) as u8;
                if v_isSharedCheck_5076_ == 0 {
                    v___x_5069_ = v_s_5050_;
                    v_isShared_5070_ = v_isSharedCheck_5076_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_denote_5067_);
                    leanh::lean_inc(v_varMap_5066_);
                    leanh::lean_inc(v_vars_5065_);
                    leanh::lean_inc(v_one_x3f_5064_);
                    leanh::lean_inc(v_natCastFn_x3f_5063_);
                    leanh::lean_inc(v_intCastFn_x3f_5062_);
                    leanh::lean_inc(v_powFn_x3f_5061_);
                    leanh::lean_inc(v_negFn_x3f_5060_);
                    leanh::lean_inc(v_subFn_x3f_5059_);
                    leanh::lean_inc(v_mulFn_x3f_5058_);
                    leanh::lean_inc(v_addFn_x3f_5057_);
                    leanh::lean_inc(v_charInst_x3f_5056_);
                    leanh::lean_inc(v_semiringInst_5055_);
                    leanh::lean_inc(v_ringInst_5054_);
                    leanh::lean_inc(v_u_5053_);
                    leanh::lean_inc(v_type_5052_);
                    leanh::lean_inc(v_id_5051_);
                    leanh::lean_dec(v_s_5050_);
                    v___x_5069_ = leanh::lean_box(0);
                    v_isShared_5070_ = v_isSharedCheck_5076_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_e_5046_);
                v___x_5071_ = l_Lean_PersistentArray_push___redArg(v_vars_5065_, v_e_5046_);
                v___x_5072_ = l_Lean_PersistentHashMap_insert___redArg(
                    v___f_5047_,
                    v___f_5048_,
                    v_varMap_5066_,
                    v_e_5046_,
                    v_size_5049_,
                );
                if v_isShared_5070_ == 0 {
                    leanh::lean_ctor_set(v___x_5069_, 15, v___x_5072_);
                    leanh::lean_ctor_set(v___x_5069_, 14, v___x_5071_);
                    v___x_5074_ = v___x_5069_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5075_ = leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 0, v_id_5051_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 1, v_type_5052_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 2, v_u_5053_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 3, v_ringInst_5054_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 4, v_semiringInst_5055_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 5, v_charInst_x3f_5056_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 6, v_addFn_x3f_5057_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 7, v_mulFn_x3f_5058_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 8, v_subFn_x3f_5059_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 9, v_negFn_x3f_5060_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 10, v_powFn_x3f_5061_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 11, v_intCastFn_x3f_5062_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 12, v_natCastFn_x3f_5063_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 13, v_one_x3f_5064_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 14, v___x_5071_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 15, v___x_5072_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 16, v_denote_5067_);
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
    mut v_toPure_5077_: *mut leanh::LeanObject,
    mut v_size_5078_: *mut leanh::LeanObject,
    mut v_____r_5079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5080_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5080_ =
        leanh::lean_apply_2(v_toPure_5077_, leanh::lean_box(0), v_size_5078_);
    return v___x_5080_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2(
    mut v_e_5081_: *mut leanh::LeanObject,
    mut v_inst_5082_: *mut leanh::LeanObject,
    mut v_toBind_5083_: *mut leanh::LeanObject,
    mut v___f_5084_: *mut leanh::LeanObject,
    mut v_____r_5085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5086_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
    v___x_5087_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_SolverExtension_markTerm___boxed as *mut core::ffi::c_void,
        14,
        3,
    );
    leanh::lean_closure_set(v___x_5087_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_5087_, 1, v___x_5086_);
    leanh::lean_closure_set(v___x_5087_, 2, v_e_5081_);
    v___x_5088_ = leanh::lean_apply_2(v_inst_5082_, leanh::lean_box(0), v___x_5087_);
    v___x_5089_ = leanh::lean_apply_4(
        v_toBind_5083_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5088_,
        v___f_5084_,
    );
    return v___x_5089_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3(
    mut v_inst_5090_: *mut leanh::LeanObject,
    mut v_e_5091_: *mut leanh::LeanObject,
    mut v_toBind_5092_: *mut leanh::LeanObject,
    mut v___f_5093_: *mut leanh::LeanObject,
    mut v_____r_5094_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5095_ = leanh::lean_apply_1(v_inst_5090_, v_e_5091_);
    v___x_5096_ = leanh::lean_apply_4(
        v_toBind_5092_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5095_,
        v___f_5093_,
    );
    return v___x_5096_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4(
    mut v___f_5097_: *mut leanh::LeanObject,
    mut v___f_5098_: *mut leanh::LeanObject,
    mut v_e_5099_: *mut leanh::LeanObject,
    mut v_toPure_5100_: *mut leanh::LeanObject,
    mut v_inst_5101_: *mut leanh::LeanObject,
    mut v_toBind_5102_: *mut leanh::LeanObject,
    mut v_inst_5103_: *mut leanh::LeanObject,
    mut v_modifyRing_5104_: *mut leanh::LeanObject,
    mut v_s_5105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_vars_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_5107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_vars_5106_ = leanh::lean_ctor_get(v_s_5105_, 14);
    leanh::lean_inc_ref(v_vars_5106_);
    v_varMap_5107_ = leanh::lean_ctor_get(v_s_5105_, 15);
    leanh::lean_inc_ref(v_varMap_5107_);
    leanh::lean_dec_ref(v_s_5105_);
    leanh::lean_inc_ref(v_e_5099_);
    leanh::lean_inc_ref(v___f_5098_);
    leanh::lean_inc_ref(v___f_5097_);
    v___x_5108_ = l_Lean_PersistentHashMap_find_x3f___redArg(
        v___f_5097_,
        v___f_5098_,
        v_varMap_5107_,
        v_e_5099_,
    );
    leanh::lean_dec_ref(v_varMap_5107_);
    if leanh::lean_obj_tag(v___x_5108_) == 1 {
        let mut v_val_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_vars_5106_);
        leanh::lean_dec(v_modifyRing_5104_);
        leanh::lean_dec(v_inst_5103_);
        leanh::lean_dec(v_toBind_5102_);
        leanh::lean_dec(v_inst_5101_);
        leanh::lean_dec_ref(v_e_5099_);
        leanh::lean_dec_ref(v___f_5098_);
        leanh::lean_dec_ref(v___f_5097_);
        v_val_5109_ = leanh::lean_ctor_get(v___x_5108_, 0);
        leanh::lean_inc(v_val_5109_);
        leanh::lean_dec_ref_known(v___x_5108_, 1);
        v___x_5110_ =
            leanh::lean_apply_2(v_toPure_5100_, leanh::lean_box(0), v_val_5109_);
        return v___x_5110_;
    } else {
        let mut v_size_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5112_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5113_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5115_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5117_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_5108_);
        v_size_5111_ = leanh::lean_ctor_get(v_vars_5106_, 2);
        leanh::lean_inc_n(v_size_5111_, 2);
        leanh::lean_dec_ref(v_vars_5106_);
        leanh::lean_inc_ref_n(v_e_5099_, 2);
        v___f_5112_ = leanh::lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        leanh::lean_closure_set(v___f_5112_, 0, v_e_5099_);
        leanh::lean_closure_set(v___f_5112_, 1, v___f_5097_);
        leanh::lean_closure_set(v___f_5112_, 2, v___f_5098_);
        leanh::lean_closure_set(v___f_5112_, 3, v_size_5111_);
        v___f_5113_ = leanh::lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_5113_, 0, v_toPure_5100_);
        leanh::lean_closure_set(v___f_5113_, 1, v_size_5111_);
        leanh::lean_inc_n(v_toBind_5102_, 2);
        v___f_5114_ = leanh::lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2 as *mut core::ffi::c_void,
            5,
            4,
        );
        leanh::lean_closure_set(v___f_5114_, 0, v_e_5099_);
        leanh::lean_closure_set(v___f_5114_, 1, v_inst_5101_);
        leanh::lean_closure_set(v___f_5114_, 2, v_toBind_5102_);
        leanh::lean_closure_set(v___f_5114_, 3, v___f_5113_);
        v___f_5115_ = leanh::lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3 as *mut core::ffi::c_void,
            5,
            4,
        );
        leanh::lean_closure_set(v___f_5115_, 0, v_inst_5103_);
        leanh::lean_closure_set(v___f_5115_, 1, v_e_5099_);
        leanh::lean_closure_set(v___f_5115_, 2, v_toBind_5102_);
        leanh::lean_closure_set(v___f_5115_, 3, v___f_5114_);
        v___x_5116_ = leanh::lean_apply_1(v_modifyRing_5104_, v___f_5112_);
        v___x_5117_ = leanh::lean_apply_4(
            v_toBind_5102_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_5116_,
            v___f_5115_,
        );
        return v___x_5117_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(
    mut v_inst_5120_: *mut leanh::LeanObject,
    mut v_inst_5121_: *mut leanh::LeanObject,
    mut v_inst_5122_: *mut leanh::LeanObject,
    mut v_inst_5123_: *mut leanh::LeanObject,
    mut v_e_5124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_5125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_5127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_5128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5125_ = leanh::lean_ctor_get(v_inst_5121_, 0);
    leanh::lean_inc_ref(v_toApplicative_5125_);
    v_toBind_5126_ = leanh::lean_ctor_get(v_inst_5121_, 1);
    leanh::lean_inc_n(v_toBind_5126_, 2);
    leanh::lean_dec_ref(v_inst_5121_);
    v_getRing_5127_ = leanh::lean_ctor_get(v_inst_5122_, 0);
    leanh::lean_inc(v_getRing_5127_);
    v_modifyRing_5128_ = leanh::lean_ctor_get(v_inst_5122_, 1);
    leanh::lean_inc(v_modifyRing_5128_);
    leanh::lean_dec_ref(v_inst_5122_);
    v_toPure_5129_ = leanh::lean_ctor_get(v_toApplicative_5125_, 1);
    leanh::lean_inc(v_toPure_5129_);
    leanh::lean_dec_ref(v_toApplicative_5125_);
    v___f_5130_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0;
    v___f_5131_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1;
    v___f_5132_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4 as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___f_5132_, 0, v___f_5130_);
    leanh::lean_closure_set(v___f_5132_, 1, v___f_5131_);
    leanh::lean_closure_set(v___f_5132_, 2, v_e_5124_);
    leanh::lean_closure_set(v___f_5132_, 3, v_toPure_5129_);
    leanh::lean_closure_set(v___f_5132_, 4, v_inst_5120_);
    leanh::lean_closure_set(v___f_5132_, 5, v_toBind_5126_);
    leanh::lean_closure_set(v___f_5132_, 6, v_inst_5123_);
    leanh::lean_closure_set(v___f_5132_, 7, v_modifyRing_5128_);
    v___x_5133_ = leanh::lean_apply_4(
        v_toBind_5126_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getRing_5127_,
        v___f_5132_,
    );
    return v___x_5133_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkVarCore(
    mut v_m_5134_: *mut leanh::LeanObject,
    mut v_inst_5135_: *mut leanh::LeanObject,
    mut v_inst_5136_: *mut leanh::LeanObject,
    mut v_inst_5137_: *mut leanh::LeanObject,
    mut v_inst_5138_: *mut leanh::LeanObject,
    mut v_e_5139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5140_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_e_5141_: *mut leanh::LeanObject,
    mut v___y_5142_: *mut leanh::LeanObject,
    mut v___y_5143_: *mut leanh::LeanObject,
    mut v___y_5144_: *mut leanh::LeanObject,
    mut v___y_5145_: *mut leanh::LeanObject,
    mut v___y_5146_: *mut leanh::LeanObject,
    mut v___y_5147_: *mut leanh::LeanObject,
    mut v___y_5148_: *mut leanh::LeanObject,
    mut v___y_5149_: *mut leanh::LeanObject,
    mut v___y_5150_: *mut leanh::LeanObject,
    mut v___y_5151_: *mut leanh::LeanObject,
    mut v___y_5152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5154_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_e_5155_: *mut leanh::LeanObject,
    mut v___y_5156_: *mut leanh::LeanObject,
    mut v___y_5157_: *mut leanh::LeanObject,
    mut v___y_5158_: *mut leanh::LeanObject,
    mut v___y_5159_: *mut leanh::LeanObject,
    mut v___y_5160_: *mut leanh::LeanObject,
    mut v___y_5161_: *mut leanh::LeanObject,
    mut v___y_5162_: *mut leanh::LeanObject,
    mut v___y_5163_: *mut leanh::LeanObject,
    mut v___y_5164_: *mut leanh::LeanObject,
    mut v___y_5165_: *mut leanh::LeanObject,
    mut v___y_5166_: *mut leanh::LeanObject,
    mut v___y_5167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_5166_);
    leanh::lean_dec_ref(v___y_5165_);
    leanh::lean_dec(v___y_5164_);
    leanh::lean_dec_ref(v___y_5163_);
    leanh::lean_dec(v___y_5162_);
    leanh::lean_dec_ref(v___y_5161_);
    leanh::lean_dec(v___y_5160_);
    leanh::lean_dec_ref(v___y_5159_);
    leanh::lean_dec(v___y_5158_);
    leanh::lean_dec(v___y_5157_);
    leanh::lean_dec_ref(v___y_5156_);
    return v_res_5168_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___lam__0(
    mut v_e_5171_: *mut leanh::LeanObject,
    mut v_size_5172_: *mut leanh::LeanObject,
    mut v_s_5173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toRing_5174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_5176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_5178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_5181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_5182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_5184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_5185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_5186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_5187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recheck_5188_: u8 = 0;
    let mut v_invSet_5189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_5190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_5191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_5192_: u8 = 0;
    let mut v___x_5194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5195_: u8 = 0;
    let mut v_id_5196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_5199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_5200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_5201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_5202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_5203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_5205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_5206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_5207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_5208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_5209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_5210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_5211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5215_: u8 = 0;
    let mut v___x_5216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5224_: u8 = 0;
    let mut v_isSharedCheck_5225_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_5174_ = leanh::lean_ctor_get(v_s_5173_, 0);
                v_invFn_x3f_5175_ = leanh::lean_ctor_get(v_s_5173_, 1);
                v_semiringId_x3f_5176_ = leanh::lean_ctor_get(v_s_5173_, 2);
                v_commSemiringInst_5177_ = leanh::lean_ctor_get(v_s_5173_, 3);
                v_commRingInst_5178_ = leanh::lean_ctor_get(v_s_5173_, 4);
                v_noZeroDivInst_x3f_5179_ = leanh::lean_ctor_get(v_s_5173_, 5);
                v_fieldInst_x3f_5180_ = leanh::lean_ctor_get(v_s_5173_, 6);
                v_powIdentityInst_x3f_5181_ = leanh::lean_ctor_get(v_s_5173_, 7);
                v_denoteEntries_5182_ = leanh::lean_ctor_get(v_s_5173_, 8);
                v_nextId_5183_ = leanh::lean_ctor_get(v_s_5173_, 9);
                v_steps_5184_ = leanh::lean_ctor_get(v_s_5173_, 10);
                v_queue_5185_ = leanh::lean_ctor_get(v_s_5173_, 11);
                v_basis_5186_ = leanh::lean_ctor_get(v_s_5173_, 12);
                v_diseqs_5187_ = leanh::lean_ctor_get(v_s_5173_, 13);
                v_recheck_5188_ = leanh::lean_ctor_get_uint8(
                    v_s_5173_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                );
                v_invSet_5189_ = leanh::lean_ctor_get(v_s_5173_, 14);
                v_powIdentityVarCount_5190_ = leanh::lean_ctor_get(v_s_5173_, 15);
                v_numEq0_x3f_5191_ = leanh::lean_ctor_get(v_s_5173_, 16);
                v_numEq0Updated_5192_ = leanh::lean_ctor_get_uint8(
                    v_s_5173_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_5225_ = (!leanh::lean_is_exclusive(v_s_5173_)) as u8;
                if v_isSharedCheck_5225_ == 0 {
                    v___x_5194_ = v_s_5173_;
                    v_isShared_5195_ = v_isSharedCheck_5225_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_numEq0_x3f_5191_);
                    leanh::lean_inc(v_powIdentityVarCount_5190_);
                    leanh::lean_inc(v_invSet_5189_);
                    leanh::lean_inc(v_diseqs_5187_);
                    leanh::lean_inc(v_basis_5186_);
                    leanh::lean_inc(v_queue_5185_);
                    leanh::lean_inc(v_steps_5184_);
                    leanh::lean_inc(v_nextId_5183_);
                    leanh::lean_inc(v_denoteEntries_5182_);
                    leanh::lean_inc(v_powIdentityInst_x3f_5181_);
                    leanh::lean_inc(v_fieldInst_x3f_5180_);
                    leanh::lean_inc(v_noZeroDivInst_x3f_5179_);
                    leanh::lean_inc(v_commRingInst_5178_);
                    leanh::lean_inc(v_commSemiringInst_5177_);
                    leanh::lean_inc(v_semiringId_x3f_5176_);
                    leanh::lean_inc(v_invFn_x3f_5175_);
                    leanh::lean_inc(v_toRing_5174_);
                    leanh::lean_dec(v_s_5173_);
                    v___x_5194_ = leanh::lean_box(0);
                    v_isShared_5195_ = v_isSharedCheck_5225_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_id_5196_ = leanh::lean_ctor_get(v_toRing_5174_, 0);
                v_type_5197_ = leanh::lean_ctor_get(v_toRing_5174_, 1);
                v_u_5198_ = leanh::lean_ctor_get(v_toRing_5174_, 2);
                v_ringInst_5199_ = leanh::lean_ctor_get(v_toRing_5174_, 3);
                v_semiringInst_5200_ = leanh::lean_ctor_get(v_toRing_5174_, 4);
                v_charInst_x3f_5201_ = leanh::lean_ctor_get(v_toRing_5174_, 5);
                v_addFn_x3f_5202_ = leanh::lean_ctor_get(v_toRing_5174_, 6);
                v_mulFn_x3f_5203_ = leanh::lean_ctor_get(v_toRing_5174_, 7);
                v_subFn_x3f_5204_ = leanh::lean_ctor_get(v_toRing_5174_, 8);
                v_negFn_x3f_5205_ = leanh::lean_ctor_get(v_toRing_5174_, 9);
                v_powFn_x3f_5206_ = leanh::lean_ctor_get(v_toRing_5174_, 10);
                v_intCastFn_x3f_5207_ = leanh::lean_ctor_get(v_toRing_5174_, 11);
                v_natCastFn_x3f_5208_ = leanh::lean_ctor_get(v_toRing_5174_, 12);
                v_one_x3f_5209_ = leanh::lean_ctor_get(v_toRing_5174_, 13);
                v_vars_5210_ = leanh::lean_ctor_get(v_toRing_5174_, 14);
                v_varMap_5211_ = leanh::lean_ctor_get(v_toRing_5174_, 15);
                v_denote_5212_ = leanh::lean_ctor_get(v_toRing_5174_, 16);
                v_isSharedCheck_5224_ = (!leanh::lean_is_exclusive(v_toRing_5174_)) as u8;
                if v_isSharedCheck_5224_ == 0 {
                    v___x_5214_ = v_toRing_5174_;
                    v_isShared_5215_ = v_isSharedCheck_5224_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_denote_5212_);
                    leanh::lean_inc(v_varMap_5211_);
                    leanh::lean_inc(v_vars_5210_);
                    leanh::lean_inc(v_one_x3f_5209_);
                    leanh::lean_inc(v_natCastFn_x3f_5208_);
                    leanh::lean_inc(v_intCastFn_x3f_5207_);
                    leanh::lean_inc(v_powFn_x3f_5206_);
                    leanh::lean_inc(v_negFn_x3f_5205_);
                    leanh::lean_inc(v_subFn_x3f_5204_);
                    leanh::lean_inc(v_mulFn_x3f_5203_);
                    leanh::lean_inc(v_addFn_x3f_5202_);
                    leanh::lean_inc(v_charInst_x3f_5201_);
                    leanh::lean_inc(v_semiringInst_5200_);
                    leanh::lean_inc(v_ringInst_5199_);
                    leanh::lean_inc(v_u_5198_);
                    leanh::lean_inc(v_type_5197_);
                    leanh::lean_inc(v_id_5196_);
                    leanh::lean_dec(v_toRing_5174_);
                    v___x_5214_ = leanh::lean_box(0);
                    v_isShared_5215_ = v_isSharedCheck_5224_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v_e_5171_);
                v___x_5216_ = l_Lean_PersistentArray_push___redArg(v_vars_5210_, v_e_5171_);
                v___x_5217_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_varMap_5211_, v_e_5171_, v_size_5172_);
                if v_isShared_5215_ == 0 {
                    leanh::lean_ctor_set(v___x_5214_, 15, v___x_5217_);
                    leanh::lean_ctor_set(v___x_5214_, 14, v___x_5216_);
                    v___x_5219_ = v___x_5214_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5223_ = leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 0, v_id_5196_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 1, v_type_5197_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 2, v_u_5198_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 3, v_ringInst_5199_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 4, v_semiringInst_5200_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 5, v_charInst_x3f_5201_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 6, v_addFn_x3f_5202_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 7, v_mulFn_x3f_5203_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 8, v_subFn_x3f_5204_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 9, v_negFn_x3f_5205_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 10, v_powFn_x3f_5206_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 11, v_intCastFn_x3f_5207_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 12, v_natCastFn_x3f_5208_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 13, v_one_x3f_5209_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 14, v___x_5216_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 15, v___x_5217_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 16, v_denote_5212_);
                    v___x_5219_ = v_reuseFailAlloc_5223_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5195_ == 0 {
                    leanh::lean_ctor_set(v___x_5194_, 0, v___x_5219_);
                    v___x_5221_ = v___x_5194_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5222_ = leanh::lean_alloc_ctor(0, 17, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 0, v___x_5219_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 1, v_invFn_x3f_5175_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 2, v_semiringId_x3f_5176_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5222_,
                        3,
                        v_commSemiringInst_5177_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 4, v_commRingInst_5178_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5222_,
                        5,
                        v_noZeroDivInst_x3f_5179_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 6, v_fieldInst_x3f_5180_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5222_,
                        7,
                        v_powIdentityInst_x3f_5181_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 8, v_denoteEntries_5182_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 9, v_nextId_5183_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 10, v_steps_5184_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 11, v_queue_5185_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 12, v_basis_5186_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 13, v_diseqs_5187_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 14, v_invSet_5189_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5222_,
                        15,
                        v_powIdentityVarCount_5190_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 16, v_numEq0_x3f_5191_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5222_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                        v_recheck_5188_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5222_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 17 + 1) as u32,
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
    mut v_e_5226_: *mut leanh::LeanObject,
    mut v___y_5227_: *mut leanh::LeanObject,
    mut v___y_5228_: *mut leanh::LeanObject,
    mut v___y_5229_: *mut leanh::LeanObject,
    mut v___y_5230_: *mut leanh::LeanObject,
    mut v___y_5231_: *mut leanh::LeanObject,
    mut v___y_5232_: *mut leanh::LeanObject,
    mut v___y_5233_: *mut leanh::LeanObject,
    mut v___y_5234_: *mut leanh::LeanObject,
    mut v___y_5235_: *mut leanh::LeanObject,
    mut v___y_5236_: *mut leanh::LeanObject,
    mut v___y_5237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5243_: u8 = 0;
    let mut v_toRing_5244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_5245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_5246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5260_: u8 = 0;
    let mut v___x_5262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5264_: u8 = 0;
    let mut v_unused_5265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5269_: u8 = 0;
    let mut v___x_5271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5273_: u8 = 0;
    let mut v_a_5274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5277_: u8 = 0;
    let mut v___x_5279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5281_: u8 = 0;
    let mut v_a_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5285_: u8 = 0;
    let mut v___x_5287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5289_: u8 = 0;
    let mut v_isSharedCheck_5290_: u8 = 0;
    let mut v_a_5291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5294_: u8 = 0;
    let mut v___x_5296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5297_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_5239_) == 0 {
                    v_a_5240_ = leanh::lean_ctor_get(v___x_5239_, 0);
                    v_isSharedCheck_5290_ = (!leanh::lean_is_exclusive(v___x_5239_)) as u8;
                    if v_isSharedCheck_5290_ == 0 {
                        v___x_5242_ = v___x_5239_;
                        v_isShared_5243_ = v_isSharedCheck_5290_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5240_);
                        leanh::lean_dec(v___x_5239_);
                        v___x_5242_ = leanh::lean_box(0);
                        v_isShared_5243_ = v_isSharedCheck_5290_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_5226_);
                    v_a_5291_ = leanh::lean_ctor_get(v___x_5239_, 0);
                    v_isSharedCheck_5298_ = (!leanh::lean_is_exclusive(v___x_5239_)) as u8;
                    if v_isSharedCheck_5298_ == 0 {
                        v___x_5293_ = v___x_5239_;
                        v_isShared_5294_ = v_isSharedCheck_5298_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5291_);
                        leanh::lean_dec(v___x_5239_);
                        v___x_5293_ = leanh::lean_box(0);
                        v_isShared_5294_ = v_isSharedCheck_5298_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v_toRing_5244_ = leanh::lean_ctor_get(v_a_5240_, 0);
                leanh::lean_inc_ref(v_toRing_5244_);
                leanh::lean_dec(v_a_5240_);
                v_vars_5245_ = leanh::lean_ctor_get(v_toRing_5244_, 14);
                leanh::lean_inc_ref(v_vars_5245_);
                v_varMap_5246_ = leanh::lean_ctor_get(v_toRing_5244_, 15);
                leanh::lean_inc_ref(v_varMap_5246_);
                leanh::lean_dec_ref(v_toRing_5244_);
                v___x_5247_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_varMap_5246_, v_e_5226_);
                leanh::lean_dec_ref(v_varMap_5246_);
                if leanh::lean_obj_tag(v___x_5247_) == 1 {
                    leanh::lean_dec_ref(v_vars_5245_);
                    leanh::lean_dec_ref(v_e_5226_);
                    v_val_5248_ = leanh::lean_ctor_get(v___x_5247_, 0);
                    leanh::lean_inc(v_val_5248_);
                    leanh::lean_dec_ref_known(v___x_5247_, 1);
                    if v_isShared_5243_ == 0 {
                        leanh::lean_ctor_set(v___x_5242_, 0, v_val_5248_);
                        v___x_5250_ = v___x_5242_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5251_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5251_, 0, v_val_5248_);
                        v___x_5250_ = v_reuseFailAlloc_5251_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_5247_);
                    leanh::lean_del_object(v___x_5242_);
                    v_size_5252_ = leanh::lean_ctor_get(v_vars_5245_, 2);
                    leanh::lean_inc_n(v_size_5252_, 2);
                    leanh::lean_dec_ref(v_vars_5245_);
                    leanh::lean_inc_ref(v_e_5226_);
                    v___f_5253_ = leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___lam__0 as *mut core::ffi::c_void, 3, 2);
                    leanh::lean_closure_set(v___f_5253_, 0, v_e_5226_);
                    leanh::lean_closure_set(v___f_5253_, 1, v_size_5252_);
                    v___x_5254_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(
                        v___f_5253_,
                        v___y_5227_,
                        v___y_5228_,
                    );
                    if leanh::lean_obj_tag(v___x_5254_) == 0 {
                        leanh::lean_dec_ref_known(v___x_5254_, 1);
                        leanh::lean_inc_ref(v_e_5226_);
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
                        if leanh::lean_obj_tag(v___x_5255_) == 0 {
                            leanh::lean_dec_ref_known(v___x_5255_, 1);
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
                            if leanh::lean_obj_tag(v___x_5257_) == 0 {
                                v_isSharedCheck_5264_ =
                                    (!leanh::lean_is_exclusive(v___x_5257_)) as u8;
                                if v_isSharedCheck_5264_ == 0 {
                                    v_unused_5265_ = leanh::lean_ctor_get(v___x_5257_, 0);
                                    leanh::lean_dec(v_unused_5265_);
                                    v___x_5259_ = v___x_5257_;
                                    v_isShared_5260_ = v_isSharedCheck_5264_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_dec(v___x_5257_);
                                    v___x_5259_ = leanh::lean_box(0);
                                    v_isShared_5260_ = v_isSharedCheck_5264_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_size_5252_);
                                v_a_5266_ = leanh::lean_ctor_get(v___x_5257_, 0);
                                v_isSharedCheck_5273_ =
                                    (!leanh::lean_is_exclusive(v___x_5257_)) as u8;
                                if v_isSharedCheck_5273_ == 0 {
                                    v___x_5268_ = v___x_5257_;
                                    v_isShared_5269_ = v_isSharedCheck_5273_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5266_);
                                    leanh::lean_dec(v___x_5257_);
                                    v___x_5268_ = leanh::lean_box(0);
                                    v_isShared_5269_ = v_isSharedCheck_5273_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_size_5252_);
                            leanh::lean_dec_ref(v_e_5226_);
                            v_a_5274_ = leanh::lean_ctor_get(v___x_5255_, 0);
                            v_isSharedCheck_5281_ =
                                (!leanh::lean_is_exclusive(v___x_5255_)) as u8;
                            if v_isSharedCheck_5281_ == 0 {
                                v___x_5276_ = v___x_5255_;
                                v_isShared_5277_ = v_isSharedCheck_5281_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5274_);
                                leanh::lean_dec(v___x_5255_);
                                v___x_5276_ = leanh::lean_box(0);
                                v_isShared_5277_ = v_isSharedCheck_5281_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_size_5252_);
                        leanh::lean_dec_ref(v_e_5226_);
                        v_a_5282_ = leanh::lean_ctor_get(v___x_5254_, 0);
                        v_isSharedCheck_5289_ =
                            (!leanh::lean_is_exclusive(v___x_5254_)) as u8;
                        if v_isSharedCheck_5289_ == 0 {
                            v___x_5284_ = v___x_5254_;
                            v_isShared_5285_ = v_isSharedCheck_5289_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5282_);
                            leanh::lean_dec(v___x_5254_);
                            v___x_5284_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_5259_, 0, v_size_5252_);
                    v___x_5262_ = v___x_5259_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5263_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5263_, 0, v_size_5252_);
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
                    v_reuseFailAlloc_5272_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5272_, 0, v_a_5266_);
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
                    v_reuseFailAlloc_5280_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5280_, 0, v_a_5274_);
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
                    v_reuseFailAlloc_5288_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5288_, 0, v_a_5282_);
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
                    v_reuseFailAlloc_5297_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5297_, 0, v_a_5291_);
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
    mut v_e_5299_: *mut leanh::LeanObject,
    mut v___y_5300_: *mut leanh::LeanObject,
    mut v___y_5301_: *mut leanh::LeanObject,
    mut v___y_5302_: *mut leanh::LeanObject,
    mut v___y_5303_: *mut leanh::LeanObject,
    mut v___y_5304_: *mut leanh::LeanObject,
    mut v___y_5305_: *mut leanh::LeanObject,
    mut v___y_5306_: *mut leanh::LeanObject,
    mut v___y_5307_: *mut leanh::LeanObject,
    mut v___y_5308_: *mut leanh::LeanObject,
    mut v___y_5309_: *mut leanh::LeanObject,
    mut v___y_5310_: *mut leanh::LeanObject,
    mut v___y_5311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5312_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(v_e_5299_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_, v___y_5309_, v___y_5310_);
    leanh::lean_dec(v___y_5310_);
    leanh::lean_dec_ref(v___y_5309_);
    leanh::lean_dec(v___y_5308_);
    leanh::lean_dec_ref(v___y_5307_);
    leanh::lean_dec(v___y_5306_);
    leanh::lean_dec_ref(v___y_5305_);
    leanh::lean_dec(v___y_5304_);
    leanh::lean_dec_ref(v___y_5303_);
    leanh::lean_dec(v___y_5302_);
    leanh::lean_dec(v___y_5301_);
    leanh::lean_dec_ref(v___y_5300_);
    return v_res_5312_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkVar(
    mut v_e_5313_: *mut leanh::LeanObject,
    mut v_a_5314_: *mut leanh::LeanObject,
    mut v_a_5315_: *mut leanh::LeanObject,
    mut v_a_5316_: *mut leanh::LeanObject,
    mut v_a_5317_: *mut leanh::LeanObject,
    mut v_a_5318_: *mut leanh::LeanObject,
    mut v_a_5319_: *mut leanh::LeanObject,
    mut v_a_5320_: *mut leanh::LeanObject,
    mut v_a_5321_: *mut leanh::LeanObject,
    mut v_a_5322_: *mut leanh::LeanObject,
    mut v_a_5323_: *mut leanh::LeanObject,
    mut v_a_5324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5326_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(v_e_5313_, v_a_5314_, v_a_5315_, v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_);
    return v___x_5326_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkVar___boxed(
    mut v_e_5327_: *mut leanh::LeanObject,
    mut v_a_5328_: *mut leanh::LeanObject,
    mut v_a_5329_: *mut leanh::LeanObject,
    mut v_a_5330_: *mut leanh::LeanObject,
    mut v_a_5331_: *mut leanh::LeanObject,
    mut v_a_5332_: *mut leanh::LeanObject,
    mut v_a_5333_: *mut leanh::LeanObject,
    mut v_a_5334_: *mut leanh::LeanObject,
    mut v_a_5335_: *mut leanh::LeanObject,
    mut v_a_5336_: *mut leanh::LeanObject,
    mut v_a_5337_: *mut leanh::LeanObject,
    mut v_a_5338_: *mut leanh::LeanObject,
    mut v_a_5339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5340_ = l_Lean_Meta_Grind_Arith_CommRing_mkVar(
        v_e_5327_, v_a_5328_, v_a_5329_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5333_, v_a_5334_,
        v_a_5335_, v_a_5336_, v_a_5337_, v_a_5338_,
    );
    leanh::lean_dec(v_a_5338_);
    leanh::lean_dec_ref(v_a_5337_);
    leanh::lean_dec(v_a_5336_);
    leanh::lean_dec_ref(v_a_5335_);
    leanh::lean_dec(v_a_5334_);
    leanh::lean_dec_ref(v_a_5333_);
    leanh::lean_dec(v_a_5332_);
    leanh::lean_dec_ref(v_a_5331_);
    leanh::lean_dec(v_a_5330_);
    leanh::lean_dec(v_a_5329_);
    leanh::lean_dec_ref(v_a_5328_);
    return v_res_5340_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_Poly(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM =
        _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Arith_Poly(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
}