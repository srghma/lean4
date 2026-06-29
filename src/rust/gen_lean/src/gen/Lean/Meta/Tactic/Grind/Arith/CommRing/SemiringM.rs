// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.SemiringM
// Imports: Lean.Meta.Tactic.Grind.Arith.CommRing.RingM Lean.Meta.Tactic.Grind.Arith.CommRing.MonadSemiring Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr Lean.Meta.Tactic.Grind.Arith.CommRing.Functions
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_int_dec_lt, lean_nat_abs, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_to_int, lean_panic_fn_borrowed, lean_st_ref_get,
    lean_uint64_to_usize, lean_usize_add, lean_usize_dec_le, lean_usize_land, lean_usize_mul,
    lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::GetElem::l_outOfBounds___redArg;
use crate::r#gen::Init::Prelude::l_instInhabitedForall___redArg___lam__0___boxed;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_get_x21___redArg, l_Lean_PersistentArray_push___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_find_x3f___redArg,
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_insert___redArg, l_Lean_PersistentHashMap_mkCollisionNode___redArg,
    l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Nat_mkType, l_Lean_instInhabitedExpr, l_Lean_mkApp3,
    l_Lean_mkApp4, l_Lean_mkAppB, l_Lean_mkConst, l_Lean_mkNatLit, l_Lean_mkRawNatLit,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::Message::{l_Lean_indentExpr, l_Lean_stringToMessageData};
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
use crate::r#gen::Lean::Meta::SynthInstance::l_Lean_Meta_synthInstance_x3f;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::DenoteExpr::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::Functions::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions,
    l_Lean_Meta_Grind_Arith_CommRing_checkInst,
    l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg,
    l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg,
    l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::MonadSemiring::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadSemiring,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadSemiring,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::RingM::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::Types::{
    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg, l_Lean_Meta_Grind_Arith_CommRing_ringExt,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg,
    l_Lean_Meta_Grind_SolverExtension_markTerm___boxed,
    l_Lean_Meta_Grind_SolverExtension_markTerm___redArg, l_Lean_Meta_Grind_instInhabitedGoalM,
};
pub static l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__1_value:
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
    m_fun: l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__2_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__1_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__0_value:
    crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 43,
    m_capacity: 43,
    m_length: 42,
    m_data: [
        96, 103, 114, 105, 110, 100, 96, 32, 105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114,
        114, 111, 114, 44, 32, 105, 110, 118, 97, 108, 105, 100, 32, 115, 101, 109, 105, 114, 105,
        110, 103, 73, 100, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___boxed
        as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__0_value:
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
static mut l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___boxed
        as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value:
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
static mut l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__2_value:
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
    m_data: [82, 105, 110, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__3_value:
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
    m_data: [79, 102, 83, 101, 109, 105, 114, 105, 110, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__4_value:
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
    m_data: [116, 111, 81, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__2_value)
            as *mut crate::leanh::LeanObject,
        10806710915646349764 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8254287559757149654 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__4_value)
            as *mut crate::leanh::LeanObject,
        5073726620895580904 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__0_value) as *mut crate::leanh::LeanObject,17313347264508353403 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__2_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [65, 100, 100, 82, 105, 103, 104, 116, 67, 97, 110, 99, 101, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__2_value) as *mut crate::leanh::LeanObject,2425446158037902625 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__0_value:
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
    m_data: [105, 110, 115, 116, 72, 65, 100, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        9594062259507646949 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__2_value:
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
    m_data: [83, 101, 109, 105, 114, 105, 110, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__3_value:
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
    m_data: [116, 111, 65, 100, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__3_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value_aux_1:
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
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value_aux_2:
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
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        12050285396929189622 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value:
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
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        5442360487226035463 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__5_value:
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
    m_data: [72, 65, 100, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__6_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__5_value
        ) as *mut crate::leanh::LeanObject,
        10393083817453678557 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__7_value:
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
    m_data: [104, 65, 100, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__7_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__5_value
        ) as *mut crate::leanh::LeanObject,
        10393083817453678557 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8_value:
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
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__7_value
        ) as *mut crate::leanh::LeanObject,
        10680564408669940870 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__0_value:
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
    m_data: [105, 110, 115, 116, 72, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        18134279130838690737 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__2_value:
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
    m_data: [116, 111, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__2_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value_aux_1:
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
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value_aux_2:
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
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        12050285396929189622 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value:
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
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        7102027102192867304 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__4_value:
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
    m_data: [72, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__5_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        2929883540436775422 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__6_value:
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
    m_data: [104, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__6_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        2929883540436775422 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7_value:
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
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__6_value
        ) as *mut crate::leanh::LeanObject,
        1611444129324655608 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__0_value:
    crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 38,
    m_capacity: 38,
    m_length: 37,
    m_data: [
        101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 105, 110, 32, 116, 119, 111, 32, 100,
        105, 102, 102, 101, 114, 101, 110, 116, 32, 115, 101, 109, 105, 114, 105, 110, 103, 115, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0_value:
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
static mut l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__1_value:
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
static mut l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__0_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 102, 105, 110, 100, 32, 105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 111, 78, 101, 103, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__2_value) as *mut crate::leanh::LeanObject,10806710915646349764 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,10040236838748678500 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 101, 103, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__2_value) as *mut crate::leanh::LeanObject,9626815015619986526 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__4_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 101, 103, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__4_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__2_value) as *mut crate::leanh::LeanObject,9626815015619986526 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__4_value) as *mut crate::leanh::LeanObject,17185717442815859305 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,17636616155771105671 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__2_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,17636616155771105671 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__2_value) as *mut crate::leanh::LeanObject,15578568367168711682 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__2_value) as *mut crate::leanh::LeanObject,12050285396929189622 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__2_value) as *mut crate::leanh::LeanObject,9341924117480681831 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 80, 111, 119, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,12847922472053947547 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 112, 111, 119, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__2_value) as *mut crate::leanh::LeanObject,12050285396929189622 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__3_value) as *mut crate::leanh::LeanObject,18388652353510661091 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__5_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 80, 111, 119, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__5_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__0_value) as *mut crate::leanh::LeanObject,12847922472053947547 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__5_value) as *mut crate::leanh::LeanObject,10422657989269798688 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__0_value: crate::leanh::LeanStringObject<48> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 48, m_capacity: 48, m_length: 47, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 67, 111, 109, 109, 82, 105, 110, 103, 46, 83, 101, 109, 105, 114, 105, 110, 103, 77, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__1_value: crate::leanh::LeanStringObject<104> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 104, m_capacity: 104, m_length: 103, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 67, 111, 109, 109, 82, 105, 110, 103, 46, 83, 101, 109, 105, 114, 105, 110, 103, 77, 46, 48, 46, 76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 67, 111, 109, 109, 82, 105, 110, 103, 46, 69, 120, 112, 114, 46, 100, 101, 110, 111, 116, 101, 65, 115, 82, 105, 110, 103, 69, 120, 112, 114, 46, 103, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__2_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___redArg(
    mut v_semiringId_3057_: *mut crate::leanh::LeanObject,
    mut v_x_3058_: *mut crate::leanh::LeanObject,
    mut v_a_3059_: *mut crate::leanh::LeanObject,
    mut v_a_3060_: *mut crate::leanh::LeanObject,
    mut v_a_3061_: *mut crate::leanh::LeanObject,
    mut v_a_3062_: *mut crate::leanh::LeanObject,
    mut v_a_3063_: *mut crate::leanh::LeanObject,
    mut v_a_3064_: *mut crate::leanh::LeanObject,
    mut v_a_3065_: *mut crate::leanh::LeanObject,
    mut v_a_3066_: *mut crate::leanh::LeanObject,
    mut v_a_3067_: *mut crate::leanh::LeanObject,
    mut v_a_3068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_3068_);
    crate::leanh::lean_inc_ref(v_a_3067_);
    crate::leanh::lean_inc(v_a_3066_);
    crate::leanh::lean_inc_ref(v_a_3065_);
    crate::leanh::lean_inc(v_a_3064_);
    crate::leanh::lean_inc_ref(v_a_3063_);
    crate::leanh::lean_inc(v_a_3062_);
    crate::leanh::lean_inc_ref(v_a_3061_);
    crate::leanh::lean_inc(v_a_3060_);
    crate::leanh::lean_inc(v_a_3059_);
    v___x_3070_ = crate::leanh::lean_apply_12(
        v_x_3058_,
        v_semiringId_3057_,
        v_a_3059_,
        v_a_3060_,
        v_a_3061_,
        v_a_3062_,
        v_a_3063_,
        v_a_3064_,
        v_a_3065_,
        v_a_3066_,
        v_a_3067_,
        v_a_3068_,
        crate::leanh::lean_box(0),
    );
    return v___x_3070_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___redArg___boxed(
    mut v_semiringId_3071_: *mut crate::leanh::LeanObject,
    mut v_x_3072_: *mut crate::leanh::LeanObject,
    mut v_a_3073_: *mut crate::leanh::LeanObject,
    mut v_a_3074_: *mut crate::leanh::LeanObject,
    mut v_a_3075_: *mut crate::leanh::LeanObject,
    mut v_a_3076_: *mut crate::leanh::LeanObject,
    mut v_a_3077_: *mut crate::leanh::LeanObject,
    mut v_a_3078_: *mut crate::leanh::LeanObject,
    mut v_a_3079_: *mut crate::leanh::LeanObject,
    mut v_a_3080_: *mut crate::leanh::LeanObject,
    mut v_a_3081_: *mut crate::leanh::LeanObject,
    mut v_a_3082_: *mut crate::leanh::LeanObject,
    mut v_a_3083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3084_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___redArg(
        v_semiringId_3071_,
        v_x_3072_,
        v_a_3073_,
        v_a_3074_,
        v_a_3075_,
        v_a_3076_,
        v_a_3077_,
        v_a_3078_,
        v_a_3079_,
        v_a_3080_,
        v_a_3081_,
        v_a_3082_,
    );
    crate::leanh::lean_dec(v_a_3082_);
    crate::leanh::lean_dec_ref(v_a_3081_);
    crate::leanh::lean_dec(v_a_3080_);
    crate::leanh::lean_dec_ref(v_a_3079_);
    crate::leanh::lean_dec(v_a_3078_);
    crate::leanh::lean_dec_ref(v_a_3077_);
    crate::leanh::lean_dec(v_a_3076_);
    crate::leanh::lean_dec_ref(v_a_3075_);
    crate::leanh::lean_dec(v_a_3074_);
    crate::leanh::lean_dec(v_a_3073_);
    return v_res_3084_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run(
    mut v_00_u03b1_3085_: *mut crate::leanh::LeanObject,
    mut v_semiringId_3086_: *mut crate::leanh::LeanObject,
    mut v_x_3087_: *mut crate::leanh::LeanObject,
    mut v_a_3088_: *mut crate::leanh::LeanObject,
    mut v_a_3089_: *mut crate::leanh::LeanObject,
    mut v_a_3090_: *mut crate::leanh::LeanObject,
    mut v_a_3091_: *mut crate::leanh::LeanObject,
    mut v_a_3092_: *mut crate::leanh::LeanObject,
    mut v_a_3093_: *mut crate::leanh::LeanObject,
    mut v_a_3094_: *mut crate::leanh::LeanObject,
    mut v_a_3095_: *mut crate::leanh::LeanObject,
    mut v_a_3096_: *mut crate::leanh::LeanObject,
    mut v_a_3097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_3097_);
    crate::leanh::lean_inc_ref(v_a_3096_);
    crate::leanh::lean_inc(v_a_3095_);
    crate::leanh::lean_inc_ref(v_a_3094_);
    crate::leanh::lean_inc(v_a_3093_);
    crate::leanh::lean_inc_ref(v_a_3092_);
    crate::leanh::lean_inc(v_a_3091_);
    crate::leanh::lean_inc_ref(v_a_3090_);
    crate::leanh::lean_inc(v_a_3089_);
    crate::leanh::lean_inc(v_a_3088_);
    v___x_3099_ = crate::leanh::lean_apply_12(
        v_x_3087_,
        v_semiringId_3086_,
        v_a_3088_,
        v_a_3089_,
        v_a_3090_,
        v_a_3091_,
        v_a_3092_,
        v_a_3093_,
        v_a_3094_,
        v_a_3095_,
        v_a_3096_,
        v_a_3097_,
        crate::leanh::lean_box(0),
    );
    return v___x_3099_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___boxed(
    mut v_00_u03b1_3100_: *mut crate::leanh::LeanObject,
    mut v_semiringId_3101_: *mut crate::leanh::LeanObject,
    mut v_x_3102_: *mut crate::leanh::LeanObject,
    mut v_a_3103_: *mut crate::leanh::LeanObject,
    mut v_a_3104_: *mut crate::leanh::LeanObject,
    mut v_a_3105_: *mut crate::leanh::LeanObject,
    mut v_a_3106_: *mut crate::leanh::LeanObject,
    mut v_a_3107_: *mut crate::leanh::LeanObject,
    mut v_a_3108_: *mut crate::leanh::LeanObject,
    mut v_a_3109_: *mut crate::leanh::LeanObject,
    mut v_a_3110_: *mut crate::leanh::LeanObject,
    mut v_a_3111_: *mut crate::leanh::LeanObject,
    mut v_a_3112_: *mut crate::leanh::LeanObject,
    mut v_a_3113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3114_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run(
        v_00_u03b1_3100_,
        v_semiringId_3101_,
        v_x_3102_,
        v_a_3103_,
        v_a_3104_,
        v_a_3105_,
        v_a_3106_,
        v_a_3107_,
        v_a_3108_,
        v_a_3109_,
        v_a_3110_,
        v_a_3111_,
        v_a_3112_,
    );
    crate::leanh::lean_dec(v_a_3112_);
    crate::leanh::lean_dec_ref(v_a_3111_);
    crate::leanh::lean_dec(v_a_3110_);
    crate::leanh::lean_dec_ref(v_a_3109_);
    crate::leanh::lean_dec(v_a_3108_);
    crate::leanh::lean_dec_ref(v_a_3107_);
    crate::leanh::lean_dec(v_a_3106_);
    crate::leanh::lean_dec_ref(v_a_3105_);
    crate::leanh::lean_dec(v_a_3104_);
    crate::leanh::lean_dec(v_a_3103_);
    return v_res_3114_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___redArg(
    mut v_a_3115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_3115_);
    v___x_3117_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3117_, 0, v_a_3115_);
    return v___x_3117_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___redArg___boxed(
    mut v_a_3118_: *mut crate::leanh::LeanObject,
    mut v_a_3119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3120_ = l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___redArg(v_a_3118_);
    crate::leanh::lean_dec(v_a_3118_);
    return v_res_3120_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getSemiringId(
    mut v_a_3121_: *mut crate::leanh::LeanObject,
    mut v_a_3122_: *mut crate::leanh::LeanObject,
    mut v_a_3123_: *mut crate::leanh::LeanObject,
    mut v_a_3124_: *mut crate::leanh::LeanObject,
    mut v_a_3125_: *mut crate::leanh::LeanObject,
    mut v_a_3126_: *mut crate::leanh::LeanObject,
    mut v_a_3127_: *mut crate::leanh::LeanObject,
    mut v_a_3128_: *mut crate::leanh::LeanObject,
    mut v_a_3129_: *mut crate::leanh::LeanObject,
    mut v_a_3130_: *mut crate::leanh::LeanObject,
    mut v_a_3131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_3121_);
    v___x_3133_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3133_, 0, v_a_3121_);
    return v___x_3133_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___boxed(
    mut v_a_3134_: *mut crate::leanh::LeanObject,
    mut v_a_3135_: *mut crate::leanh::LeanObject,
    mut v_a_3136_: *mut crate::leanh::LeanObject,
    mut v_a_3137_: *mut crate::leanh::LeanObject,
    mut v_a_3138_: *mut crate::leanh::LeanObject,
    mut v_a_3139_: *mut crate::leanh::LeanObject,
    mut v_a_3140_: *mut crate::leanh::LeanObject,
    mut v_a_3141_: *mut crate::leanh::LeanObject,
    mut v_a_3142_: *mut crate::leanh::LeanObject,
    mut v_a_3143_: *mut crate::leanh::LeanObject,
    mut v_a_3144_: *mut crate::leanh::LeanObject,
    mut v_a_3145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3146_ = l_Lean_Meta_Grind_Arith_CommRing_getSemiringId(
        v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_, v_a_3138_, v_a_3139_, v_a_3140_, v_a_3141_,
        v_a_3142_, v_a_3143_, v_a_3144_,
    );
    crate::leanh::lean_dec(v_a_3144_);
    crate::leanh::lean_dec_ref(v_a_3143_);
    crate::leanh::lean_dec(v_a_3142_);
    crate::leanh::lean_dec_ref(v_a_3141_);
    crate::leanh::lean_dec(v_a_3140_);
    crate::leanh::lean_dec_ref(v_a_3139_);
    crate::leanh::lean_dec(v_a_3138_);
    crate::leanh::lean_dec_ref(v_a_3137_);
    crate::leanh::lean_dec(v_a_3136_);
    crate::leanh::lean_dec(v_a_3135_);
    crate::leanh::lean_dec(v_a_3134_);
    return v_res_3146_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0(
    mut v_e_3147_: *mut crate::leanh::LeanObject,
    mut v___y_3148_: *mut crate::leanh::LeanObject,
    mut v___y_3149_: *mut crate::leanh::LeanObject,
    mut v___y_3150_: *mut crate::leanh::LeanObject,
    mut v___y_3151_: *mut crate::leanh::LeanObject,
    mut v___y_3152_: *mut crate::leanh::LeanObject,
    mut v___y_3153_: *mut crate::leanh::LeanObject,
    mut v___y_3154_: *mut crate::leanh::LeanObject,
    mut v___y_3155_: *mut crate::leanh::LeanObject,
    mut v___y_3156_: *mut crate::leanh::LeanObject,
    mut v___y_3157_: *mut crate::leanh::LeanObject,
    mut v___y_3158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3160_ = l_Lean_Meta_Sym_canon(
        v_e_3147_,
        v___y_3153_,
        v___y_3154_,
        v___y_3155_,
        v___y_3156_,
        v___y_3157_,
        v___y_3158_,
    );
    if crate::leanh::lean_obj_tag(v___x_3160_) == 0 {
        let mut v_a_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_3161_ = crate::leanh::lean_ctor_get(v___x_3160_, 0);
        crate::leanh::lean_inc(v_a_3161_);
        crate::leanh::lean_dec_ref_known(v___x_3160_, 1);
        v___x_3162_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_3161_, v___y_3154_);
        return v___x_3162_;
    } else {
        return v___x_3160_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0___boxed(
    mut v_e_3163_: *mut crate::leanh::LeanObject,
    mut v___y_3164_: *mut crate::leanh::LeanObject,
    mut v___y_3165_: *mut crate::leanh::LeanObject,
    mut v___y_3166_: *mut crate::leanh::LeanObject,
    mut v___y_3167_: *mut crate::leanh::LeanObject,
    mut v___y_3168_: *mut crate::leanh::LeanObject,
    mut v___y_3169_: *mut crate::leanh::LeanObject,
    mut v___y_3170_: *mut crate::leanh::LeanObject,
    mut v___y_3171_: *mut crate::leanh::LeanObject,
    mut v___y_3172_: *mut crate::leanh::LeanObject,
    mut v___y_3173_: *mut crate::leanh::LeanObject,
    mut v___y_3174_: *mut crate::leanh::LeanObject,
    mut v___y_3175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3176_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0(
        v_e_3163_,
        v___y_3164_,
        v___y_3165_,
        v___y_3166_,
        v___y_3167_,
        v___y_3168_,
        v___y_3169_,
        v___y_3170_,
        v___y_3171_,
        v___y_3172_,
        v___y_3173_,
        v___y_3174_,
    );
    crate::leanh::lean_dec(v___y_3174_);
    crate::leanh::lean_dec_ref(v___y_3173_);
    crate::leanh::lean_dec(v___y_3172_);
    crate::leanh::lean_dec_ref(v___y_3171_);
    crate::leanh::lean_dec(v___y_3170_);
    crate::leanh::lean_dec_ref(v___y_3169_);
    crate::leanh::lean_dec(v___y_3168_);
    crate::leanh::lean_dec_ref(v___y_3167_);
    crate::leanh::lean_dec(v___y_3166_);
    crate::leanh::lean_dec(v___y_3165_);
    crate::leanh::lean_dec(v___y_3164_);
    return v_res_3176_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__1(
    mut v_e_3177_: *mut crate::leanh::LeanObject,
    mut v___y_3178_: *mut crate::leanh::LeanObject,
    mut v___y_3179_: *mut crate::leanh::LeanObject,
    mut v___y_3180_: *mut crate::leanh::LeanObject,
    mut v___y_3181_: *mut crate::leanh::LeanObject,
    mut v___y_3182_: *mut crate::leanh::LeanObject,
    mut v___y_3183_: *mut crate::leanh::LeanObject,
    mut v___y_3184_: *mut crate::leanh::LeanObject,
    mut v___y_3185_: *mut crate::leanh::LeanObject,
    mut v___y_3186_: *mut crate::leanh::LeanObject,
    mut v___y_3187_: *mut crate::leanh::LeanObject,
    mut v___y_3188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3190_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
        v_e_3177_,
        v___y_3185_,
        v___y_3186_,
        v___y_3187_,
        v___y_3188_,
    );
    return v___x_3190_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__1___boxed(
    mut v_e_3191_: *mut crate::leanh::LeanObject,
    mut v___y_3192_: *mut crate::leanh::LeanObject,
    mut v___y_3193_: *mut crate::leanh::LeanObject,
    mut v___y_3194_: *mut crate::leanh::LeanObject,
    mut v___y_3195_: *mut crate::leanh::LeanObject,
    mut v___y_3196_: *mut crate::leanh::LeanObject,
    mut v___y_3197_: *mut crate::leanh::LeanObject,
    mut v___y_3198_: *mut crate::leanh::LeanObject,
    mut v___y_3199_: *mut crate::leanh::LeanObject,
    mut v___y_3200_: *mut crate::leanh::LeanObject,
    mut v___y_3201_: *mut crate::leanh::LeanObject,
    mut v___y_3202_: *mut crate::leanh::LeanObject,
    mut v___y_3203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3204_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__1(
        v_e_3191_,
        v___y_3192_,
        v___y_3193_,
        v___y_3194_,
        v___y_3195_,
        v___y_3196_,
        v___y_3197_,
        v___y_3198_,
        v___y_3199_,
        v___y_3200_,
        v___y_3201_,
        v___y_3202_,
    );
    crate::leanh::lean_dec(v___y_3202_);
    crate::leanh::lean_dec_ref(v___y_3201_);
    crate::leanh::lean_dec(v___y_3200_);
    crate::leanh::lean_dec_ref(v___y_3199_);
    crate::leanh::lean_dec(v___y_3198_);
    crate::leanh::lean_dec_ref(v___y_3197_);
    crate::leanh::lean_dec(v___y_3196_);
    crate::leanh::lean_dec_ref(v___y_3195_);
    crate::leanh::lean_dec(v___y_3194_);
    crate::leanh::lean_dec(v___y_3193_);
    crate::leanh::lean_dec(v___y_3192_);
    return v_res_3204_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0(
    mut v_msgData_3211_: *mut crate::leanh::LeanObject,
    mut v___y_3212_: *mut crate::leanh::LeanObject,
    mut v___y_3213_: *mut crate::leanh::LeanObject,
    mut v___y_3214_: *mut crate::leanh::LeanObject,
    mut v___y_3215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3217_ = lean_st_ref_get(v___y_3215_);
    v_env_3218_ = crate::leanh::lean_ctor_get(v___x_3217_, 0);
    crate::leanh::lean_inc_ref(v_env_3218_);
    crate::leanh::lean_dec(v___x_3217_);
    v___x_3219_ = lean_st_ref_get(v___y_3213_);
    v_mctx_3220_ = crate::leanh::lean_ctor_get(v___x_3219_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3220_);
    crate::leanh::lean_dec(v___x_3219_);
    v_lctx_3221_ = crate::leanh::lean_ctor_get(v___y_3212_, 2);
    v_options_3222_ = crate::leanh::lean_ctor_get(v___y_3214_, 2);
    crate::leanh::lean_inc_ref(v_options_3222_);
    crate::leanh::lean_inc_ref(v_lctx_3221_);
    v___x_3223_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3223_, 0, v_env_3218_);
    crate::leanh::lean_ctor_set(v___x_3223_, 1, v_mctx_3220_);
    crate::leanh::lean_ctor_set(v___x_3223_, 2, v_lctx_3221_);
    crate::leanh::lean_ctor_set(v___x_3223_, 3, v_options_3222_);
    v___x_3224_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3224_, 0, v___x_3223_);
    crate::leanh::lean_ctor_set(v___x_3224_, 1, v_msgData_3211_);
    v___x_3225_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3225_, 0, v___x_3224_);
    return v___x_3225_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0___boxed(
    mut v_msgData_3226_: *mut crate::leanh::LeanObject,
    mut v___y_3227_: *mut crate::leanh::LeanObject,
    mut v___y_3228_: *mut crate::leanh::LeanObject,
    mut v___y_3229_: *mut crate::leanh::LeanObject,
    mut v___y_3230_: *mut crate::leanh::LeanObject,
    mut v___y_3231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3232_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0(v_msgData_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
    crate::leanh::lean_dec(v___y_3230_);
    crate::leanh::lean_dec_ref(v___y_3229_);
    crate::leanh::lean_dec(v___y_3228_);
    crate::leanh::lean_dec_ref(v___y_3227_);
    return v_res_3232_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(
    mut v_msg_3233_: *mut crate::leanh::LeanObject,
    mut v___y_3234_: *mut crate::leanh::LeanObject,
    mut v___y_3235_: *mut crate::leanh::LeanObject,
    mut v___y_3236_: *mut crate::leanh::LeanObject,
    mut v___y_3237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3244_: u8 = 0;
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3249_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3239_ = crate::leanh::lean_ctor_get(v___y_3236_, 5);
                v___x_3240_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0(v_msg_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
                v_a_3241_ = crate::leanh::lean_ctor_get(v___x_3240_, 0);
                v_isSharedCheck_3249_ = (!crate::leanh::lean_is_exclusive(v___x_3240_)) as u8;
                if v_isSharedCheck_3249_ == 0 {
                    v___x_3243_ = v___x_3240_;
                    v_isShared_3244_ = v_isSharedCheck_3249_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3241_);
                    crate::leanh::lean_dec(v___x_3240_);
                    v___x_3243_ = crate::leanh::lean_box(0);
                    v_isShared_3244_ = v_isSharedCheck_3249_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_3239_);
                v___x_3245_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3245_, 0, v_ref_3239_);
                crate::leanh::lean_ctor_set(v___x_3245_, 1, v_a_3241_);
                if v_isShared_3244_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3243_, 1);
                    crate::leanh::lean_ctor_set(v___x_3243_, 0, v___x_3245_);
                    v___x_3247_ = v___x_3243_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3248_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3245_);
                    v___x_3247_ = v_reuseFailAlloc_3248_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3247_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg___boxed(
    mut v_msg_3250_: *mut crate::leanh::LeanObject,
    mut v___y_3251_: *mut crate::leanh::LeanObject,
    mut v___y_3252_: *mut crate::leanh::LeanObject,
    mut v___y_3253_: *mut crate::leanh::LeanObject,
    mut v___y_3254_: *mut crate::leanh::LeanObject,
    mut v___y_3255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3256_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v_msg_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_);
    crate::leanh::lean_dec(v___y_3254_);
    crate::leanh::lean_dec_ref(v___y_3253_);
    crate::leanh::lean_dec(v___y_3252_);
    crate::leanh::lean_dec_ref(v___y_3251_);
    return v_res_3256_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3258_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__0;
    v___x_3259_ = l_Lean_stringToMessageData(v___x_3258_);
    return v___x_3259_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(
    mut v_a_3260_: *mut crate::leanh::LeanObject,
    mut v_a_3261_: *mut crate::leanh::LeanObject,
    mut v_a_3262_: *mut crate::leanh::LeanObject,
    mut v_a_3263_: *mut crate::leanh::LeanObject,
    mut v_a_3264_: *mut crate::leanh::LeanObject,
    mut v_a_3265_: *mut crate::leanh::LeanObject,
    mut v_a_3266_: *mut crate::leanh::LeanObject,
    mut v_a_3267_: *mut crate::leanh::LeanObject,
    mut v_a_3268_: *mut crate::leanh::LeanObject,
    mut v_a_3269_: *mut crate::leanh::LeanObject,
    mut v_a_3270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3276_: u8 = 0;
    let mut v_semirings_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: u8 = 0;
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3286_: u8 = 0;
    let mut v_a_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3290_: u8 = 0;
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3294_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3272_ =
                    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_3261_, v_a_3269_);
                if crate::leanh::lean_obj_tag(v___x_3272_) == 0 {
                    v_a_3273_ = crate::leanh::lean_ctor_get(v___x_3272_, 0);
                    v_isSharedCheck_3286_ = (!crate::leanh::lean_is_exclusive(v___x_3272_)) as u8;
                    if v_isSharedCheck_3286_ == 0 {
                        v___x_3275_ = v___x_3272_;
                        v_isShared_3276_ = v_isSharedCheck_3286_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3273_);
                        crate::leanh::lean_dec(v___x_3272_);
                        v___x_3275_ = crate::leanh::lean_box(0);
                        v_isShared_3276_ = v_isSharedCheck_3286_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3287_ = crate::leanh::lean_ctor_get(v___x_3272_, 0);
                    v_isSharedCheck_3294_ = (!crate::leanh::lean_is_exclusive(v___x_3272_)) as u8;
                    if v_isSharedCheck_3294_ == 0 {
                        v___x_3289_ = v___x_3272_;
                        v_isShared_3290_ = v_isSharedCheck_3294_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3287_);
                        crate::leanh::lean_dec(v___x_3272_);
                        v___x_3289_ = crate::leanh::lean_box(0);
                        v_isShared_3290_ = v_isSharedCheck_3294_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_semirings_3277_ = crate::leanh::lean_ctor_get(v_a_3273_, 3);
                crate::leanh::lean_inc_ref(v_semirings_3277_);
                crate::leanh::lean_dec(v_a_3273_);
                v___x_3278_ = lean_array_get_size(v_semirings_3277_);
                v___x_3279_ = lean_nat_dec_lt(v_a_3260_, v___x_3278_);
                if v___x_3279_ == 0 {
                    crate::leanh::lean_dec_ref(v_semirings_3277_);
                    crate::leanh::lean_del_object(v___x_3275_);
                    v___x_3280_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1_once), _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1);
                    v___x_3281_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v___x_3280_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_);
                    return v___x_3281_;
                } else {
                    v___x_3282_ = lean_array_fget(v_semirings_3277_, v_a_3260_);
                    crate::leanh::lean_dec_ref(v_semirings_3277_);
                    if v_isShared_3276_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3275_, 0, v___x_3282_);
                        v___x_3284_ = v___x_3275_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3285_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3285_, 0, v___x_3282_);
                        v___x_3284_ = v_reuseFailAlloc_3285_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3284_;
            }
            3 => {
                if v_isShared_3290_ == 0 {
                    v___x_3292_ = v___x_3289_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3293_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_a_3287_);
                    v___x_3292_ = v_reuseFailAlloc_3293_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3292_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___boxed(
    mut v_a_3295_: *mut crate::leanh::LeanObject,
    mut v_a_3296_: *mut crate::leanh::LeanObject,
    mut v_a_3297_: *mut crate::leanh::LeanObject,
    mut v_a_3298_: *mut crate::leanh::LeanObject,
    mut v_a_3299_: *mut crate::leanh::LeanObject,
    mut v_a_3300_: *mut crate::leanh::LeanObject,
    mut v_a_3301_: *mut crate::leanh::LeanObject,
    mut v_a_3302_: *mut crate::leanh::LeanObject,
    mut v_a_3303_: *mut crate::leanh::LeanObject,
    mut v_a_3304_: *mut crate::leanh::LeanObject,
    mut v_a_3305_: *mut crate::leanh::LeanObject,
    mut v_a_3306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3307_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(
        v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_,
        v_a_3303_, v_a_3304_, v_a_3305_,
    );
    crate::leanh::lean_dec(v_a_3305_);
    crate::leanh::lean_dec_ref(v_a_3304_);
    crate::leanh::lean_dec(v_a_3303_);
    crate::leanh::lean_dec_ref(v_a_3302_);
    crate::leanh::lean_dec(v_a_3301_);
    crate::leanh::lean_dec_ref(v_a_3300_);
    crate::leanh::lean_dec(v_a_3299_);
    crate::leanh::lean_dec_ref(v_a_3298_);
    crate::leanh::lean_dec(v_a_3297_);
    crate::leanh::lean_dec(v_a_3296_);
    crate::leanh::lean_dec(v_a_3295_);
    return v_res_3307_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0(
    mut v_00_u03b1_3308_: *mut crate::leanh::LeanObject,
    mut v_msg_3309_: *mut crate::leanh::LeanObject,
    mut v___y_3310_: *mut crate::leanh::LeanObject,
    mut v___y_3311_: *mut crate::leanh::LeanObject,
    mut v___y_3312_: *mut crate::leanh::LeanObject,
    mut v___y_3313_: *mut crate::leanh::LeanObject,
    mut v___y_3314_: *mut crate::leanh::LeanObject,
    mut v___y_3315_: *mut crate::leanh::LeanObject,
    mut v___y_3316_: *mut crate::leanh::LeanObject,
    mut v___y_3317_: *mut crate::leanh::LeanObject,
    mut v___y_3318_: *mut crate::leanh::LeanObject,
    mut v___y_3319_: *mut crate::leanh::LeanObject,
    mut v___y_3320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3322_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v_msg_3309_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
    return v___x_3322_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___boxed(
    mut v_00_u03b1_3323_: *mut crate::leanh::LeanObject,
    mut v_msg_3324_: *mut crate::leanh::LeanObject,
    mut v___y_3325_: *mut crate::leanh::LeanObject,
    mut v___y_3326_: *mut crate::leanh::LeanObject,
    mut v___y_3327_: *mut crate::leanh::LeanObject,
    mut v___y_3328_: *mut crate::leanh::LeanObject,
    mut v___y_3329_: *mut crate::leanh::LeanObject,
    mut v___y_3330_: *mut crate::leanh::LeanObject,
    mut v___y_3331_: *mut crate::leanh::LeanObject,
    mut v___y_3332_: *mut crate::leanh::LeanObject,
    mut v___y_3333_: *mut crate::leanh::LeanObject,
    mut v___y_3334_: *mut crate::leanh::LeanObject,
    mut v___y_3335_: *mut crate::leanh::LeanObject,
    mut v___y_3336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3337_ =
        l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0(
            v_00_u03b1_3323_,
            v_msg_3324_,
            v___y_3325_,
            v___y_3326_,
            v___y_3327_,
            v___y_3328_,
            v___y_3329_,
            v___y_3330_,
            v___y_3331_,
            v___y_3332_,
            v___y_3333_,
            v___y_3334_,
            v___y_3335_,
        );
    crate::leanh::lean_dec(v___y_3335_);
    crate::leanh::lean_dec_ref(v___y_3334_);
    crate::leanh::lean_dec(v___y_3333_);
    crate::leanh::lean_dec_ref(v___y_3332_);
    crate::leanh::lean_dec(v___y_3331_);
    crate::leanh::lean_dec_ref(v___y_3330_);
    crate::leanh::lean_dec(v___y_3329_);
    crate::leanh::lean_dec_ref(v___y_3328_);
    crate::leanh::lean_dec(v___y_3327_);
    crate::leanh::lean_dec(v___y_3326_);
    crate::leanh::lean_dec(v___y_3325_);
    return v_res_3337_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0(
    mut v_a_3338_: *mut crate::leanh::LeanObject,
    mut v_f_3339_: *mut crate::leanh::LeanObject,
    mut v_s_3340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_rings_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_3354_: u8 = 0;
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: u8 = 0;
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3359_: u8 = 0;
    let mut v_v_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3368_: u8 = 0;
    let mut v_unused_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_3341_ = crate::leanh::lean_ctor_get(v_s_3340_, 0);
                v_typeIdOf_3342_ = crate::leanh::lean_ctor_get(v_s_3340_, 1);
                v_exprToRingId_3343_ = crate::leanh::lean_ctor_get(v_s_3340_, 2);
                v_semirings_3344_ = crate::leanh::lean_ctor_get(v_s_3340_, 3);
                v_stypeIdOf_3345_ = crate::leanh::lean_ctor_get(v_s_3340_, 4);
                v_exprToSemiringId_3346_ = crate::leanh::lean_ctor_get(v_s_3340_, 5);
                v_ncRings_3347_ = crate::leanh::lean_ctor_get(v_s_3340_, 6);
                v_exprToNCRingId_3348_ = crate::leanh::lean_ctor_get(v_s_3340_, 7);
                v_nctypeIdOf_3349_ = crate::leanh::lean_ctor_get(v_s_3340_, 8);
                v_ncSemirings_3350_ = crate::leanh::lean_ctor_get(v_s_3340_, 9);
                v_exprToNCSemiringId_3351_ = crate::leanh::lean_ctor_get(v_s_3340_, 10);
                v_ncstypeIdOf_3352_ = crate::leanh::lean_ctor_get(v_s_3340_, 11);
                v_steps_3353_ = crate::leanh::lean_ctor_get(v_s_3340_, 12);
                v_reportedMaxDegreeIssue_3354_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_3340_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                v___x_3355_ = lean_array_get_size(v_semirings_3344_);
                v___x_3356_ = lean_nat_dec_lt(v_a_3338_, v___x_3355_);
                if v___x_3356_ == 0 {
                    crate::leanh::lean_dec_ref(v_f_3339_);
                    return v_s_3340_;
                } else {
                    crate::leanh::lean_inc(v_steps_3353_);
                    crate::leanh::lean_inc_ref(v_ncstypeIdOf_3352_);
                    crate::leanh::lean_inc_ref(v_exprToNCSemiringId_3351_);
                    crate::leanh::lean_inc_ref(v_ncSemirings_3350_);
                    crate::leanh::lean_inc_ref(v_nctypeIdOf_3349_);
                    crate::leanh::lean_inc_ref(v_exprToNCRingId_3348_);
                    crate::leanh::lean_inc_ref(v_ncRings_3347_);
                    crate::leanh::lean_inc_ref(v_exprToSemiringId_3346_);
                    crate::leanh::lean_inc_ref(v_stypeIdOf_3345_);
                    crate::leanh::lean_inc_ref(v_semirings_3344_);
                    crate::leanh::lean_inc_ref(v_exprToRingId_3343_);
                    crate::leanh::lean_inc_ref(v_typeIdOf_3342_);
                    crate::leanh::lean_inc_ref(v_rings_3341_);
                    v_isSharedCheck_3368_ = (!crate::leanh::lean_is_exclusive(v_s_3340_)) as u8;
                    if v_isSharedCheck_3368_ == 0 {
                        v_unused_3369_ = crate::leanh::lean_ctor_get(v_s_3340_, 12);
                        crate::leanh::lean_dec(v_unused_3369_);
                        v_unused_3370_ = crate::leanh::lean_ctor_get(v_s_3340_, 11);
                        crate::leanh::lean_dec(v_unused_3370_);
                        v_unused_3371_ = crate::leanh::lean_ctor_get(v_s_3340_, 10);
                        crate::leanh::lean_dec(v_unused_3371_);
                        v_unused_3372_ = crate::leanh::lean_ctor_get(v_s_3340_, 9);
                        crate::leanh::lean_dec(v_unused_3372_);
                        v_unused_3373_ = crate::leanh::lean_ctor_get(v_s_3340_, 8);
                        crate::leanh::lean_dec(v_unused_3373_);
                        v_unused_3374_ = crate::leanh::lean_ctor_get(v_s_3340_, 7);
                        crate::leanh::lean_dec(v_unused_3374_);
                        v_unused_3375_ = crate::leanh::lean_ctor_get(v_s_3340_, 6);
                        crate::leanh::lean_dec(v_unused_3375_);
                        v_unused_3376_ = crate::leanh::lean_ctor_get(v_s_3340_, 5);
                        crate::leanh::lean_dec(v_unused_3376_);
                        v_unused_3377_ = crate::leanh::lean_ctor_get(v_s_3340_, 4);
                        crate::leanh::lean_dec(v_unused_3377_);
                        v_unused_3378_ = crate::leanh::lean_ctor_get(v_s_3340_, 3);
                        crate::leanh::lean_dec(v_unused_3378_);
                        v_unused_3379_ = crate::leanh::lean_ctor_get(v_s_3340_, 2);
                        crate::leanh::lean_dec(v_unused_3379_);
                        v_unused_3380_ = crate::leanh::lean_ctor_get(v_s_3340_, 1);
                        crate::leanh::lean_dec(v_unused_3380_);
                        v_unused_3381_ = crate::leanh::lean_ctor_get(v_s_3340_, 0);
                        crate::leanh::lean_dec(v_unused_3381_);
                        v___x_3358_ = v_s_3340_;
                        v_isShared_3359_ = v_isSharedCheck_3368_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_s_3340_);
                        v___x_3358_ = crate::leanh::lean_box(0);
                        v_isShared_3359_ = v_isSharedCheck_3368_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3360_ = lean_array_fget(v_semirings_3344_, v_a_3338_);
                v___x_3361_ = crate::leanh::lean_box(0);
                v_xs_x27_3362_ = lean_array_fset(v_semirings_3344_, v_a_3338_, v___x_3361_);
                v___x_3363_ = crate::leanh::lean_apply_1(v_f_3339_, v_v_3360_);
                v___x_3364_ = lean_array_fset(v_xs_x27_3362_, v_a_3338_, v___x_3363_);
                if v_isShared_3359_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3358_, 3, v___x_3364_);
                    v___x_3366_ = v___x_3358_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3367_ = crate::leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_rings_3341_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 1, v_typeIdOf_3342_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 2, v_exprToRingId_3343_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 3, v___x_3364_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 4, v_stypeIdOf_3345_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3367_,
                        5,
                        v_exprToSemiringId_3346_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 6, v_ncRings_3347_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 7, v_exprToNCRingId_3348_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 8, v_nctypeIdOf_3349_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 9, v_ncSemirings_3350_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3367_,
                        10,
                        v_exprToNCSemiringId_3351_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 11, v_ncstypeIdOf_3352_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 12, v_steps_3353_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3367_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                        v_reportedMaxDegreeIssue_3354_,
                    );
                    v___x_3366_ = v_reuseFailAlloc_3367_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3366_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0___boxed(
    mut v_a_3382_: *mut crate::leanh::LeanObject,
    mut v_f_3383_: *mut crate::leanh::LeanObject,
    mut v_s_3384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3385_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0(
        v_a_3382_, v_f_3383_, v_s_3384_,
    );
    crate::leanh::lean_dec(v_a_3382_);
    return v_res_3385_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg(
    mut v_f_3386_: *mut crate::leanh::LeanObject,
    mut v_a_3387_: *mut crate::leanh::LeanObject,
    mut v_a_3388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_3387_);
    v___f_3390_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3390_, 0, v_a_3387_);
    crate::leanh::lean_closure_set(v___f_3390_, 1, v_f_3386_);
    v___x_3391_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
    v___x_3392_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3391_, v___f_3390_, v_a_3388_);
    return v___x_3392_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___boxed(
    mut v_f_3393_: *mut crate::leanh::LeanObject,
    mut v_a_3394_: *mut crate::leanh::LeanObject,
    mut v_a_3395_: *mut crate::leanh::LeanObject,
    mut v_a_3396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3397_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg(
        v_f_3393_, v_a_3394_, v_a_3395_,
    );
    crate::leanh::lean_dec(v_a_3395_);
    crate::leanh::lean_dec(v_a_3394_);
    return v_res_3397_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring(
    mut v_f_3398_: *mut crate::leanh::LeanObject,
    mut v_a_3399_: *mut crate::leanh::LeanObject,
    mut v_a_3400_: *mut crate::leanh::LeanObject,
    mut v_a_3401_: *mut crate::leanh::LeanObject,
    mut v_a_3402_: *mut crate::leanh::LeanObject,
    mut v_a_3403_: *mut crate::leanh::LeanObject,
    mut v_a_3404_: *mut crate::leanh::LeanObject,
    mut v_a_3405_: *mut crate::leanh::LeanObject,
    mut v_a_3406_: *mut crate::leanh::LeanObject,
    mut v_a_3407_: *mut crate::leanh::LeanObject,
    mut v_a_3408_: *mut crate::leanh::LeanObject,
    mut v_a_3409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_3399_);
    v___f_3411_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3411_, 0, v_a_3399_);
    crate::leanh::lean_closure_set(v___f_3411_, 1, v_f_3398_);
    v___x_3412_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
    v___x_3413_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3412_, v___f_3411_, v_a_3400_);
    return v___x_3413_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___boxed(
    mut v_f_3414_: *mut crate::leanh::LeanObject,
    mut v_a_3415_: *mut crate::leanh::LeanObject,
    mut v_a_3416_: *mut crate::leanh::LeanObject,
    mut v_a_3417_: *mut crate::leanh::LeanObject,
    mut v_a_3418_: *mut crate::leanh::LeanObject,
    mut v_a_3419_: *mut crate::leanh::LeanObject,
    mut v_a_3420_: *mut crate::leanh::LeanObject,
    mut v_a_3421_: *mut crate::leanh::LeanObject,
    mut v_a_3422_: *mut crate::leanh::LeanObject,
    mut v_a_3423_: *mut crate::leanh::LeanObject,
    mut v_a_3424_: *mut crate::leanh::LeanObject,
    mut v_a_3425_: *mut crate::leanh::LeanObject,
    mut v_a_3426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3427_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring(
        v_f_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_,
        v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_,
    );
    crate::leanh::lean_dec(v_a_3425_);
    crate::leanh::lean_dec_ref(v_a_3424_);
    crate::leanh::lean_dec(v_a_3423_);
    crate::leanh::lean_dec_ref(v_a_3422_);
    crate::leanh::lean_dec(v_a_3421_);
    crate::leanh::lean_dec_ref(v_a_3420_);
    crate::leanh::lean_dec(v_a_3419_);
    crate::leanh::lean_dec_ref(v_a_3418_);
    crate::leanh::lean_dec(v_a_3417_);
    crate::leanh::lean_dec(v_a_3416_);
    crate::leanh::lean_dec(v_a_3415_);
    return v_res_3427_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3429_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__0;
    v___x_3430_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___boxed
            as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_3431_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3431_, 0, v___x_3430_);
    crate::leanh::lean_ctor_set(v___x_3431_, 1, v___x_3429_);
    return v___x_3431_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3432_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1,
    );
    return v___x_3432_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3434_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__0;
    v___x_3435_ = l_Lean_stringToMessageData(v___x_3434_);
    return v___x_3435_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(
    mut v_a_3436_: *mut crate::leanh::LeanObject,
    mut v_a_3437_: *mut crate::leanh::LeanObject,
    mut v_a_3438_: *mut crate::leanh::LeanObject,
    mut v_a_3439_: *mut crate::leanh::LeanObject,
    mut v_a_3440_: *mut crate::leanh::LeanObject,
    mut v_a_3441_: *mut crate::leanh::LeanObject,
    mut v_a_3442_: *mut crate::leanh::LeanObject,
    mut v_a_3443_: *mut crate::leanh::LeanObject,
    mut v_a_3444_: *mut crate::leanh::LeanObject,
    mut v_a_3445_: *mut crate::leanh::LeanObject,
    mut v_a_3446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3454_: u8 = 0;
    let mut v_ringId_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rings_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: u8 = 0;
    let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3465_: u8 = 0;
    let mut v_a_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3469_: u8 = 0;
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3473_: u8 = 0;
    let mut v_a_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3477_: u8 = 0;
    let mut v___x_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3481_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3448_ =
                    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_3437_, v_a_3445_);
                if crate::leanh::lean_obj_tag(v___x_3448_) == 0 {
                    v_a_3449_ = crate::leanh::lean_ctor_get(v___x_3448_, 0);
                    crate::leanh::lean_inc(v_a_3449_);
                    crate::leanh::lean_dec_ref_known(v___x_3448_, 1);
                    v___x_3450_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(
                        v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_,
                        v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3450_) == 0 {
                        v_a_3451_ = crate::leanh::lean_ctor_get(v___x_3450_, 0);
                        v_isSharedCheck_3465_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3450_)) as u8;
                        if v_isSharedCheck_3465_ == 0 {
                            v___x_3453_ = v___x_3450_;
                            v_isShared_3454_ = v_isSharedCheck_3465_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3451_);
                            crate::leanh::lean_dec(v___x_3450_);
                            v___x_3453_ = crate::leanh::lean_box(0);
                            v_isShared_3454_ = v_isSharedCheck_3465_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3449_);
                        v_a_3466_ = crate::leanh::lean_ctor_get(v___x_3450_, 0);
                        v_isSharedCheck_3473_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3450_)) as u8;
                        if v_isSharedCheck_3473_ == 0 {
                            v___x_3468_ = v___x_3450_;
                            v_isShared_3469_ = v_isSharedCheck_3473_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3466_);
                            crate::leanh::lean_dec(v___x_3450_);
                            v___x_3468_ = crate::leanh::lean_box(0);
                            v_isShared_3469_ = v_isSharedCheck_3473_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_3474_ = crate::leanh::lean_ctor_get(v___x_3448_, 0);
                    v_isSharedCheck_3481_ = (!crate::leanh::lean_is_exclusive(v___x_3448_)) as u8;
                    if v_isSharedCheck_3481_ == 0 {
                        v___x_3476_ = v___x_3448_;
                        v_isShared_3477_ = v_isSharedCheck_3481_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3474_);
                        crate::leanh::lean_dec(v___x_3448_);
                        v___x_3476_ = crate::leanh::lean_box(0);
                        v_isShared_3477_ = v_isSharedCheck_3481_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_ringId_3455_ = crate::leanh::lean_ctor_get(v_a_3451_, 1);
                crate::leanh::lean_inc(v_ringId_3455_);
                crate::leanh::lean_dec(v_a_3451_);
                v_rings_3456_ = crate::leanh::lean_ctor_get(v_a_3449_, 0);
                crate::leanh::lean_inc_ref(v_rings_3456_);
                crate::leanh::lean_dec(v_a_3449_);
                v___x_3457_ = lean_array_get_size(v_rings_3456_);
                v___x_3458_ = lean_nat_dec_lt(v_ringId_3455_, v___x_3457_);
                if v___x_3458_ == 0 {
                    crate::leanh::lean_dec_ref(v_rings_3456_);
                    crate::leanh::lean_dec(v_ringId_3455_);
                    crate::leanh::lean_del_object(v___x_3453_);
                    v___x_3459_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1,
                    );
                    v___x_3460_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v___x_3459_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_);
                    return v___x_3460_;
                } else {
                    v___x_3461_ = lean_array_fget(v_rings_3456_, v_ringId_3455_);
                    crate::leanh::lean_dec(v_ringId_3455_);
                    crate::leanh::lean_dec_ref(v_rings_3456_);
                    if v_isShared_3454_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3453_, 0, v___x_3461_);
                        v___x_3463_ = v___x_3453_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3464_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3461_);
                        v___x_3463_ = v_reuseFailAlloc_3464_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3463_;
            }
            3 => {
                if v_isShared_3469_ == 0 {
                    v___x_3471_ = v___x_3468_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3472_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_a_3466_);
                    v___x_3471_ = v_reuseFailAlloc_3472_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3471_;
            }
            5 => {
                if v_isShared_3477_ == 0 {
                    v___x_3479_ = v___x_3476_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3480_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3474_);
                    v___x_3479_ = v_reuseFailAlloc_3480_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3479_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___boxed(
    mut v_a_3482_: *mut crate::leanh::LeanObject,
    mut v_a_3483_: *mut crate::leanh::LeanObject,
    mut v_a_3484_: *mut crate::leanh::LeanObject,
    mut v_a_3485_: *mut crate::leanh::LeanObject,
    mut v_a_3486_: *mut crate::leanh::LeanObject,
    mut v_a_3487_: *mut crate::leanh::LeanObject,
    mut v_a_3488_: *mut crate::leanh::LeanObject,
    mut v_a_3489_: *mut crate::leanh::LeanObject,
    mut v_a_3490_: *mut crate::leanh::LeanObject,
    mut v_a_3491_: *mut crate::leanh::LeanObject,
    mut v_a_3492_: *mut crate::leanh::LeanObject,
    mut v_a_3493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3494_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(
        v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_,
        v_a_3490_, v_a_3491_, v_a_3492_,
    );
    crate::leanh::lean_dec(v_a_3492_);
    crate::leanh::lean_dec_ref(v_a_3491_);
    crate::leanh::lean_dec(v_a_3490_);
    crate::leanh::lean_dec_ref(v_a_3489_);
    crate::leanh::lean_dec(v_a_3488_);
    crate::leanh::lean_dec_ref(v_a_3487_);
    crate::leanh::lean_dec(v_a_3486_);
    crate::leanh::lean_dec_ref(v_a_3485_);
    crate::leanh::lean_dec(v_a_3484_);
    crate::leanh::lean_dec(v_a_3483_);
    crate::leanh::lean_dec(v_a_3482_);
    return v_res_3494_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0(
    mut v_ringId_3495_: *mut crate::leanh::LeanObject,
    mut v_f_3496_: *mut crate::leanh::LeanObject,
    mut v_s_3497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_rings_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_3511_: u8 = 0;
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: u8 = 0;
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3516_: u8 = 0;
    let mut v_v_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3525_: u8 = 0;
    let mut v_unused_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_3498_ = crate::leanh::lean_ctor_get(v_s_3497_, 0);
                v_typeIdOf_3499_ = crate::leanh::lean_ctor_get(v_s_3497_, 1);
                v_exprToRingId_3500_ = crate::leanh::lean_ctor_get(v_s_3497_, 2);
                v_semirings_3501_ = crate::leanh::lean_ctor_get(v_s_3497_, 3);
                v_stypeIdOf_3502_ = crate::leanh::lean_ctor_get(v_s_3497_, 4);
                v_exprToSemiringId_3503_ = crate::leanh::lean_ctor_get(v_s_3497_, 5);
                v_ncRings_3504_ = crate::leanh::lean_ctor_get(v_s_3497_, 6);
                v_exprToNCRingId_3505_ = crate::leanh::lean_ctor_get(v_s_3497_, 7);
                v_nctypeIdOf_3506_ = crate::leanh::lean_ctor_get(v_s_3497_, 8);
                v_ncSemirings_3507_ = crate::leanh::lean_ctor_get(v_s_3497_, 9);
                v_exprToNCSemiringId_3508_ = crate::leanh::lean_ctor_get(v_s_3497_, 10);
                v_ncstypeIdOf_3509_ = crate::leanh::lean_ctor_get(v_s_3497_, 11);
                v_steps_3510_ = crate::leanh::lean_ctor_get(v_s_3497_, 12);
                v_reportedMaxDegreeIssue_3511_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_3497_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                v___x_3512_ = lean_array_get_size(v_rings_3498_);
                v___x_3513_ = lean_nat_dec_lt(v_ringId_3495_, v___x_3512_);
                if v___x_3513_ == 0 {
                    crate::leanh::lean_dec_ref(v_f_3496_);
                    return v_s_3497_;
                } else {
                    crate::leanh::lean_inc(v_steps_3510_);
                    crate::leanh::lean_inc_ref(v_ncstypeIdOf_3509_);
                    crate::leanh::lean_inc_ref(v_exprToNCSemiringId_3508_);
                    crate::leanh::lean_inc_ref(v_ncSemirings_3507_);
                    crate::leanh::lean_inc_ref(v_nctypeIdOf_3506_);
                    crate::leanh::lean_inc_ref(v_exprToNCRingId_3505_);
                    crate::leanh::lean_inc_ref(v_ncRings_3504_);
                    crate::leanh::lean_inc_ref(v_exprToSemiringId_3503_);
                    crate::leanh::lean_inc_ref(v_stypeIdOf_3502_);
                    crate::leanh::lean_inc_ref(v_semirings_3501_);
                    crate::leanh::lean_inc_ref(v_exprToRingId_3500_);
                    crate::leanh::lean_inc_ref(v_typeIdOf_3499_);
                    crate::leanh::lean_inc_ref(v_rings_3498_);
                    v_isSharedCheck_3525_ = (!crate::leanh::lean_is_exclusive(v_s_3497_)) as u8;
                    if v_isSharedCheck_3525_ == 0 {
                        v_unused_3526_ = crate::leanh::lean_ctor_get(v_s_3497_, 12);
                        crate::leanh::lean_dec(v_unused_3526_);
                        v_unused_3527_ = crate::leanh::lean_ctor_get(v_s_3497_, 11);
                        crate::leanh::lean_dec(v_unused_3527_);
                        v_unused_3528_ = crate::leanh::lean_ctor_get(v_s_3497_, 10);
                        crate::leanh::lean_dec(v_unused_3528_);
                        v_unused_3529_ = crate::leanh::lean_ctor_get(v_s_3497_, 9);
                        crate::leanh::lean_dec(v_unused_3529_);
                        v_unused_3530_ = crate::leanh::lean_ctor_get(v_s_3497_, 8);
                        crate::leanh::lean_dec(v_unused_3530_);
                        v_unused_3531_ = crate::leanh::lean_ctor_get(v_s_3497_, 7);
                        crate::leanh::lean_dec(v_unused_3531_);
                        v_unused_3532_ = crate::leanh::lean_ctor_get(v_s_3497_, 6);
                        crate::leanh::lean_dec(v_unused_3532_);
                        v_unused_3533_ = crate::leanh::lean_ctor_get(v_s_3497_, 5);
                        crate::leanh::lean_dec(v_unused_3533_);
                        v_unused_3534_ = crate::leanh::lean_ctor_get(v_s_3497_, 4);
                        crate::leanh::lean_dec(v_unused_3534_);
                        v_unused_3535_ = crate::leanh::lean_ctor_get(v_s_3497_, 3);
                        crate::leanh::lean_dec(v_unused_3535_);
                        v_unused_3536_ = crate::leanh::lean_ctor_get(v_s_3497_, 2);
                        crate::leanh::lean_dec(v_unused_3536_);
                        v_unused_3537_ = crate::leanh::lean_ctor_get(v_s_3497_, 1);
                        crate::leanh::lean_dec(v_unused_3537_);
                        v_unused_3538_ = crate::leanh::lean_ctor_get(v_s_3497_, 0);
                        crate::leanh::lean_dec(v_unused_3538_);
                        v___x_3515_ = v_s_3497_;
                        v_isShared_3516_ = v_isSharedCheck_3525_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_s_3497_);
                        v___x_3515_ = crate::leanh::lean_box(0);
                        v_isShared_3516_ = v_isSharedCheck_3525_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3517_ = lean_array_fget(v_rings_3498_, v_ringId_3495_);
                v___x_3518_ = crate::leanh::lean_box(0);
                v_xs_x27_3519_ = lean_array_fset(v_rings_3498_, v_ringId_3495_, v___x_3518_);
                v___x_3520_ = crate::leanh::lean_apply_1(v_f_3496_, v_v_3517_);
                v___x_3521_ = lean_array_fset(v_xs_x27_3519_, v_ringId_3495_, v___x_3520_);
                if v_isShared_3516_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3515_, 0, v___x_3521_);
                    v___x_3523_ = v___x_3515_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3524_ = crate::leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3521_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 1, v_typeIdOf_3499_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 2, v_exprToRingId_3500_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 3, v_semirings_3501_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 4, v_stypeIdOf_3502_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3524_,
                        5,
                        v_exprToSemiringId_3503_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 6, v_ncRings_3504_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 7, v_exprToNCRingId_3505_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 8, v_nctypeIdOf_3506_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 9, v_ncSemirings_3507_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3524_,
                        10,
                        v_exprToNCSemiringId_3508_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 11, v_ncstypeIdOf_3509_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 12, v_steps_3510_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3524_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                        v_reportedMaxDegreeIssue_3511_,
                    );
                    v___x_3523_ = v_reuseFailAlloc_3524_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3523_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0___boxed(
    mut v_ringId_3539_: *mut crate::leanh::LeanObject,
    mut v_f_3540_: *mut crate::leanh::LeanObject,
    mut v_s_3541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3542_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0(
        v_ringId_3539_,
        v_f_3540_,
        v_s_3541_,
    );
    crate::leanh::lean_dec(v_ringId_3539_);
    return v_res_3542_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(
    mut v_f_3543_: *mut crate::leanh::LeanObject,
    mut v_a_3544_: *mut crate::leanh::LeanObject,
    mut v_a_3545_: *mut crate::leanh::LeanObject,
    mut v_a_3546_: *mut crate::leanh::LeanObject,
    mut v_a_3547_: *mut crate::leanh::LeanObject,
    mut v_a_3548_: *mut crate::leanh::LeanObject,
    mut v_a_3549_: *mut crate::leanh::LeanObject,
    mut v_a_3550_: *mut crate::leanh::LeanObject,
    mut v_a_3551_: *mut crate::leanh::LeanObject,
    mut v_a_3552_: *mut crate::leanh::LeanObject,
    mut v_a_3553_: *mut crate::leanh::LeanObject,
    mut v_a_3554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringId_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3565_: u8 = 0;
    let mut v___x_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3569_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3556_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(
                    v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_,
                    v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_,
                );
                if crate::leanh::lean_obj_tag(v___x_3556_) == 0 {
                    v_a_3557_ = crate::leanh::lean_ctor_get(v___x_3556_, 0);
                    crate::leanh::lean_inc(v_a_3557_);
                    crate::leanh::lean_dec_ref_known(v___x_3556_, 1);
                    v_ringId_3558_ = crate::leanh::lean_ctor_get(v_a_3557_, 1);
                    crate::leanh::lean_inc(v_ringId_3558_);
                    crate::leanh::lean_dec(v_a_3557_);
                    v___f_3559_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0___boxed
                            as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_3559_, 0, v_ringId_3558_);
                    crate::leanh::lean_closure_set(v___f_3559_, 1, v_f_3543_);
                    v___x_3560_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                    v___x_3561_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3560_, v___f_3559_, v_a_3545_);
                    return v___x_3561_;
                } else {
                    crate::leanh::lean_dec_ref(v_f_3543_);
                    v_a_3562_ = crate::leanh::lean_ctor_get(v___x_3556_, 0);
                    v_isSharedCheck_3569_ = (!crate::leanh::lean_is_exclusive(v___x_3556_)) as u8;
                    if v_isSharedCheck_3569_ == 0 {
                        v___x_3564_ = v___x_3556_;
                        v_isShared_3565_ = v_isSharedCheck_3569_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3562_);
                        crate::leanh::lean_dec(v___x_3556_);
                        v___x_3564_ = crate::leanh::lean_box(0);
                        v_isShared_3565_ = v_isSharedCheck_3569_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3565_ == 0 {
                    v___x_3567_ = v___x_3564_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3568_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3562_);
                    v___x_3567_ = v_reuseFailAlloc_3568_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3567_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___boxed(
    mut v_f_3570_: *mut crate::leanh::LeanObject,
    mut v_a_3571_: *mut crate::leanh::LeanObject,
    mut v_a_3572_: *mut crate::leanh::LeanObject,
    mut v_a_3573_: *mut crate::leanh::LeanObject,
    mut v_a_3574_: *mut crate::leanh::LeanObject,
    mut v_a_3575_: *mut crate::leanh::LeanObject,
    mut v_a_3576_: *mut crate::leanh::LeanObject,
    mut v_a_3577_: *mut crate::leanh::LeanObject,
    mut v_a_3578_: *mut crate::leanh::LeanObject,
    mut v_a_3579_: *mut crate::leanh::LeanObject,
    mut v_a_3580_: *mut crate::leanh::LeanObject,
    mut v_a_3581_: *mut crate::leanh::LeanObject,
    mut v_a_3582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3583_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(
        v_f_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_,
        v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_,
    );
    crate::leanh::lean_dec(v_a_3581_);
    crate::leanh::lean_dec_ref(v_a_3580_);
    crate::leanh::lean_dec(v_a_3579_);
    crate::leanh::lean_dec_ref(v_a_3578_);
    crate::leanh::lean_dec(v_a_3577_);
    crate::leanh::lean_dec_ref(v_a_3576_);
    crate::leanh::lean_dec(v_a_3575_);
    crate::leanh::lean_dec_ref(v_a_3574_);
    crate::leanh::lean_dec(v_a_3573_);
    crate::leanh::lean_dec(v_a_3572_);
    crate::leanh::lean_dec(v_a_3571_);
    return v_res_3583_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3585_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__0;
    v___x_3586_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___boxed as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_3587_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3587_, 0, v___x_3586_);
    crate::leanh::lean_ctor_set(v___x_3587_, 1, v___x_3585_);
    return v___x_3587_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3588_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1,
    );
    return v___x_3588_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getToQFn___lam__0(
    mut v_a_3589_: *mut crate::leanh::LeanObject,
    mut v_a_3590_: *mut crate::leanh::LeanObject,
    mut v_s_3591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_rings_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_3605_: u8 = 0;
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: u8 = 0;
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3610_: u8 = 0;
    let mut v_v_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSemiring_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringId_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addRightCancelInst_x3f_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3618_: u8 = 0;
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3629_: u8 = 0;
    let mut v_unused_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3631_: u8 = 0;
    let mut v_unused_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_3592_ = crate::leanh::lean_ctor_get(v_s_3591_, 0);
                v_typeIdOf_3593_ = crate::leanh::lean_ctor_get(v_s_3591_, 1);
                v_exprToRingId_3594_ = crate::leanh::lean_ctor_get(v_s_3591_, 2);
                v_semirings_3595_ = crate::leanh::lean_ctor_get(v_s_3591_, 3);
                v_stypeIdOf_3596_ = crate::leanh::lean_ctor_get(v_s_3591_, 4);
                v_exprToSemiringId_3597_ = crate::leanh::lean_ctor_get(v_s_3591_, 5);
                v_ncRings_3598_ = crate::leanh::lean_ctor_get(v_s_3591_, 6);
                v_exprToNCRingId_3599_ = crate::leanh::lean_ctor_get(v_s_3591_, 7);
                v_nctypeIdOf_3600_ = crate::leanh::lean_ctor_get(v_s_3591_, 8);
                v_ncSemirings_3601_ = crate::leanh::lean_ctor_get(v_s_3591_, 9);
                v_exprToNCSemiringId_3602_ = crate::leanh::lean_ctor_get(v_s_3591_, 10);
                v_ncstypeIdOf_3603_ = crate::leanh::lean_ctor_get(v_s_3591_, 11);
                v_steps_3604_ = crate::leanh::lean_ctor_get(v_s_3591_, 12);
                v_reportedMaxDegreeIssue_3605_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_3591_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                v___x_3606_ = lean_array_get_size(v_semirings_3595_);
                v___x_3607_ = lean_nat_dec_lt(v_a_3589_, v___x_3606_);
                if v___x_3607_ == 0 {
                    crate::leanh::lean_dec_ref(v_a_3590_);
                    return v_s_3591_;
                } else {
                    crate::leanh::lean_inc(v_steps_3604_);
                    crate::leanh::lean_inc_ref(v_ncstypeIdOf_3603_);
                    crate::leanh::lean_inc_ref(v_exprToNCSemiringId_3602_);
                    crate::leanh::lean_inc_ref(v_ncSemirings_3601_);
                    crate::leanh::lean_inc_ref(v_nctypeIdOf_3600_);
                    crate::leanh::lean_inc_ref(v_exprToNCRingId_3599_);
                    crate::leanh::lean_inc_ref(v_ncRings_3598_);
                    crate::leanh::lean_inc_ref(v_exprToSemiringId_3597_);
                    crate::leanh::lean_inc_ref(v_stypeIdOf_3596_);
                    crate::leanh::lean_inc_ref(v_semirings_3595_);
                    crate::leanh::lean_inc_ref(v_exprToRingId_3594_);
                    crate::leanh::lean_inc_ref(v_typeIdOf_3593_);
                    crate::leanh::lean_inc_ref(v_rings_3592_);
                    v_isSharedCheck_3631_ = (!crate::leanh::lean_is_exclusive(v_s_3591_)) as u8;
                    if v_isSharedCheck_3631_ == 0 {
                        v_unused_3632_ = crate::leanh::lean_ctor_get(v_s_3591_, 12);
                        crate::leanh::lean_dec(v_unused_3632_);
                        v_unused_3633_ = crate::leanh::lean_ctor_get(v_s_3591_, 11);
                        crate::leanh::lean_dec(v_unused_3633_);
                        v_unused_3634_ = crate::leanh::lean_ctor_get(v_s_3591_, 10);
                        crate::leanh::lean_dec(v_unused_3634_);
                        v_unused_3635_ = crate::leanh::lean_ctor_get(v_s_3591_, 9);
                        crate::leanh::lean_dec(v_unused_3635_);
                        v_unused_3636_ = crate::leanh::lean_ctor_get(v_s_3591_, 8);
                        crate::leanh::lean_dec(v_unused_3636_);
                        v_unused_3637_ = crate::leanh::lean_ctor_get(v_s_3591_, 7);
                        crate::leanh::lean_dec(v_unused_3637_);
                        v_unused_3638_ = crate::leanh::lean_ctor_get(v_s_3591_, 6);
                        crate::leanh::lean_dec(v_unused_3638_);
                        v_unused_3639_ = crate::leanh::lean_ctor_get(v_s_3591_, 5);
                        crate::leanh::lean_dec(v_unused_3639_);
                        v_unused_3640_ = crate::leanh::lean_ctor_get(v_s_3591_, 4);
                        crate::leanh::lean_dec(v_unused_3640_);
                        v_unused_3641_ = crate::leanh::lean_ctor_get(v_s_3591_, 3);
                        crate::leanh::lean_dec(v_unused_3641_);
                        v_unused_3642_ = crate::leanh::lean_ctor_get(v_s_3591_, 2);
                        crate::leanh::lean_dec(v_unused_3642_);
                        v_unused_3643_ = crate::leanh::lean_ctor_get(v_s_3591_, 1);
                        crate::leanh::lean_dec(v_unused_3643_);
                        v_unused_3644_ = crate::leanh::lean_ctor_get(v_s_3591_, 0);
                        crate::leanh::lean_dec(v_unused_3644_);
                        v___x_3609_ = v_s_3591_;
                        v_isShared_3610_ = v_isSharedCheck_3631_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_s_3591_);
                        v___x_3609_ = crate::leanh::lean_box(0);
                        v_isShared_3610_ = v_isSharedCheck_3631_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3611_ = lean_array_fget(v_semirings_3595_, v_a_3589_);
                v_toSemiring_3612_ = crate::leanh::lean_ctor_get(v_v_3611_, 0);
                v_ringId_3613_ = crate::leanh::lean_ctor_get(v_v_3611_, 1);
                v_commSemiringInst_3614_ = crate::leanh::lean_ctor_get(v_v_3611_, 2);
                v_addRightCancelInst_x3f_3615_ = crate::leanh::lean_ctor_get(v_v_3611_, 3);
                v_isSharedCheck_3629_ = (!crate::leanh::lean_is_exclusive(v_v_3611_)) as u8;
                if v_isSharedCheck_3629_ == 0 {
                    v_unused_3630_ = crate::leanh::lean_ctor_get(v_v_3611_, 4);
                    crate::leanh::lean_dec(v_unused_3630_);
                    v___x_3617_ = v_v_3611_;
                    v_isShared_3618_ = v_isSharedCheck_3629_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_addRightCancelInst_x3f_3615_);
                    crate::leanh::lean_inc(v_commSemiringInst_3614_);
                    crate::leanh::lean_inc(v_ringId_3613_);
                    crate::leanh::lean_inc(v_toSemiring_3612_);
                    crate::leanh::lean_dec(v_v_3611_);
                    v___x_3617_ = crate::leanh::lean_box(0);
                    v_isShared_3618_ = v_isSharedCheck_3629_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3619_ = crate::leanh::lean_box(0);
                v_xs_x27_3620_ = lean_array_fset(v_semirings_3595_, v_a_3589_, v___x_3619_);
                v___x_3621_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3621_, 0, v_a_3590_);
                if v_isShared_3618_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3617_, 4, v___x_3621_);
                    v___x_3623_ = v___x_3617_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3628_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_toSemiring_3612_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3628_, 1, v_ringId_3613_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3628_,
                        2,
                        v_commSemiringInst_3614_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3628_,
                        3,
                        v_addRightCancelInst_x3f_3615_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3628_, 4, v___x_3621_);
                    v___x_3623_ = v_reuseFailAlloc_3628_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3624_ = lean_array_fset(v_xs_x27_3620_, v_a_3589_, v___x_3623_);
                if v_isShared_3610_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3609_, 3, v___x_3624_);
                    v___x_3626_ = v___x_3609_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3627_ = crate::leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_rings_3592_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 1, v_typeIdOf_3593_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 2, v_exprToRingId_3594_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 3, v___x_3624_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 4, v_stypeIdOf_3596_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3627_,
                        5,
                        v_exprToSemiringId_3597_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 6, v_ncRings_3598_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 7, v_exprToNCRingId_3599_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 8, v_nctypeIdOf_3600_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 9, v_ncSemirings_3601_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3627_,
                        10,
                        v_exprToNCSemiringId_3602_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 11, v_ncstypeIdOf_3603_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 12, v_steps_3604_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3627_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                        v_reportedMaxDegreeIssue_3605_,
                    );
                    v___x_3626_ = v_reuseFailAlloc_3627_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3626_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getToQFn___lam__0___boxed(
    mut v_a_3645_: *mut crate::leanh::LeanObject,
    mut v_a_3646_: *mut crate::leanh::LeanObject,
    mut v_s_3647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3648_ =
        l_Lean_Meta_Grind_Arith_CommRing_getToQFn___lam__0(v_a_3645_, v_a_3646_, v_s_3647_);
    crate::leanh::lean_dec(v_a_3645_);
    return v_res_3648_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getToQFn(
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
    let mut v___y_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3680_: u8 = 0;
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3684_: u8 = 0;
    let mut v_unused_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3689_: u8 = 0;
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3693_: u8 = 0;
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3698_: u8 = 0;
    let mut v_toQFn_x3f_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSemiring_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3716_: u8 = 0;
    let mut v_a_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3720_: u8 = 0;
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3724_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3694_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(
                    v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_,
                    v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_,
                );
                if crate::leanh::lean_obj_tag(v___x_3694_) == 0 {
                    v_a_3695_ = crate::leanh::lean_ctor_get(v___x_3694_, 0);
                    v_isSharedCheck_3716_ = (!crate::leanh::lean_is_exclusive(v___x_3694_)) as u8;
                    if v_isSharedCheck_3716_ == 0 {
                        v___x_3697_ = v___x_3694_;
                        v_isShared_3698_ = v_isSharedCheck_3716_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3695_);
                        crate::leanh::lean_dec(v___x_3694_);
                        v___x_3697_ = crate::leanh::lean_box(0);
                        v_isShared_3698_ = v_isSharedCheck_3716_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_a_3717_ = crate::leanh::lean_ctor_get(v___x_3694_, 0);
                    v_isSharedCheck_3724_ = (!crate::leanh::lean_is_exclusive(v___x_3694_)) as u8;
                    if v_isSharedCheck_3724_ == 0 {
                        v___x_3719_ = v___x_3694_;
                        v_isShared_3720_ = v_isSharedCheck_3724_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3717_);
                        crate::leanh::lean_dec(v___x_3694_);
                        v___x_3719_ = crate::leanh::lean_box(0);
                        v_isShared_3720_ = v_isSharedCheck_3724_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_3673_) == 0 {
                    v_a_3674_ = crate::leanh::lean_ctor_get(v___y_3673_, 0);
                    crate::leanh::lean_inc_n(v_a_3674_, 2);
                    crate::leanh::lean_dec_ref_known(v___y_3673_, 1);
                    crate::leanh::lean_inc(v_a_3660_);
                    v___f_3675_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Meta_Grind_Arith_CommRing_getToQFn___lam__0___boxed
                            as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_3675_, 0, v_a_3660_);
                    crate::leanh::lean_closure_set(v___f_3675_, 1, v_a_3674_);
                    v___x_3676_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                    v___x_3677_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3676_, v___f_3675_, v_a_3661_);
                    if crate::leanh::lean_obj_tag(v___x_3677_) == 0 {
                        v_isSharedCheck_3684_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3677_)) as u8;
                        if v_isSharedCheck_3684_ == 0 {
                            v_unused_3685_ = crate::leanh::lean_ctor_get(v___x_3677_, 0);
                            crate::leanh::lean_dec(v_unused_3685_);
                            v___x_3679_ = v___x_3677_;
                            v_isShared_3680_ = v_isSharedCheck_3684_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3677_);
                            v___x_3679_ = crate::leanh::lean_box(0);
                            v_isShared_3680_ = v_isSharedCheck_3684_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3674_);
                        v_a_3686_ = crate::leanh::lean_ctor_get(v___x_3677_, 0);
                        v_isSharedCheck_3693_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3677_)) as u8;
                        if v_isSharedCheck_3693_ == 0 {
                            v___x_3688_ = v___x_3677_;
                            v_isShared_3689_ = v_isSharedCheck_3693_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3686_);
                            crate::leanh::lean_dec(v___x_3677_);
                            v___x_3688_ = crate::leanh::lean_box(0);
                            v_isShared_3689_ = v_isSharedCheck_3693_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    return v___y_3673_;
                }
            }
            2 => {
                if v_isShared_3680_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3679_, 0, v_a_3674_);
                    v___x_3682_ = v___x_3679_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3683_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3674_);
                    v___x_3682_ = v_reuseFailAlloc_3683_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3682_;
            }
            4 => {
                if v_isShared_3689_ == 0 {
                    v___x_3691_ = v___x_3688_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3692_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
                    v___x_3691_ = v_reuseFailAlloc_3692_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3691_;
            }
            6 => {
                v_toQFn_x3f_3699_ = crate::leanh::lean_ctor_get(v_a_3695_, 4);
                if crate::leanh::lean_obj_tag(v_toQFn_x3f_3699_) == 1 {
                    crate::leanh::lean_inc_ref(v_toQFn_x3f_3699_);
                    crate::leanh::lean_dec(v_a_3695_);
                    v_val_3700_ = crate::leanh::lean_ctor_get(v_toQFn_x3f_3699_, 0);
                    crate::leanh::lean_inc(v_val_3700_);
                    crate::leanh::lean_dec_ref_known(v_toQFn_x3f_3699_, 1);
                    if v_isShared_3698_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3697_, 0, v_val_3700_);
                        v___x_3702_ = v___x_3697_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3703_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3703_, 0, v_val_3700_);
                        v___x_3702_ = v_reuseFailAlloc_3703_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3697_);
                    v_toSemiring_3704_ = crate::leanh::lean_ctor_get(v_a_3695_, 0);
                    crate::leanh::lean_inc_ref(v_toSemiring_3704_);
                    crate::leanh::lean_dec(v_a_3695_);
                    v_type_3705_ = crate::leanh::lean_ctor_get(v_toSemiring_3704_, 1);
                    crate::leanh::lean_inc_ref(v_type_3705_);
                    v_u_3706_ = crate::leanh::lean_ctor_get(v_toSemiring_3704_, 2);
                    crate::leanh::lean_inc(v_u_3706_);
                    v_semiringInst_3707_ = crate::leanh::lean_ctor_get(v_toSemiring_3704_, 3);
                    crate::leanh::lean_inc_ref(v_semiringInst_3707_);
                    crate::leanh::lean_dec_ref(v_toSemiring_3704_);
                    v___x_3708_ = l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5;
                    v___x_3709_ = crate::leanh::lean_box(0);
                    v___x_3710_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3710_, 0, v_u_3706_);
                    crate::leanh::lean_ctor_set(v___x_3710_, 1, v___x_3709_);
                    v___x_3711_ = l_Lean_mkConst(v___x_3708_, v___x_3710_);
                    v___x_3712_ = l_Lean_mkAppB(v___x_3711_, v_type_3705_, v_semiringInst_3707_);
                    v___x_3713_ = l_Lean_Meta_Sym_canon(
                        v___x_3712_,
                        v_a_3665_,
                        v_a_3666_,
                        v_a_3667_,
                        v_a_3668_,
                        v_a_3669_,
                        v_a_3670_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3713_) == 0 {
                        v_a_3714_ = crate::leanh::lean_ctor_get(v___x_3713_, 0);
                        crate::leanh::lean_inc(v_a_3714_);
                        crate::leanh::lean_dec_ref_known(v___x_3713_, 1);
                        v___x_3715_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_3714_, v_a_3666_);
                        v___y_3673_ = v___x_3715_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3673_ = v___x_3713_;
                        state = 1;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_3702_;
            }
            8 => {
                if v_isShared_3720_ == 0 {
                    v___x_3722_ = v___x_3719_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3723_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_a_3717_);
                    v___x_3722_ = v_reuseFailAlloc_3723_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3722_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getToQFn___boxed(
    mut v_a_3725_: *mut crate::leanh::LeanObject,
    mut v_a_3726_: *mut crate::leanh::LeanObject,
    mut v_a_3727_: *mut crate::leanh::LeanObject,
    mut v_a_3728_: *mut crate::leanh::LeanObject,
    mut v_a_3729_: *mut crate::leanh::LeanObject,
    mut v_a_3730_: *mut crate::leanh::LeanObject,
    mut v_a_3731_: *mut crate::leanh::LeanObject,
    mut v_a_3732_: *mut crate::leanh::LeanObject,
    mut v_a_3733_: *mut crate::leanh::LeanObject,
    mut v_a_3734_: *mut crate::leanh::LeanObject,
    mut v_a_3735_: *mut crate::leanh::LeanObject,
    mut v_a_3736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3737_ = l_Lean_Meta_Grind_Arith_CommRing_getToQFn(
        v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_,
        v_a_3733_, v_a_3734_, v_a_3735_,
    );
    crate::leanh::lean_dec(v_a_3735_);
    crate::leanh::lean_dec_ref(v_a_3734_);
    crate::leanh::lean_dec(v_a_3733_);
    crate::leanh::lean_dec_ref(v_a_3732_);
    crate::leanh::lean_dec(v_a_3731_);
    crate::leanh::lean_dec_ref(v_a_3730_);
    crate::leanh::lean_dec(v_a_3729_);
    crate::leanh::lean_dec_ref(v_a_3728_);
    crate::leanh::lean_dec(v_a_3727_);
    crate::leanh::lean_dec(v_a_3726_);
    crate::leanh::lean_dec(v_a_3725_);
    return v_res_3737_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(
    mut v_u_3746_: *mut crate::leanh::LeanObject,
    mut v_type_3747_: *mut crate::leanh::LeanObject,
    mut v_a_3748_: *mut crate::leanh::LeanObject,
    mut v_a_3749_: *mut crate::leanh::LeanObject,
    mut v_a_3750_: *mut crate::leanh::LeanObject,
    mut v_a_3751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_add_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3762_: u8 = 0;
    let mut v_val_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3772_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3753_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__1;
                v___x_3754_ = crate::leanh::lean_box(0);
                v___x_3755_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3755_, 0, v_u_3746_);
                crate::leanh::lean_ctor_set(v___x_3755_, 1, v___x_3754_);
                crate::leanh::lean_inc_ref(v___x_3755_);
                v___x_3756_ = l_Lean_mkConst(v___x_3753_, v___x_3755_);
                crate::leanh::lean_inc_ref(v_type_3747_);
                v_add_3757_ = l_Lean_Expr_app___override(v___x_3756_, v_type_3747_);
                v___x_3758_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                    v_add_3757_,
                    v_a_3748_,
                    v_a_3749_,
                    v_a_3750_,
                    v_a_3751_,
                );
                if crate::leanh::lean_obj_tag(v___x_3758_) == 0 {
                    v_a_3759_ = crate::leanh::lean_ctor_get(v___x_3758_, 0);
                    v_isSharedCheck_3772_ = (!crate::leanh::lean_is_exclusive(v___x_3758_)) as u8;
                    if v_isSharedCheck_3772_ == 0 {
                        v___x_3761_ = v___x_3758_;
                        v_isShared_3762_ = v_isSharedCheck_3772_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3759_);
                        crate::leanh::lean_dec(v___x_3758_);
                        v___x_3761_ = crate::leanh::lean_box(0);
                        v_isShared_3762_ = v_isSharedCheck_3772_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_3755_, 2);
                    crate::leanh::lean_dec_ref(v_type_3747_);
                    return v___x_3758_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3759_) == 1 {
                    crate::leanh::lean_del_object(v___x_3761_);
                    v_val_3763_ = crate::leanh::lean_ctor_get(v_a_3759_, 0);
                    crate::leanh::lean_inc(v_val_3763_);
                    crate::leanh::lean_dec_ref_known(v_a_3759_, 1);
                    v___x_3764_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3;
                    v___x_3765_ = l_Lean_mkConst(v___x_3764_, v___x_3755_);
                    v___x_3766_ = l_Lean_mkAppB(v___x_3765_, v_type_3747_, v_val_3763_);
                    v___x_3767_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_3766_,
                        v_a_3748_,
                        v_a_3749_,
                        v_a_3750_,
                        v_a_3751_,
                    );
                    return v___x_3767_;
                } else {
                    crate::leanh::lean_dec(v_a_3759_);
                    crate::leanh::lean_dec_ref_known(v___x_3755_, 2);
                    crate::leanh::lean_dec_ref(v_type_3747_);
                    v___x_3768_ = crate::leanh::lean_box(0);
                    if v_isShared_3762_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3761_, 0, v___x_3768_);
                        v___x_3770_ = v___x_3761_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3771_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3768_);
                        v___x_3770_ = v_reuseFailAlloc_3771_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3770_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___boxed(
    mut v_u_3773_: *mut crate::leanh::LeanObject,
    mut v_type_3774_: *mut crate::leanh::LeanObject,
    mut v_a_3775_: *mut crate::leanh::LeanObject,
    mut v_a_3776_: *mut crate::leanh::LeanObject,
    mut v_a_3777_: *mut crate::leanh::LeanObject,
    mut v_a_3778_: *mut crate::leanh::LeanObject,
    mut v_a_3779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3780_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(v_u_3773_, v_type_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_);
    crate::leanh::lean_dec(v_a_3778_);
    crate::leanh::lean_dec_ref(v_a_3777_);
    crate::leanh::lean_dec(v_a_3776_);
    crate::leanh::lean_dec_ref(v_a_3775_);
    return v_res_3780_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f(
    mut v_u_3781_: *mut crate::leanh::LeanObject,
    mut v_type_3782_: *mut crate::leanh::LeanObject,
    mut v_a_3783_: *mut crate::leanh::LeanObject,
    mut v_a_3784_: *mut crate::leanh::LeanObject,
    mut v_a_3785_: *mut crate::leanh::LeanObject,
    mut v_a_3786_: *mut crate::leanh::LeanObject,
    mut v_a_3787_: *mut crate::leanh::LeanObject,
    mut v_a_3788_: *mut crate::leanh::LeanObject,
    mut v_a_3789_: *mut crate::leanh::LeanObject,
    mut v_a_3790_: *mut crate::leanh::LeanObject,
    mut v_a_3791_: *mut crate::leanh::LeanObject,
    mut v_a_3792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3794_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(v_u_3781_, v_type_3782_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_);
    return v___x_3794_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___boxed(
    mut v_u_3795_: *mut crate::leanh::LeanObject,
    mut v_type_3796_: *mut crate::leanh::LeanObject,
    mut v_a_3797_: *mut crate::leanh::LeanObject,
    mut v_a_3798_: *mut crate::leanh::LeanObject,
    mut v_a_3799_: *mut crate::leanh::LeanObject,
    mut v_a_3800_: *mut crate::leanh::LeanObject,
    mut v_a_3801_: *mut crate::leanh::LeanObject,
    mut v_a_3802_: *mut crate::leanh::LeanObject,
    mut v_a_3803_: *mut crate::leanh::LeanObject,
    mut v_a_3804_: *mut crate::leanh::LeanObject,
    mut v_a_3805_: *mut crate::leanh::LeanObject,
    mut v_a_3806_: *mut crate::leanh::LeanObject,
    mut v_a_3807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3808_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f(v_u_3795_, v_type_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_, v_a_3806_);
    crate::leanh::lean_dec(v_a_3806_);
    crate::leanh::lean_dec_ref(v_a_3805_);
    crate::leanh::lean_dec(v_a_3804_);
    crate::leanh::lean_dec_ref(v_a_3803_);
    crate::leanh::lean_dec(v_a_3802_);
    crate::leanh::lean_dec_ref(v_a_3801_);
    crate::leanh::lean_dec(v_a_3800_);
    crate::leanh::lean_dec_ref(v_a_3799_);
    crate::leanh::lean_dec(v_a_3798_);
    crate::leanh::lean_dec(v_a_3797_);
    return v_res_3808_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0(
    mut v_a_3809_: *mut crate::leanh::LeanObject,
    mut v_a_3810_: *mut crate::leanh::LeanObject,
    mut v_s_3811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_rings_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_3825_: u8 = 0;
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: u8 = 0;
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3830_: u8 = 0;
    let mut v_v_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSemiring_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringId_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toQFn_x3f_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3838_: u8 = 0;
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3849_: u8 = 0;
    let mut v_unused_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3851_: u8 = 0;
    let mut v_unused_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_3812_ = crate::leanh::lean_ctor_get(v_s_3811_, 0);
                v_typeIdOf_3813_ = crate::leanh::lean_ctor_get(v_s_3811_, 1);
                v_exprToRingId_3814_ = crate::leanh::lean_ctor_get(v_s_3811_, 2);
                v_semirings_3815_ = crate::leanh::lean_ctor_get(v_s_3811_, 3);
                v_stypeIdOf_3816_ = crate::leanh::lean_ctor_get(v_s_3811_, 4);
                v_exprToSemiringId_3817_ = crate::leanh::lean_ctor_get(v_s_3811_, 5);
                v_ncRings_3818_ = crate::leanh::lean_ctor_get(v_s_3811_, 6);
                v_exprToNCRingId_3819_ = crate::leanh::lean_ctor_get(v_s_3811_, 7);
                v_nctypeIdOf_3820_ = crate::leanh::lean_ctor_get(v_s_3811_, 8);
                v_ncSemirings_3821_ = crate::leanh::lean_ctor_get(v_s_3811_, 9);
                v_exprToNCSemiringId_3822_ = crate::leanh::lean_ctor_get(v_s_3811_, 10);
                v_ncstypeIdOf_3823_ = crate::leanh::lean_ctor_get(v_s_3811_, 11);
                v_steps_3824_ = crate::leanh::lean_ctor_get(v_s_3811_, 12);
                v_reportedMaxDegreeIssue_3825_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_3811_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                v___x_3826_ = lean_array_get_size(v_semirings_3815_);
                v___x_3827_ = lean_nat_dec_lt(v_a_3809_, v___x_3826_);
                if v___x_3827_ == 0 {
                    crate::leanh::lean_dec(v_a_3810_);
                    return v_s_3811_;
                } else {
                    crate::leanh::lean_inc(v_steps_3824_);
                    crate::leanh::lean_inc_ref(v_ncstypeIdOf_3823_);
                    crate::leanh::lean_inc_ref(v_exprToNCSemiringId_3822_);
                    crate::leanh::lean_inc_ref(v_ncSemirings_3821_);
                    crate::leanh::lean_inc_ref(v_nctypeIdOf_3820_);
                    crate::leanh::lean_inc_ref(v_exprToNCRingId_3819_);
                    crate::leanh::lean_inc_ref(v_ncRings_3818_);
                    crate::leanh::lean_inc_ref(v_exprToSemiringId_3817_);
                    crate::leanh::lean_inc_ref(v_stypeIdOf_3816_);
                    crate::leanh::lean_inc_ref(v_semirings_3815_);
                    crate::leanh::lean_inc_ref(v_exprToRingId_3814_);
                    crate::leanh::lean_inc_ref(v_typeIdOf_3813_);
                    crate::leanh::lean_inc_ref(v_rings_3812_);
                    v_isSharedCheck_3851_ = (!crate::leanh::lean_is_exclusive(v_s_3811_)) as u8;
                    if v_isSharedCheck_3851_ == 0 {
                        v_unused_3852_ = crate::leanh::lean_ctor_get(v_s_3811_, 12);
                        crate::leanh::lean_dec(v_unused_3852_);
                        v_unused_3853_ = crate::leanh::lean_ctor_get(v_s_3811_, 11);
                        crate::leanh::lean_dec(v_unused_3853_);
                        v_unused_3854_ = crate::leanh::lean_ctor_get(v_s_3811_, 10);
                        crate::leanh::lean_dec(v_unused_3854_);
                        v_unused_3855_ = crate::leanh::lean_ctor_get(v_s_3811_, 9);
                        crate::leanh::lean_dec(v_unused_3855_);
                        v_unused_3856_ = crate::leanh::lean_ctor_get(v_s_3811_, 8);
                        crate::leanh::lean_dec(v_unused_3856_);
                        v_unused_3857_ = crate::leanh::lean_ctor_get(v_s_3811_, 7);
                        crate::leanh::lean_dec(v_unused_3857_);
                        v_unused_3858_ = crate::leanh::lean_ctor_get(v_s_3811_, 6);
                        crate::leanh::lean_dec(v_unused_3858_);
                        v_unused_3859_ = crate::leanh::lean_ctor_get(v_s_3811_, 5);
                        crate::leanh::lean_dec(v_unused_3859_);
                        v_unused_3860_ = crate::leanh::lean_ctor_get(v_s_3811_, 4);
                        crate::leanh::lean_dec(v_unused_3860_);
                        v_unused_3861_ = crate::leanh::lean_ctor_get(v_s_3811_, 3);
                        crate::leanh::lean_dec(v_unused_3861_);
                        v_unused_3862_ = crate::leanh::lean_ctor_get(v_s_3811_, 2);
                        crate::leanh::lean_dec(v_unused_3862_);
                        v_unused_3863_ = crate::leanh::lean_ctor_get(v_s_3811_, 1);
                        crate::leanh::lean_dec(v_unused_3863_);
                        v_unused_3864_ = crate::leanh::lean_ctor_get(v_s_3811_, 0);
                        crate::leanh::lean_dec(v_unused_3864_);
                        v___x_3829_ = v_s_3811_;
                        v_isShared_3830_ = v_isSharedCheck_3851_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_s_3811_);
                        v___x_3829_ = crate::leanh::lean_box(0);
                        v_isShared_3830_ = v_isSharedCheck_3851_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3831_ = lean_array_fget(v_semirings_3815_, v_a_3809_);
                v_toSemiring_3832_ = crate::leanh::lean_ctor_get(v_v_3831_, 0);
                v_ringId_3833_ = crate::leanh::lean_ctor_get(v_v_3831_, 1);
                v_commSemiringInst_3834_ = crate::leanh::lean_ctor_get(v_v_3831_, 2);
                v_toQFn_x3f_3835_ = crate::leanh::lean_ctor_get(v_v_3831_, 4);
                v_isSharedCheck_3849_ = (!crate::leanh::lean_is_exclusive(v_v_3831_)) as u8;
                if v_isSharedCheck_3849_ == 0 {
                    v_unused_3850_ = crate::leanh::lean_ctor_get(v_v_3831_, 3);
                    crate::leanh::lean_dec(v_unused_3850_);
                    v___x_3837_ = v_v_3831_;
                    v_isShared_3838_ = v_isSharedCheck_3849_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toQFn_x3f_3835_);
                    crate::leanh::lean_inc(v_commSemiringInst_3834_);
                    crate::leanh::lean_inc(v_ringId_3833_);
                    crate::leanh::lean_inc(v_toSemiring_3832_);
                    crate::leanh::lean_dec(v_v_3831_);
                    v___x_3837_ = crate::leanh::lean_box(0);
                    v_isShared_3838_ = v_isSharedCheck_3849_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3839_ = crate::leanh::lean_box(0);
                v_xs_x27_3840_ = lean_array_fset(v_semirings_3815_, v_a_3809_, v___x_3839_);
                v___x_3841_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3841_, 0, v_a_3810_);
                if v_isShared_3838_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3837_, 3, v___x_3841_);
                    v___x_3843_ = v___x_3837_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3848_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_toSemiring_3832_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 1, v_ringId_3833_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3848_,
                        2,
                        v_commSemiringInst_3834_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 3, v___x_3841_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 4, v_toQFn_x3f_3835_);
                    v___x_3843_ = v_reuseFailAlloc_3848_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3844_ = lean_array_fset(v_xs_x27_3840_, v_a_3809_, v___x_3843_);
                if v_isShared_3830_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3829_, 3, v___x_3844_);
                    v___x_3846_ = v___x_3829_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3847_ = crate::leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_rings_3812_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 1, v_typeIdOf_3813_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 2, v_exprToRingId_3814_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 3, v___x_3844_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 4, v_stypeIdOf_3816_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3847_,
                        5,
                        v_exprToSemiringId_3817_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 6, v_ncRings_3818_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 7, v_exprToNCRingId_3819_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 8, v_nctypeIdOf_3820_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 9, v_ncSemirings_3821_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3847_,
                        10,
                        v_exprToNCSemiringId_3822_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 11, v_ncstypeIdOf_3823_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 12, v_steps_3824_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3847_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                        v_reportedMaxDegreeIssue_3825_,
                    );
                    v___x_3846_ = v_reuseFailAlloc_3847_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3846_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0___boxed(
    mut v_a_3865_: *mut crate::leanh::LeanObject,
    mut v_a_3866_: *mut crate::leanh::LeanObject,
    mut v_s_3867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3868_ = l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0(
        v_a_3865_, v_a_3866_, v_s_3867_,
    );
    crate::leanh::lean_dec(v_a_3865_);
    return v_res_3868_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f(
    mut v_a_3869_: *mut crate::leanh::LeanObject,
    mut v_a_3870_: *mut crate::leanh::LeanObject,
    mut v_a_3871_: *mut crate::leanh::LeanObject,
    mut v_a_3872_: *mut crate::leanh::LeanObject,
    mut v_a_3873_: *mut crate::leanh::LeanObject,
    mut v_a_3874_: *mut crate::leanh::LeanObject,
    mut v_a_3875_: *mut crate::leanh::LeanObject,
    mut v_a_3876_: *mut crate::leanh::LeanObject,
    mut v_a_3877_: *mut crate::leanh::LeanObject,
    mut v_a_3878_: *mut crate::leanh::LeanObject,
    mut v_a_3879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3885_: u8 = 0;
    let mut v_addRightCancelInst_x3f_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSemiring_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3901_: u8 = 0;
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3905_: u8 = 0;
    let mut v_unused_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3910_: u8 = 0;
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3914_: u8 = 0;
    let mut v_isSharedCheck_3915_: u8 = 0;
    let mut v_a_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3919_: u8 = 0;
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3923_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3881_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(
                    v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_,
                    v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_,
                );
                if crate::leanh::lean_obj_tag(v___x_3881_) == 0 {
                    v_a_3882_ = crate::leanh::lean_ctor_get(v___x_3881_, 0);
                    v_isSharedCheck_3915_ = (!crate::leanh::lean_is_exclusive(v___x_3881_)) as u8;
                    if v_isSharedCheck_3915_ == 0 {
                        v___x_3884_ = v___x_3881_;
                        v_isShared_3885_ = v_isSharedCheck_3915_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3882_);
                        crate::leanh::lean_dec(v___x_3881_);
                        v___x_3884_ = crate::leanh::lean_box(0);
                        v_isShared_3885_ = v_isSharedCheck_3915_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3916_ = crate::leanh::lean_ctor_get(v___x_3881_, 0);
                    v_isSharedCheck_3923_ = (!crate::leanh::lean_is_exclusive(v___x_3881_)) as u8;
                    if v_isSharedCheck_3923_ == 0 {
                        v___x_3918_ = v___x_3881_;
                        v_isShared_3919_ = v_isSharedCheck_3923_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3916_);
                        crate::leanh::lean_dec(v___x_3881_);
                        v___x_3918_ = crate::leanh::lean_box(0);
                        v_isShared_3919_ = v_isSharedCheck_3923_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_addRightCancelInst_x3f_3886_ = crate::leanh::lean_ctor_get(v_a_3882_, 3);
                if crate::leanh::lean_obj_tag(v_addRightCancelInst_x3f_3886_) == 1 {
                    crate::leanh::lean_inc_ref(v_addRightCancelInst_x3f_3886_);
                    crate::leanh::lean_dec(v_a_3882_);
                    v_val_3887_ = crate::leanh::lean_ctor_get(v_addRightCancelInst_x3f_3886_, 0);
                    crate::leanh::lean_inc(v_val_3887_);
                    crate::leanh::lean_dec_ref_known(v_addRightCancelInst_x3f_3886_, 1);
                    if v_isShared_3885_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3884_, 0, v_val_3887_);
                        v___x_3889_ = v___x_3884_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3890_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_val_3887_);
                        v___x_3889_ = v_reuseFailAlloc_3890_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3884_);
                    v_toSemiring_3891_ = crate::leanh::lean_ctor_get(v_a_3882_, 0);
                    crate::leanh::lean_inc_ref(v_toSemiring_3891_);
                    crate::leanh::lean_dec(v_a_3882_);
                    v_type_3892_ = crate::leanh::lean_ctor_get(v_toSemiring_3891_, 1);
                    crate::leanh::lean_inc_ref(v_type_3892_);
                    v_u_3893_ = crate::leanh::lean_ctor_get(v_toSemiring_3891_, 2);
                    crate::leanh::lean_inc(v_u_3893_);
                    crate::leanh::lean_dec_ref(v_toSemiring_3891_);
                    v___x_3894_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(v_u_3893_, v_type_3892_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_);
                    if crate::leanh::lean_obj_tag(v___x_3894_) == 0 {
                        v_a_3895_ = crate::leanh::lean_ctor_get(v___x_3894_, 0);
                        crate::leanh::lean_inc_n(v_a_3895_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_3894_, 1);
                        crate::leanh::lean_inc(v_a_3869_);
                        v___f_3896_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                        crate::leanh::lean_closure_set(v___f_3896_, 0, v_a_3869_);
                        crate::leanh::lean_closure_set(v___f_3896_, 1, v_a_3895_);
                        v___x_3897_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                        v___x_3898_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3897_, v___f_3896_, v_a_3870_);
                        if crate::leanh::lean_obj_tag(v___x_3898_) == 0 {
                            v_isSharedCheck_3905_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3898_)) as u8;
                            if v_isSharedCheck_3905_ == 0 {
                                v_unused_3906_ = crate::leanh::lean_ctor_get(v___x_3898_, 0);
                                crate::leanh::lean_dec(v_unused_3906_);
                                v___x_3900_ = v___x_3898_;
                                v_isShared_3901_ = v_isSharedCheck_3905_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_3898_);
                                v___x_3900_ = crate::leanh::lean_box(0);
                                v_isShared_3901_ = v_isSharedCheck_3905_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3895_);
                            v_a_3907_ = crate::leanh::lean_ctor_get(v___x_3898_, 0);
                            v_isSharedCheck_3914_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3898_)) as u8;
                            if v_isSharedCheck_3914_ == 0 {
                                v___x_3909_ = v___x_3898_;
                                v_isShared_3910_ = v_isSharedCheck_3914_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3907_);
                                crate::leanh::lean_dec(v___x_3898_);
                                v___x_3909_ = crate::leanh::lean_box(0);
                                v_isShared_3910_ = v_isSharedCheck_3914_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        return v___x_3894_;
                    }
                }
            }
            2 => {
                return v___x_3889_;
            }
            3 => {
                if v_isShared_3901_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3900_, 0, v_a_3895_);
                    v___x_3903_ = v___x_3900_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3904_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_a_3895_);
                    v___x_3903_ = v_reuseFailAlloc_3904_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3903_;
            }
            5 => {
                if v_isShared_3910_ == 0 {
                    v___x_3912_ = v___x_3909_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3913_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3913_, 0, v_a_3907_);
                    v___x_3912_ = v_reuseFailAlloc_3913_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3912_;
            }
            7 => {
                if v_isShared_3919_ == 0 {
                    v___x_3921_ = v___x_3918_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3922_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_a_3916_);
                    v___x_3921_ = v_reuseFailAlloc_3922_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3921_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___boxed(
    mut v_a_3924_: *mut crate::leanh::LeanObject,
    mut v_a_3925_: *mut crate::leanh::LeanObject,
    mut v_a_3926_: *mut crate::leanh::LeanObject,
    mut v_a_3927_: *mut crate::leanh::LeanObject,
    mut v_a_3928_: *mut crate::leanh::LeanObject,
    mut v_a_3929_: *mut crate::leanh::LeanObject,
    mut v_a_3930_: *mut crate::leanh::LeanObject,
    mut v_a_3931_: *mut crate::leanh::LeanObject,
    mut v_a_3932_: *mut crate::leanh::LeanObject,
    mut v_a_3933_: *mut crate::leanh::LeanObject,
    mut v_a_3934_: *mut crate::leanh::LeanObject,
    mut v_a_3935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3936_ = l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f(
        v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_,
        v_a_3932_, v_a_3933_, v_a_3934_,
    );
    crate::leanh::lean_dec(v_a_3934_);
    crate::leanh::lean_dec_ref(v_a_3933_);
    crate::leanh::lean_dec(v_a_3932_);
    crate::leanh::lean_dec_ref(v_a_3931_);
    crate::leanh::lean_dec(v_a_3930_);
    crate::leanh::lean_dec_ref(v_a_3929_);
    crate::leanh::lean_dec(v_a_3928_);
    crate::leanh::lean_dec_ref(v_a_3927_);
    crate::leanh::lean_dec(v_a_3926_);
    crate::leanh::lean_dec(v_a_3925_);
    crate::leanh::lean_dec(v_a_3924_);
    return v_res_3936_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__0(
    mut v_addFn_3937_: *mut crate::leanh::LeanObject,
    mut v_s_3938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3951_: u8 = 0;
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3956_: u8 = 0;
    let mut v_unused_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_3939_ = crate::leanh::lean_ctor_get(v_s_3938_, 0);
                v_type_3940_ = crate::leanh::lean_ctor_get(v_s_3938_, 1);
                v_u_3941_ = crate::leanh::lean_ctor_get(v_s_3938_, 2);
                v_semiringInst_3942_ = crate::leanh::lean_ctor_get(v_s_3938_, 3);
                v_mulFn_x3f_3943_ = crate::leanh::lean_ctor_get(v_s_3938_, 5);
                v_powFn_x3f_3944_ = crate::leanh::lean_ctor_get(v_s_3938_, 6);
                v_natCastFn_x3f_3945_ = crate::leanh::lean_ctor_get(v_s_3938_, 7);
                v_denote_3946_ = crate::leanh::lean_ctor_get(v_s_3938_, 8);
                v_vars_3947_ = crate::leanh::lean_ctor_get(v_s_3938_, 9);
                v_varMap_3948_ = crate::leanh::lean_ctor_get(v_s_3938_, 10);
                v_isSharedCheck_3956_ = (!crate::leanh::lean_is_exclusive(v_s_3938_)) as u8;
                if v_isSharedCheck_3956_ == 0 {
                    v_unused_3957_ = crate::leanh::lean_ctor_get(v_s_3938_, 4);
                    crate::leanh::lean_dec(v_unused_3957_);
                    v___x_3950_ = v_s_3938_;
                    v_isShared_3951_ = v_isSharedCheck_3956_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_varMap_3948_);
                    crate::leanh::lean_inc(v_vars_3947_);
                    crate::leanh::lean_inc(v_denote_3946_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_3945_);
                    crate::leanh::lean_inc(v_powFn_x3f_3944_);
                    crate::leanh::lean_inc(v_mulFn_x3f_3943_);
                    crate::leanh::lean_inc(v_semiringInst_3942_);
                    crate::leanh::lean_inc(v_u_3941_);
                    crate::leanh::lean_inc(v_type_3940_);
                    crate::leanh::lean_inc(v_id_3939_);
                    crate::leanh::lean_dec(v_s_3938_);
                    v___x_3950_ = crate::leanh::lean_box(0);
                    v_isShared_3951_ = v_isSharedCheck_3956_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3952_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3952_, 0, v_addFn_3937_);
                if v_isShared_3951_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3950_, 4, v___x_3952_);
                    v___x_3954_ = v___x_3950_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3955_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_id_3939_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 1, v_type_3940_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 2, v_u_3941_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 3, v_semiringInst_3942_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 4, v___x_3952_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 5, v_mulFn_x3f_3943_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 6, v_powFn_x3f_3944_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 7, v_natCastFn_x3f_3945_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 8, v_denote_3946_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 9, v_vars_3947_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 10, v_varMap_3948_);
                    v___x_3954_ = v_reuseFailAlloc_3955_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3954_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__1(
    mut v_toPure_3958_: *mut crate::leanh::LeanObject,
    mut v_addFn_3959_: *mut crate::leanh::LeanObject,
    mut v_____r_3960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3961_ =
        crate::leanh::lean_apply_2(v_toPure_3958_, crate::leanh::lean_box(0), v_addFn_3959_);
    return v___x_3961_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__2(
    mut v_toPure_3962_: *mut crate::leanh::LeanObject,
    mut v_modifySemiring_3963_: *mut crate::leanh::LeanObject,
    mut v_toBind_3964_: *mut crate::leanh::LeanObject,
    mut v_addFn_3965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_addFn_3965_);
    v___f_3966_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3966_, 0, v_addFn_3965_);
    v___f_3967_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3967_, 0, v_toPure_3962_);
    crate::leanh::lean_closure_set(v___f_3967_, 1, v_addFn_3965_);
    v___x_3968_ = crate::leanh::lean_apply_1(v_modifySemiring_3963_, v___f_3966_);
    v___x_3969_ = crate::leanh::lean_apply_4(
        v_toBind_3964_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3968_,
        v___f_3967_,
    );
    return v___x_3969_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3(
    mut v_toPure_3987_: *mut crate::leanh::LeanObject,
    mut v_inst_3988_: *mut crate::leanh::LeanObject,
    mut v_inst_3989_: *mut crate::leanh::LeanObject,
    mut v_inst_3990_: *mut crate::leanh::LeanObject,
    mut v_inst_3991_: *mut crate::leanh::LeanObject,
    mut v_toBind_3992_: *mut crate::leanh::LeanObject,
    mut v___f_3993_: *mut crate::leanh::LeanObject,
    mut v_s_3994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_addFn_x3f_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_addFn_x3f_3995_ = crate::leanh::lean_ctor_get(v_s_3994_, 4);
    if crate::leanh::lean_obj_tag(v_addFn_x3f_3995_) == 1 {
        let mut v_val_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_addFn_x3f_3995_);
        crate::leanh::lean_dec_ref(v_s_3994_);
        crate::leanh::lean_dec(v___f_3993_);
        crate::leanh::lean_dec(v_toBind_3992_);
        crate::leanh::lean_dec_ref(v_inst_3991_);
        crate::leanh::lean_dec_ref(v_inst_3990_);
        crate::leanh::lean_dec_ref(v_inst_3989_);
        crate::leanh::lean_dec(v_inst_3988_);
        v_val_3996_ = crate::leanh::lean_ctor_get(v_addFn_x3f_3995_, 0);
        crate::leanh::lean_inc(v_val_3996_);
        crate::leanh::lean_dec_ref_known(v_addFn_x3f_3995_, 1);
        v___x_3997_ =
            crate::leanh::lean_apply_2(v_toPure_3987_, crate::leanh::lean_box(0), v_val_3996_);
        return v___x_3997_;
    } else {
        let mut v_type_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_expectedInst_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_3987_);
        v_type_3998_ = crate::leanh::lean_ctor_get(v_s_3994_, 1);
        crate::leanh::lean_inc_ref_n(v_type_3998_, 3);
        v_u_3999_ = crate::leanh::lean_ctor_get(v_s_3994_, 2);
        crate::leanh::lean_inc_n(v_u_3999_, 2);
        v_semiringInst_4000_ = crate::leanh::lean_ctor_get(v_s_3994_, 3);
        crate::leanh::lean_inc_ref(v_semiringInst_4000_);
        crate::leanh::lean_dec_ref(v_s_3994_);
        v___x_4001_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1;
        v___x_4002_ = crate::leanh::lean_box(0);
        v___x_4003_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4003_, 0, v_u_3999_);
        crate::leanh::lean_ctor_set(v___x_4003_, 1, v___x_4002_);
        crate::leanh::lean_inc_ref(v___x_4003_);
        v___x_4004_ = l_Lean_mkConst(v___x_4001_, v___x_4003_);
        v___x_4005_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4;
        v___x_4006_ = l_Lean_mkConst(v___x_4005_, v___x_4003_);
        v___x_4007_ = l_Lean_mkAppB(v___x_4006_, v_type_3998_, v_semiringInst_4000_);
        v_expectedInst_4008_ = l_Lean_mkAppB(v___x_4004_, v_type_3998_, v___x_4007_);
        v___x_4009_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__6;
        v___x_4010_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8;
        v___x_4011_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(
            v_inst_3988_,
            v_inst_3989_,
            v_inst_3990_,
            v_inst_3991_,
            v_type_3998_,
            v_u_3999_,
            v___x_4009_,
            v___x_4010_,
            v_expectedInst_4008_,
        );
        v___x_4012_ = crate::leanh::lean_apply_4(
            v_toBind_3992_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_4011_,
            v___f_3993_,
        );
        return v___x_4012_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg(
    mut v_inst_4013_: *mut crate::leanh::LeanObject,
    mut v_inst_4014_: *mut crate::leanh::LeanObject,
    mut v_inst_4015_: *mut crate::leanh::LeanObject,
    mut v_inst_4016_: *mut crate::leanh::LeanObject,
    mut v_inst_4017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getSemiring_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifySemiring_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4018_ = crate::leanh::lean_ctor_get(v_inst_4015_, 0);
    v_toBind_4019_ = crate::leanh::lean_ctor_get(v_inst_4015_, 1);
    crate::leanh::lean_inc_n(v_toBind_4019_, 3);
    v_getSemiring_4020_ = crate::leanh::lean_ctor_get(v_inst_4017_, 0);
    crate::leanh::lean_inc(v_getSemiring_4020_);
    v_modifySemiring_4021_ = crate::leanh::lean_ctor_get(v_inst_4017_, 1);
    crate::leanh::lean_inc(v_modifySemiring_4021_);
    crate::leanh::lean_dec_ref(v_inst_4017_);
    v_toPure_4022_ = crate::leanh::lean_ctor_get(v_toApplicative_4018_, 1);
    crate::leanh::lean_inc_n(v_toPure_4022_, 2);
    v___f_4023_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4023_, 0, v_toPure_4022_);
    crate::leanh::lean_closure_set(v___f_4023_, 1, v_modifySemiring_4021_);
    crate::leanh::lean_closure_set(v___f_4023_, 2, v_toBind_4019_);
    v___f_4024_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_4024_, 0, v_toPure_4022_);
    crate::leanh::lean_closure_set(v___f_4024_, 1, v_inst_4013_);
    crate::leanh::lean_closure_set(v___f_4024_, 2, v_inst_4014_);
    crate::leanh::lean_closure_set(v___f_4024_, 3, v_inst_4015_);
    crate::leanh::lean_closure_set(v___f_4024_, 4, v_inst_4016_);
    crate::leanh::lean_closure_set(v___f_4024_, 5, v_toBind_4019_);
    crate::leanh::lean_closure_set(v___f_4024_, 6, v___f_4023_);
    v___x_4025_ = crate::leanh::lean_apply_4(
        v_toBind_4019_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getSemiring_4020_,
        v___f_4024_,
    );
    return v___x_4025_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27(
    mut v_m_4026_: *mut crate::leanh::LeanObject,
    mut v_inst_4027_: *mut crate::leanh::LeanObject,
    mut v_inst_4028_: *mut crate::leanh::LeanObject,
    mut v_inst_4029_: *mut crate::leanh::LeanObject,
    mut v_inst_4030_: *mut crate::leanh::LeanObject,
    mut v_inst_4031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4032_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg(
        v_inst_4027_,
        v_inst_4028_,
        v_inst_4029_,
        v_inst_4030_,
        v_inst_4031_,
    );
    return v___x_4032_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__0(
    mut v_mulFn_4033_: *mut crate::leanh::LeanObject,
    mut v_s_4034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4047_: u8 = 0;
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4052_: u8 = 0;
    let mut v_unused_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_4035_ = crate::leanh::lean_ctor_get(v_s_4034_, 0);
                v_type_4036_ = crate::leanh::lean_ctor_get(v_s_4034_, 1);
                v_u_4037_ = crate::leanh::lean_ctor_get(v_s_4034_, 2);
                v_semiringInst_4038_ = crate::leanh::lean_ctor_get(v_s_4034_, 3);
                v_addFn_x3f_4039_ = crate::leanh::lean_ctor_get(v_s_4034_, 4);
                v_powFn_x3f_4040_ = crate::leanh::lean_ctor_get(v_s_4034_, 6);
                v_natCastFn_x3f_4041_ = crate::leanh::lean_ctor_get(v_s_4034_, 7);
                v_denote_4042_ = crate::leanh::lean_ctor_get(v_s_4034_, 8);
                v_vars_4043_ = crate::leanh::lean_ctor_get(v_s_4034_, 9);
                v_varMap_4044_ = crate::leanh::lean_ctor_get(v_s_4034_, 10);
                v_isSharedCheck_4052_ = (!crate::leanh::lean_is_exclusive(v_s_4034_)) as u8;
                if v_isSharedCheck_4052_ == 0 {
                    v_unused_4053_ = crate::leanh::lean_ctor_get(v_s_4034_, 5);
                    crate::leanh::lean_dec(v_unused_4053_);
                    v___x_4046_ = v_s_4034_;
                    v_isShared_4047_ = v_isSharedCheck_4052_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_varMap_4044_);
                    crate::leanh::lean_inc(v_vars_4043_);
                    crate::leanh::lean_inc(v_denote_4042_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_4041_);
                    crate::leanh::lean_inc(v_powFn_x3f_4040_);
                    crate::leanh::lean_inc(v_addFn_x3f_4039_);
                    crate::leanh::lean_inc(v_semiringInst_4038_);
                    crate::leanh::lean_inc(v_u_4037_);
                    crate::leanh::lean_inc(v_type_4036_);
                    crate::leanh::lean_inc(v_id_4035_);
                    crate::leanh::lean_dec(v_s_4034_);
                    v___x_4046_ = crate::leanh::lean_box(0);
                    v_isShared_4047_ = v_isSharedCheck_4052_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4048_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4048_, 0, v_mulFn_4033_);
                if v_isShared_4047_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4046_, 5, v___x_4048_);
                    v___x_4050_ = v___x_4046_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4051_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_id_4035_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4051_, 1, v_type_4036_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4051_, 2, v_u_4037_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4051_, 3, v_semiringInst_4038_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4051_, 4, v_addFn_x3f_4039_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4051_, 5, v___x_4048_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4051_, 6, v_powFn_x3f_4040_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4051_, 7, v_natCastFn_x3f_4041_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4051_, 8, v_denote_4042_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4051_, 9, v_vars_4043_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4051_, 10, v_varMap_4044_);
                    v___x_4050_ = v_reuseFailAlloc_4051_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4050_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__1(
    mut v_toPure_4054_: *mut crate::leanh::LeanObject,
    mut v_mulFn_4055_: *mut crate::leanh::LeanObject,
    mut v_____r_4056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4057_ =
        crate::leanh::lean_apply_2(v_toPure_4054_, crate::leanh::lean_box(0), v_mulFn_4055_);
    return v___x_4057_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__2(
    mut v_toPure_4058_: *mut crate::leanh::LeanObject,
    mut v_modifySemiring_4059_: *mut crate::leanh::LeanObject,
    mut v_toBind_4060_: *mut crate::leanh::LeanObject,
    mut v_mulFn_4061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_mulFn_4061_);
    v___f_4062_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4062_, 0, v_mulFn_4061_);
    v___f_4063_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4063_, 0, v_toPure_4058_);
    crate::leanh::lean_closure_set(v___f_4063_, 1, v_mulFn_4061_);
    v___x_4064_ = crate::leanh::lean_apply_1(v_modifySemiring_4059_, v___f_4062_);
    v___x_4065_ = crate::leanh::lean_apply_4(
        v_toBind_4060_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4064_,
        v___f_4063_,
    );
    return v___x_4065_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3(
    mut v_toPure_4082_: *mut crate::leanh::LeanObject,
    mut v_inst_4083_: *mut crate::leanh::LeanObject,
    mut v_inst_4084_: *mut crate::leanh::LeanObject,
    mut v_inst_4085_: *mut crate::leanh::LeanObject,
    mut v_inst_4086_: *mut crate::leanh::LeanObject,
    mut v_toBind_4087_: *mut crate::leanh::LeanObject,
    mut v___f_4088_: *mut crate::leanh::LeanObject,
    mut v_s_4089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mulFn_x3f_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mulFn_x3f_4090_ = crate::leanh::lean_ctor_get(v_s_4089_, 5);
    if crate::leanh::lean_obj_tag(v_mulFn_x3f_4090_) == 1 {
        let mut v_val_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_mulFn_x3f_4090_);
        crate::leanh::lean_dec_ref(v_s_4089_);
        crate::leanh::lean_dec(v___f_4088_);
        crate::leanh::lean_dec(v_toBind_4087_);
        crate::leanh::lean_dec_ref(v_inst_4086_);
        crate::leanh::lean_dec_ref(v_inst_4085_);
        crate::leanh::lean_dec_ref(v_inst_4084_);
        crate::leanh::lean_dec(v_inst_4083_);
        v_val_4091_ = crate::leanh::lean_ctor_get(v_mulFn_x3f_4090_, 0);
        crate::leanh::lean_inc(v_val_4091_);
        crate::leanh::lean_dec_ref_known(v_mulFn_x3f_4090_, 1);
        v___x_4092_ =
            crate::leanh::lean_apply_2(v_toPure_4082_, crate::leanh::lean_box(0), v_val_4091_);
        return v___x_4092_;
    } else {
        let mut v_type_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_expectedInst_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_4082_);
        v_type_4093_ = crate::leanh::lean_ctor_get(v_s_4089_, 1);
        crate::leanh::lean_inc_ref_n(v_type_4093_, 3);
        v_u_4094_ = crate::leanh::lean_ctor_get(v_s_4089_, 2);
        crate::leanh::lean_inc_n(v_u_4094_, 2);
        v_semiringInst_4095_ = crate::leanh::lean_ctor_get(v_s_4089_, 3);
        crate::leanh::lean_inc_ref(v_semiringInst_4095_);
        crate::leanh::lean_dec_ref(v_s_4089_);
        v___x_4096_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1;
        v___x_4097_ = crate::leanh::lean_box(0);
        v___x_4098_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4098_, 0, v_u_4094_);
        crate::leanh::lean_ctor_set(v___x_4098_, 1, v___x_4097_);
        crate::leanh::lean_inc_ref(v___x_4098_);
        v___x_4099_ = l_Lean_mkConst(v___x_4096_, v___x_4098_);
        v___x_4100_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3;
        v___x_4101_ = l_Lean_mkConst(v___x_4100_, v___x_4098_);
        v___x_4102_ = l_Lean_mkAppB(v___x_4101_, v_type_4093_, v_semiringInst_4095_);
        v_expectedInst_4103_ = l_Lean_mkAppB(v___x_4099_, v_type_4093_, v___x_4102_);
        v___x_4104_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__5;
        v___x_4105_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7;
        v___x_4106_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(
            v_inst_4083_,
            v_inst_4084_,
            v_inst_4085_,
            v_inst_4086_,
            v_type_4093_,
            v_u_4094_,
            v___x_4104_,
            v___x_4105_,
            v_expectedInst_4103_,
        );
        v___x_4107_ = crate::leanh::lean_apply_4(
            v_toBind_4087_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_4106_,
            v___f_4088_,
        );
        return v___x_4107_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg(
    mut v_inst_4108_: *mut crate::leanh::LeanObject,
    mut v_inst_4109_: *mut crate::leanh::LeanObject,
    mut v_inst_4110_: *mut crate::leanh::LeanObject,
    mut v_inst_4111_: *mut crate::leanh::LeanObject,
    mut v_inst_4112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getSemiring_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifySemiring_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4113_ = crate::leanh::lean_ctor_get(v_inst_4110_, 0);
    v_toBind_4114_ = crate::leanh::lean_ctor_get(v_inst_4110_, 1);
    crate::leanh::lean_inc_n(v_toBind_4114_, 3);
    v_getSemiring_4115_ = crate::leanh::lean_ctor_get(v_inst_4112_, 0);
    crate::leanh::lean_inc(v_getSemiring_4115_);
    v_modifySemiring_4116_ = crate::leanh::lean_ctor_get(v_inst_4112_, 1);
    crate::leanh::lean_inc(v_modifySemiring_4116_);
    crate::leanh::lean_dec_ref(v_inst_4112_);
    v_toPure_4117_ = crate::leanh::lean_ctor_get(v_toApplicative_4113_, 1);
    crate::leanh::lean_inc_n(v_toPure_4117_, 2);
    v___f_4118_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4118_, 0, v_toPure_4117_);
    crate::leanh::lean_closure_set(v___f_4118_, 1, v_modifySemiring_4116_);
    crate::leanh::lean_closure_set(v___f_4118_, 2, v_toBind_4114_);
    v___f_4119_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_4119_, 0, v_toPure_4117_);
    crate::leanh::lean_closure_set(v___f_4119_, 1, v_inst_4108_);
    crate::leanh::lean_closure_set(v___f_4119_, 2, v_inst_4109_);
    crate::leanh::lean_closure_set(v___f_4119_, 3, v_inst_4110_);
    crate::leanh::lean_closure_set(v___f_4119_, 4, v_inst_4111_);
    crate::leanh::lean_closure_set(v___f_4119_, 5, v_toBind_4114_);
    crate::leanh::lean_closure_set(v___f_4119_, 6, v___f_4118_);
    v___x_4120_ = crate::leanh::lean_apply_4(
        v_toBind_4114_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getSemiring_4115_,
        v___f_4119_,
    );
    return v___x_4120_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27(
    mut v_m_4121_: *mut crate::leanh::LeanObject,
    mut v_inst_4122_: *mut crate::leanh::LeanObject,
    mut v_inst_4123_: *mut crate::leanh::LeanObject,
    mut v_inst_4124_: *mut crate::leanh::LeanObject,
    mut v_inst_4125_: *mut crate::leanh::LeanObject,
    mut v_inst_4126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4127_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg(
        v_inst_4122_,
        v_inst_4123_,
        v_inst_4124_,
        v_inst_4125_,
        v_inst_4126_,
    );
    return v___x_4127_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__0(
    mut v_powFn_4128_: *mut crate::leanh::LeanObject,
    mut v_s_4129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4142_: u8 = 0;
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4147_: u8 = 0;
    let mut v_unused_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_4130_ = crate::leanh::lean_ctor_get(v_s_4129_, 0);
                v_type_4131_ = crate::leanh::lean_ctor_get(v_s_4129_, 1);
                v_u_4132_ = crate::leanh::lean_ctor_get(v_s_4129_, 2);
                v_semiringInst_4133_ = crate::leanh::lean_ctor_get(v_s_4129_, 3);
                v_addFn_x3f_4134_ = crate::leanh::lean_ctor_get(v_s_4129_, 4);
                v_mulFn_x3f_4135_ = crate::leanh::lean_ctor_get(v_s_4129_, 5);
                v_natCastFn_x3f_4136_ = crate::leanh::lean_ctor_get(v_s_4129_, 7);
                v_denote_4137_ = crate::leanh::lean_ctor_get(v_s_4129_, 8);
                v_vars_4138_ = crate::leanh::lean_ctor_get(v_s_4129_, 9);
                v_varMap_4139_ = crate::leanh::lean_ctor_get(v_s_4129_, 10);
                v_isSharedCheck_4147_ = (!crate::leanh::lean_is_exclusive(v_s_4129_)) as u8;
                if v_isSharedCheck_4147_ == 0 {
                    v_unused_4148_ = crate::leanh::lean_ctor_get(v_s_4129_, 6);
                    crate::leanh::lean_dec(v_unused_4148_);
                    v___x_4141_ = v_s_4129_;
                    v_isShared_4142_ = v_isSharedCheck_4147_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_varMap_4139_);
                    crate::leanh::lean_inc(v_vars_4138_);
                    crate::leanh::lean_inc(v_denote_4137_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_4136_);
                    crate::leanh::lean_inc(v_mulFn_x3f_4135_);
                    crate::leanh::lean_inc(v_addFn_x3f_4134_);
                    crate::leanh::lean_inc(v_semiringInst_4133_);
                    crate::leanh::lean_inc(v_u_4132_);
                    crate::leanh::lean_inc(v_type_4131_);
                    crate::leanh::lean_inc(v_id_4130_);
                    crate::leanh::lean_dec(v_s_4129_);
                    v___x_4141_ = crate::leanh::lean_box(0);
                    v_isShared_4142_ = v_isSharedCheck_4147_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4143_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4143_, 0, v_powFn_4128_);
                if v_isShared_4142_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4141_, 6, v___x_4143_);
                    v___x_4145_ = v___x_4141_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4146_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_id_4130_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 1, v_type_4131_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 2, v_u_4132_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 3, v_semiringInst_4133_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 4, v_addFn_x3f_4134_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 5, v_mulFn_x3f_4135_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 6, v___x_4143_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 7, v_natCastFn_x3f_4136_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 8, v_denote_4137_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 9, v_vars_4138_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 10, v_varMap_4139_);
                    v___x_4145_ = v_reuseFailAlloc_4146_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4145_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__1(
    mut v_toPure_4149_: *mut crate::leanh::LeanObject,
    mut v_powFn_4150_: *mut crate::leanh::LeanObject,
    mut v_____r_4151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4152_ =
        crate::leanh::lean_apply_2(v_toPure_4149_, crate::leanh::lean_box(0), v_powFn_4150_);
    return v___x_4152_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__2(
    mut v_toPure_4153_: *mut crate::leanh::LeanObject,
    mut v_modifySemiring_4154_: *mut crate::leanh::LeanObject,
    mut v_toBind_4155_: *mut crate::leanh::LeanObject,
    mut v_powFn_4156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_powFn_4156_);
    v___f_4157_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4157_, 0, v_powFn_4156_);
    v___f_4158_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4158_, 0, v_toPure_4153_);
    crate::leanh::lean_closure_set(v___f_4158_, 1, v_powFn_4156_);
    v___x_4159_ = crate::leanh::lean_apply_1(v_modifySemiring_4154_, v___f_4157_);
    v___x_4160_ = crate::leanh::lean_apply_4(
        v_toBind_4155_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4159_,
        v___f_4158_,
    );
    return v___x_4160_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__3(
    mut v_toPure_4161_: *mut crate::leanh::LeanObject,
    mut v_inst_4162_: *mut crate::leanh::LeanObject,
    mut v_inst_4163_: *mut crate::leanh::LeanObject,
    mut v_inst_4164_: *mut crate::leanh::LeanObject,
    mut v_inst_4165_: *mut crate::leanh::LeanObject,
    mut v_toBind_4166_: *mut crate::leanh::LeanObject,
    mut v___f_4167_: *mut crate::leanh::LeanObject,
    mut v_s_4168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_powFn_x3f_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_powFn_x3f_4169_ = crate::leanh::lean_ctor_get(v_s_4168_, 6);
    if crate::leanh::lean_obj_tag(v_powFn_x3f_4169_) == 1 {
        let mut v_val_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_powFn_x3f_4169_);
        crate::leanh::lean_dec_ref(v_s_4168_);
        crate::leanh::lean_dec(v___f_4167_);
        crate::leanh::lean_dec(v_toBind_4166_);
        crate::leanh::lean_dec_ref(v_inst_4165_);
        crate::leanh::lean_dec_ref(v_inst_4164_);
        crate::leanh::lean_dec_ref(v_inst_4163_);
        crate::leanh::lean_dec(v_inst_4162_);
        v_val_4170_ = crate::leanh::lean_ctor_get(v_powFn_x3f_4169_, 0);
        crate::leanh::lean_inc(v_val_4170_);
        crate::leanh::lean_dec_ref_known(v_powFn_x3f_4169_, 1);
        v___x_4171_ =
            crate::leanh::lean_apply_2(v_toPure_4161_, crate::leanh::lean_box(0), v_val_4170_);
        return v___x_4171_;
    } else {
        let mut v_type_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_4161_);
        v_type_4172_ = crate::leanh::lean_ctor_get(v_s_4168_, 1);
        crate::leanh::lean_inc_ref(v_type_4172_);
        v_u_4173_ = crate::leanh::lean_ctor_get(v_s_4168_, 2);
        crate::leanh::lean_inc(v_u_4173_);
        v_semiringInst_4174_ = crate::leanh::lean_ctor_get(v_s_4168_, 3);
        crate::leanh::lean_inc_ref(v_semiringInst_4174_);
        crate::leanh::lean_dec_ref(v_s_4168_);
        v___x_4175_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg(
            v_inst_4162_,
            v_inst_4163_,
            v_inst_4164_,
            v_inst_4165_,
            v_u_4173_,
            v_type_4172_,
            v_semiringInst_4174_,
        );
        v___x_4176_ = crate::leanh::lean_apply_4(
            v_toBind_4166_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_4175_,
            v___f_4167_,
        );
        return v___x_4176_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg(
    mut v_inst_4177_: *mut crate::leanh::LeanObject,
    mut v_inst_4178_: *mut crate::leanh::LeanObject,
    mut v_inst_4179_: *mut crate::leanh::LeanObject,
    mut v_inst_4180_: *mut crate::leanh::LeanObject,
    mut v_inst_4181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getSemiring_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifySemiring_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4182_ = crate::leanh::lean_ctor_get(v_inst_4179_, 0);
    v_toBind_4183_ = crate::leanh::lean_ctor_get(v_inst_4179_, 1);
    crate::leanh::lean_inc_n(v_toBind_4183_, 3);
    v_getSemiring_4184_ = crate::leanh::lean_ctor_get(v_inst_4181_, 0);
    crate::leanh::lean_inc(v_getSemiring_4184_);
    v_modifySemiring_4185_ = crate::leanh::lean_ctor_get(v_inst_4181_, 1);
    crate::leanh::lean_inc(v_modifySemiring_4185_);
    crate::leanh::lean_dec_ref(v_inst_4181_);
    v_toPure_4186_ = crate::leanh::lean_ctor_get(v_toApplicative_4182_, 1);
    crate::leanh::lean_inc_n(v_toPure_4186_, 2);
    v___f_4187_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4187_, 0, v_toPure_4186_);
    crate::leanh::lean_closure_set(v___f_4187_, 1, v_modifySemiring_4185_);
    crate::leanh::lean_closure_set(v___f_4187_, 2, v_toBind_4183_);
    v___f_4188_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_4188_, 0, v_toPure_4186_);
    crate::leanh::lean_closure_set(v___f_4188_, 1, v_inst_4177_);
    crate::leanh::lean_closure_set(v___f_4188_, 2, v_inst_4178_);
    crate::leanh::lean_closure_set(v___f_4188_, 3, v_inst_4179_);
    crate::leanh::lean_closure_set(v___f_4188_, 4, v_inst_4180_);
    crate::leanh::lean_closure_set(v___f_4188_, 5, v_toBind_4183_);
    crate::leanh::lean_closure_set(v___f_4188_, 6, v___f_4187_);
    v___x_4189_ = crate::leanh::lean_apply_4(
        v_toBind_4183_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getSemiring_4184_,
        v___f_4188_,
    );
    return v___x_4189_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27(
    mut v_m_4190_: *mut crate::leanh::LeanObject,
    mut v_inst_4191_: *mut crate::leanh::LeanObject,
    mut v_inst_4192_: *mut crate::leanh::LeanObject,
    mut v_inst_4193_: *mut crate::leanh::LeanObject,
    mut v_inst_4194_: *mut crate::leanh::LeanObject,
    mut v_inst_4195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4196_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg(
        v_inst_4191_,
        v_inst_4192_,
        v_inst_4193_,
        v_inst_4194_,
        v_inst_4195_,
    );
    return v___x_4196_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__0(
    mut v_natCastFn_4197_: *mut crate::leanh::LeanObject,
    mut v_s_4198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4211_: u8 = 0;
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4216_: u8 = 0;
    let mut v_unused_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_4199_ = crate::leanh::lean_ctor_get(v_s_4198_, 0);
                v_type_4200_ = crate::leanh::lean_ctor_get(v_s_4198_, 1);
                v_u_4201_ = crate::leanh::lean_ctor_get(v_s_4198_, 2);
                v_semiringInst_4202_ = crate::leanh::lean_ctor_get(v_s_4198_, 3);
                v_addFn_x3f_4203_ = crate::leanh::lean_ctor_get(v_s_4198_, 4);
                v_mulFn_x3f_4204_ = crate::leanh::lean_ctor_get(v_s_4198_, 5);
                v_powFn_x3f_4205_ = crate::leanh::lean_ctor_get(v_s_4198_, 6);
                v_denote_4206_ = crate::leanh::lean_ctor_get(v_s_4198_, 8);
                v_vars_4207_ = crate::leanh::lean_ctor_get(v_s_4198_, 9);
                v_varMap_4208_ = crate::leanh::lean_ctor_get(v_s_4198_, 10);
                v_isSharedCheck_4216_ = (!crate::leanh::lean_is_exclusive(v_s_4198_)) as u8;
                if v_isSharedCheck_4216_ == 0 {
                    v_unused_4217_ = crate::leanh::lean_ctor_get(v_s_4198_, 7);
                    crate::leanh::lean_dec(v_unused_4217_);
                    v___x_4210_ = v_s_4198_;
                    v_isShared_4211_ = v_isSharedCheck_4216_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_varMap_4208_);
                    crate::leanh::lean_inc(v_vars_4207_);
                    crate::leanh::lean_inc(v_denote_4206_);
                    crate::leanh::lean_inc(v_powFn_x3f_4205_);
                    crate::leanh::lean_inc(v_mulFn_x3f_4204_);
                    crate::leanh::lean_inc(v_addFn_x3f_4203_);
                    crate::leanh::lean_inc(v_semiringInst_4202_);
                    crate::leanh::lean_inc(v_u_4201_);
                    crate::leanh::lean_inc(v_type_4200_);
                    crate::leanh::lean_inc(v_id_4199_);
                    crate::leanh::lean_dec(v_s_4198_);
                    v___x_4210_ = crate::leanh::lean_box(0);
                    v_isShared_4211_ = v_isSharedCheck_4216_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4212_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4212_, 0, v_natCastFn_4197_);
                if v_isShared_4211_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4210_, 7, v___x_4212_);
                    v___x_4214_ = v___x_4210_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4215_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4215_, 0, v_id_4199_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4215_, 1, v_type_4200_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4215_, 2, v_u_4201_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4215_, 3, v_semiringInst_4202_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4215_, 4, v_addFn_x3f_4203_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4215_, 5, v_mulFn_x3f_4204_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4215_, 6, v_powFn_x3f_4205_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4215_, 7, v___x_4212_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4215_, 8, v_denote_4206_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4215_, 9, v_vars_4207_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4215_, 10, v_varMap_4208_);
                    v___x_4214_ = v_reuseFailAlloc_4215_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4214_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__1(
    mut v_toPure_4218_: *mut crate::leanh::LeanObject,
    mut v_natCastFn_4219_: *mut crate::leanh::LeanObject,
    mut v_____r_4220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4221_ =
        crate::leanh::lean_apply_2(v_toPure_4218_, crate::leanh::lean_box(0), v_natCastFn_4219_);
    return v___x_4221_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__2(
    mut v_toPure_4222_: *mut crate::leanh::LeanObject,
    mut v_modifySemiring_4223_: *mut crate::leanh::LeanObject,
    mut v_toBind_4224_: *mut crate::leanh::LeanObject,
    mut v_natCastFn_4225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_natCastFn_4225_);
    v___f_4226_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4226_, 0, v_natCastFn_4225_);
    v___f_4227_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__1
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4227_, 0, v_toPure_4222_);
    crate::leanh::lean_closure_set(v___f_4227_, 1, v_natCastFn_4225_);
    v___x_4228_ = crate::leanh::lean_apply_1(v_modifySemiring_4223_, v___f_4226_);
    v___x_4229_ = crate::leanh::lean_apply_4(
        v_toBind_4224_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4228_,
        v___f_4227_,
    );
    return v___x_4229_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__3(
    mut v_toPure_4230_: *mut crate::leanh::LeanObject,
    mut v_inst_4231_: *mut crate::leanh::LeanObject,
    mut v_inst_4232_: *mut crate::leanh::LeanObject,
    mut v_inst_4233_: *mut crate::leanh::LeanObject,
    mut v_toBind_4234_: *mut crate::leanh::LeanObject,
    mut v___f_4235_: *mut crate::leanh::LeanObject,
    mut v_s_4236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_natCastFn_x3f_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_natCastFn_x3f_4237_ = crate::leanh::lean_ctor_get(v_s_4236_, 7);
    if crate::leanh::lean_obj_tag(v_natCastFn_x3f_4237_) == 1 {
        let mut v_val_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_natCastFn_x3f_4237_);
        crate::leanh::lean_dec_ref(v_s_4236_);
        crate::leanh::lean_dec(v___f_4235_);
        crate::leanh::lean_dec(v_toBind_4234_);
        crate::leanh::lean_dec_ref(v_inst_4233_);
        crate::leanh::lean_dec_ref(v_inst_4232_);
        crate::leanh::lean_dec(v_inst_4231_);
        v_val_4238_ = crate::leanh::lean_ctor_get(v_natCastFn_x3f_4237_, 0);
        crate::leanh::lean_inc(v_val_4238_);
        crate::leanh::lean_dec_ref_known(v_natCastFn_x3f_4237_, 1);
        v___x_4239_ =
            crate::leanh::lean_apply_2(v_toPure_4230_, crate::leanh::lean_box(0), v_val_4238_);
        return v___x_4239_;
    } else {
        let mut v_type_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_4230_);
        v_type_4240_ = crate::leanh::lean_ctor_get(v_s_4236_, 1);
        crate::leanh::lean_inc_ref(v_type_4240_);
        v_u_4241_ = crate::leanh::lean_ctor_get(v_s_4236_, 2);
        crate::leanh::lean_inc(v_u_4241_);
        v_semiringInst_4242_ = crate::leanh::lean_ctor_get(v_s_4236_, 3);
        crate::leanh::lean_inc_ref(v_semiringInst_4242_);
        crate::leanh::lean_dec_ref(v_s_4236_);
        v___x_4243_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg(
            v_inst_4231_,
            v_inst_4232_,
            v_inst_4233_,
            v_u_4241_,
            v_type_4240_,
            v_semiringInst_4242_,
        );
        v___x_4244_ = crate::leanh::lean_apply_4(
            v_toBind_4234_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_4243_,
            v___f_4235_,
        );
        return v___x_4244_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg(
    mut v_inst_4245_: *mut crate::leanh::LeanObject,
    mut v_inst_4246_: *mut crate::leanh::LeanObject,
    mut v_inst_4247_: *mut crate::leanh::LeanObject,
    mut v_inst_4248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getSemiring_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifySemiring_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4249_ = crate::leanh::lean_ctor_get(v_inst_4246_, 0);
    v_toBind_4250_ = crate::leanh::lean_ctor_get(v_inst_4246_, 1);
    crate::leanh::lean_inc_n(v_toBind_4250_, 3);
    v_getSemiring_4251_ = crate::leanh::lean_ctor_get(v_inst_4248_, 0);
    crate::leanh::lean_inc(v_getSemiring_4251_);
    v_modifySemiring_4252_ = crate::leanh::lean_ctor_get(v_inst_4248_, 1);
    crate::leanh::lean_inc(v_modifySemiring_4252_);
    crate::leanh::lean_dec_ref(v_inst_4248_);
    v_toPure_4253_ = crate::leanh::lean_ctor_get(v_toApplicative_4249_, 1);
    crate::leanh::lean_inc_n(v_toPure_4253_, 2);
    v___f_4254_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__2
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4254_, 0, v_toPure_4253_);
    crate::leanh::lean_closure_set(v___f_4254_, 1, v_modifySemiring_4252_);
    crate::leanh::lean_closure_set(v___f_4254_, 2, v_toBind_4250_);
    v___f_4255_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__3
            as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_4255_, 0, v_toPure_4253_);
    crate::leanh::lean_closure_set(v___f_4255_, 1, v_inst_4245_);
    crate::leanh::lean_closure_set(v___f_4255_, 2, v_inst_4246_);
    crate::leanh::lean_closure_set(v___f_4255_, 3, v_inst_4247_);
    crate::leanh::lean_closure_set(v___f_4255_, 4, v_toBind_4250_);
    crate::leanh::lean_closure_set(v___f_4255_, 5, v___f_4254_);
    v___x_4256_ = crate::leanh::lean_apply_4(
        v_toBind_4250_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getSemiring_4251_,
        v___f_4255_,
    );
    return v___x_4256_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27(
    mut v_m_4257_: *mut crate::leanh::LeanObject,
    mut v_inst_4258_: *mut crate::leanh::LeanObject,
    mut v_inst_4259_: *mut crate::leanh::LeanObject,
    mut v_inst_4260_: *mut crate::leanh::LeanObject,
    mut v_inst_4261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4262_ = l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg(
        v_inst_4258_,
        v_inst_4259_,
        v_inst_4260_,
        v_inst_4261_,
    );
    return v___x_4262_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_keys_4263_: *mut crate::leanh::LeanObject,
    mut v_vals_4264_: *mut crate::leanh::LeanObject,
    mut v_i_4265_: *mut crate::leanh::LeanObject,
    mut v_k_4266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: u8 = 0;
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: u8 = 0;
    let mut v___x_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4267_ = lean_array_get_size(v_keys_4263_);
                v___x_4268_ = lean_nat_dec_lt(v_i_4265_, v___x_4267_);
                if v___x_4268_ == 0 {
                    crate::leanh::lean_dec(v_i_4265_);
                    v___x_4269_ = crate::leanh::lean_box(0);
                    return v___x_4269_;
                } else {
                    v_k_x27_4270_ = lean_array_fget_borrowed(v_keys_4263_, v_i_4265_);
                    v___x_4271_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_4266_,
                            v_k_x27_4270_,
                        );
                    if v___x_4271_ == 0 {
                        v___x_4272_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4273_ = lean_nat_add(v_i_4265_, v___x_4272_);
                        crate::leanh::lean_dec(v_i_4265_);
                        v_i_4265_ = v___x_4273_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4275_ = lean_array_fget_borrowed(v_vals_4264_, v_i_4265_);
                        crate::leanh::lean_dec(v_i_4265_);
                        crate::leanh::lean_inc(v___x_4275_);
                        v___x_4276_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4276_, 0, v___x_4275_);
                        return v___x_4276_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_4277_: *mut crate::leanh::LeanObject,
    mut v_vals_4278_: *mut crate::leanh::LeanObject,
    mut v_i_4279_: *mut crate::leanh::LeanObject,
    mut v_k_4280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4281_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4277_, v_vals_4278_, v_i_4279_, v_k_4280_);
    crate::leanh::lean_dec_ref(v_k_4280_);
    crate::leanh::lean_dec_ref(v_vals_4278_);
    crate::leanh::lean_dec_ref(v_keys_4277_);
    return v_res_4281_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_4282_: usize = 0;
    let mut v___x_4283_: usize = 0;
    let mut v___x_4284_: usize = 0;
    v___x_4282_ = 5usize;
    v___x_4283_ = 1usize;
    v___x_4284_ = lean_usize_shift_left(v___x_4283_, v___x_4282_);
    return v___x_4284_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_4285_: usize = 0;
    let mut v___x_4286_: usize = 0;
    let mut v___x_4287_: usize = 0;
    v___x_4285_ = 1usize;
    v___x_4286_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__0);
    v___x_4287_ = lean_usize_sub(v___x_4286_, v___x_4285_);
    return v___x_4287_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(
    mut v_x_4288_: *mut crate::leanh::LeanObject,
    mut v_x_4289_: usize,
    mut v_x_4290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: usize = 0;
    let mut v___x_4294_: usize = 0;
    let mut v___x_4295_: usize = 0;
    let mut v_j_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: u8 = 0;
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: usize = 0;
    let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4288_) == 0 {
                    v_es_4291_ = crate::leanh::lean_ctor_get(v_x_4288_, 0);
                    v___x_4292_ = crate::leanh::lean_box(2);
                    v___x_4293_ = 5usize;
                    v___x_4294_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_4295_ = lean_usize_land(v_x_4289_, v___x_4294_);
                    v_j_4296_ = lean_usize_to_nat(v___x_4295_);
                    v___x_4297_ = lean_array_get_borrowed(v___x_4292_, v_es_4291_, v_j_4296_);
                    crate::leanh::lean_dec(v_j_4296_);
                    match crate::leanh::lean_obj_tag(v___x_4297_) {
                        0 => {
                            v_key_4298_ = crate::leanh::lean_ctor_get(v___x_4297_, 0);
                            v_val_4299_ = crate::leanh::lean_ctor_get(v___x_4297_, 1);
                            v___x_4300_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_4290_, v_key_4298_);
                            if v___x_4300_ == 0 {
                                v___x_4301_ = crate::leanh::lean_box(0);
                                return v___x_4301_;
                            } else {
                                crate::leanh::lean_inc(v_val_4299_);
                                v___x_4302_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4302_, 0, v_val_4299_);
                                return v___x_4302_;
                            }
                        }
                        1 => {
                            v_node_4303_ = crate::leanh::lean_ctor_get(v___x_4297_, 0);
                            v___x_4304_ = lean_usize_shift_right(v_x_4289_, v___x_4293_);
                            v_x_4288_ = v_node_4303_;
                            v_x_4289_ = v___x_4304_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4306_ = crate::leanh::lean_box(0);
                            return v___x_4306_;
                        }
                    }
                } else {
                    v_ks_4307_ = crate::leanh::lean_ctor_get(v_x_4288_, 0);
                    v_vs_4308_ = crate::leanh::lean_ctor_get(v_x_4288_, 1);
                    v___x_4309_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4310_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_4307_, v_vs_4308_, v___x_4309_, v_x_4290_);
                    return v___x_4310_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_4311_: *mut crate::leanh::LeanObject,
    mut v_x_4312_: *mut crate::leanh::LeanObject,
    mut v_x_4313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_867__boxed_4314_: usize = 0;
    let mut v_res_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_867__boxed_4314_ = crate::leanh::lean_unbox_usize(v_x_4312_);
    crate::leanh::lean_dec(v_x_4312_);
    v_res_4315_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_4311_, v_x_867__boxed_4314_, v_x_4313_);
    crate::leanh::lean_dec_ref(v_x_4313_);
    crate::leanh::lean_dec_ref(v_x_4311_);
    return v_res_4315_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(
    mut v_x_4316_: *mut crate::leanh::LeanObject,
    mut v_x_4317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4318_: u64 = 0;
    let mut v___x_4319_: usize = 0;
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4318_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_4317_);
    v___x_4319_ = lean_uint64_to_usize(v___x_4318_);
    v___x_4320_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_4316_, v___x_4319_, v_x_4317_);
    return v___x_4320_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg___boxed(
    mut v_x_4321_: *mut crate::leanh::LeanObject,
    mut v_x_4322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4323_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_x_4321_, v_x_4322_);
    crate::leanh::lean_dec_ref(v_x_4322_);
    crate::leanh::lean_dec_ref(v_x_4321_);
    return v_res_4323_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(
    mut v_e_4324_: *mut crate::leanh::LeanObject,
    mut v_a_4325_: *mut crate::leanh::LeanObject,
    mut v_a_4326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4332_: u8 = 0;
    let mut v_exprToSemiringId_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4338_: u8 = 0;
    let mut v_a_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4342_: u8 = 0;
    let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4346_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4328_ =
                    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_4325_, v_a_4326_);
                if crate::leanh::lean_obj_tag(v___x_4328_) == 0 {
                    v_a_4329_ = crate::leanh::lean_ctor_get(v___x_4328_, 0);
                    v_isSharedCheck_4338_ = (!crate::leanh::lean_is_exclusive(v___x_4328_)) as u8;
                    if v_isSharedCheck_4338_ == 0 {
                        v___x_4331_ = v___x_4328_;
                        v_isShared_4332_ = v_isSharedCheck_4338_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4329_);
                        crate::leanh::lean_dec(v___x_4328_);
                        v___x_4331_ = crate::leanh::lean_box(0);
                        v_isShared_4332_ = v_isSharedCheck_4338_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4339_ = crate::leanh::lean_ctor_get(v___x_4328_, 0);
                    v_isSharedCheck_4346_ = (!crate::leanh::lean_is_exclusive(v___x_4328_)) as u8;
                    if v_isSharedCheck_4346_ == 0 {
                        v___x_4341_ = v___x_4328_;
                        v_isShared_4342_ = v_isSharedCheck_4346_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4339_);
                        crate::leanh::lean_dec(v___x_4328_);
                        v___x_4341_ = crate::leanh::lean_box(0);
                        v_isShared_4342_ = v_isSharedCheck_4346_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_exprToSemiringId_4333_ = crate::leanh::lean_ctor_get(v_a_4329_, 5);
                crate::leanh::lean_inc_ref(v_exprToSemiringId_4333_);
                crate::leanh::lean_dec(v_a_4329_);
                v___x_4334_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_exprToSemiringId_4333_, v_e_4324_);
                crate::leanh::lean_dec_ref(v_exprToSemiringId_4333_);
                if v_isShared_4332_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4331_, 0, v___x_4334_);
                    v___x_4336_ = v___x_4331_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4337_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4337_, 0, v___x_4334_);
                    v___x_4336_ = v_reuseFailAlloc_4337_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4336_;
            }
            3 => {
                if v_isShared_4342_ == 0 {
                    v___x_4344_ = v___x_4341_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4345_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_a_4339_);
                    v___x_4344_ = v_reuseFailAlloc_4345_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4344_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg___boxed(
    mut v_e_4347_: *mut crate::leanh::LeanObject,
    mut v_a_4348_: *mut crate::leanh::LeanObject,
    mut v_a_4349_: *mut crate::leanh::LeanObject,
    mut v_a_4350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4351_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(
        v_e_4347_, v_a_4348_, v_a_4349_,
    );
    crate::leanh::lean_dec_ref(v_a_4349_);
    crate::leanh::lean_dec(v_a_4348_);
    crate::leanh::lean_dec_ref(v_e_4347_);
    return v_res_4351_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f(
    mut v_e_4352_: *mut crate::leanh::LeanObject,
    mut v_a_4353_: *mut crate::leanh::LeanObject,
    mut v_a_4354_: *mut crate::leanh::LeanObject,
    mut v_a_4355_: *mut crate::leanh::LeanObject,
    mut v_a_4356_: *mut crate::leanh::LeanObject,
    mut v_a_4357_: *mut crate::leanh::LeanObject,
    mut v_a_4358_: *mut crate::leanh::LeanObject,
    mut v_a_4359_: *mut crate::leanh::LeanObject,
    mut v_a_4360_: *mut crate::leanh::LeanObject,
    mut v_a_4361_: *mut crate::leanh::LeanObject,
    mut v_a_4362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4364_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(
        v_e_4352_, v_a_4353_, v_a_4361_,
    );
    return v___x_4364_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___boxed(
    mut v_e_4365_: *mut crate::leanh::LeanObject,
    mut v_a_4366_: *mut crate::leanh::LeanObject,
    mut v_a_4367_: *mut crate::leanh::LeanObject,
    mut v_a_4368_: *mut crate::leanh::LeanObject,
    mut v_a_4369_: *mut crate::leanh::LeanObject,
    mut v_a_4370_: *mut crate::leanh::LeanObject,
    mut v_a_4371_: *mut crate::leanh::LeanObject,
    mut v_a_4372_: *mut crate::leanh::LeanObject,
    mut v_a_4373_: *mut crate::leanh::LeanObject,
    mut v_a_4374_: *mut crate::leanh::LeanObject,
    mut v_a_4375_: *mut crate::leanh::LeanObject,
    mut v_a_4376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4377_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f(
        v_e_4365_, v_a_4366_, v_a_4367_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_,
        v_a_4373_, v_a_4374_, v_a_4375_,
    );
    crate::leanh::lean_dec(v_a_4375_);
    crate::leanh::lean_dec_ref(v_a_4374_);
    crate::leanh::lean_dec(v_a_4373_);
    crate::leanh::lean_dec_ref(v_a_4372_);
    crate::leanh::lean_dec(v_a_4371_);
    crate::leanh::lean_dec_ref(v_a_4370_);
    crate::leanh::lean_dec(v_a_4369_);
    crate::leanh::lean_dec_ref(v_a_4368_);
    crate::leanh::lean_dec(v_a_4367_);
    crate::leanh::lean_dec(v_a_4366_);
    crate::leanh::lean_dec_ref(v_e_4365_);
    return v_res_4377_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0(
    mut v_00_u03b2_4378_: *mut crate::leanh::LeanObject,
    mut v_x_4379_: *mut crate::leanh::LeanObject,
    mut v_x_4380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4381_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_x_4379_, v_x_4380_);
    return v___x_4381_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___boxed(
    mut v_00_u03b2_4382_: *mut crate::leanh::LeanObject,
    mut v_x_4383_: *mut crate::leanh::LeanObject,
    mut v_x_4384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4385_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0(v_00_u03b2_4382_, v_x_4383_, v_x_4384_);
    crate::leanh::lean_dec_ref(v_x_4384_);
    crate::leanh::lean_dec_ref(v_x_4383_);
    return v_res_4385_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0(
    mut v_00_u03b2_4386_: *mut crate::leanh::LeanObject,
    mut v_x_4387_: *mut crate::leanh::LeanObject,
    mut v_x_4388_: usize,
    mut v_x_4389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4390_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_4387_, v_x_4388_, v_x_4389_);
    return v___x_4390_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_4391_: *mut crate::leanh::LeanObject,
    mut v_x_4392_: *mut crate::leanh::LeanObject,
    mut v_x_4393_: *mut crate::leanh::LeanObject,
    mut v_x_4394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_984__boxed_4395_: usize = 0;
    let mut v_res_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_984__boxed_4395_ = crate::leanh::lean_unbox_usize(v_x_4393_);
    crate::leanh::lean_dec(v_x_4393_);
    v_res_4396_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0(v_00_u03b2_4391_, v_x_4392_, v_x_984__boxed_4395_, v_x_4394_);
    crate::leanh::lean_dec_ref(v_x_4394_);
    crate::leanh::lean_dec_ref(v_x_4392_);
    return v_res_4396_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4397_: *mut crate::leanh::LeanObject,
    mut v_keys_4398_: *mut crate::leanh::LeanObject,
    mut v_vals_4399_: *mut crate::leanh::LeanObject,
    mut v_heq_4400_: *mut crate::leanh::LeanObject,
    mut v_i_4401_: *mut crate::leanh::LeanObject,
    mut v_k_4402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4403_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4398_, v_vals_4399_, v_i_4401_, v_k_4402_);
    return v___x_4403_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4404_: *mut crate::leanh::LeanObject,
    mut v_keys_4405_: *mut crate::leanh::LeanObject,
    mut v_vals_4406_: *mut crate::leanh::LeanObject,
    mut v_heq_4407_: *mut crate::leanh::LeanObject,
    mut v_i_4408_: *mut crate::leanh::LeanObject,
    mut v_k_4409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4410_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_4404_, v_keys_4405_, v_vals_4406_, v_heq_4407_, v_i_4408_, v_k_4409_);
    crate::leanh::lean_dec_ref(v_k_4409_);
    crate::leanh::lean_dec_ref(v_vals_4406_);
    crate::leanh::lean_dec_ref(v_keys_4405_);
    return v_res_4410_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_x_4411_: *mut crate::leanh::LeanObject,
    mut v_x_4412_: *mut crate::leanh::LeanObject,
    mut v_x_4413_: *mut crate::leanh::LeanObject,
    mut v_x_4414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4419_: u8 = 0;
    let mut v___x_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: u8 = 0;
    let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: u8 = 0;
    let mut v___x_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4440_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4415_ = crate::leanh::lean_ctor_get(v_x_4411_, 0);
                v_vs_4416_ = crate::leanh::lean_ctor_get(v_x_4411_, 1);
                v_isSharedCheck_4440_ = (!crate::leanh::lean_is_exclusive(v_x_4411_)) as u8;
                if v_isSharedCheck_4440_ == 0 {
                    v___x_4418_ = v_x_4411_;
                    v_isShared_4419_ = v_isSharedCheck_4440_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_4416_);
                    crate::leanh::lean_inc(v_ks_4415_);
                    crate::leanh::lean_dec(v_x_4411_);
                    v___x_4418_ = crate::leanh::lean_box(0);
                    v_isShared_4419_ = v_isSharedCheck_4440_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4420_ = lean_array_get_size(v_ks_4415_);
                v___x_4421_ = lean_nat_dec_lt(v_x_4412_, v___x_4420_);
                if v___x_4421_ == 0 {
                    crate::leanh::lean_dec(v_x_4412_);
                    v___x_4422_ = lean_array_push(v_ks_4415_, v_x_4413_);
                    v___x_4423_ = lean_array_push(v_vs_4416_, v_x_4414_);
                    if v_isShared_4419_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4418_, 1, v___x_4423_);
                        crate::leanh::lean_ctor_set(v___x_4418_, 0, v___x_4422_);
                        v___x_4425_ = v___x_4418_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4426_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4426_, 0, v___x_4422_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4426_, 1, v___x_4423_);
                        v___x_4425_ = v_reuseFailAlloc_4426_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_4427_ = lean_array_fget_borrowed(v_ks_4415_, v_x_4412_);
                    v___x_4428_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_x_4413_,
                            v_k_x27_4427_,
                        );
                    if v___x_4428_ == 0 {
                        if v_isShared_4419_ == 0 {
                            v___x_4430_ = v___x_4418_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4434_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4434_, 0, v_ks_4415_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4434_, 1, v_vs_4416_);
                            v___x_4430_ = v_reuseFailAlloc_4434_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4435_ = lean_array_fset(v_ks_4415_, v_x_4412_, v_x_4413_);
                        v___x_4436_ = lean_array_fset(v_vs_4416_, v_x_4412_, v_x_4414_);
                        crate::leanh::lean_dec(v_x_4412_);
                        if v_isShared_4419_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4418_, 1, v___x_4436_);
                            crate::leanh::lean_ctor_set(v___x_4418_, 0, v___x_4435_);
                            v___x_4438_ = v___x_4418_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4439_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4439_, 0, v___x_4435_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4439_, 1, v___x_4436_);
                            v___x_4438_ = v_reuseFailAlloc_4439_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4425_;
            }
            3 => {
                v___x_4431_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4432_ = lean_nat_add(v_x_4412_, v___x_4431_);
                crate::leanh::lean_dec(v_x_4412_);
                v_x_4411_ = v___x_4430_;
                v_x_4412_ = v___x_4432_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_4438_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(
    mut v_n_4441_: *mut crate::leanh::LeanObject,
    mut v_k_4442_: *mut crate::leanh::LeanObject,
    mut v_v_4443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4444_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4445_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_4441_, v___x_4444_, v_k_4442_, v_v_4443_);
    return v___x_4445_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4446_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4446_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(
    mut v_x_4447_: *mut crate::leanh::LeanObject,
    mut v_x_4448_: usize,
    mut v_x_4449_: usize,
    mut v_x_4450_: *mut crate::leanh::LeanObject,
    mut v_x_4451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: usize = 0;
    let mut v___x_4454_: usize = 0;
    let mut v___x_4455_: usize = 0;
    let mut v___x_4456_: usize = 0;
    let mut v_j_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: u8 = 0;
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4462_: u8 = 0;
    let mut v_v_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4476_: u8 = 0;
    let mut v___x_4477_: u8 = 0;
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4483_: u8 = 0;
    let mut v_node_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4487_: u8 = 0;
    let mut v___x_4488_: usize = 0;
    let mut v___x_4489_: usize = 0;
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4494_: u8 = 0;
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4496_: u8 = 0;
    let mut v_unused_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4502_: u8 = 0;
    let mut v___x_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4507_: u8 = 0;
    let mut v_ks_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: usize = 0;
    let mut v___x_4514_: u8 = 0;
    let mut v___x_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: u8 = 0;
    let mut v_reuseFailAlloc_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4519_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4447_) == 0 {
                    v_es_4452_ = crate::leanh::lean_ctor_get(v_x_4447_, 0);
                    v___x_4453_ = 5usize;
                    v___x_4454_ = 1usize;
                    v___x_4455_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_4456_ = lean_usize_land(v_x_4448_, v___x_4455_);
                    v_j_4457_ = lean_usize_to_nat(v___x_4456_);
                    v___x_4458_ = lean_array_get_size(v_es_4452_);
                    v___x_4459_ = lean_nat_dec_lt(v_j_4457_, v___x_4458_);
                    if v___x_4459_ == 0 {
                        crate::leanh::lean_dec(v_j_4457_);
                        crate::leanh::lean_dec(v_x_4451_);
                        crate::leanh::lean_dec_ref(v_x_4450_);
                        return v_x_4447_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_4452_);
                        v_isSharedCheck_4496_ = (!crate::leanh::lean_is_exclusive(v_x_4447_)) as u8;
                        if v_isSharedCheck_4496_ == 0 {
                            v_unused_4497_ = crate::leanh::lean_ctor_get(v_x_4447_, 0);
                            crate::leanh::lean_dec(v_unused_4497_);
                            v___x_4461_ = v_x_4447_;
                            v_isShared_4462_ = v_isSharedCheck_4496_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_4447_);
                            v___x_4461_ = crate::leanh::lean_box(0);
                            v_isShared_4462_ = v_isSharedCheck_4496_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4498_ = crate::leanh::lean_ctor_get(v_x_4447_, 0);
                    v_vs_4499_ = crate::leanh::lean_ctor_get(v_x_4447_, 1);
                    v_isSharedCheck_4519_ = (!crate::leanh::lean_is_exclusive(v_x_4447_)) as u8;
                    if v_isSharedCheck_4519_ == 0 {
                        v___x_4501_ = v_x_4447_;
                        v_isShared_4502_ = v_isSharedCheck_4519_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_4499_);
                        crate::leanh::lean_inc(v_ks_4498_);
                        crate::leanh::lean_dec(v_x_4447_);
                        v___x_4501_ = crate::leanh::lean_box(0);
                        v_isShared_4502_ = v_isSharedCheck_4519_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4463_ = lean_array_fget(v_es_4452_, v_j_4457_);
                v___x_4464_ = crate::leanh::lean_box(0);
                v_xs_x27_4465_ = lean_array_fset(v_es_4452_, v_j_4457_, v___x_4464_);
                match crate::leanh::lean_obj_tag(v_v_4463_) {
                    0 => {
                        v_key_4472_ = crate::leanh::lean_ctor_get(v_v_4463_, 0);
                        v_val_4473_ = crate::leanh::lean_ctor_get(v_v_4463_, 1);
                        v_isSharedCheck_4483_ = (!crate::leanh::lean_is_exclusive(v_v_4463_)) as u8;
                        if v_isSharedCheck_4483_ == 0 {
                            v___x_4475_ = v_v_4463_;
                            v_isShared_4476_ = v_isSharedCheck_4483_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4473_);
                            crate::leanh::lean_inc(v_key_4472_);
                            crate::leanh::lean_dec(v_v_4463_);
                            v___x_4475_ = crate::leanh::lean_box(0);
                            v_isShared_4476_ = v_isSharedCheck_4483_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4484_ = crate::leanh::lean_ctor_get(v_v_4463_, 0);
                        v_isSharedCheck_4494_ = (!crate::leanh::lean_is_exclusive(v_v_4463_)) as u8;
                        if v_isSharedCheck_4494_ == 0 {
                            v___x_4486_ = v_v_4463_;
                            v_isShared_4487_ = v_isSharedCheck_4494_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_4484_);
                            crate::leanh::lean_dec(v_v_4463_);
                            v___x_4486_ = crate::leanh::lean_box(0);
                            v_isShared_4487_ = v_isSharedCheck_4494_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4495_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4495_, 0, v_x_4450_);
                        crate::leanh::lean_ctor_set(v___x_4495_, 1, v_x_4451_);
                        v___y_4467_ = v___x_4495_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4468_ = lean_array_fset(v_xs_x27_4465_, v_j_4457_, v___y_4467_);
                crate::leanh::lean_dec(v_j_4457_);
                if v_isShared_4462_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4461_, 0, v___x_4468_);
                    v___x_4470_ = v___x_4461_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4471_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4471_, 0, v___x_4468_);
                    v___x_4470_ = v_reuseFailAlloc_4471_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4470_;
            }
            4 => {
                v___x_4477_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_x_4450_,
                        v_key_4472_,
                    );
                if v___x_4477_ == 0 {
                    crate::leanh::lean_del_object(v___x_4475_);
                    v___x_4478_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4472_,
                        v_val_4473_,
                        v_x_4450_,
                        v_x_4451_,
                    );
                    v___x_4479_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4479_, 0, v___x_4478_);
                    v___y_4467_ = v___x_4479_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_4473_);
                    crate::leanh::lean_dec(v_key_4472_);
                    if v_isShared_4476_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4475_, 1, v_x_4451_);
                        crate::leanh::lean_ctor_set(v___x_4475_, 0, v_x_4450_);
                        v___x_4481_ = v___x_4475_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4482_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_x_4450_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4482_, 1, v_x_4451_);
                        v___x_4481_ = v_reuseFailAlloc_4482_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_4467_ = v___x_4481_;
                state = 2;
                continue;
            }
            6 => {
                v___x_4488_ = lean_usize_shift_right(v_x_4448_, v___x_4453_);
                v___x_4489_ = lean_usize_add(v_x_4449_, v___x_4454_);
                v___x_4490_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_node_4484_, v___x_4488_, v___x_4489_, v_x_4450_, v_x_4451_);
                if v_isShared_4487_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4486_, 0, v___x_4490_);
                    v___x_4492_ = v___x_4486_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4493_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4493_, 0, v___x_4490_);
                    v___x_4492_ = v_reuseFailAlloc_4493_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_4467_ = v___x_4492_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_4502_ == 0 {
                    v___x_4504_ = v___x_4501_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4518_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4518_, 0, v_ks_4498_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4518_, 1, v_vs_4499_);
                    v___x_4504_ = v_reuseFailAlloc_4518_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_4505_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(v___x_4504_, v_x_4450_, v_x_4451_);
                v___x_4513_ = 7usize;
                v___x_4514_ = lean_usize_dec_le(v___x_4513_, v_x_4449_);
                if v___x_4514_ == 0 {
                    v___x_4515_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4505_);
                    v___x_4516_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_4517_ = lean_nat_dec_lt(v___x_4515_, v___x_4516_);
                    crate::leanh::lean_dec(v___x_4515_);
                    v___y_4507_ = v___x_4517_;
                    state = 10;
                    continue;
                } else {
                    v___y_4507_ = v___x_4514_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_4507_ == 0 {
                    v_ks_4508_ = crate::leanh::lean_ctor_get(v_newNode_4505_, 0);
                    crate::leanh::lean_inc_ref(v_ks_4508_);
                    v_vs_4509_ = crate::leanh::lean_ctor_get(v_newNode_4505_, 1);
                    crate::leanh::lean_inc_ref(v_vs_4509_);
                    crate::leanh::lean_dec_ref(v_newNode_4505_);
                    v___x_4510_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4511_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0);
                    v___x_4512_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_x_4449_, v_ks_4508_, v_vs_4509_, v___x_4510_, v___x_4511_);
                    crate::leanh::lean_dec_ref(v_vs_4509_);
                    crate::leanh::lean_dec_ref(v_ks_4508_);
                    return v___x_4512_;
                } else {
                    return v_newNode_4505_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(
    mut v_depth_4520_: usize,
    mut v_keys_4521_: *mut crate::leanh::LeanObject,
    mut v_vals_4522_: *mut crate::leanh::LeanObject,
    mut v_i_4523_: *mut crate::leanh::LeanObject,
    mut v_entries_4524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: u8 = 0;
    let mut v_k_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: u64 = 0;
    let mut v_h_4530_: usize = 0;
    let mut v___x_4531_: usize = 0;
    let mut v___x_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: usize = 0;
    let mut v___x_4534_: usize = 0;
    let mut v___x_4535_: usize = 0;
    let mut v_h_4536_: usize = 0;
    let mut v___x_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4525_ = lean_array_get_size(v_keys_4521_);
                v___x_4526_ = lean_nat_dec_lt(v_i_4523_, v___x_4525_);
                if v___x_4526_ == 0 {
                    crate::leanh::lean_dec(v_i_4523_);
                    return v_entries_4524_;
                } else {
                    v_k_4527_ = lean_array_fget_borrowed(v_keys_4521_, v_i_4523_);
                    v_v_4528_ = lean_array_fget_borrowed(v_vals_4522_, v_i_4523_);
                    v___x_4529_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_4527_);
                    v_h_4530_ = lean_uint64_to_usize(v___x_4529_);
                    v___x_4531_ = 5usize;
                    v___x_4532_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4533_ = 1usize;
                    v___x_4534_ = lean_usize_sub(v_depth_4520_, v___x_4533_);
                    v___x_4535_ = lean_usize_mul(v___x_4531_, v___x_4534_);
                    v_h_4536_ = lean_usize_shift_right(v_h_4530_, v___x_4535_);
                    v___x_4537_ = lean_nat_add(v_i_4523_, v___x_4532_);
                    crate::leanh::lean_dec(v_i_4523_);
                    crate::leanh::lean_inc(v_v_4528_);
                    crate::leanh::lean_inc(v_k_4527_);
                    v___x_4538_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_entries_4524_, v_h_4536_, v_depth_4520_, v_k_4527_, v_v_4528_);
                    v_i_4523_ = v___x_4537_;
                    v_entries_4524_ = v___x_4538_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_depth_4540_: *mut crate::leanh::LeanObject,
    mut v_keys_4541_: *mut crate::leanh::LeanObject,
    mut v_vals_4542_: *mut crate::leanh::LeanObject,
    mut v_i_4543_: *mut crate::leanh::LeanObject,
    mut v_entries_4544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_4545_: usize = 0;
    let mut v_res_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4545_ = crate::leanh::lean_unbox_usize(v_depth_4540_);
    crate::leanh::lean_dec(v_depth_4540_);
    v_res_4546_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_4545_, v_keys_4541_, v_vals_4542_, v_i_4543_, v_entries_4544_);
    crate::leanh::lean_dec_ref(v_vals_4542_);
    crate::leanh::lean_dec_ref(v_keys_4541_);
    return v_res_4546_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___boxed(
    mut v_x_4547_: *mut crate::leanh::LeanObject,
    mut v_x_4548_: *mut crate::leanh::LeanObject,
    mut v_x_4549_: *mut crate::leanh::LeanObject,
    mut v_x_4550_: *mut crate::leanh::LeanObject,
    mut v_x_4551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_7240__boxed_4552_: usize = 0;
    let mut v_x_7241__boxed_4553_: usize = 0;
    let mut v_res_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_7240__boxed_4552_ = crate::leanh::lean_unbox_usize(v_x_4548_);
    crate::leanh::lean_dec(v_x_4548_);
    v_x_7241__boxed_4553_ = crate::leanh::lean_unbox_usize(v_x_4549_);
    crate::leanh::lean_dec(v_x_4549_);
    v_res_4554_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_4547_, v_x_7240__boxed_4552_, v_x_7241__boxed_4553_, v_x_4550_, v_x_4551_);
    return v_res_4554_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(
    mut v_x_4555_: *mut crate::leanh::LeanObject,
    mut v_x_4556_: *mut crate::leanh::LeanObject,
    mut v_x_4557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4558_: u64 = 0;
    let mut v___x_4559_: usize = 0;
    let mut v___x_4560_: usize = 0;
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4558_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_4556_);
    v___x_4559_ = lean_uint64_to_usize(v___x_4558_);
    v___x_4560_ = 1usize;
    v___x_4561_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_4555_, v___x_4559_, v___x_4560_, v_x_4556_, v_x_4557_);
    return v___x_4561_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0(
    mut v_e_4562_: *mut crate::leanh::LeanObject,
    mut v_a_4563_: *mut crate::leanh::LeanObject,
    mut v_s_4564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_rings_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_4578_: u8 = 0;
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4581_: u8 = 0;
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4586_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_4565_ = crate::leanh::lean_ctor_get(v_s_4564_, 0);
                v_typeIdOf_4566_ = crate::leanh::lean_ctor_get(v_s_4564_, 1);
                v_exprToRingId_4567_ = crate::leanh::lean_ctor_get(v_s_4564_, 2);
                v_semirings_4568_ = crate::leanh::lean_ctor_get(v_s_4564_, 3);
                v_stypeIdOf_4569_ = crate::leanh::lean_ctor_get(v_s_4564_, 4);
                v_exprToSemiringId_4570_ = crate::leanh::lean_ctor_get(v_s_4564_, 5);
                v_ncRings_4571_ = crate::leanh::lean_ctor_get(v_s_4564_, 6);
                v_exprToNCRingId_4572_ = crate::leanh::lean_ctor_get(v_s_4564_, 7);
                v_nctypeIdOf_4573_ = crate::leanh::lean_ctor_get(v_s_4564_, 8);
                v_ncSemirings_4574_ = crate::leanh::lean_ctor_get(v_s_4564_, 9);
                v_exprToNCSemiringId_4575_ = crate::leanh::lean_ctor_get(v_s_4564_, 10);
                v_ncstypeIdOf_4576_ = crate::leanh::lean_ctor_get(v_s_4564_, 11);
                v_steps_4577_ = crate::leanh::lean_ctor_get(v_s_4564_, 12);
                v_reportedMaxDegreeIssue_4578_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_4564_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                v_isSharedCheck_4586_ = (!crate::leanh::lean_is_exclusive(v_s_4564_)) as u8;
                if v_isSharedCheck_4586_ == 0 {
                    v___x_4580_ = v_s_4564_;
                    v_isShared_4581_ = v_isSharedCheck_4586_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_steps_4577_);
                    crate::leanh::lean_inc(v_ncstypeIdOf_4576_);
                    crate::leanh::lean_inc(v_exprToNCSemiringId_4575_);
                    crate::leanh::lean_inc(v_ncSemirings_4574_);
                    crate::leanh::lean_inc(v_nctypeIdOf_4573_);
                    crate::leanh::lean_inc(v_exprToNCRingId_4572_);
                    crate::leanh::lean_inc(v_ncRings_4571_);
                    crate::leanh::lean_inc(v_exprToSemiringId_4570_);
                    crate::leanh::lean_inc(v_stypeIdOf_4569_);
                    crate::leanh::lean_inc(v_semirings_4568_);
                    crate::leanh::lean_inc(v_exprToRingId_4567_);
                    crate::leanh::lean_inc(v_typeIdOf_4566_);
                    crate::leanh::lean_inc(v_rings_4565_);
                    crate::leanh::lean_dec(v_s_4564_);
                    v___x_4580_ = crate::leanh::lean_box(0);
                    v_isShared_4581_ = v_isSharedCheck_4586_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_4563_);
                v___x_4582_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_exprToSemiringId_4570_, v_e_4562_, v_a_4563_);
                if v_isShared_4581_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4580_, 5, v___x_4582_);
                    v___x_4584_ = v___x_4580_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4585_ = crate::leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 0, v_rings_4565_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 1, v_typeIdOf_4566_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 2, v_exprToRingId_4567_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 3, v_semirings_4568_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 4, v_stypeIdOf_4569_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 5, v___x_4582_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 6, v_ncRings_4571_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 7, v_exprToNCRingId_4572_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 8, v_nctypeIdOf_4573_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 9, v_ncSemirings_4574_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4585_,
                        10,
                        v_exprToNCSemiringId_4575_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 11, v_ncstypeIdOf_4576_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 12, v_steps_4577_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4585_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                        v_reportedMaxDegreeIssue_4578_,
                    );
                    v___x_4584_ = v_reuseFailAlloc_4585_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4584_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0___boxed(
    mut v_e_4587_: *mut crate::leanh::LeanObject,
    mut v_a_4588_: *mut crate::leanh::LeanObject,
    mut v_s_4589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4590_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0(
        v_e_4587_, v_a_4588_, v_s_4589_,
    );
    crate::leanh::lean_dec(v_a_4588_);
    return v_res_4590_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4592_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__0;
    v___x_4593_ = l_Lean_stringToMessageData(v___x_4592_);
    return v___x_4593_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(
    mut v_e_4594_: *mut crate::leanh::LeanObject,
    mut v_a_4595_: *mut crate::leanh::LeanObject,
    mut v_a_4596_: *mut crate::leanh::LeanObject,
    mut v_a_4597_: *mut crate::leanh::LeanObject,
    mut v_a_4598_: *mut crate::leanh::LeanObject,
    mut v_a_4599_: *mut crate::leanh::LeanObject,
    mut v_a_4600_: *mut crate::leanh::LeanObject,
    mut v_a_4601_: *mut crate::leanh::LeanObject,
    mut v_a_4602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: u8 = 0;
    let mut v___x_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: u8 = 0;
    let mut v___x_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4621_: u8 = 0;
    let mut v___x_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4625_: u8 = 0;
    let mut v___f_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4632_: u8 = 0;
    let mut v___x_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4636_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4607_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(
                    v_e_4594_, v_a_4596_, v_a_4601_,
                );
                if crate::leanh::lean_obj_tag(v___x_4607_) == 0 {
                    v_a_4608_ = crate::leanh::lean_ctor_get(v___x_4607_, 0);
                    crate::leanh::lean_inc(v_a_4608_);
                    crate::leanh::lean_dec_ref_known(v___x_4607_, 1);
                    if crate::leanh::lean_obj_tag(v_a_4608_) == 1 {
                        v_val_4609_ = crate::leanh::lean_ctor_get(v_a_4608_, 0);
                        crate::leanh::lean_inc(v_val_4609_);
                        crate::leanh::lean_dec_ref_known(v_a_4608_, 1);
                        v___x_4610_ = lean_nat_dec_eq(v_val_4609_, v_a_4595_);
                        crate::leanh::lean_dec(v_val_4609_);
                        if v___x_4610_ == 0 {
                            v___x_4611_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_4597_);
                            if crate::leanh::lean_obj_tag(v___x_4611_) == 0 {
                                v_a_4612_ = crate::leanh::lean_ctor_get(v___x_4611_, 0);
                                crate::leanh::lean_inc(v_a_4612_);
                                crate::leanh::lean_dec_ref_known(v___x_4611_, 1);
                                v___x_4613_ = (crate::leanh::lean_unbox(v_a_4612_) as u8);
                                crate::leanh::lean_dec(v_a_4612_);
                                if v___x_4613_ == 0 {
                                    crate::leanh::lean_dec_ref(v_e_4594_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_4614_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1_once), _init_l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1);
                                    v___x_4615_ = l_Lean_indentExpr(v_e_4594_);
                                    v___x_4616_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4616_, 0, v___x_4614_);
                                    crate::leanh::lean_ctor_set(v___x_4616_, 1, v___x_4615_);
                                    v___x_4617_ = l_Lean_Meta_Sym_reportIssue(
                                        v___x_4616_,
                                        v_a_4597_,
                                        v_a_4598_,
                                        v_a_4599_,
                                        v_a_4600_,
                                        v_a_4601_,
                                        v_a_4602_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_4617_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_4617_, 1);
                                        state = 1;
                                        continue;
                                    } else {
                                        return v___x_4617_;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_e_4594_);
                                v_a_4618_ = crate::leanh::lean_ctor_get(v___x_4611_, 0);
                                v_isSharedCheck_4625_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4611_)) as u8;
                                if v_isSharedCheck_4625_ == 0 {
                                    v___x_4620_ = v___x_4611_;
                                    v_isShared_4621_ = v_isSharedCheck_4625_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4618_);
                                    crate::leanh::lean_dec(v___x_4611_);
                                    v___x_4620_ = crate::leanh::lean_box(0);
                                    v_isShared_4621_ = v_isSharedCheck_4625_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_e_4594_);
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4608_);
                        crate::leanh::lean_inc(v_a_4595_);
                        v___f_4626_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                        crate::leanh::lean_closure_set(v___f_4626_, 0, v_e_4594_);
                        crate::leanh::lean_closure_set(v___f_4626_, 1, v_a_4595_);
                        v___x_4627_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                        v___x_4628_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4627_, v___f_4626_, v_a_4596_);
                        return v___x_4628_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_4594_);
                    v_a_4629_ = crate::leanh::lean_ctor_get(v___x_4607_, 0);
                    v_isSharedCheck_4636_ = (!crate::leanh::lean_is_exclusive(v___x_4607_)) as u8;
                    if v_isSharedCheck_4636_ == 0 {
                        v___x_4631_ = v___x_4607_;
                        v_isShared_4632_ = v_isSharedCheck_4636_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4629_);
                        crate::leanh::lean_dec(v___x_4607_);
                        v___x_4631_ = crate::leanh::lean_box(0);
                        v_isShared_4632_ = v_isSharedCheck_4636_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4605_ = crate::leanh::lean_box(0);
                v___x_4606_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4606_, 0, v___x_4605_);
                return v___x_4606_;
            }
            2 => {
                if v_isShared_4621_ == 0 {
                    v___x_4623_ = v___x_4620_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4624_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4624_, 0, v_a_4618_);
                    v___x_4623_ = v_reuseFailAlloc_4624_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4623_;
            }
            4 => {
                if v_isShared_4632_ == 0 {
                    v___x_4634_ = v___x_4631_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4635_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4635_, 0, v_a_4629_);
                    v___x_4634_ = v_reuseFailAlloc_4635_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4634_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___boxed(
    mut v_e_4637_: *mut crate::leanh::LeanObject,
    mut v_a_4638_: *mut crate::leanh::LeanObject,
    mut v_a_4639_: *mut crate::leanh::LeanObject,
    mut v_a_4640_: *mut crate::leanh::LeanObject,
    mut v_a_4641_: *mut crate::leanh::LeanObject,
    mut v_a_4642_: *mut crate::leanh::LeanObject,
    mut v_a_4643_: *mut crate::leanh::LeanObject,
    mut v_a_4644_: *mut crate::leanh::LeanObject,
    mut v_a_4645_: *mut crate::leanh::LeanObject,
    mut v_a_4646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4647_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(
        v_e_4637_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_,
        v_a_4645_,
    );
    crate::leanh::lean_dec(v_a_4645_);
    crate::leanh::lean_dec_ref(v_a_4644_);
    crate::leanh::lean_dec(v_a_4643_);
    crate::leanh::lean_dec_ref(v_a_4642_);
    crate::leanh::lean_dec(v_a_4641_);
    crate::leanh::lean_dec_ref(v_a_4640_);
    crate::leanh::lean_dec(v_a_4639_);
    crate::leanh::lean_dec(v_a_4638_);
    return v_res_4647_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(
    mut v_e_4648_: *mut crate::leanh::LeanObject,
    mut v_a_4649_: *mut crate::leanh::LeanObject,
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
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4661_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(
        v_e_4648_, v_a_4649_, v_a_4650_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_,
        v_a_4659_,
    );
    return v___x_4661_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___boxed(
    mut v_e_4662_: *mut crate::leanh::LeanObject,
    mut v_a_4663_: *mut crate::leanh::LeanObject,
    mut v_a_4664_: *mut crate::leanh::LeanObject,
    mut v_a_4665_: *mut crate::leanh::LeanObject,
    mut v_a_4666_: *mut crate::leanh::LeanObject,
    mut v_a_4667_: *mut crate::leanh::LeanObject,
    mut v_a_4668_: *mut crate::leanh::LeanObject,
    mut v_a_4669_: *mut crate::leanh::LeanObject,
    mut v_a_4670_: *mut crate::leanh::LeanObject,
    mut v_a_4671_: *mut crate::leanh::LeanObject,
    mut v_a_4672_: *mut crate::leanh::LeanObject,
    mut v_a_4673_: *mut crate::leanh::LeanObject,
    mut v_a_4674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4675_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(
        v_e_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_, v_a_4668_, v_a_4669_,
        v_a_4670_, v_a_4671_, v_a_4672_, v_a_4673_,
    );
    crate::leanh::lean_dec(v_a_4673_);
    crate::leanh::lean_dec_ref(v_a_4672_);
    crate::leanh::lean_dec(v_a_4671_);
    crate::leanh::lean_dec_ref(v_a_4670_);
    crate::leanh::lean_dec(v_a_4669_);
    crate::leanh::lean_dec_ref(v_a_4668_);
    crate::leanh::lean_dec(v_a_4667_);
    crate::leanh::lean_dec_ref(v_a_4666_);
    crate::leanh::lean_dec(v_a_4665_);
    crate::leanh::lean_dec(v_a_4664_);
    crate::leanh::lean_dec(v_a_4663_);
    return v_res_4675_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0(
    mut v_00_u03b2_4676_: *mut crate::leanh::LeanObject,
    mut v_x_4677_: *mut crate::leanh::LeanObject,
    mut v_x_4678_: *mut crate::leanh::LeanObject,
    mut v_x_4679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4680_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_x_4677_, v_x_4678_, v_x_4679_);
    return v___x_4680_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(
    mut v_00_u03b2_4681_: *mut crate::leanh::LeanObject,
    mut v_x_4682_: *mut crate::leanh::LeanObject,
    mut v_x_4683_: usize,
    mut v_x_4684_: usize,
    mut v_x_4685_: *mut crate::leanh::LeanObject,
    mut v_x_4686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4687_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_4682_, v_x_4683_, v_x_4684_, v_x_4685_, v_x_4686_);
    return v___x_4687_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___boxed(
    mut v_00_u03b2_4688_: *mut crate::leanh::LeanObject,
    mut v_x_4689_: *mut crate::leanh::LeanObject,
    mut v_x_4690_: *mut crate::leanh::LeanObject,
    mut v_x_4691_: *mut crate::leanh::LeanObject,
    mut v_x_4692_: *mut crate::leanh::LeanObject,
    mut v_x_4693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_7519__boxed_4694_: usize = 0;
    let mut v_x_7520__boxed_4695_: usize = 0;
    let mut v_res_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_7519__boxed_4694_ = crate::leanh::lean_unbox_usize(v_x_4690_);
    crate::leanh::lean_dec(v_x_4690_);
    v_x_7520__boxed_4695_ = crate::leanh::lean_unbox_usize(v_x_4691_);
    crate::leanh::lean_dec(v_x_4691_);
    v_res_4696_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(v_00_u03b2_4688_, v_x_4689_, v_x_7519__boxed_4694_, v_x_7520__boxed_4695_, v_x_4692_, v_x_4693_);
    return v_res_4696_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4697_: *mut crate::leanh::LeanObject,
    mut v_n_4698_: *mut crate::leanh::LeanObject,
    mut v_k_4699_: *mut crate::leanh::LeanObject,
    mut v_v_4700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4701_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(v_n_4698_, v_k_4699_, v_v_4700_);
    return v___x_4701_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(
    mut v_00_u03b2_4702_: *mut crate::leanh::LeanObject,
    mut v_depth_4703_: usize,
    mut v_keys_4704_: *mut crate::leanh::LeanObject,
    mut v_vals_4705_: *mut crate::leanh::LeanObject,
    mut v_heq_4706_: *mut crate::leanh::LeanObject,
    mut v_i_4707_: *mut crate::leanh::LeanObject,
    mut v_entries_4708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4709_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_4703_, v_keys_4704_, v_vals_4705_, v_i_4707_, v_entries_4708_);
    return v___x_4709_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_4710_: *mut crate::leanh::LeanObject,
    mut v_depth_4711_: *mut crate::leanh::LeanObject,
    mut v_keys_4712_: *mut crate::leanh::LeanObject,
    mut v_vals_4713_: *mut crate::leanh::LeanObject,
    mut v_heq_4714_: *mut crate::leanh::LeanObject,
    mut v_i_4715_: *mut crate::leanh::LeanObject,
    mut v_entries_4716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_4717_: usize = 0;
    let mut v_res_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4717_ = crate::leanh::lean_unbox_usize(v_depth_4711_);
    crate::leanh::lean_dec(v_depth_4711_);
    v_res_4718_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(v_00_u03b2_4710_, v_depth_boxed_4717_, v_keys_4712_, v_vals_4713_, v_heq_4714_, v_i_4715_, v_entries_4716_);
    crate::leanh::lean_dec_ref(v_vals_4713_);
    crate::leanh::lean_dec_ref(v_keys_4712_);
    return v_res_4718_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_4719_: *mut crate::leanh::LeanObject,
    mut v_x_4720_: *mut crate::leanh::LeanObject,
    mut v_x_4721_: *mut crate::leanh::LeanObject,
    mut v_x_4722_: *mut crate::leanh::LeanObject,
    mut v_x_4723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4724_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_4720_, v_x_4721_, v_x_4722_, v_x_4723_);
    return v___x_4724_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0(
    mut v_e_4725_: *mut crate::leanh::LeanObject,
    mut v___y_4726_: *mut crate::leanh::LeanObject,
    mut v___y_4727_: *mut crate::leanh::LeanObject,
    mut v___y_4728_: *mut crate::leanh::LeanObject,
    mut v___y_4729_: *mut crate::leanh::LeanObject,
    mut v___y_4730_: *mut crate::leanh::LeanObject,
    mut v___y_4731_: *mut crate::leanh::LeanObject,
    mut v___y_4732_: *mut crate::leanh::LeanObject,
    mut v___y_4733_: *mut crate::leanh::LeanObject,
    mut v___y_4734_: *mut crate::leanh::LeanObject,
    mut v___y_4735_: *mut crate::leanh::LeanObject,
    mut v___y_4736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4738_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(
        v_e_4725_,
        v___y_4726_,
        v___y_4727_,
        v___y_4731_,
        v___y_4732_,
        v___y_4733_,
        v___y_4734_,
        v___y_4735_,
        v___y_4736_,
    );
    return v___x_4738_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0___boxed(
    mut v_e_4739_: *mut crate::leanh::LeanObject,
    mut v___y_4740_: *mut crate::leanh::LeanObject,
    mut v___y_4741_: *mut crate::leanh::LeanObject,
    mut v___y_4742_: *mut crate::leanh::LeanObject,
    mut v___y_4743_: *mut crate::leanh::LeanObject,
    mut v___y_4744_: *mut crate::leanh::LeanObject,
    mut v___y_4745_: *mut crate::leanh::LeanObject,
    mut v___y_4746_: *mut crate::leanh::LeanObject,
    mut v___y_4747_: *mut crate::leanh::LeanObject,
    mut v___y_4748_: *mut crate::leanh::LeanObject,
    mut v___y_4749_: *mut crate::leanh::LeanObject,
    mut v___y_4750_: *mut crate::leanh::LeanObject,
    mut v___y_4751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4752_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0(
        v_e_4739_,
        v___y_4740_,
        v___y_4741_,
        v___y_4742_,
        v___y_4743_,
        v___y_4744_,
        v___y_4745_,
        v___y_4746_,
        v___y_4747_,
        v___y_4748_,
        v___y_4749_,
        v___y_4750_,
    );
    crate::leanh::lean_dec(v___y_4750_);
    crate::leanh::lean_dec_ref(v___y_4749_);
    crate::leanh::lean_dec(v___y_4748_);
    crate::leanh::lean_dec_ref(v___y_4747_);
    crate::leanh::lean_dec(v___y_4746_);
    crate::leanh::lean_dec_ref(v___y_4745_);
    crate::leanh::lean_dec(v___y_4744_);
    crate::leanh::lean_dec_ref(v___y_4743_);
    crate::leanh::lean_dec(v___y_4742_);
    crate::leanh::lean_dec(v___y_4741_);
    crate::leanh::lean_dec(v___y_4740_);
    return v_res_4752_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__0(
    mut v_e_4755_: *mut crate::leanh::LeanObject,
    mut v___f_4756_: *mut crate::leanh::LeanObject,
    mut v___f_4757_: *mut crate::leanh::LeanObject,
    mut v_size_4758_: *mut crate::leanh::LeanObject,
    mut v_s_4759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4773_: u8 = 0;
    let mut v___x_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_4760_ = crate::leanh::lean_ctor_get(v_s_4759_, 0);
                v_type_4761_ = crate::leanh::lean_ctor_get(v_s_4759_, 1);
                v_u_4762_ = crate::leanh::lean_ctor_get(v_s_4759_, 2);
                v_semiringInst_4763_ = crate::leanh::lean_ctor_get(v_s_4759_, 3);
                v_addFn_x3f_4764_ = crate::leanh::lean_ctor_get(v_s_4759_, 4);
                v_mulFn_x3f_4765_ = crate::leanh::lean_ctor_get(v_s_4759_, 5);
                v_powFn_x3f_4766_ = crate::leanh::lean_ctor_get(v_s_4759_, 6);
                v_natCastFn_x3f_4767_ = crate::leanh::lean_ctor_get(v_s_4759_, 7);
                v_denote_4768_ = crate::leanh::lean_ctor_get(v_s_4759_, 8);
                v_vars_4769_ = crate::leanh::lean_ctor_get(v_s_4759_, 9);
                v_varMap_4770_ = crate::leanh::lean_ctor_get(v_s_4759_, 10);
                v_isSharedCheck_4779_ = (!crate::leanh::lean_is_exclusive(v_s_4759_)) as u8;
                if v_isSharedCheck_4779_ == 0 {
                    v___x_4772_ = v_s_4759_;
                    v_isShared_4773_ = v_isSharedCheck_4779_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_varMap_4770_);
                    crate::leanh::lean_inc(v_vars_4769_);
                    crate::leanh::lean_inc(v_denote_4768_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_4767_);
                    crate::leanh::lean_inc(v_powFn_x3f_4766_);
                    crate::leanh::lean_inc(v_mulFn_x3f_4765_);
                    crate::leanh::lean_inc(v_addFn_x3f_4764_);
                    crate::leanh::lean_inc(v_semiringInst_4763_);
                    crate::leanh::lean_inc(v_u_4762_);
                    crate::leanh::lean_inc(v_type_4761_);
                    crate::leanh::lean_inc(v_id_4760_);
                    crate::leanh::lean_dec(v_s_4759_);
                    v___x_4772_ = crate::leanh::lean_box(0);
                    v_isShared_4773_ = v_isSharedCheck_4779_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_e_4755_);
                v___x_4774_ = l_Lean_PersistentArray_push___redArg(v_vars_4769_, v_e_4755_);
                v___x_4775_ = l_Lean_PersistentHashMap_insert___redArg(
                    v___f_4756_,
                    v___f_4757_,
                    v_varMap_4770_,
                    v_e_4755_,
                    v_size_4758_,
                );
                if v_isShared_4773_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4772_, 10, v___x_4775_);
                    crate::leanh::lean_ctor_set(v___x_4772_, 9, v___x_4774_);
                    v___x_4777_ = v___x_4772_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4778_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4778_, 0, v_id_4760_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4778_, 1, v_type_4761_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4778_, 2, v_u_4762_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4778_, 3, v_semiringInst_4763_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4778_, 4, v_addFn_x3f_4764_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4778_, 5, v_mulFn_x3f_4765_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4778_, 6, v_powFn_x3f_4766_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4778_, 7, v_natCastFn_x3f_4767_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4778_, 8, v_denote_4768_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4778_, 9, v___x_4774_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4778_, 10, v___x_4775_);
                    v___x_4777_ = v_reuseFailAlloc_4778_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4777_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__1(
    mut v_toPure_4780_: *mut crate::leanh::LeanObject,
    mut v_size_4781_: *mut crate::leanh::LeanObject,
    mut v_____r_4782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4783_ =
        crate::leanh::lean_apply_2(v_toPure_4780_, crate::leanh::lean_box(0), v_size_4781_);
    return v___x_4783_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__2(
    mut v_e_4784_: *mut crate::leanh::LeanObject,
    mut v_inst_4785_: *mut crate::leanh::LeanObject,
    mut v_toBind_4786_: *mut crate::leanh::LeanObject,
    mut v___f_4787_: *mut crate::leanh::LeanObject,
    mut v_____r_4788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4789_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
    v___x_4790_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_SolverExtension_markTerm___boxed as *mut core::ffi::c_void,
        14,
        3,
    );
    crate::leanh::lean_closure_set(v___x_4790_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4790_, 1, v___x_4789_);
    crate::leanh::lean_closure_set(v___x_4790_, 2, v_e_4784_);
    v___x_4791_ = crate::leanh::lean_apply_2(v_inst_4785_, crate::leanh::lean_box(0), v___x_4790_);
    v___x_4792_ = crate::leanh::lean_apply_4(
        v_toBind_4786_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4791_,
        v___f_4787_,
    );
    return v___x_4792_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__3(
    mut v_inst_4793_: *mut crate::leanh::LeanObject,
    mut v_e_4794_: *mut crate::leanh::LeanObject,
    mut v_toBind_4795_: *mut crate::leanh::LeanObject,
    mut v___f_4796_: *mut crate::leanh::LeanObject,
    mut v_____r_4797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4798_ = crate::leanh::lean_apply_1(v_inst_4793_, v_e_4794_);
    v___x_4799_ = crate::leanh::lean_apply_4(
        v_toBind_4795_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4798_,
        v___f_4796_,
    );
    return v___x_4799_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__4(
    mut v___f_4800_: *mut crate::leanh::LeanObject,
    mut v___f_4801_: *mut crate::leanh::LeanObject,
    mut v_e_4802_: *mut crate::leanh::LeanObject,
    mut v_toPure_4803_: *mut crate::leanh::LeanObject,
    mut v_inst_4804_: *mut crate::leanh::LeanObject,
    mut v_toBind_4805_: *mut crate::leanh::LeanObject,
    mut v_inst_4806_: *mut crate::leanh::LeanObject,
    mut v_modifySemiring_4807_: *mut crate::leanh::LeanObject,
    mut v_s_4808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vars_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_vars_4809_ = crate::leanh::lean_ctor_get(v_s_4808_, 9);
    crate::leanh::lean_inc_ref(v_vars_4809_);
    v_varMap_4810_ = crate::leanh::lean_ctor_get(v_s_4808_, 10);
    crate::leanh::lean_inc_ref(v_varMap_4810_);
    crate::leanh::lean_dec_ref(v_s_4808_);
    crate::leanh::lean_inc_ref(v_e_4802_);
    crate::leanh::lean_inc_ref(v___f_4801_);
    crate::leanh::lean_inc_ref(v___f_4800_);
    v___x_4811_ = l_Lean_PersistentHashMap_find_x3f___redArg(
        v___f_4800_,
        v___f_4801_,
        v_varMap_4810_,
        v_e_4802_,
    );
    crate::leanh::lean_dec_ref(v_varMap_4810_);
    if crate::leanh::lean_obj_tag(v___x_4811_) == 1 {
        let mut v_val_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_vars_4809_);
        crate::leanh::lean_dec(v_modifySemiring_4807_);
        crate::leanh::lean_dec(v_inst_4806_);
        crate::leanh::lean_dec(v_toBind_4805_);
        crate::leanh::lean_dec(v_inst_4804_);
        crate::leanh::lean_dec_ref(v_e_4802_);
        crate::leanh::lean_dec_ref(v___f_4801_);
        crate::leanh::lean_dec_ref(v___f_4800_);
        v_val_4812_ = crate::leanh::lean_ctor_get(v___x_4811_, 0);
        crate::leanh::lean_inc(v_val_4812_);
        crate::leanh::lean_dec_ref_known(v___x_4811_, 1);
        v___x_4813_ =
            crate::leanh::lean_apply_2(v_toPure_4803_, crate::leanh::lean_box(0), v_val_4812_);
        return v___x_4813_;
    } else {
        let mut v_size_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_4811_);
        v_size_4814_ = crate::leanh::lean_ctor_get(v_vars_4809_, 2);
        crate::leanh::lean_inc_n(v_size_4814_, 2);
        crate::leanh::lean_dec_ref(v_vars_4809_);
        crate::leanh::lean_inc_ref_n(v_e_4802_, 2);
        v___f_4815_ = crate::leanh::lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_4815_, 0, v_e_4802_);
        crate::leanh::lean_closure_set(v___f_4815_, 1, v___f_4800_);
        crate::leanh::lean_closure_set(v___f_4815_, 2, v___f_4801_);
        crate::leanh::lean_closure_set(v___f_4815_, 3, v_size_4814_);
        v___f_4816_ = crate::leanh::lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_4816_, 0, v_toPure_4803_);
        crate::leanh::lean_closure_set(v___f_4816_, 1, v_size_4814_);
        crate::leanh::lean_inc_n(v_toBind_4805_, 2);
        v___f_4817_ = crate::leanh::lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__2 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_4817_, 0, v_e_4802_);
        crate::leanh::lean_closure_set(v___f_4817_, 1, v_inst_4804_);
        crate::leanh::lean_closure_set(v___f_4817_, 2, v_toBind_4805_);
        crate::leanh::lean_closure_set(v___f_4817_, 3, v___f_4816_);
        v___f_4818_ = crate::leanh::lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__3 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_4818_, 0, v_inst_4806_);
        crate::leanh::lean_closure_set(v___f_4818_, 1, v_e_4802_);
        crate::leanh::lean_closure_set(v___f_4818_, 2, v_toBind_4805_);
        crate::leanh::lean_closure_set(v___f_4818_, 3, v___f_4817_);
        v___x_4819_ = crate::leanh::lean_apply_1(v_modifySemiring_4807_, v___f_4815_);
        v___x_4820_ = crate::leanh::lean_apply_4(
            v_toBind_4805_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_4819_,
            v___f_4818_,
        );
        return v___x_4820_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(
    mut v_inst_4823_: *mut crate::leanh::LeanObject,
    mut v_inst_4824_: *mut crate::leanh::LeanObject,
    mut v_inst_4825_: *mut crate::leanh::LeanObject,
    mut v_inst_4826_: *mut crate::leanh::LeanObject,
    mut v_e_4827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getSemiring_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifySemiring_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4828_ = crate::leanh::lean_ctor_get(v_inst_4824_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4828_);
    v_toBind_4829_ = crate::leanh::lean_ctor_get(v_inst_4824_, 1);
    crate::leanh::lean_inc_n(v_toBind_4829_, 2);
    crate::leanh::lean_dec_ref(v_inst_4824_);
    v_getSemiring_4830_ = crate::leanh::lean_ctor_get(v_inst_4825_, 0);
    crate::leanh::lean_inc(v_getSemiring_4830_);
    v_modifySemiring_4831_ = crate::leanh::lean_ctor_get(v_inst_4825_, 1);
    crate::leanh::lean_inc(v_modifySemiring_4831_);
    crate::leanh::lean_dec_ref(v_inst_4825_);
    v_toPure_4832_ = crate::leanh::lean_ctor_get(v_toApplicative_4828_, 1);
    crate::leanh::lean_inc(v_toPure_4832_);
    crate::leanh::lean_dec_ref(v_toApplicative_4828_);
    v___f_4833_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0;
    v___f_4834_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__1;
    v___f_4835_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__4 as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_4835_, 0, v___f_4833_);
    crate::leanh::lean_closure_set(v___f_4835_, 1, v___f_4834_);
    crate::leanh::lean_closure_set(v___f_4835_, 2, v_e_4827_);
    crate::leanh::lean_closure_set(v___f_4835_, 3, v_toPure_4832_);
    crate::leanh::lean_closure_set(v___f_4835_, 4, v_inst_4823_);
    crate::leanh::lean_closure_set(v___f_4835_, 5, v_toBind_4829_);
    crate::leanh::lean_closure_set(v___f_4835_, 6, v_inst_4826_);
    crate::leanh::lean_closure_set(v___f_4835_, 7, v_modifySemiring_4831_);
    v___x_4836_ = crate::leanh::lean_apply_4(
        v_toBind_4829_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getSemiring_4830_,
        v___f_4835_,
    );
    return v___x_4836_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore(
    mut v_m_4837_: *mut crate::leanh::LeanObject,
    mut v_inst_4838_: *mut crate::leanh::LeanObject,
    mut v_inst_4839_: *mut crate::leanh::LeanObject,
    mut v_inst_4840_: *mut crate::leanh::LeanObject,
    mut v_inst_4841_: *mut crate::leanh::LeanObject,
    mut v_e_4842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4843_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(
        v_inst_4838_,
        v_inst_4839_,
        v_inst_4840_,
        v_inst_4841_,
        v_e_4842_,
    );
    return v___x_4843_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0(
    mut v___y_4844_: *mut crate::leanh::LeanObject,
    mut v_e_4845_: *mut crate::leanh::LeanObject,
    mut v_size_4846_: *mut crate::leanh::LeanObject,
    mut v_s_4847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_rings_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_4861_: u8 = 0;
    let mut v___x_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: u8 = 0;
    let mut v___x_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4866_: u8 = 0;
    let mut v_v_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSemiring_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringId_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addRightCancelInst_x3f_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toQFn_x3f_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4875_: u8 = 0;
    let mut v_id_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4889_: u8 = 0;
    let mut v___x_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4904_: u8 = 0;
    let mut v_isSharedCheck_4905_: u8 = 0;
    let mut v_isSharedCheck_4906_: u8 = 0;
    let mut v_unused_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_4848_ = crate::leanh::lean_ctor_get(v_s_4847_, 0);
                v_typeIdOf_4849_ = crate::leanh::lean_ctor_get(v_s_4847_, 1);
                v_exprToRingId_4850_ = crate::leanh::lean_ctor_get(v_s_4847_, 2);
                v_semirings_4851_ = crate::leanh::lean_ctor_get(v_s_4847_, 3);
                v_stypeIdOf_4852_ = crate::leanh::lean_ctor_get(v_s_4847_, 4);
                v_exprToSemiringId_4853_ = crate::leanh::lean_ctor_get(v_s_4847_, 5);
                v_ncRings_4854_ = crate::leanh::lean_ctor_get(v_s_4847_, 6);
                v_exprToNCRingId_4855_ = crate::leanh::lean_ctor_get(v_s_4847_, 7);
                v_nctypeIdOf_4856_ = crate::leanh::lean_ctor_get(v_s_4847_, 8);
                v_ncSemirings_4857_ = crate::leanh::lean_ctor_get(v_s_4847_, 9);
                v_exprToNCSemiringId_4858_ = crate::leanh::lean_ctor_get(v_s_4847_, 10);
                v_ncstypeIdOf_4859_ = crate::leanh::lean_ctor_get(v_s_4847_, 11);
                v_steps_4860_ = crate::leanh::lean_ctor_get(v_s_4847_, 12);
                v_reportedMaxDegreeIssue_4861_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_4847_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                v___x_4862_ = lean_array_get_size(v_semirings_4851_);
                v___x_4863_ = lean_nat_dec_lt(v___y_4844_, v___x_4862_);
                if v___x_4863_ == 0 {
                    crate::leanh::lean_dec(v_size_4846_);
                    crate::leanh::lean_dec_ref(v_e_4845_);
                    return v_s_4847_;
                } else {
                    crate::leanh::lean_inc(v_steps_4860_);
                    crate::leanh::lean_inc_ref(v_ncstypeIdOf_4859_);
                    crate::leanh::lean_inc_ref(v_exprToNCSemiringId_4858_);
                    crate::leanh::lean_inc_ref(v_ncSemirings_4857_);
                    crate::leanh::lean_inc_ref(v_nctypeIdOf_4856_);
                    crate::leanh::lean_inc_ref(v_exprToNCRingId_4855_);
                    crate::leanh::lean_inc_ref(v_ncRings_4854_);
                    crate::leanh::lean_inc_ref(v_exprToSemiringId_4853_);
                    crate::leanh::lean_inc_ref(v_stypeIdOf_4852_);
                    crate::leanh::lean_inc_ref(v_semirings_4851_);
                    crate::leanh::lean_inc_ref(v_exprToRingId_4850_);
                    crate::leanh::lean_inc_ref(v_typeIdOf_4849_);
                    crate::leanh::lean_inc_ref(v_rings_4848_);
                    v_isSharedCheck_4906_ = (!crate::leanh::lean_is_exclusive(v_s_4847_)) as u8;
                    if v_isSharedCheck_4906_ == 0 {
                        v_unused_4907_ = crate::leanh::lean_ctor_get(v_s_4847_, 12);
                        crate::leanh::lean_dec(v_unused_4907_);
                        v_unused_4908_ = crate::leanh::lean_ctor_get(v_s_4847_, 11);
                        crate::leanh::lean_dec(v_unused_4908_);
                        v_unused_4909_ = crate::leanh::lean_ctor_get(v_s_4847_, 10);
                        crate::leanh::lean_dec(v_unused_4909_);
                        v_unused_4910_ = crate::leanh::lean_ctor_get(v_s_4847_, 9);
                        crate::leanh::lean_dec(v_unused_4910_);
                        v_unused_4911_ = crate::leanh::lean_ctor_get(v_s_4847_, 8);
                        crate::leanh::lean_dec(v_unused_4911_);
                        v_unused_4912_ = crate::leanh::lean_ctor_get(v_s_4847_, 7);
                        crate::leanh::lean_dec(v_unused_4912_);
                        v_unused_4913_ = crate::leanh::lean_ctor_get(v_s_4847_, 6);
                        crate::leanh::lean_dec(v_unused_4913_);
                        v_unused_4914_ = crate::leanh::lean_ctor_get(v_s_4847_, 5);
                        crate::leanh::lean_dec(v_unused_4914_);
                        v_unused_4915_ = crate::leanh::lean_ctor_get(v_s_4847_, 4);
                        crate::leanh::lean_dec(v_unused_4915_);
                        v_unused_4916_ = crate::leanh::lean_ctor_get(v_s_4847_, 3);
                        crate::leanh::lean_dec(v_unused_4916_);
                        v_unused_4917_ = crate::leanh::lean_ctor_get(v_s_4847_, 2);
                        crate::leanh::lean_dec(v_unused_4917_);
                        v_unused_4918_ = crate::leanh::lean_ctor_get(v_s_4847_, 1);
                        crate::leanh::lean_dec(v_unused_4918_);
                        v_unused_4919_ = crate::leanh::lean_ctor_get(v_s_4847_, 0);
                        crate::leanh::lean_dec(v_unused_4919_);
                        v___x_4865_ = v_s_4847_;
                        v_isShared_4866_ = v_isSharedCheck_4906_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_s_4847_);
                        v___x_4865_ = crate::leanh::lean_box(0);
                        v_isShared_4866_ = v_isSharedCheck_4906_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4867_ = lean_array_fget(v_semirings_4851_, v___y_4844_);
                v_toSemiring_4868_ = crate::leanh::lean_ctor_get(v_v_4867_, 0);
                v_ringId_4869_ = crate::leanh::lean_ctor_get(v_v_4867_, 1);
                v_commSemiringInst_4870_ = crate::leanh::lean_ctor_get(v_v_4867_, 2);
                v_addRightCancelInst_x3f_4871_ = crate::leanh::lean_ctor_get(v_v_4867_, 3);
                v_toQFn_x3f_4872_ = crate::leanh::lean_ctor_get(v_v_4867_, 4);
                v_isSharedCheck_4905_ = (!crate::leanh::lean_is_exclusive(v_v_4867_)) as u8;
                if v_isSharedCheck_4905_ == 0 {
                    v___x_4874_ = v_v_4867_;
                    v_isShared_4875_ = v_isSharedCheck_4905_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toQFn_x3f_4872_);
                    crate::leanh::lean_inc(v_addRightCancelInst_x3f_4871_);
                    crate::leanh::lean_inc(v_commSemiringInst_4870_);
                    crate::leanh::lean_inc(v_ringId_4869_);
                    crate::leanh::lean_inc(v_toSemiring_4868_);
                    crate::leanh::lean_dec(v_v_4867_);
                    v___x_4874_ = crate::leanh::lean_box(0);
                    v_isShared_4875_ = v_isSharedCheck_4905_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_id_4876_ = crate::leanh::lean_ctor_get(v_toSemiring_4868_, 0);
                v_type_4877_ = crate::leanh::lean_ctor_get(v_toSemiring_4868_, 1);
                v_u_4878_ = crate::leanh::lean_ctor_get(v_toSemiring_4868_, 2);
                v_semiringInst_4879_ = crate::leanh::lean_ctor_get(v_toSemiring_4868_, 3);
                v_addFn_x3f_4880_ = crate::leanh::lean_ctor_get(v_toSemiring_4868_, 4);
                v_mulFn_x3f_4881_ = crate::leanh::lean_ctor_get(v_toSemiring_4868_, 5);
                v_powFn_x3f_4882_ = crate::leanh::lean_ctor_get(v_toSemiring_4868_, 6);
                v_natCastFn_x3f_4883_ = crate::leanh::lean_ctor_get(v_toSemiring_4868_, 7);
                v_denote_4884_ = crate::leanh::lean_ctor_get(v_toSemiring_4868_, 8);
                v_vars_4885_ = crate::leanh::lean_ctor_get(v_toSemiring_4868_, 9);
                v_varMap_4886_ = crate::leanh::lean_ctor_get(v_toSemiring_4868_, 10);
                v_isSharedCheck_4904_ =
                    (!crate::leanh::lean_is_exclusive(v_toSemiring_4868_)) as u8;
                if v_isSharedCheck_4904_ == 0 {
                    v___x_4888_ = v_toSemiring_4868_;
                    v_isShared_4889_ = v_isSharedCheck_4904_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_varMap_4886_);
                    crate::leanh::lean_inc(v_vars_4885_);
                    crate::leanh::lean_inc(v_denote_4884_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_4883_);
                    crate::leanh::lean_inc(v_powFn_x3f_4882_);
                    crate::leanh::lean_inc(v_mulFn_x3f_4881_);
                    crate::leanh::lean_inc(v_addFn_x3f_4880_);
                    crate::leanh::lean_inc(v_semiringInst_4879_);
                    crate::leanh::lean_inc(v_u_4878_);
                    crate::leanh::lean_inc(v_type_4877_);
                    crate::leanh::lean_inc(v_id_4876_);
                    crate::leanh::lean_dec(v_toSemiring_4868_);
                    v___x_4888_ = crate::leanh::lean_box(0);
                    v_isShared_4889_ = v_isSharedCheck_4904_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4890_ = crate::leanh::lean_box(0);
                v_xs_x27_4891_ = lean_array_fset(v_semirings_4851_, v___y_4844_, v___x_4890_);
                crate::leanh::lean_inc_ref(v_e_4845_);
                v___x_4892_ = l_Lean_PersistentArray_push___redArg(v_vars_4885_, v_e_4845_);
                v___x_4893_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_varMap_4886_, v_e_4845_, v_size_4846_);
                if v_isShared_4889_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4888_, 10, v___x_4893_);
                    crate::leanh::lean_ctor_set(v___x_4888_, 9, v___x_4892_);
                    v___x_4895_ = v___x_4888_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4903_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_id_4876_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4903_, 1, v_type_4877_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4903_, 2, v_u_4878_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4903_, 3, v_semiringInst_4879_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4903_, 4, v_addFn_x3f_4880_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4903_, 5, v_mulFn_x3f_4881_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4903_, 6, v_powFn_x3f_4882_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4903_, 7, v_natCastFn_x3f_4883_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4903_, 8, v_denote_4884_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4903_, 9, v___x_4892_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4903_, 10, v___x_4893_);
                    v___x_4895_ = v_reuseFailAlloc_4903_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4875_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4874_, 0, v___x_4895_);
                    v___x_4897_ = v___x_4874_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4902_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4902_, 0, v___x_4895_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4902_, 1, v_ringId_4869_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4902_,
                        2,
                        v_commSemiringInst_4870_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4902_,
                        3,
                        v_addRightCancelInst_x3f_4871_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4902_, 4, v_toQFn_x3f_4872_);
                    v___x_4897_ = v_reuseFailAlloc_4902_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4898_ = lean_array_fset(v_xs_x27_4891_, v___y_4844_, v___x_4897_);
                if v_isShared_4866_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4865_, 3, v___x_4898_);
                    v___x_4900_ = v___x_4865_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4901_ = crate::leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4901_, 0, v_rings_4848_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4901_, 1, v_typeIdOf_4849_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4901_, 2, v_exprToRingId_4850_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4901_, 3, v___x_4898_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4901_, 4, v_stypeIdOf_4852_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4901_,
                        5,
                        v_exprToSemiringId_4853_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4901_, 6, v_ncRings_4854_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4901_, 7, v_exprToNCRingId_4855_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4901_, 8, v_nctypeIdOf_4856_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4901_, 9, v_ncSemirings_4857_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4901_,
                        10,
                        v_exprToNCSemiringId_4858_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4901_, 11, v_ncstypeIdOf_4859_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4901_, 12, v_steps_4860_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4901_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                        v_reportedMaxDegreeIssue_4861_,
                    );
                    v___x_4900_ = v_reuseFailAlloc_4901_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4900_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0___boxed(
    mut v___y_4920_: *mut crate::leanh::LeanObject,
    mut v_e_4921_: *mut crate::leanh::LeanObject,
    mut v_size_4922_: *mut crate::leanh::LeanObject,
    mut v_s_4923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4924_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0(v___y_4920_, v_e_4921_, v_size_4922_, v_s_4923_);
    crate::leanh::lean_dec(v___y_4920_);
    return v_res_4924_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(
    mut v_e_4925_: *mut crate::leanh::LeanObject,
    mut v___y_4926_: *mut crate::leanh::LeanObject,
    mut v___y_4927_: *mut crate::leanh::LeanObject,
    mut v___y_4928_: *mut crate::leanh::LeanObject,
    mut v___y_4929_: *mut crate::leanh::LeanObject,
    mut v___y_4930_: *mut crate::leanh::LeanObject,
    mut v___y_4931_: *mut crate::leanh::LeanObject,
    mut v___y_4932_: *mut crate::leanh::LeanObject,
    mut v___y_4933_: *mut crate::leanh::LeanObject,
    mut v___y_4934_: *mut crate::leanh::LeanObject,
    mut v___y_4935_: *mut crate::leanh::LeanObject,
    mut v___y_4936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4942_: u8 = 0;
    let mut v_toSemiring_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4959_: u8 = 0;
    let mut v___x_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4963_: u8 = 0;
    let mut v_unused_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4968_: u8 = 0;
    let mut v___x_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4972_: u8 = 0;
    let mut v_a_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4976_: u8 = 0;
    let mut v___x_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4980_: u8 = 0;
    let mut v_a_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4984_: u8 = 0;
    let mut v___x_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4988_: u8 = 0;
    let mut v_isSharedCheck_4989_: u8 = 0;
    let mut v_a_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4993_: u8 = 0;
    let mut v___x_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4997_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4938_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(
                    v___y_4926_,
                    v___y_4927_,
                    v___y_4928_,
                    v___y_4929_,
                    v___y_4930_,
                    v___y_4931_,
                    v___y_4932_,
                    v___y_4933_,
                    v___y_4934_,
                    v___y_4935_,
                    v___y_4936_,
                );
                if crate::leanh::lean_obj_tag(v___x_4938_) == 0 {
                    v_a_4939_ = crate::leanh::lean_ctor_get(v___x_4938_, 0);
                    v_isSharedCheck_4989_ = (!crate::leanh::lean_is_exclusive(v___x_4938_)) as u8;
                    if v_isSharedCheck_4989_ == 0 {
                        v___x_4941_ = v___x_4938_;
                        v_isShared_4942_ = v_isSharedCheck_4989_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4939_);
                        crate::leanh::lean_dec(v___x_4938_);
                        v___x_4941_ = crate::leanh::lean_box(0);
                        v_isShared_4942_ = v_isSharedCheck_4989_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_4925_);
                    v_a_4990_ = crate::leanh::lean_ctor_get(v___x_4938_, 0);
                    v_isSharedCheck_4997_ = (!crate::leanh::lean_is_exclusive(v___x_4938_)) as u8;
                    if v_isSharedCheck_4997_ == 0 {
                        v___x_4992_ = v___x_4938_;
                        v_isShared_4993_ = v_isSharedCheck_4997_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4990_);
                        crate::leanh::lean_dec(v___x_4938_);
                        v___x_4992_ = crate::leanh::lean_box(0);
                        v_isShared_4993_ = v_isSharedCheck_4997_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v_toSemiring_4943_ = crate::leanh::lean_ctor_get(v_a_4939_, 0);
                crate::leanh::lean_inc_ref(v_toSemiring_4943_);
                crate::leanh::lean_dec(v_a_4939_);
                v_vars_4944_ = crate::leanh::lean_ctor_get(v_toSemiring_4943_, 9);
                crate::leanh::lean_inc_ref(v_vars_4944_);
                v_varMap_4945_ = crate::leanh::lean_ctor_get(v_toSemiring_4943_, 10);
                crate::leanh::lean_inc_ref(v_varMap_4945_);
                crate::leanh::lean_dec_ref(v_toSemiring_4943_);
                v___x_4946_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_varMap_4945_, v_e_4925_);
                crate::leanh::lean_dec_ref(v_varMap_4945_);
                if crate::leanh::lean_obj_tag(v___x_4946_) == 1 {
                    crate::leanh::lean_dec_ref(v_vars_4944_);
                    crate::leanh::lean_dec_ref(v_e_4925_);
                    v_val_4947_ = crate::leanh::lean_ctor_get(v___x_4946_, 0);
                    crate::leanh::lean_inc(v_val_4947_);
                    crate::leanh::lean_dec_ref_known(v___x_4946_, 1);
                    if v_isShared_4942_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4941_, 0, v_val_4947_);
                        v___x_4949_ = v___x_4941_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4950_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4950_, 0, v_val_4947_);
                        v___x_4949_ = v_reuseFailAlloc_4950_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4946_);
                    crate::leanh::lean_del_object(v___x_4941_);
                    v_size_4951_ = crate::leanh::lean_ctor_get(v_vars_4944_, 2);
                    crate::leanh::lean_inc_n(v_size_4951_, 2);
                    crate::leanh::lean_dec_ref(v_vars_4944_);
                    crate::leanh::lean_inc_ref(v_e_4925_);
                    crate::leanh::lean_inc(v___y_4926_);
                    v___f_4952_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0___boxed as *mut core::ffi::c_void, 4, 3);
                    crate::leanh::lean_closure_set(v___f_4952_, 0, v___y_4926_);
                    crate::leanh::lean_closure_set(v___f_4952_, 1, v_e_4925_);
                    crate::leanh::lean_closure_set(v___f_4952_, 2, v_size_4951_);
                    v___x_4953_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                    v___x_4954_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4953_, v___f_4952_, v___y_4927_);
                    if crate::leanh::lean_obj_tag(v___x_4954_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4954_, 1);
                        crate::leanh::lean_inc_ref(v_e_4925_);
                        v___x_4955_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(
                            v_e_4925_,
                            v___y_4926_,
                            v___y_4927_,
                            v___y_4931_,
                            v___y_4932_,
                            v___y_4933_,
                            v___y_4934_,
                            v___y_4935_,
                            v___y_4936_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4955_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4955_, 1);
                            v___x_4956_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(
                                v___x_4953_,
                                v_e_4925_,
                                v___y_4927_,
                                v___y_4928_,
                                v___y_4929_,
                                v___y_4930_,
                                v___y_4931_,
                                v___y_4932_,
                                v___y_4933_,
                                v___y_4934_,
                                v___y_4935_,
                                v___y_4936_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4956_) == 0 {
                                v_isSharedCheck_4963_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4956_)) as u8;
                                if v_isSharedCheck_4963_ == 0 {
                                    v_unused_4964_ = crate::leanh::lean_ctor_get(v___x_4956_, 0);
                                    crate::leanh::lean_dec(v_unused_4964_);
                                    v___x_4958_ = v___x_4956_;
                                    v_isShared_4959_ = v_isSharedCheck_4963_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_4956_);
                                    v___x_4958_ = crate::leanh::lean_box(0);
                                    v_isShared_4959_ = v_isSharedCheck_4963_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_size_4951_);
                                v_a_4965_ = crate::leanh::lean_ctor_get(v___x_4956_, 0);
                                v_isSharedCheck_4972_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4956_)) as u8;
                                if v_isSharedCheck_4972_ == 0 {
                                    v___x_4967_ = v___x_4956_;
                                    v_isShared_4968_ = v_isSharedCheck_4972_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4965_);
                                    crate::leanh::lean_dec(v___x_4956_);
                                    v___x_4967_ = crate::leanh::lean_box(0);
                                    v_isShared_4968_ = v_isSharedCheck_4972_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_size_4951_);
                            crate::leanh::lean_dec_ref(v_e_4925_);
                            v_a_4973_ = crate::leanh::lean_ctor_get(v___x_4955_, 0);
                            v_isSharedCheck_4980_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4955_)) as u8;
                            if v_isSharedCheck_4980_ == 0 {
                                v___x_4975_ = v___x_4955_;
                                v_isShared_4976_ = v_isSharedCheck_4980_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4973_);
                                crate::leanh::lean_dec(v___x_4955_);
                                v___x_4975_ = crate::leanh::lean_box(0);
                                v_isShared_4976_ = v_isSharedCheck_4980_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_size_4951_);
                        crate::leanh::lean_dec_ref(v_e_4925_);
                        v_a_4981_ = crate::leanh::lean_ctor_get(v___x_4954_, 0);
                        v_isSharedCheck_4988_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4954_)) as u8;
                        if v_isSharedCheck_4988_ == 0 {
                            v___x_4983_ = v___x_4954_;
                            v_isShared_4984_ = v_isSharedCheck_4988_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4981_);
                            crate::leanh::lean_dec(v___x_4954_);
                            v___x_4983_ = crate::leanh::lean_box(0);
                            v_isShared_4984_ = v_isSharedCheck_4988_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4949_;
            }
            3 => {
                if v_isShared_4959_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4958_, 0, v_size_4951_);
                    v___x_4961_ = v___x_4958_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4962_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4962_, 0, v_size_4951_);
                    v___x_4961_ = v_reuseFailAlloc_4962_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4961_;
            }
            5 => {
                if v_isShared_4968_ == 0 {
                    v___x_4970_ = v___x_4967_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4971_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4971_, 0, v_a_4965_);
                    v___x_4970_ = v_reuseFailAlloc_4971_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4970_;
            }
            7 => {
                if v_isShared_4976_ == 0 {
                    v___x_4978_ = v___x_4975_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4979_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4979_, 0, v_a_4973_);
                    v___x_4978_ = v_reuseFailAlloc_4979_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4978_;
            }
            9 => {
                if v_isShared_4984_ == 0 {
                    v___x_4986_ = v___x_4983_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4987_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4987_, 0, v_a_4981_);
                    v___x_4986_ = v_reuseFailAlloc_4987_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4986_;
            }
            11 => {
                if v_isShared_4993_ == 0 {
                    v___x_4995_ = v___x_4992_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4996_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4996_, 0, v_a_4990_);
                    v___x_4995_ = v_reuseFailAlloc_4996_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4995_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___boxed(
    mut v_e_4998_: *mut crate::leanh::LeanObject,
    mut v___y_4999_: *mut crate::leanh::LeanObject,
    mut v___y_5000_: *mut crate::leanh::LeanObject,
    mut v___y_5001_: *mut crate::leanh::LeanObject,
    mut v___y_5002_: *mut crate::leanh::LeanObject,
    mut v___y_5003_: *mut crate::leanh::LeanObject,
    mut v___y_5004_: *mut crate::leanh::LeanObject,
    mut v___y_5005_: *mut crate::leanh::LeanObject,
    mut v___y_5006_: *mut crate::leanh::LeanObject,
    mut v___y_5007_: *mut crate::leanh::LeanObject,
    mut v___y_5008_: *mut crate::leanh::LeanObject,
    mut v___y_5009_: *mut crate::leanh::LeanObject,
    mut v___y_5010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5011_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(v_e_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_);
    crate::leanh::lean_dec(v___y_5009_);
    crate::leanh::lean_dec_ref(v___y_5008_);
    crate::leanh::lean_dec(v___y_5007_);
    crate::leanh::lean_dec_ref(v___y_5006_);
    crate::leanh::lean_dec(v___y_5005_);
    crate::leanh::lean_dec_ref(v___y_5004_);
    crate::leanh::lean_dec(v___y_5003_);
    crate::leanh::lean_dec_ref(v___y_5002_);
    crate::leanh::lean_dec(v___y_5001_);
    crate::leanh::lean_dec(v___y_5000_);
    crate::leanh::lean_dec(v___y_4999_);
    return v_res_5011_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkSVar(
    mut v_e_5012_: *mut crate::leanh::LeanObject,
    mut v_a_5013_: *mut crate::leanh::LeanObject,
    mut v_a_5014_: *mut crate::leanh::LeanObject,
    mut v_a_5015_: *mut crate::leanh::LeanObject,
    mut v_a_5016_: *mut crate::leanh::LeanObject,
    mut v_a_5017_: *mut crate::leanh::LeanObject,
    mut v_a_5018_: *mut crate::leanh::LeanObject,
    mut v_a_5019_: *mut crate::leanh::LeanObject,
    mut v_a_5020_: *mut crate::leanh::LeanObject,
    mut v_a_5021_: *mut crate::leanh::LeanObject,
    mut v_a_5022_: *mut crate::leanh::LeanObject,
    mut v_a_5023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5025_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(v_e_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_);
    return v___x_5025_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkSVar___boxed(
    mut v_e_5026_: *mut crate::leanh::LeanObject,
    mut v_a_5027_: *mut crate::leanh::LeanObject,
    mut v_a_5028_: *mut crate::leanh::LeanObject,
    mut v_a_5029_: *mut crate::leanh::LeanObject,
    mut v_a_5030_: *mut crate::leanh::LeanObject,
    mut v_a_5031_: *mut crate::leanh::LeanObject,
    mut v_a_5032_: *mut crate::leanh::LeanObject,
    mut v_a_5033_: *mut crate::leanh::LeanObject,
    mut v_a_5034_: *mut crate::leanh::LeanObject,
    mut v_a_5035_: *mut crate::leanh::LeanObject,
    mut v_a_5036_: *mut crate::leanh::LeanObject,
    mut v_a_5037_: *mut crate::leanh::LeanObject,
    mut v_a_5038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5039_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVar(
        v_e_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_,
        v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_,
    );
    crate::leanh::lean_dec(v_a_5037_);
    crate::leanh::lean_dec_ref(v_a_5036_);
    crate::leanh::lean_dec(v_a_5035_);
    crate::leanh::lean_dec_ref(v_a_5034_);
    crate::leanh::lean_dec(v_a_5033_);
    crate::leanh::lean_dec_ref(v_a_5032_);
    crate::leanh::lean_dec(v_a_5031_);
    crate::leanh::lean_dec_ref(v_a_5030_);
    crate::leanh::lean_dec(v_a_5029_);
    crate::leanh::lean_dec(v_a_5028_);
    crate::leanh::lean_dec(v_a_5027_);
    return v_res_5039_;
}
pub unsafe fn l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__1(
    mut v_a_5040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5041_ = lean_nat_to_int(v_a_5040_);
    return v___x_5041_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5042_ = l_Lean_Meta_Grind_instInhabitedGoalM(crate::leanh::lean_box(0));
    return v___x_5042_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(
    mut v_msg_5043_: *mut crate::leanh::LeanObject,
    mut v___y_5044_: *mut crate::leanh::LeanObject,
    mut v___y_5045_: *mut crate::leanh::LeanObject,
    mut v___y_5046_: *mut crate::leanh::LeanObject,
    mut v___y_5047_: *mut crate::leanh::LeanObject,
    mut v___y_5048_: *mut crate::leanh::LeanObject,
    mut v___y_5049_: *mut crate::leanh::LeanObject,
    mut v___y_5050_: *mut crate::leanh::LeanObject,
    mut v___y_5051_: *mut crate::leanh::LeanObject,
    mut v___y_5052_: *mut crate::leanh::LeanObject,
    mut v___y_5053_: *mut crate::leanh::LeanObject,
    mut v___y_5054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_40218__overap_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5056_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0);
    v___f_5057_ = crate::leanh::lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5057_, 0, v___x_5056_);
    v___x_40218__overap_5058_ = lean_panic_fn_borrowed(v___f_5057_, v_msg_5043_);
    crate::leanh::lean_dec_ref(v___f_5057_);
    crate::leanh::lean_inc(v___y_5054_);
    crate::leanh::lean_inc_ref(v___y_5053_);
    crate::leanh::lean_inc(v___y_5052_);
    crate::leanh::lean_inc_ref(v___y_5051_);
    crate::leanh::lean_inc(v___y_5050_);
    crate::leanh::lean_inc_ref(v___y_5049_);
    crate::leanh::lean_inc(v___y_5048_);
    crate::leanh::lean_inc_ref(v___y_5047_);
    crate::leanh::lean_inc(v___y_5046_);
    crate::leanh::lean_inc(v___y_5045_);
    crate::leanh::lean_inc(v___y_5044_);
    v___x_5059_ = crate::leanh::lean_apply_12(
        v___x_40218__overap_5058_,
        v___y_5044_,
        v___y_5045_,
        v___y_5046_,
        v___y_5047_,
        v___y_5048_,
        v___y_5049_,
        v___y_5050_,
        v___y_5051_,
        v___y_5052_,
        v___y_5053_,
        v___y_5054_,
        crate::leanh::lean_box(0),
    );
    return v___x_5059_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___boxed(
    mut v_msg_5060_: *mut crate::leanh::LeanObject,
    mut v___y_5061_: *mut crate::leanh::LeanObject,
    mut v___y_5062_: *mut crate::leanh::LeanObject,
    mut v___y_5063_: *mut crate::leanh::LeanObject,
    mut v___y_5064_: *mut crate::leanh::LeanObject,
    mut v___y_5065_: *mut crate::leanh::LeanObject,
    mut v___y_5066_: *mut crate::leanh::LeanObject,
    mut v___y_5067_: *mut crate::leanh::LeanObject,
    mut v___y_5068_: *mut crate::leanh::LeanObject,
    mut v___y_5069_: *mut crate::leanh::LeanObject,
    mut v___y_5070_: *mut crate::leanh::LeanObject,
    mut v___y_5071_: *mut crate::leanh::LeanObject,
    mut v___y_5072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5073_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(v_msg_5060_, v___y_5061_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_, v___y_5069_, v___y_5070_, v___y_5071_);
    crate::leanh::lean_dec(v___y_5071_);
    crate::leanh::lean_dec_ref(v___y_5070_);
    crate::leanh::lean_dec(v___y_5069_);
    crate::leanh::lean_dec_ref(v___y_5068_);
    crate::leanh::lean_dec(v___y_5067_);
    crate::leanh::lean_dec_ref(v___y_5066_);
    crate::leanh::lean_dec(v___y_5065_);
    crate::leanh::lean_dec_ref(v___y_5064_);
    crate::leanh::lean_dec(v___y_5063_);
    crate::leanh::lean_dec(v___y_5062_);
    crate::leanh::lean_dec(v___y_5061_);
    return v_res_5073_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5075_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__0;
    v___x_5076_ = l_Lean_stringToMessageData(v___x_5075_);
    return v___x_5076_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(
    mut v_type_5077_: *mut crate::leanh::LeanObject,
    mut v___y_5078_: *mut crate::leanh::LeanObject,
    mut v___y_5079_: *mut crate::leanh::LeanObject,
    mut v___y_5080_: *mut crate::leanh::LeanObject,
    mut v___y_5081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5087_: u8 = 0;
    let mut v_val_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5096_: u8 = 0;
    let mut v_a_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5100_: u8 = 0;
    let mut v___x_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5104_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_type_5077_);
                v___x_5083_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                    v_type_5077_,
                    v___y_5078_,
                    v___y_5079_,
                    v___y_5080_,
                    v___y_5081_,
                );
                if crate::leanh::lean_obj_tag(v___x_5083_) == 0 {
                    v_a_5084_ = crate::leanh::lean_ctor_get(v___x_5083_, 0);
                    v_isSharedCheck_5096_ = (!crate::leanh::lean_is_exclusive(v___x_5083_)) as u8;
                    if v_isSharedCheck_5096_ == 0 {
                        v___x_5086_ = v___x_5083_;
                        v_isShared_5087_ = v_isSharedCheck_5096_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5084_);
                        crate::leanh::lean_dec(v___x_5083_);
                        v___x_5086_ = crate::leanh::lean_box(0);
                        v_isShared_5087_ = v_isSharedCheck_5096_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_5077_);
                    v_a_5097_ = crate::leanh::lean_ctor_get(v___x_5083_, 0);
                    v_isSharedCheck_5104_ = (!crate::leanh::lean_is_exclusive(v___x_5083_)) as u8;
                    if v_isSharedCheck_5104_ == 0 {
                        v___x_5099_ = v___x_5083_;
                        v_isShared_5100_ = v_isSharedCheck_5104_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5097_);
                        crate::leanh::lean_dec(v___x_5083_);
                        v___x_5099_ = crate::leanh::lean_box(0);
                        v_isShared_5100_ = v_isSharedCheck_5104_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5084_) == 1 {
                    crate::leanh::lean_dec_ref(v_type_5077_);
                    v_val_5088_ = crate::leanh::lean_ctor_get(v_a_5084_, 0);
                    crate::leanh::lean_inc(v_val_5088_);
                    crate::leanh::lean_dec_ref_known(v_a_5084_, 1);
                    if v_isShared_5087_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5086_, 0, v_val_5088_);
                        v___x_5090_ = v___x_5086_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5091_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5091_, 0, v_val_5088_);
                        v___x_5090_ = v_reuseFailAlloc_5091_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5086_);
                    crate::leanh::lean_dec(v_a_5084_);
                    v___x_5092_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1_once), _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1);
                    v___x_5093_ = l_Lean_indentExpr(v_type_5077_);
                    v___x_5094_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5094_, 0, v___x_5092_);
                    crate::leanh::lean_ctor_set(v___x_5094_, 1, v___x_5093_);
                    v___x_5095_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v___x_5094_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_);
                    return v___x_5095_;
                }
            }
            2 => {
                return v___x_5090_;
            }
            3 => {
                if v_isShared_5100_ == 0 {
                    v___x_5102_ = v___x_5099_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5103_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5103_, 0, v_a_5097_);
                    v___x_5102_ = v_reuseFailAlloc_5103_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5102_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___boxed(
    mut v_type_5105_: *mut crate::leanh::LeanObject,
    mut v___y_5106_: *mut crate::leanh::LeanObject,
    mut v___y_5107_: *mut crate::leanh::LeanObject,
    mut v___y_5108_: *mut crate::leanh::LeanObject,
    mut v___y_5109_: *mut crate::leanh::LeanObject,
    mut v___y_5110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5111_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v_type_5105_, v___y_5106_, v___y_5107_, v___y_5108_, v___y_5109_);
    crate::leanh::lean_dec(v___y_5109_);
    crate::leanh::lean_dec_ref(v___y_5108_);
    crate::leanh::lean_dec(v___y_5107_);
    crate::leanh::lean_dec_ref(v___y_5106_);
    return v_res_5111_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(
    mut v_type_5112_: *mut crate::leanh::LeanObject,
    mut v_u_5113_: *mut crate::leanh::LeanObject,
    mut v_instDeclName_5114_: *mut crate::leanh::LeanObject,
    mut v_declName_5115_: *mut crate::leanh::LeanObject,
    mut v_expectedInst_5116_: *mut crate::leanh::LeanObject,
    mut v___y_5117_: *mut crate::leanh::LeanObject,
    mut v___y_5118_: *mut crate::leanh::LeanObject,
    mut v___y_5119_: *mut crate::leanh::LeanObject,
    mut v___y_5120_: *mut crate::leanh::LeanObject,
    mut v___y_5121_: *mut crate::leanh::LeanObject,
    mut v___y_5122_: *mut crate::leanh::LeanObject,
    mut v___y_5123_: *mut crate::leanh::LeanObject,
    mut v___y_5124_: *mut crate::leanh::LeanObject,
    mut v___y_5125_: *mut crate::leanh::LeanObject,
    mut v___y_5126_: *mut crate::leanh::LeanObject,
    mut v___y_5127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5146_: u8 = 0;
    let mut v___x_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5150_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5129_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_n(v_u_5113_, 2);
                v___x_5130_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5130_, 0, v_u_5113_);
                crate::leanh::lean_ctor_set(v___x_5130_, 1, v___x_5129_);
                v___x_5131_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5131_, 0, v_u_5113_);
                crate::leanh::lean_ctor_set(v___x_5131_, 1, v___x_5130_);
                v___x_5132_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5132_, 0, v_u_5113_);
                crate::leanh::lean_ctor_set(v___x_5132_, 1, v___x_5131_);
                crate::leanh::lean_inc_ref(v___x_5132_);
                v___x_5133_ = l_Lean_mkConst(v_instDeclName_5114_, v___x_5132_);
                crate::leanh::lean_inc_ref_n(v_type_5112_, 3);
                v___x_5134_ = l_Lean_mkApp3(v___x_5133_, v_type_5112_, v_type_5112_, v_type_5112_);
                v___x_5135_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_5134_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_);
                if crate::leanh::lean_obj_tag(v___x_5135_) == 0 {
                    v_a_5136_ = crate::leanh::lean_ctor_get(v___x_5135_, 0);
                    crate::leanh::lean_inc_n(v_a_5136_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_5135_, 1);
                    crate::leanh::lean_inc(v_declName_5115_);
                    v___x_5137_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(
                        v_declName_5115_,
                        v_a_5136_,
                        v_expectedInst_5116_,
                        v___y_5124_,
                        v___y_5125_,
                        v___y_5126_,
                        v___y_5127_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5137_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5137_, 1);
                        v___x_5138_ = l_Lean_mkConst(v_declName_5115_, v___x_5132_);
                        crate::leanh::lean_inc_ref_n(v_type_5112_, 2);
                        v___x_5139_ = l_Lean_mkApp4(
                            v___x_5138_,
                            v_type_5112_,
                            v_type_5112_,
                            v_type_5112_,
                            v_a_5136_,
                        );
                        v___x_5140_ = l_Lean_Meta_Sym_canon(
                            v___x_5139_,
                            v___y_5122_,
                            v___y_5123_,
                            v___y_5124_,
                            v___y_5125_,
                            v___y_5126_,
                            v___y_5127_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5140_) == 0 {
                            v_a_5141_ = crate::leanh::lean_ctor_get(v___x_5140_, 0);
                            crate::leanh::lean_inc(v_a_5141_);
                            crate::leanh::lean_dec_ref_known(v___x_5140_, 1);
                            v___x_5142_ =
                                l_Lean_Meta_Sym_shareCommon___redArg(v_a_5141_, v___y_5123_);
                            return v___x_5142_;
                        } else {
                            return v___x_5140_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5136_);
                        crate::leanh::lean_dec_ref_known(v___x_5132_, 2);
                        crate::leanh::lean_dec(v_declName_5115_);
                        crate::leanh::lean_dec_ref(v_type_5112_);
                        v_a_5143_ = crate::leanh::lean_ctor_get(v___x_5137_, 0);
                        v_isSharedCheck_5150_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5137_)) as u8;
                        if v_isSharedCheck_5150_ == 0 {
                            v___x_5145_ = v___x_5137_;
                            v_isShared_5146_ = v_isSharedCheck_5150_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5143_);
                            crate::leanh::lean_dec(v___x_5137_);
                            v___x_5145_ = crate::leanh::lean_box(0);
                            v_isShared_5146_ = v_isSharedCheck_5150_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_5132_, 2);
                    crate::leanh::lean_dec_ref(v_expectedInst_5116_);
                    crate::leanh::lean_dec(v_declName_5115_);
                    crate::leanh::lean_dec_ref(v_type_5112_);
                    return v___x_5135_;
                }
            }
            1 => {
                if v_isShared_5146_ == 0 {
                    v___x_5148_ = v___x_5145_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5149_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5149_, 0, v_a_5143_);
                    v___x_5148_ = v_reuseFailAlloc_5149_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5148_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_type_5151_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_u_5152_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_instDeclName_5153_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_declName_5154_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_expectedInst_5155_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___y_5156_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_5157_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_5158_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_5159_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_5160_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_5161_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_5162_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_5163_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_5164_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_5165_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_5166_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_5167_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5168_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(v_type_5151_, v_u_5152_, v_instDeclName_5153_, v_declName_5154_, v_expectedInst_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_, v___y_5165_, v___y_5166_);
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
    crate::leanh::lean_dec(v___y_5156_);
    return v_res_5168_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___lam__0(
    mut v_a_5169_: *mut crate::leanh::LeanObject,
    mut v_s_5170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toRing_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recheck_5185_: u8 = 0;
    let mut v_invSet_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_5189_: u8 = 0;
    let mut v___x_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5192_: u8 = 0;
    let mut v_id_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5211_: u8 = 0;
    let mut v___x_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5219_: u8 = 0;
    let mut v_unused_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5221_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_5171_ = crate::leanh::lean_ctor_get(v_s_5170_, 0);
                v_invFn_x3f_5172_ = crate::leanh::lean_ctor_get(v_s_5170_, 1);
                v_semiringId_x3f_5173_ = crate::leanh::lean_ctor_get(v_s_5170_, 2);
                v_commSemiringInst_5174_ = crate::leanh::lean_ctor_get(v_s_5170_, 3);
                v_commRingInst_5175_ = crate::leanh::lean_ctor_get(v_s_5170_, 4);
                v_noZeroDivInst_x3f_5176_ = crate::leanh::lean_ctor_get(v_s_5170_, 5);
                v_fieldInst_x3f_5177_ = crate::leanh::lean_ctor_get(v_s_5170_, 6);
                v_powIdentityInst_x3f_5178_ = crate::leanh::lean_ctor_get(v_s_5170_, 7);
                v_denoteEntries_5179_ = crate::leanh::lean_ctor_get(v_s_5170_, 8);
                v_nextId_5180_ = crate::leanh::lean_ctor_get(v_s_5170_, 9);
                v_steps_5181_ = crate::leanh::lean_ctor_get(v_s_5170_, 10);
                v_queue_5182_ = crate::leanh::lean_ctor_get(v_s_5170_, 11);
                v_basis_5183_ = crate::leanh::lean_ctor_get(v_s_5170_, 12);
                v_diseqs_5184_ = crate::leanh::lean_ctor_get(v_s_5170_, 13);
                v_recheck_5185_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_5170_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                );
                v_invSet_5186_ = crate::leanh::lean_ctor_get(v_s_5170_, 14);
                v_powIdentityVarCount_5187_ = crate::leanh::lean_ctor_get(v_s_5170_, 15);
                v_numEq0_x3f_5188_ = crate::leanh::lean_ctor_get(v_s_5170_, 16);
                v_numEq0Updated_5189_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_5170_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_5221_ = (!crate::leanh::lean_is_exclusive(v_s_5170_)) as u8;
                if v_isSharedCheck_5221_ == 0 {
                    v___x_5191_ = v_s_5170_;
                    v_isShared_5192_ = v_isSharedCheck_5221_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_numEq0_x3f_5188_);
                    crate::leanh::lean_inc(v_powIdentityVarCount_5187_);
                    crate::leanh::lean_inc(v_invSet_5186_);
                    crate::leanh::lean_inc(v_diseqs_5184_);
                    crate::leanh::lean_inc(v_basis_5183_);
                    crate::leanh::lean_inc(v_queue_5182_);
                    crate::leanh::lean_inc(v_steps_5181_);
                    crate::leanh::lean_inc(v_nextId_5180_);
                    crate::leanh::lean_inc(v_denoteEntries_5179_);
                    crate::leanh::lean_inc(v_powIdentityInst_x3f_5178_);
                    crate::leanh::lean_inc(v_fieldInst_x3f_5177_);
                    crate::leanh::lean_inc(v_noZeroDivInst_x3f_5176_);
                    crate::leanh::lean_inc(v_commRingInst_5175_);
                    crate::leanh::lean_inc(v_commSemiringInst_5174_);
                    crate::leanh::lean_inc(v_semiringId_x3f_5173_);
                    crate::leanh::lean_inc(v_invFn_x3f_5172_);
                    crate::leanh::lean_inc(v_toRing_5171_);
                    crate::leanh::lean_dec(v_s_5170_);
                    v___x_5191_ = crate::leanh::lean_box(0);
                    v_isShared_5192_ = v_isSharedCheck_5221_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_id_5193_ = crate::leanh::lean_ctor_get(v_toRing_5171_, 0);
                v_type_5194_ = crate::leanh::lean_ctor_get(v_toRing_5171_, 1);
                v_u_5195_ = crate::leanh::lean_ctor_get(v_toRing_5171_, 2);
                v_ringInst_5196_ = crate::leanh::lean_ctor_get(v_toRing_5171_, 3);
                v_semiringInst_5197_ = crate::leanh::lean_ctor_get(v_toRing_5171_, 4);
                v_charInst_x3f_5198_ = crate::leanh::lean_ctor_get(v_toRing_5171_, 5);
                v_addFn_x3f_5199_ = crate::leanh::lean_ctor_get(v_toRing_5171_, 6);
                v_subFn_x3f_5200_ = crate::leanh::lean_ctor_get(v_toRing_5171_, 8);
                v_negFn_x3f_5201_ = crate::leanh::lean_ctor_get(v_toRing_5171_, 9);
                v_powFn_x3f_5202_ = crate::leanh::lean_ctor_get(v_toRing_5171_, 10);
                v_intCastFn_x3f_5203_ = crate::leanh::lean_ctor_get(v_toRing_5171_, 11);
                v_natCastFn_x3f_5204_ = crate::leanh::lean_ctor_get(v_toRing_5171_, 12);
                v_one_x3f_5205_ = crate::leanh::lean_ctor_get(v_toRing_5171_, 13);
                v_vars_5206_ = crate::leanh::lean_ctor_get(v_toRing_5171_, 14);
                v_varMap_5207_ = crate::leanh::lean_ctor_get(v_toRing_5171_, 15);
                v_denote_5208_ = crate::leanh::lean_ctor_get(v_toRing_5171_, 16);
                v_isSharedCheck_5219_ = (!crate::leanh::lean_is_exclusive(v_toRing_5171_)) as u8;
                if v_isSharedCheck_5219_ == 0 {
                    v_unused_5220_ = crate::leanh::lean_ctor_get(v_toRing_5171_, 7);
                    crate::leanh::lean_dec(v_unused_5220_);
                    v___x_5210_ = v_toRing_5171_;
                    v_isShared_5211_ = v_isSharedCheck_5219_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_denote_5208_);
                    crate::leanh::lean_inc(v_varMap_5207_);
                    crate::leanh::lean_inc(v_vars_5206_);
                    crate::leanh::lean_inc(v_one_x3f_5205_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_5204_);
                    crate::leanh::lean_inc(v_intCastFn_x3f_5203_);
                    crate::leanh::lean_inc(v_powFn_x3f_5202_);
                    crate::leanh::lean_inc(v_negFn_x3f_5201_);
                    crate::leanh::lean_inc(v_subFn_x3f_5200_);
                    crate::leanh::lean_inc(v_addFn_x3f_5199_);
                    crate::leanh::lean_inc(v_charInst_x3f_5198_);
                    crate::leanh::lean_inc(v_semiringInst_5197_);
                    crate::leanh::lean_inc(v_ringInst_5196_);
                    crate::leanh::lean_inc(v_u_5195_);
                    crate::leanh::lean_inc(v_type_5194_);
                    crate::leanh::lean_inc(v_id_5193_);
                    crate::leanh::lean_dec(v_toRing_5171_);
                    v___x_5210_ = crate::leanh::lean_box(0);
                    v_isShared_5211_ = v_isSharedCheck_5219_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5212_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5212_, 0, v_a_5169_);
                if v_isShared_5211_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5210_, 7, v___x_5212_);
                    v___x_5214_ = v___x_5210_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5218_ = crate::leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 0, v_id_5193_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 1, v_type_5194_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 2, v_u_5195_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 3, v_ringInst_5196_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 4, v_semiringInst_5197_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 5, v_charInst_x3f_5198_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 6, v_addFn_x3f_5199_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 7, v___x_5212_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 8, v_subFn_x3f_5200_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 9, v_negFn_x3f_5201_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 10, v_powFn_x3f_5202_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 11, v_intCastFn_x3f_5203_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 12, v_natCastFn_x3f_5204_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 13, v_one_x3f_5205_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 14, v_vars_5206_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 15, v_varMap_5207_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 16, v_denote_5208_);
                    v___x_5214_ = v_reuseFailAlloc_5218_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5192_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5191_, 0, v___x_5214_);
                    v___x_5216_ = v___x_5191_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5217_ = crate::leanh::lean_alloc_ctor(0, 17, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5217_, 0, v___x_5214_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5217_, 1, v_invFn_x3f_5172_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5217_, 2, v_semiringId_x3f_5173_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5217_,
                        3,
                        v_commSemiringInst_5174_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5217_, 4, v_commRingInst_5175_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5217_,
                        5,
                        v_noZeroDivInst_x3f_5176_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5217_, 6, v_fieldInst_x3f_5177_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5217_,
                        7,
                        v_powIdentityInst_x3f_5178_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5217_, 8, v_denoteEntries_5179_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5217_, 9, v_nextId_5180_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5217_, 10, v_steps_5181_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5217_, 11, v_queue_5182_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5217_, 12, v_basis_5183_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5217_, 13, v_diseqs_5184_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5217_, 14, v_invSet_5186_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5217_,
                        15,
                        v_powIdentityVarCount_5187_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5217_, 16, v_numEq0_x3f_5188_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5217_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                        v_recheck_5185_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5217_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                        v_numEq0Updated_5189_,
                    );
                    v___x_5216_ = v_reuseFailAlloc_5217_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5216_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(
    mut v___y_5222_: *mut crate::leanh::LeanObject,
    mut v___y_5223_: *mut crate::leanh::LeanObject,
    mut v___y_5224_: *mut crate::leanh::LeanObject,
    mut v___y_5225_: *mut crate::leanh::LeanObject,
    mut v___y_5226_: *mut crate::leanh::LeanObject,
    mut v___y_5227_: *mut crate::leanh::LeanObject,
    mut v___y_5228_: *mut crate::leanh::LeanObject,
    mut v___y_5229_: *mut crate::leanh::LeanObject,
    mut v___y_5230_: *mut crate::leanh::LeanObject,
    mut v___y_5231_: *mut crate::leanh::LeanObject,
    mut v___y_5232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5238_: u8 = 0;
    let mut v_toRing_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expectedInst_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5264_: u8 = 0;
    let mut v___x_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5268_: u8 = 0;
    let mut v_unused_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5273_: u8 = 0;
    let mut v___x_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5277_: u8 = 0;
    let mut v_isSharedCheck_5278_: u8 = 0;
    let mut v_a_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5282_: u8 = 0;
    let mut v___x_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5286_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5234_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(
                    v___y_5222_,
                    v___y_5223_,
                    v___y_5224_,
                    v___y_5225_,
                    v___y_5226_,
                    v___y_5227_,
                    v___y_5228_,
                    v___y_5229_,
                    v___y_5230_,
                    v___y_5231_,
                    v___y_5232_,
                );
                if crate::leanh::lean_obj_tag(v___x_5234_) == 0 {
                    v_a_5235_ = crate::leanh::lean_ctor_get(v___x_5234_, 0);
                    v_isSharedCheck_5278_ = (!crate::leanh::lean_is_exclusive(v___x_5234_)) as u8;
                    if v_isSharedCheck_5278_ == 0 {
                        v___x_5237_ = v___x_5234_;
                        v_isShared_5238_ = v_isSharedCheck_5278_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5235_);
                        crate::leanh::lean_dec(v___x_5234_);
                        v___x_5237_ = crate::leanh::lean_box(0);
                        v_isShared_5238_ = v_isSharedCheck_5278_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5279_ = crate::leanh::lean_ctor_get(v___x_5234_, 0);
                    v_isSharedCheck_5286_ = (!crate::leanh::lean_is_exclusive(v___x_5234_)) as u8;
                    if v_isSharedCheck_5286_ == 0 {
                        v___x_5281_ = v___x_5234_;
                        v_isShared_5282_ = v_isSharedCheck_5286_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5279_);
                        crate::leanh::lean_dec(v___x_5234_);
                        v___x_5281_ = crate::leanh::lean_box(0);
                        v_isShared_5282_ = v_isSharedCheck_5286_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_toRing_5239_ = crate::leanh::lean_ctor_get(v_a_5235_, 0);
                crate::leanh::lean_inc_ref(v_toRing_5239_);
                crate::leanh::lean_dec(v_a_5235_);
                v_mulFn_x3f_5240_ = crate::leanh::lean_ctor_get(v_toRing_5239_, 7);
                if crate::leanh::lean_obj_tag(v_mulFn_x3f_5240_) == 1 {
                    crate::leanh::lean_inc_ref(v_mulFn_x3f_5240_);
                    crate::leanh::lean_dec_ref(v_toRing_5239_);
                    v_val_5241_ = crate::leanh::lean_ctor_get(v_mulFn_x3f_5240_, 0);
                    crate::leanh::lean_inc(v_val_5241_);
                    crate::leanh::lean_dec_ref_known(v_mulFn_x3f_5240_, 1);
                    if v_isShared_5238_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5237_, 0, v_val_5241_);
                        v___x_5243_ = v___x_5237_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5244_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5244_, 0, v_val_5241_);
                        v___x_5243_ = v_reuseFailAlloc_5244_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5237_);
                    v_type_5245_ = crate::leanh::lean_ctor_get(v_toRing_5239_, 1);
                    crate::leanh::lean_inc_ref_n(v_type_5245_, 3);
                    v_u_5246_ = crate::leanh::lean_ctor_get(v_toRing_5239_, 2);
                    crate::leanh::lean_inc_n(v_u_5246_, 2);
                    v_semiringInst_5247_ = crate::leanh::lean_ctor_get(v_toRing_5239_, 4);
                    crate::leanh::lean_inc_ref(v_semiringInst_5247_);
                    crate::leanh::lean_dec_ref(v_toRing_5239_);
                    v___x_5248_ =
                        l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1;
                    v___x_5249_ = crate::leanh::lean_box(0);
                    v___x_5250_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5250_, 0, v_u_5246_);
                    crate::leanh::lean_ctor_set(v___x_5250_, 1, v___x_5249_);
                    crate::leanh::lean_inc_ref(v___x_5250_);
                    v___x_5251_ = l_Lean_mkConst(v___x_5248_, v___x_5250_);
                    v___x_5252_ =
                        l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3;
                    v___x_5253_ = l_Lean_mkConst(v___x_5252_, v___x_5250_);
                    v___x_5254_ = l_Lean_mkAppB(v___x_5253_, v_type_5245_, v_semiringInst_5247_);
                    v_expectedInst_5255_ = l_Lean_mkAppB(v___x_5251_, v_type_5245_, v___x_5254_);
                    v___x_5256_ =
                        l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__5;
                    v___x_5257_ =
                        l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7;
                    v___x_5258_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(v_type_5245_, v_u_5246_, v___x_5256_, v___x_5257_, v_expectedInst_5255_, v___y_5222_, v___y_5223_, v___y_5224_, v___y_5225_, v___y_5226_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_);
                    if crate::leanh::lean_obj_tag(v___x_5258_) == 0 {
                        v_a_5259_ = crate::leanh::lean_ctor_get(v___x_5258_, 0);
                        crate::leanh::lean_inc_n(v_a_5259_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_5258_, 1);
                        v___f_5260_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___lam__0 as *mut core::ffi::c_void, 2, 1);
                        crate::leanh::lean_closure_set(v___f_5260_, 0, v_a_5259_);
                        v___x_5261_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(
                            v___f_5260_,
                            v___y_5222_,
                            v___y_5223_,
                            v___y_5224_,
                            v___y_5225_,
                            v___y_5226_,
                            v___y_5227_,
                            v___y_5228_,
                            v___y_5229_,
                            v___y_5230_,
                            v___y_5231_,
                            v___y_5232_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5261_) == 0 {
                            v_isSharedCheck_5268_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5261_)) as u8;
                            if v_isSharedCheck_5268_ == 0 {
                                v_unused_5269_ = crate::leanh::lean_ctor_get(v___x_5261_, 0);
                                crate::leanh::lean_dec(v_unused_5269_);
                                v___x_5263_ = v___x_5261_;
                                v_isShared_5264_ = v_isSharedCheck_5268_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_5261_);
                                v___x_5263_ = crate::leanh::lean_box(0);
                                v_isShared_5264_ = v_isSharedCheck_5268_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5259_);
                            v_a_5270_ = crate::leanh::lean_ctor_get(v___x_5261_, 0);
                            v_isSharedCheck_5277_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5261_)) as u8;
                            if v_isSharedCheck_5277_ == 0 {
                                v___x_5272_ = v___x_5261_;
                                v_isShared_5273_ = v_isSharedCheck_5277_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5270_);
                                crate::leanh::lean_dec(v___x_5261_);
                                v___x_5272_ = crate::leanh::lean_box(0);
                                v_isShared_5273_ = v_isSharedCheck_5277_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        return v___x_5258_;
                    }
                }
            }
            2 => {
                return v___x_5243_;
            }
            3 => {
                if v_isShared_5264_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5263_, 0, v_a_5259_);
                    v___x_5266_ = v___x_5263_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5267_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5267_, 0, v_a_5259_);
                    v___x_5266_ = v_reuseFailAlloc_5267_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5266_;
            }
            5 => {
                if v_isShared_5273_ == 0 {
                    v___x_5275_ = v___x_5272_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5276_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5276_, 0, v_a_5270_);
                    v___x_5275_ = v_reuseFailAlloc_5276_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5275_;
            }
            7 => {
                if v_isShared_5282_ == 0 {
                    v___x_5284_ = v___x_5281_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5285_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5285_, 0, v_a_5279_);
                    v___x_5284_ = v_reuseFailAlloc_5285_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5284_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___boxed(
    mut v___y_5287_: *mut crate::leanh::LeanObject,
    mut v___y_5288_: *mut crate::leanh::LeanObject,
    mut v___y_5289_: *mut crate::leanh::LeanObject,
    mut v___y_5290_: *mut crate::leanh::LeanObject,
    mut v___y_5291_: *mut crate::leanh::LeanObject,
    mut v___y_5292_: *mut crate::leanh::LeanObject,
    mut v___y_5293_: *mut crate::leanh::LeanObject,
    mut v___y_5294_: *mut crate::leanh::LeanObject,
    mut v___y_5295_: *mut crate::leanh::LeanObject,
    mut v___y_5296_: *mut crate::leanh::LeanObject,
    mut v___y_5297_: *mut crate::leanh::LeanObject,
    mut v___y_5298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5299_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(v___y_5287_, v___y_5288_, v___y_5289_, v___y_5290_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_, v___y_5295_, v___y_5296_, v___y_5297_);
    crate::leanh::lean_dec(v___y_5297_);
    crate::leanh::lean_dec_ref(v___y_5296_);
    crate::leanh::lean_dec(v___y_5295_);
    crate::leanh::lean_dec_ref(v___y_5294_);
    crate::leanh::lean_dec(v___y_5293_);
    crate::leanh::lean_dec_ref(v___y_5292_);
    crate::leanh::lean_dec(v___y_5291_);
    crate::leanh::lean_dec_ref(v___y_5290_);
    crate::leanh::lean_dec(v___y_5289_);
    crate::leanh::lean_dec(v___y_5288_);
    crate::leanh::lean_dec(v___y_5287_);
    return v_res_5299_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0(
    mut v_a_5300_: *mut crate::leanh::LeanObject,
    mut v_s_5301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toRing_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recheck_5316_: u8 = 0;
    let mut v_invSet_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_5320_: u8 = 0;
    let mut v___x_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5323_: u8 = 0;
    let mut v_id_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5342_: u8 = 0;
    let mut v___x_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5350_: u8 = 0;
    let mut v_unused_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5352_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_5302_ = crate::leanh::lean_ctor_get(v_s_5301_, 0);
                v_invFn_x3f_5303_ = crate::leanh::lean_ctor_get(v_s_5301_, 1);
                v_semiringId_x3f_5304_ = crate::leanh::lean_ctor_get(v_s_5301_, 2);
                v_commSemiringInst_5305_ = crate::leanh::lean_ctor_get(v_s_5301_, 3);
                v_commRingInst_5306_ = crate::leanh::lean_ctor_get(v_s_5301_, 4);
                v_noZeroDivInst_x3f_5307_ = crate::leanh::lean_ctor_get(v_s_5301_, 5);
                v_fieldInst_x3f_5308_ = crate::leanh::lean_ctor_get(v_s_5301_, 6);
                v_powIdentityInst_x3f_5309_ = crate::leanh::lean_ctor_get(v_s_5301_, 7);
                v_denoteEntries_5310_ = crate::leanh::lean_ctor_get(v_s_5301_, 8);
                v_nextId_5311_ = crate::leanh::lean_ctor_get(v_s_5301_, 9);
                v_steps_5312_ = crate::leanh::lean_ctor_get(v_s_5301_, 10);
                v_queue_5313_ = crate::leanh::lean_ctor_get(v_s_5301_, 11);
                v_basis_5314_ = crate::leanh::lean_ctor_get(v_s_5301_, 12);
                v_diseqs_5315_ = crate::leanh::lean_ctor_get(v_s_5301_, 13);
                v_recheck_5316_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_5301_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                );
                v_invSet_5317_ = crate::leanh::lean_ctor_get(v_s_5301_, 14);
                v_powIdentityVarCount_5318_ = crate::leanh::lean_ctor_get(v_s_5301_, 15);
                v_numEq0_x3f_5319_ = crate::leanh::lean_ctor_get(v_s_5301_, 16);
                v_numEq0Updated_5320_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_5301_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_5352_ = (!crate::leanh::lean_is_exclusive(v_s_5301_)) as u8;
                if v_isSharedCheck_5352_ == 0 {
                    v___x_5322_ = v_s_5301_;
                    v_isShared_5323_ = v_isSharedCheck_5352_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_numEq0_x3f_5319_);
                    crate::leanh::lean_inc(v_powIdentityVarCount_5318_);
                    crate::leanh::lean_inc(v_invSet_5317_);
                    crate::leanh::lean_inc(v_diseqs_5315_);
                    crate::leanh::lean_inc(v_basis_5314_);
                    crate::leanh::lean_inc(v_queue_5313_);
                    crate::leanh::lean_inc(v_steps_5312_);
                    crate::leanh::lean_inc(v_nextId_5311_);
                    crate::leanh::lean_inc(v_denoteEntries_5310_);
                    crate::leanh::lean_inc(v_powIdentityInst_x3f_5309_);
                    crate::leanh::lean_inc(v_fieldInst_x3f_5308_);
                    crate::leanh::lean_inc(v_noZeroDivInst_x3f_5307_);
                    crate::leanh::lean_inc(v_commRingInst_5306_);
                    crate::leanh::lean_inc(v_commSemiringInst_5305_);
                    crate::leanh::lean_inc(v_semiringId_x3f_5304_);
                    crate::leanh::lean_inc(v_invFn_x3f_5303_);
                    crate::leanh::lean_inc(v_toRing_5302_);
                    crate::leanh::lean_dec(v_s_5301_);
                    v___x_5322_ = crate::leanh::lean_box(0);
                    v_isShared_5323_ = v_isSharedCheck_5352_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_id_5324_ = crate::leanh::lean_ctor_get(v_toRing_5302_, 0);
                v_type_5325_ = crate::leanh::lean_ctor_get(v_toRing_5302_, 1);
                v_u_5326_ = crate::leanh::lean_ctor_get(v_toRing_5302_, 2);
                v_ringInst_5327_ = crate::leanh::lean_ctor_get(v_toRing_5302_, 3);
                v_semiringInst_5328_ = crate::leanh::lean_ctor_get(v_toRing_5302_, 4);
                v_charInst_x3f_5329_ = crate::leanh::lean_ctor_get(v_toRing_5302_, 5);
                v_mulFn_x3f_5330_ = crate::leanh::lean_ctor_get(v_toRing_5302_, 7);
                v_subFn_x3f_5331_ = crate::leanh::lean_ctor_get(v_toRing_5302_, 8);
                v_negFn_x3f_5332_ = crate::leanh::lean_ctor_get(v_toRing_5302_, 9);
                v_powFn_x3f_5333_ = crate::leanh::lean_ctor_get(v_toRing_5302_, 10);
                v_intCastFn_x3f_5334_ = crate::leanh::lean_ctor_get(v_toRing_5302_, 11);
                v_natCastFn_x3f_5335_ = crate::leanh::lean_ctor_get(v_toRing_5302_, 12);
                v_one_x3f_5336_ = crate::leanh::lean_ctor_get(v_toRing_5302_, 13);
                v_vars_5337_ = crate::leanh::lean_ctor_get(v_toRing_5302_, 14);
                v_varMap_5338_ = crate::leanh::lean_ctor_get(v_toRing_5302_, 15);
                v_denote_5339_ = crate::leanh::lean_ctor_get(v_toRing_5302_, 16);
                v_isSharedCheck_5350_ = (!crate::leanh::lean_is_exclusive(v_toRing_5302_)) as u8;
                if v_isSharedCheck_5350_ == 0 {
                    v_unused_5351_ = crate::leanh::lean_ctor_get(v_toRing_5302_, 6);
                    crate::leanh::lean_dec(v_unused_5351_);
                    v___x_5341_ = v_toRing_5302_;
                    v_isShared_5342_ = v_isSharedCheck_5350_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_denote_5339_);
                    crate::leanh::lean_inc(v_varMap_5338_);
                    crate::leanh::lean_inc(v_vars_5337_);
                    crate::leanh::lean_inc(v_one_x3f_5336_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_5335_);
                    crate::leanh::lean_inc(v_intCastFn_x3f_5334_);
                    crate::leanh::lean_inc(v_powFn_x3f_5333_);
                    crate::leanh::lean_inc(v_negFn_x3f_5332_);
                    crate::leanh::lean_inc(v_subFn_x3f_5331_);
                    crate::leanh::lean_inc(v_mulFn_x3f_5330_);
                    crate::leanh::lean_inc(v_charInst_x3f_5329_);
                    crate::leanh::lean_inc(v_semiringInst_5328_);
                    crate::leanh::lean_inc(v_ringInst_5327_);
                    crate::leanh::lean_inc(v_u_5326_);
                    crate::leanh::lean_inc(v_type_5325_);
                    crate::leanh::lean_inc(v_id_5324_);
                    crate::leanh::lean_dec(v_toRing_5302_);
                    v___x_5341_ = crate::leanh::lean_box(0);
                    v_isShared_5342_ = v_isSharedCheck_5350_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5343_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5343_, 0, v_a_5300_);
                if v_isShared_5342_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5341_, 6, v___x_5343_);
                    v___x_5345_ = v___x_5341_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5349_ = crate::leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 0, v_id_5324_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 1, v_type_5325_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 2, v_u_5326_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 3, v_ringInst_5327_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 4, v_semiringInst_5328_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 5, v_charInst_x3f_5329_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 6, v___x_5343_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 7, v_mulFn_x3f_5330_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 8, v_subFn_x3f_5331_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 9, v_negFn_x3f_5332_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 10, v_powFn_x3f_5333_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 11, v_intCastFn_x3f_5334_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 12, v_natCastFn_x3f_5335_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 13, v_one_x3f_5336_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 14, v_vars_5337_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 15, v_varMap_5338_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 16, v_denote_5339_);
                    v___x_5345_ = v_reuseFailAlloc_5349_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5323_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5322_, 0, v___x_5345_);
                    v___x_5347_ = v___x_5322_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5348_ = crate::leanh::lean_alloc_ctor(0, 17, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 0, v___x_5345_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 1, v_invFn_x3f_5303_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 2, v_semiringId_x3f_5304_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5348_,
                        3,
                        v_commSemiringInst_5305_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 4, v_commRingInst_5306_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5348_,
                        5,
                        v_noZeroDivInst_x3f_5307_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 6, v_fieldInst_x3f_5308_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5348_,
                        7,
                        v_powIdentityInst_x3f_5309_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 8, v_denoteEntries_5310_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 9, v_nextId_5311_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 10, v_steps_5312_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 11, v_queue_5313_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 12, v_basis_5314_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 13, v_diseqs_5315_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 14, v_invSet_5317_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5348_,
                        15,
                        v_powIdentityVarCount_5318_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 16, v_numEq0_x3f_5319_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5348_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                        v_recheck_5316_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5348_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                        v_numEq0Updated_5320_,
                    );
                    v___x_5347_ = v_reuseFailAlloc_5348_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5347_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(
    mut v___y_5353_: *mut crate::leanh::LeanObject,
    mut v___y_5354_: *mut crate::leanh::LeanObject,
    mut v___y_5355_: *mut crate::leanh::LeanObject,
    mut v___y_5356_: *mut crate::leanh::LeanObject,
    mut v___y_5357_: *mut crate::leanh::LeanObject,
    mut v___y_5358_: *mut crate::leanh::LeanObject,
    mut v___y_5359_: *mut crate::leanh::LeanObject,
    mut v___y_5360_: *mut crate::leanh::LeanObject,
    mut v___y_5361_: *mut crate::leanh::LeanObject,
    mut v___y_5362_: *mut crate::leanh::LeanObject,
    mut v___y_5363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5369_: u8 = 0;
    let mut v_toRing_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expectedInst_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5395_: u8 = 0;
    let mut v___x_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5399_: u8 = 0;
    let mut v_unused_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5404_: u8 = 0;
    let mut v___x_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5408_: u8 = 0;
    let mut v_isSharedCheck_5409_: u8 = 0;
    let mut v_a_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5413_: u8 = 0;
    let mut v___x_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5417_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5365_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(
                    v___y_5353_,
                    v___y_5354_,
                    v___y_5355_,
                    v___y_5356_,
                    v___y_5357_,
                    v___y_5358_,
                    v___y_5359_,
                    v___y_5360_,
                    v___y_5361_,
                    v___y_5362_,
                    v___y_5363_,
                );
                if crate::leanh::lean_obj_tag(v___x_5365_) == 0 {
                    v_a_5366_ = crate::leanh::lean_ctor_get(v___x_5365_, 0);
                    v_isSharedCheck_5409_ = (!crate::leanh::lean_is_exclusive(v___x_5365_)) as u8;
                    if v_isSharedCheck_5409_ == 0 {
                        v___x_5368_ = v___x_5365_;
                        v_isShared_5369_ = v_isSharedCheck_5409_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5366_);
                        crate::leanh::lean_dec(v___x_5365_);
                        v___x_5368_ = crate::leanh::lean_box(0);
                        v_isShared_5369_ = v_isSharedCheck_5409_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5410_ = crate::leanh::lean_ctor_get(v___x_5365_, 0);
                    v_isSharedCheck_5417_ = (!crate::leanh::lean_is_exclusive(v___x_5365_)) as u8;
                    if v_isSharedCheck_5417_ == 0 {
                        v___x_5412_ = v___x_5365_;
                        v_isShared_5413_ = v_isSharedCheck_5417_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5410_);
                        crate::leanh::lean_dec(v___x_5365_);
                        v___x_5412_ = crate::leanh::lean_box(0);
                        v_isShared_5413_ = v_isSharedCheck_5417_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_toRing_5370_ = crate::leanh::lean_ctor_get(v_a_5366_, 0);
                crate::leanh::lean_inc_ref(v_toRing_5370_);
                crate::leanh::lean_dec(v_a_5366_);
                v_addFn_x3f_5371_ = crate::leanh::lean_ctor_get(v_toRing_5370_, 6);
                if crate::leanh::lean_obj_tag(v_addFn_x3f_5371_) == 1 {
                    crate::leanh::lean_inc_ref(v_addFn_x3f_5371_);
                    crate::leanh::lean_dec_ref(v_toRing_5370_);
                    v_val_5372_ = crate::leanh::lean_ctor_get(v_addFn_x3f_5371_, 0);
                    crate::leanh::lean_inc(v_val_5372_);
                    crate::leanh::lean_dec_ref_known(v_addFn_x3f_5371_, 1);
                    if v_isShared_5369_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5368_, 0, v_val_5372_);
                        v___x_5374_ = v___x_5368_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5375_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5375_, 0, v_val_5372_);
                        v___x_5374_ = v_reuseFailAlloc_5375_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5368_);
                    v_type_5376_ = crate::leanh::lean_ctor_get(v_toRing_5370_, 1);
                    crate::leanh::lean_inc_ref_n(v_type_5376_, 3);
                    v_u_5377_ = crate::leanh::lean_ctor_get(v_toRing_5370_, 2);
                    crate::leanh::lean_inc_n(v_u_5377_, 2);
                    v_semiringInst_5378_ = crate::leanh::lean_ctor_get(v_toRing_5370_, 4);
                    crate::leanh::lean_inc_ref(v_semiringInst_5378_);
                    crate::leanh::lean_dec_ref(v_toRing_5370_);
                    v___x_5379_ =
                        l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1;
                    v___x_5380_ = crate::leanh::lean_box(0);
                    v___x_5381_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5381_, 0, v_u_5377_);
                    crate::leanh::lean_ctor_set(v___x_5381_, 1, v___x_5380_);
                    crate::leanh::lean_inc_ref(v___x_5381_);
                    v___x_5382_ = l_Lean_mkConst(v___x_5379_, v___x_5381_);
                    v___x_5383_ =
                        l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4;
                    v___x_5384_ = l_Lean_mkConst(v___x_5383_, v___x_5381_);
                    v___x_5385_ = l_Lean_mkAppB(v___x_5384_, v_type_5376_, v_semiringInst_5378_);
                    v_expectedInst_5386_ = l_Lean_mkAppB(v___x_5382_, v_type_5376_, v___x_5385_);
                    v___x_5387_ =
                        l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__6;
                    v___x_5388_ =
                        l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8;
                    v___x_5389_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(v_type_5376_, v_u_5377_, v___x_5387_, v___x_5388_, v_expectedInst_5386_, v___y_5353_, v___y_5354_, v___y_5355_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_, v___y_5363_);
                    if crate::leanh::lean_obj_tag(v___x_5389_) == 0 {
                        v_a_5390_ = crate::leanh::lean_ctor_get(v___x_5389_, 0);
                        crate::leanh::lean_inc_n(v_a_5390_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_5389_, 1);
                        v___f_5391_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0 as *mut core::ffi::c_void, 2, 1);
                        crate::leanh::lean_closure_set(v___f_5391_, 0, v_a_5390_);
                        v___x_5392_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(
                            v___f_5391_,
                            v___y_5353_,
                            v___y_5354_,
                            v___y_5355_,
                            v___y_5356_,
                            v___y_5357_,
                            v___y_5358_,
                            v___y_5359_,
                            v___y_5360_,
                            v___y_5361_,
                            v___y_5362_,
                            v___y_5363_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5392_) == 0 {
                            v_isSharedCheck_5399_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5392_)) as u8;
                            if v_isSharedCheck_5399_ == 0 {
                                v_unused_5400_ = crate::leanh::lean_ctor_get(v___x_5392_, 0);
                                crate::leanh::lean_dec(v_unused_5400_);
                                v___x_5394_ = v___x_5392_;
                                v_isShared_5395_ = v_isSharedCheck_5399_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_5392_);
                                v___x_5394_ = crate::leanh::lean_box(0);
                                v_isShared_5395_ = v_isSharedCheck_5399_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5390_);
                            v_a_5401_ = crate::leanh::lean_ctor_get(v___x_5392_, 0);
                            v_isSharedCheck_5408_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5392_)) as u8;
                            if v_isSharedCheck_5408_ == 0 {
                                v___x_5403_ = v___x_5392_;
                                v_isShared_5404_ = v_isSharedCheck_5408_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5401_);
                                crate::leanh::lean_dec(v___x_5392_);
                                v___x_5403_ = crate::leanh::lean_box(0);
                                v_isShared_5404_ = v_isSharedCheck_5408_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        return v___x_5389_;
                    }
                }
            }
            2 => {
                return v___x_5374_;
            }
            3 => {
                if v_isShared_5395_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5394_, 0, v_a_5390_);
                    v___x_5397_ = v___x_5394_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5398_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5398_, 0, v_a_5390_);
                    v___x_5397_ = v_reuseFailAlloc_5398_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5397_;
            }
            5 => {
                if v_isShared_5404_ == 0 {
                    v___x_5406_ = v___x_5403_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5407_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5407_, 0, v_a_5401_);
                    v___x_5406_ = v_reuseFailAlloc_5407_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5406_;
            }
            7 => {
                if v_isShared_5413_ == 0 {
                    v___x_5415_ = v___x_5412_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5416_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5416_, 0, v_a_5410_);
                    v___x_5415_ = v_reuseFailAlloc_5416_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5415_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___boxed(
    mut v___y_5418_: *mut crate::leanh::LeanObject,
    mut v___y_5419_: *mut crate::leanh::LeanObject,
    mut v___y_5420_: *mut crate::leanh::LeanObject,
    mut v___y_5421_: *mut crate::leanh::LeanObject,
    mut v___y_5422_: *mut crate::leanh::LeanObject,
    mut v___y_5423_: *mut crate::leanh::LeanObject,
    mut v___y_5424_: *mut crate::leanh::LeanObject,
    mut v___y_5425_: *mut crate::leanh::LeanObject,
    mut v___y_5426_: *mut crate::leanh::LeanObject,
    mut v___y_5427_: *mut crate::leanh::LeanObject,
    mut v___y_5428_: *mut crate::leanh::LeanObject,
    mut v___y_5429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5430_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_);
    crate::leanh::lean_dec(v___y_5428_);
    crate::leanh::lean_dec_ref(v___y_5427_);
    crate::leanh::lean_dec(v___y_5426_);
    crate::leanh::lean_dec_ref(v___y_5425_);
    crate::leanh::lean_dec(v___y_5424_);
    crate::leanh::lean_dec_ref(v___y_5423_);
    crate::leanh::lean_dec(v___y_5422_);
    crate::leanh::lean_dec_ref(v___y_5421_);
    crate::leanh::lean_dec(v___y_5420_);
    crate::leanh::lean_dec(v___y_5419_);
    crate::leanh::lean_dec(v___y_5418_);
    return v_res_5430_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(
    mut v_type_5431_: *mut crate::leanh::LeanObject,
    mut v_u_5432_: *mut crate::leanh::LeanObject,
    mut v_instDeclName_5433_: *mut crate::leanh::LeanObject,
    mut v_declName_5434_: *mut crate::leanh::LeanObject,
    mut v_expectedInst_5435_: *mut crate::leanh::LeanObject,
    mut v___y_5436_: *mut crate::leanh::LeanObject,
    mut v___y_5437_: *mut crate::leanh::LeanObject,
    mut v___y_5438_: *mut crate::leanh::LeanObject,
    mut v___y_5439_: *mut crate::leanh::LeanObject,
    mut v___y_5440_: *mut crate::leanh::LeanObject,
    mut v___y_5441_: *mut crate::leanh::LeanObject,
    mut v___y_5442_: *mut crate::leanh::LeanObject,
    mut v___y_5443_: *mut crate::leanh::LeanObject,
    mut v___y_5444_: *mut crate::leanh::LeanObject,
    mut v___y_5445_: *mut crate::leanh::LeanObject,
    mut v___y_5446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5463_: u8 = 0;
    let mut v___x_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5467_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5448_ = crate::leanh::lean_box(0);
                v___x_5449_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5449_, 0, v_u_5432_);
                crate::leanh::lean_ctor_set(v___x_5449_, 1, v___x_5448_);
                crate::leanh::lean_inc_ref(v___x_5449_);
                v___x_5450_ = l_Lean_mkConst(v_instDeclName_5433_, v___x_5449_);
                crate::leanh::lean_inc_ref(v_type_5431_);
                v___x_5451_ = l_Lean_Expr_app___override(v___x_5450_, v_type_5431_);
                v___x_5452_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_5451_, v___y_5443_, v___y_5444_, v___y_5445_, v___y_5446_);
                if crate::leanh::lean_obj_tag(v___x_5452_) == 0 {
                    v_a_5453_ = crate::leanh::lean_ctor_get(v___x_5452_, 0);
                    crate::leanh::lean_inc_n(v_a_5453_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_5452_, 1);
                    crate::leanh::lean_inc(v_declName_5434_);
                    v___x_5454_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(
                        v_declName_5434_,
                        v_a_5453_,
                        v_expectedInst_5435_,
                        v___y_5443_,
                        v___y_5444_,
                        v___y_5445_,
                        v___y_5446_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5454_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5454_, 1);
                        v___x_5455_ = l_Lean_mkConst(v_declName_5434_, v___x_5449_);
                        v___x_5456_ = l_Lean_mkAppB(v___x_5455_, v_type_5431_, v_a_5453_);
                        v___x_5457_ = l_Lean_Meta_Sym_canon(
                            v___x_5456_,
                            v___y_5441_,
                            v___y_5442_,
                            v___y_5443_,
                            v___y_5444_,
                            v___y_5445_,
                            v___y_5446_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5457_) == 0 {
                            v_a_5458_ = crate::leanh::lean_ctor_get(v___x_5457_, 0);
                            crate::leanh::lean_inc(v_a_5458_);
                            crate::leanh::lean_dec_ref_known(v___x_5457_, 1);
                            v___x_5459_ =
                                l_Lean_Meta_Sym_shareCommon___redArg(v_a_5458_, v___y_5442_);
                            return v___x_5459_;
                        } else {
                            return v___x_5457_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5453_);
                        crate::leanh::lean_dec_ref_known(v___x_5449_, 2);
                        crate::leanh::lean_dec(v_declName_5434_);
                        crate::leanh::lean_dec_ref(v_type_5431_);
                        v_a_5460_ = crate::leanh::lean_ctor_get(v___x_5454_, 0);
                        v_isSharedCheck_5467_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5454_)) as u8;
                        if v_isSharedCheck_5467_ == 0 {
                            v___x_5462_ = v___x_5454_;
                            v_isShared_5463_ = v_isSharedCheck_5467_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5460_);
                            crate::leanh::lean_dec(v___x_5454_);
                            v___x_5462_ = crate::leanh::lean_box(0);
                            v_isShared_5463_ = v_isSharedCheck_5467_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_5449_, 2);
                    crate::leanh::lean_dec_ref(v_expectedInst_5435_);
                    crate::leanh::lean_dec(v_declName_5434_);
                    crate::leanh::lean_dec_ref(v_type_5431_);
                    return v___x_5452_;
                }
            }
            1 => {
                if v_isShared_5463_ == 0 {
                    v___x_5465_ = v___x_5462_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5466_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5466_, 0, v_a_5460_);
                    v___x_5465_ = v_reuseFailAlloc_5466_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5465_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_type_5468_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_u_5469_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_instDeclName_5470_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_declName_5471_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_expectedInst_5472_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___y_5473_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_5474_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_5475_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_5476_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_5477_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_5478_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_5479_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_5480_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_5481_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_5482_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_5483_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_5484_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5485_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(v_type_5468_, v_u_5469_, v_instDeclName_5470_, v_declName_5471_, v_expectedInst_5472_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_, v___y_5477_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_);
    crate::leanh::lean_dec(v___y_5483_);
    crate::leanh::lean_dec_ref(v___y_5482_);
    crate::leanh::lean_dec(v___y_5481_);
    crate::leanh::lean_dec_ref(v___y_5480_);
    crate::leanh::lean_dec(v___y_5479_);
    crate::leanh::lean_dec_ref(v___y_5478_);
    crate::leanh::lean_dec(v___y_5477_);
    crate::leanh::lean_dec_ref(v___y_5476_);
    crate::leanh::lean_dec(v___y_5475_);
    crate::leanh::lean_dec(v___y_5474_);
    crate::leanh::lean_dec(v___y_5473_);
    return v_res_5485_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___lam__0(
    mut v_a_5486_: *mut crate::leanh::LeanObject,
    mut v_s_5487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toRing_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recheck_5502_: u8 = 0;
    let mut v_invSet_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_5506_: u8 = 0;
    let mut v___x_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5509_: u8 = 0;
    let mut v_id_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5528_: u8 = 0;
    let mut v___x_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5536_: u8 = 0;
    let mut v_unused_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5538_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_5488_ = crate::leanh::lean_ctor_get(v_s_5487_, 0);
                v_invFn_x3f_5489_ = crate::leanh::lean_ctor_get(v_s_5487_, 1);
                v_semiringId_x3f_5490_ = crate::leanh::lean_ctor_get(v_s_5487_, 2);
                v_commSemiringInst_5491_ = crate::leanh::lean_ctor_get(v_s_5487_, 3);
                v_commRingInst_5492_ = crate::leanh::lean_ctor_get(v_s_5487_, 4);
                v_noZeroDivInst_x3f_5493_ = crate::leanh::lean_ctor_get(v_s_5487_, 5);
                v_fieldInst_x3f_5494_ = crate::leanh::lean_ctor_get(v_s_5487_, 6);
                v_powIdentityInst_x3f_5495_ = crate::leanh::lean_ctor_get(v_s_5487_, 7);
                v_denoteEntries_5496_ = crate::leanh::lean_ctor_get(v_s_5487_, 8);
                v_nextId_5497_ = crate::leanh::lean_ctor_get(v_s_5487_, 9);
                v_steps_5498_ = crate::leanh::lean_ctor_get(v_s_5487_, 10);
                v_queue_5499_ = crate::leanh::lean_ctor_get(v_s_5487_, 11);
                v_basis_5500_ = crate::leanh::lean_ctor_get(v_s_5487_, 12);
                v_diseqs_5501_ = crate::leanh::lean_ctor_get(v_s_5487_, 13);
                v_recheck_5502_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_5487_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                );
                v_invSet_5503_ = crate::leanh::lean_ctor_get(v_s_5487_, 14);
                v_powIdentityVarCount_5504_ = crate::leanh::lean_ctor_get(v_s_5487_, 15);
                v_numEq0_x3f_5505_ = crate::leanh::lean_ctor_get(v_s_5487_, 16);
                v_numEq0Updated_5506_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_5487_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_5538_ = (!crate::leanh::lean_is_exclusive(v_s_5487_)) as u8;
                if v_isSharedCheck_5538_ == 0 {
                    v___x_5508_ = v_s_5487_;
                    v_isShared_5509_ = v_isSharedCheck_5538_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_numEq0_x3f_5505_);
                    crate::leanh::lean_inc(v_powIdentityVarCount_5504_);
                    crate::leanh::lean_inc(v_invSet_5503_);
                    crate::leanh::lean_inc(v_diseqs_5501_);
                    crate::leanh::lean_inc(v_basis_5500_);
                    crate::leanh::lean_inc(v_queue_5499_);
                    crate::leanh::lean_inc(v_steps_5498_);
                    crate::leanh::lean_inc(v_nextId_5497_);
                    crate::leanh::lean_inc(v_denoteEntries_5496_);
                    crate::leanh::lean_inc(v_powIdentityInst_x3f_5495_);
                    crate::leanh::lean_inc(v_fieldInst_x3f_5494_);
                    crate::leanh::lean_inc(v_noZeroDivInst_x3f_5493_);
                    crate::leanh::lean_inc(v_commRingInst_5492_);
                    crate::leanh::lean_inc(v_commSemiringInst_5491_);
                    crate::leanh::lean_inc(v_semiringId_x3f_5490_);
                    crate::leanh::lean_inc(v_invFn_x3f_5489_);
                    crate::leanh::lean_inc(v_toRing_5488_);
                    crate::leanh::lean_dec(v_s_5487_);
                    v___x_5508_ = crate::leanh::lean_box(0);
                    v_isShared_5509_ = v_isSharedCheck_5538_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_id_5510_ = crate::leanh::lean_ctor_get(v_toRing_5488_, 0);
                v_type_5511_ = crate::leanh::lean_ctor_get(v_toRing_5488_, 1);
                v_u_5512_ = crate::leanh::lean_ctor_get(v_toRing_5488_, 2);
                v_ringInst_5513_ = crate::leanh::lean_ctor_get(v_toRing_5488_, 3);
                v_semiringInst_5514_ = crate::leanh::lean_ctor_get(v_toRing_5488_, 4);
                v_charInst_x3f_5515_ = crate::leanh::lean_ctor_get(v_toRing_5488_, 5);
                v_addFn_x3f_5516_ = crate::leanh::lean_ctor_get(v_toRing_5488_, 6);
                v_mulFn_x3f_5517_ = crate::leanh::lean_ctor_get(v_toRing_5488_, 7);
                v_subFn_x3f_5518_ = crate::leanh::lean_ctor_get(v_toRing_5488_, 8);
                v_powFn_x3f_5519_ = crate::leanh::lean_ctor_get(v_toRing_5488_, 10);
                v_intCastFn_x3f_5520_ = crate::leanh::lean_ctor_get(v_toRing_5488_, 11);
                v_natCastFn_x3f_5521_ = crate::leanh::lean_ctor_get(v_toRing_5488_, 12);
                v_one_x3f_5522_ = crate::leanh::lean_ctor_get(v_toRing_5488_, 13);
                v_vars_5523_ = crate::leanh::lean_ctor_get(v_toRing_5488_, 14);
                v_varMap_5524_ = crate::leanh::lean_ctor_get(v_toRing_5488_, 15);
                v_denote_5525_ = crate::leanh::lean_ctor_get(v_toRing_5488_, 16);
                v_isSharedCheck_5536_ = (!crate::leanh::lean_is_exclusive(v_toRing_5488_)) as u8;
                if v_isSharedCheck_5536_ == 0 {
                    v_unused_5537_ = crate::leanh::lean_ctor_get(v_toRing_5488_, 9);
                    crate::leanh::lean_dec(v_unused_5537_);
                    v___x_5527_ = v_toRing_5488_;
                    v_isShared_5528_ = v_isSharedCheck_5536_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_denote_5525_);
                    crate::leanh::lean_inc(v_varMap_5524_);
                    crate::leanh::lean_inc(v_vars_5523_);
                    crate::leanh::lean_inc(v_one_x3f_5522_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_5521_);
                    crate::leanh::lean_inc(v_intCastFn_x3f_5520_);
                    crate::leanh::lean_inc(v_powFn_x3f_5519_);
                    crate::leanh::lean_inc(v_subFn_x3f_5518_);
                    crate::leanh::lean_inc(v_mulFn_x3f_5517_);
                    crate::leanh::lean_inc(v_addFn_x3f_5516_);
                    crate::leanh::lean_inc(v_charInst_x3f_5515_);
                    crate::leanh::lean_inc(v_semiringInst_5514_);
                    crate::leanh::lean_inc(v_ringInst_5513_);
                    crate::leanh::lean_inc(v_u_5512_);
                    crate::leanh::lean_inc(v_type_5511_);
                    crate::leanh::lean_inc(v_id_5510_);
                    crate::leanh::lean_dec(v_toRing_5488_);
                    v___x_5527_ = crate::leanh::lean_box(0);
                    v_isShared_5528_ = v_isSharedCheck_5536_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5529_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5529_, 0, v_a_5486_);
                if v_isShared_5528_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5527_, 9, v___x_5529_);
                    v___x_5531_ = v___x_5527_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5535_ = crate::leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 0, v_id_5510_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 1, v_type_5511_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 2, v_u_5512_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 3, v_ringInst_5513_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 4, v_semiringInst_5514_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 5, v_charInst_x3f_5515_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 6, v_addFn_x3f_5516_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 7, v_mulFn_x3f_5517_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 8, v_subFn_x3f_5518_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 9, v___x_5529_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 10, v_powFn_x3f_5519_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 11, v_intCastFn_x3f_5520_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 12, v_natCastFn_x3f_5521_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 13, v_one_x3f_5522_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 14, v_vars_5523_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 15, v_varMap_5524_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 16, v_denote_5525_);
                    v___x_5531_ = v_reuseFailAlloc_5535_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5509_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5508_, 0, v___x_5531_);
                    v___x_5533_ = v___x_5508_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5534_ = crate::leanh::lean_alloc_ctor(0, 17, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5534_, 0, v___x_5531_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5534_, 1, v_invFn_x3f_5489_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5534_, 2, v_semiringId_x3f_5490_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5534_,
                        3,
                        v_commSemiringInst_5491_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5534_, 4, v_commRingInst_5492_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5534_,
                        5,
                        v_noZeroDivInst_x3f_5493_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5534_, 6, v_fieldInst_x3f_5494_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5534_,
                        7,
                        v_powIdentityInst_x3f_5495_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5534_, 8, v_denoteEntries_5496_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5534_, 9, v_nextId_5497_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5534_, 10, v_steps_5498_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5534_, 11, v_queue_5499_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5534_, 12, v_basis_5500_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5534_, 13, v_diseqs_5501_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5534_, 14, v_invSet_5503_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5534_,
                        15,
                        v_powIdentityVarCount_5504_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5534_, 16, v_numEq0_x3f_5505_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5534_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                        v_recheck_5502_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5534_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                        v_numEq0Updated_5506_,
                    );
                    v___x_5533_ = v_reuseFailAlloc_5534_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5533_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(
    mut v___y_5552_: *mut crate::leanh::LeanObject,
    mut v___y_5553_: *mut crate::leanh::LeanObject,
    mut v___y_5554_: *mut crate::leanh::LeanObject,
    mut v___y_5555_: *mut crate::leanh::LeanObject,
    mut v___y_5556_: *mut crate::leanh::LeanObject,
    mut v___y_5557_: *mut crate::leanh::LeanObject,
    mut v___y_5558_: *mut crate::leanh::LeanObject,
    mut v___y_5559_: *mut crate::leanh::LeanObject,
    mut v___y_5560_: *mut crate::leanh::LeanObject,
    mut v___y_5561_: *mut crate::leanh::LeanObject,
    mut v___y_5562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5568_: u8 = 0;
    let mut v_toRing_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expectedInst_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5591_: u8 = 0;
    let mut v___x_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5595_: u8 = 0;
    let mut v_unused_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5600_: u8 = 0;
    let mut v___x_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5604_: u8 = 0;
    let mut v_isSharedCheck_5605_: u8 = 0;
    let mut v_a_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5609_: u8 = 0;
    let mut v___x_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5613_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5564_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(
                    v___y_5552_,
                    v___y_5553_,
                    v___y_5554_,
                    v___y_5555_,
                    v___y_5556_,
                    v___y_5557_,
                    v___y_5558_,
                    v___y_5559_,
                    v___y_5560_,
                    v___y_5561_,
                    v___y_5562_,
                );
                if crate::leanh::lean_obj_tag(v___x_5564_) == 0 {
                    v_a_5565_ = crate::leanh::lean_ctor_get(v___x_5564_, 0);
                    v_isSharedCheck_5605_ = (!crate::leanh::lean_is_exclusive(v___x_5564_)) as u8;
                    if v_isSharedCheck_5605_ == 0 {
                        v___x_5567_ = v___x_5564_;
                        v_isShared_5568_ = v_isSharedCheck_5605_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5565_);
                        crate::leanh::lean_dec(v___x_5564_);
                        v___x_5567_ = crate::leanh::lean_box(0);
                        v_isShared_5568_ = v_isSharedCheck_5605_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5606_ = crate::leanh::lean_ctor_get(v___x_5564_, 0);
                    v_isSharedCheck_5613_ = (!crate::leanh::lean_is_exclusive(v___x_5564_)) as u8;
                    if v_isSharedCheck_5613_ == 0 {
                        v___x_5608_ = v___x_5564_;
                        v_isShared_5609_ = v_isSharedCheck_5613_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5606_);
                        crate::leanh::lean_dec(v___x_5564_);
                        v___x_5608_ = crate::leanh::lean_box(0);
                        v_isShared_5609_ = v_isSharedCheck_5613_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_toRing_5569_ = crate::leanh::lean_ctor_get(v_a_5565_, 0);
                crate::leanh::lean_inc_ref(v_toRing_5569_);
                crate::leanh::lean_dec(v_a_5565_);
                v_negFn_x3f_5570_ = crate::leanh::lean_ctor_get(v_toRing_5569_, 9);
                if crate::leanh::lean_obj_tag(v_negFn_x3f_5570_) == 1 {
                    crate::leanh::lean_inc_ref(v_negFn_x3f_5570_);
                    crate::leanh::lean_dec_ref(v_toRing_5569_);
                    v_val_5571_ = crate::leanh::lean_ctor_get(v_negFn_x3f_5570_, 0);
                    crate::leanh::lean_inc(v_val_5571_);
                    crate::leanh::lean_dec_ref_known(v_negFn_x3f_5570_, 1);
                    if v_isShared_5568_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5567_, 0, v_val_5571_);
                        v___x_5573_ = v___x_5567_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5574_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5574_, 0, v_val_5571_);
                        v___x_5573_ = v_reuseFailAlloc_5574_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5567_);
                    v_type_5575_ = crate::leanh::lean_ctor_get(v_toRing_5569_, 1);
                    crate::leanh::lean_inc_ref_n(v_type_5575_, 2);
                    v_u_5576_ = crate::leanh::lean_ctor_get(v_toRing_5569_, 2);
                    crate::leanh::lean_inc_n(v_u_5576_, 2);
                    v_ringInst_5577_ = crate::leanh::lean_ctor_get(v_toRing_5569_, 3);
                    crate::leanh::lean_inc_ref(v_ringInst_5577_);
                    crate::leanh::lean_dec_ref(v_toRing_5569_);
                    v___x_5578_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1;
                    v___x_5579_ = crate::leanh::lean_box(0);
                    v___x_5580_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5580_, 0, v_u_5576_);
                    crate::leanh::lean_ctor_set(v___x_5580_, 1, v___x_5579_);
                    v___x_5581_ = l_Lean_mkConst(v___x_5578_, v___x_5580_);
                    v_expectedInst_5582_ =
                        l_Lean_mkAppB(v___x_5581_, v_type_5575_, v_ringInst_5577_);
                    v___x_5583_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__3;
                    v___x_5584_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5;
                    v___x_5585_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(v_type_5575_, v_u_5576_, v___x_5583_, v___x_5584_, v_expectedInst_5582_, v___y_5552_, v___y_5553_, v___y_5554_, v___y_5555_, v___y_5556_, v___y_5557_, v___y_5558_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_);
                    if crate::leanh::lean_obj_tag(v___x_5585_) == 0 {
                        v_a_5586_ = crate::leanh::lean_ctor_get(v___x_5585_, 0);
                        crate::leanh::lean_inc_n(v_a_5586_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_5585_, 1);
                        v___f_5587_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___lam__0 as *mut core::ffi::c_void, 2, 1);
                        crate::leanh::lean_closure_set(v___f_5587_, 0, v_a_5586_);
                        v___x_5588_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(
                            v___f_5587_,
                            v___y_5552_,
                            v___y_5553_,
                            v___y_5554_,
                            v___y_5555_,
                            v___y_5556_,
                            v___y_5557_,
                            v___y_5558_,
                            v___y_5559_,
                            v___y_5560_,
                            v___y_5561_,
                            v___y_5562_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5588_) == 0 {
                            v_isSharedCheck_5595_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5588_)) as u8;
                            if v_isSharedCheck_5595_ == 0 {
                                v_unused_5596_ = crate::leanh::lean_ctor_get(v___x_5588_, 0);
                                crate::leanh::lean_dec(v_unused_5596_);
                                v___x_5590_ = v___x_5588_;
                                v_isShared_5591_ = v_isSharedCheck_5595_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_5588_);
                                v___x_5590_ = crate::leanh::lean_box(0);
                                v_isShared_5591_ = v_isSharedCheck_5595_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5586_);
                            v_a_5597_ = crate::leanh::lean_ctor_get(v___x_5588_, 0);
                            v_isSharedCheck_5604_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5588_)) as u8;
                            if v_isSharedCheck_5604_ == 0 {
                                v___x_5599_ = v___x_5588_;
                                v_isShared_5600_ = v_isSharedCheck_5604_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5597_);
                                crate::leanh::lean_dec(v___x_5588_);
                                v___x_5599_ = crate::leanh::lean_box(0);
                                v_isShared_5600_ = v_isSharedCheck_5604_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        return v___x_5585_;
                    }
                }
            }
            2 => {
                return v___x_5573_;
            }
            3 => {
                if v_isShared_5591_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5590_, 0, v_a_5586_);
                    v___x_5593_ = v___x_5590_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5594_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5594_, 0, v_a_5586_);
                    v___x_5593_ = v_reuseFailAlloc_5594_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5593_;
            }
            5 => {
                if v_isShared_5600_ == 0 {
                    v___x_5602_ = v___x_5599_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5603_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5603_, 0, v_a_5597_);
                    v___x_5602_ = v_reuseFailAlloc_5603_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5602_;
            }
            7 => {
                if v_isShared_5609_ == 0 {
                    v___x_5611_ = v___x_5608_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5612_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5612_, 0, v_a_5606_);
                    v___x_5611_ = v_reuseFailAlloc_5612_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5611_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___boxed(
    mut v___y_5614_: *mut crate::leanh::LeanObject,
    mut v___y_5615_: *mut crate::leanh::LeanObject,
    mut v___y_5616_: *mut crate::leanh::LeanObject,
    mut v___y_5617_: *mut crate::leanh::LeanObject,
    mut v___y_5618_: *mut crate::leanh::LeanObject,
    mut v___y_5619_: *mut crate::leanh::LeanObject,
    mut v___y_5620_: *mut crate::leanh::LeanObject,
    mut v___y_5621_: *mut crate::leanh::LeanObject,
    mut v___y_5622_: *mut crate::leanh::LeanObject,
    mut v___y_5623_: *mut crate::leanh::LeanObject,
    mut v___y_5624_: *mut crate::leanh::LeanObject,
    mut v___y_5625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5626_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(v___y_5614_, v___y_5615_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_, v___y_5622_, v___y_5623_, v___y_5624_);
    crate::leanh::lean_dec(v___y_5624_);
    crate::leanh::lean_dec_ref(v___y_5623_);
    crate::leanh::lean_dec(v___y_5622_);
    crate::leanh::lean_dec_ref(v___y_5621_);
    crate::leanh::lean_dec(v___y_5620_);
    crate::leanh::lean_dec_ref(v___y_5619_);
    crate::leanh::lean_dec(v___y_5618_);
    crate::leanh::lean_dec_ref(v___y_5617_);
    crate::leanh::lean_dec(v___y_5616_);
    crate::leanh::lean_dec(v___y_5615_);
    crate::leanh::lean_dec(v___y_5614_);
    return v_res_5626_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5634_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5635_ = lean_nat_to_int(v___x_5634_);
    return v___x_5635_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(
    mut v_k_5641_: *mut crate::leanh::LeanObject,
    mut v___y_5642_: *mut crate::leanh::LeanObject,
    mut v___y_5643_: *mut crate::leanh::LeanObject,
    mut v___y_5644_: *mut crate::leanh::LeanObject,
    mut v___y_5645_: *mut crate::leanh::LeanObject,
    mut v___y_5646_: *mut crate::leanh::LeanObject,
    mut v___y_5647_: *mut crate::leanh::LeanObject,
    mut v___y_5648_: *mut crate::leanh::LeanObject,
    mut v___y_5649_: *mut crate::leanh::LeanObject,
    mut v___y_5650_: *mut crate::leanh::LeanObject,
    mut v___y_5651_: *mut crate::leanh::LeanObject,
    mut v___y_5652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toRing_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5672_: u8 = 0;
    let mut v_ofNatInst_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5690_: u8 = 0;
    let mut v___x_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5698_: u8 = 0;
    let mut v___x_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5703_: u8 = 0;
    let mut v_val_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5708_: u8 = 0;
    let mut v_a_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5712_: u8 = 0;
    let mut v___x_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5716_: u8 = 0;
    let mut v_a_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5720_: u8 = 0;
    let mut v___x_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5724_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5654_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(
                    v___y_5642_,
                    v___y_5643_,
                    v___y_5644_,
                    v___y_5645_,
                    v___y_5646_,
                    v___y_5647_,
                    v___y_5648_,
                    v___y_5649_,
                    v___y_5650_,
                    v___y_5651_,
                    v___y_5652_,
                );
                if crate::leanh::lean_obj_tag(v___x_5654_) == 0 {
                    v_a_5655_ = crate::leanh::lean_ctor_get(v___x_5654_, 0);
                    crate::leanh::lean_inc(v_a_5655_);
                    crate::leanh::lean_dec_ref_known(v___x_5654_, 1);
                    v_toRing_5656_ = crate::leanh::lean_ctor_get(v_a_5655_, 0);
                    crate::leanh::lean_inc_ref(v_toRing_5656_);
                    crate::leanh::lean_dec(v_a_5655_);
                    v_type_5657_ = crate::leanh::lean_ctor_get(v_toRing_5656_, 1);
                    crate::leanh::lean_inc_ref_n(v_type_5657_, 2);
                    v_u_5658_ = crate::leanh::lean_ctor_get(v_toRing_5656_, 2);
                    crate::leanh::lean_inc(v_u_5658_);
                    v_semiringInst_5659_ = crate::leanh::lean_ctor_get(v_toRing_5656_, 4);
                    crate::leanh::lean_inc_ref(v_semiringInst_5659_);
                    crate::leanh::lean_dec_ref(v_toRing_5656_);
                    v___x_5660_ = lean_nat_abs(v_k_5641_);
                    v_n_5661_ = l_Lean_mkRawNatLit(v___x_5660_);
                    v___x_5662_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__1;
                    v___x_5663_ = crate::leanh::lean_box(0);
                    v___x_5664_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5664_, 0, v_u_5658_);
                    crate::leanh::lean_ctor_set(v___x_5664_, 1, v___x_5663_);
                    crate::leanh::lean_inc_ref(v___x_5664_);
                    v___x_5665_ = l_Lean_mkConst(v___x_5662_, v___x_5664_);
                    crate::leanh::lean_inc_ref(v_n_5661_);
                    v___x_5666_ = l_Lean_mkAppB(v___x_5665_, v_type_5657_, v_n_5661_);
                    v___x_5667_ = crate::leanh::lean_box(0);
                    v___x_5668_ = l_Lean_Meta_synthInstance_x3f(
                        v___x_5666_,
                        v___x_5667_,
                        v___y_5649_,
                        v___y_5650_,
                        v___y_5651_,
                        v___y_5652_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5668_) == 0 {
                        v_a_5669_ = crate::leanh::lean_ctor_get(v___x_5668_, 0);
                        v_isSharedCheck_5708_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5668_)) as u8;
                        if v_isSharedCheck_5708_ == 0 {
                            v___x_5671_ = v___x_5668_;
                            v_isShared_5672_ = v_isSharedCheck_5708_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5669_);
                            crate::leanh::lean_dec(v___x_5668_);
                            v___x_5671_ = crate::leanh::lean_box(0);
                            v_isShared_5672_ = v_isSharedCheck_5708_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_5664_, 2);
                        crate::leanh::lean_dec_ref(v_n_5661_);
                        crate::leanh::lean_dec_ref(v_semiringInst_5659_);
                        crate::leanh::lean_dec_ref(v_type_5657_);
                        v_a_5709_ = crate::leanh::lean_ctor_get(v___x_5668_, 0);
                        v_isSharedCheck_5716_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5668_)) as u8;
                        if v_isSharedCheck_5716_ == 0 {
                            v___x_5711_ = v___x_5668_;
                            v_isShared_5712_ = v_isSharedCheck_5716_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5709_);
                            crate::leanh::lean_dec(v___x_5668_);
                            v___x_5711_ = crate::leanh::lean_box(0);
                            v_isShared_5712_ = v_isSharedCheck_5716_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v_a_5717_ = crate::leanh::lean_ctor_get(v___x_5654_, 0);
                    v_isSharedCheck_5724_ = (!crate::leanh::lean_is_exclusive(v___x_5654_)) as u8;
                    if v_isSharedCheck_5724_ == 0 {
                        v___x_5719_ = v___x_5654_;
                        v_isShared_5720_ = v_isSharedCheck_5724_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5717_);
                        crate::leanh::lean_dec(v___x_5654_);
                        v___x_5719_ = crate::leanh::lean_box(0);
                        v_isShared_5720_ = v_isSharedCheck_5724_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5669_) == 1 {
                    crate::leanh::lean_dec_ref(v_semiringInst_5659_);
                    v_val_5704_ = crate::leanh::lean_ctor_get(v_a_5669_, 0);
                    crate::leanh::lean_inc(v_val_5704_);
                    crate::leanh::lean_dec_ref_known(v_a_5669_, 1);
                    v_ofNatInst_5674_ = v_val_5704_;
                    v___y_5675_ = v___y_5642_;
                    v___y_5676_ = v___y_5643_;
                    v___y_5677_ = v___y_5644_;
                    v___y_5678_ = v___y_5645_;
                    v___y_5679_ = v___y_5646_;
                    v___y_5680_ = v___y_5647_;
                    v___y_5681_ = v___y_5648_;
                    v___y_5682_ = v___y_5649_;
                    v___y_5683_ = v___y_5650_;
                    v___y_5684_ = v___y_5651_;
                    v___y_5685_ = v___y_5652_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_5669_);
                    v___x_5705_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5;
                    crate::leanh::lean_inc_ref(v___x_5664_);
                    v___x_5706_ = l_Lean_mkConst(v___x_5705_, v___x_5664_);
                    crate::leanh::lean_inc_ref(v_n_5661_);
                    crate::leanh::lean_inc_ref(v_type_5657_);
                    v___x_5707_ =
                        l_Lean_mkApp3(v___x_5706_, v_type_5657_, v_semiringInst_5659_, v_n_5661_);
                    v_ofNatInst_5674_ = v___x_5707_;
                    v___y_5675_ = v___y_5642_;
                    v___y_5676_ = v___y_5643_;
                    v___y_5677_ = v___y_5644_;
                    v___y_5678_ = v___y_5645_;
                    v___y_5679_ = v___y_5646_;
                    v___y_5680_ = v___y_5647_;
                    v___y_5681_ = v___y_5648_;
                    v___y_5682_ = v___y_5649_;
                    v___y_5683_ = v___y_5650_;
                    v___y_5684_ = v___y_5651_;
                    v___y_5685_ = v___y_5652_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5686_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3;
                v___x_5687_ = l_Lean_mkConst(v___x_5686_, v___x_5664_);
                v_n_5688_ = l_Lean_mkApp3(v___x_5687_, v_type_5657_, v_n_5661_, v_ofNatInst_5674_);
                v___x_5689_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4_once), _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4);
                v___x_5690_ = lean_int_dec_lt(v_k_5641_, v___x_5689_);
                if v___x_5690_ == 0 {
                    if v_isShared_5672_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5671_, 0, v_n_5688_);
                        v___x_5692_ = v___x_5671_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5693_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5693_, 0, v_n_5688_);
                        v___x_5692_ = v_reuseFailAlloc_5693_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5671_);
                    v___x_5694_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(v___y_5675_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_, v___y_5682_, v___y_5683_, v___y_5684_, v___y_5685_);
                    if crate::leanh::lean_obj_tag(v___x_5694_) == 0 {
                        v_a_5695_ = crate::leanh::lean_ctor_get(v___x_5694_, 0);
                        v_isSharedCheck_5703_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5694_)) as u8;
                        if v_isSharedCheck_5703_ == 0 {
                            v___x_5697_ = v___x_5694_;
                            v_isShared_5698_ = v_isSharedCheck_5703_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5695_);
                            crate::leanh::lean_dec(v___x_5694_);
                            v___x_5697_ = crate::leanh::lean_box(0);
                            v_isShared_5698_ = v_isSharedCheck_5703_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_n_5688_);
                        return v___x_5694_;
                    }
                }
            }
            3 => {
                return v___x_5692_;
            }
            4 => {
                v___x_5699_ = l_Lean_Expr_app___override(v_a_5695_, v_n_5688_);
                if v_isShared_5698_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5697_, 0, v___x_5699_);
                    v___x_5701_ = v___x_5697_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5702_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5702_, 0, v___x_5699_);
                    v___x_5701_ = v_reuseFailAlloc_5702_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5701_;
            }
            6 => {
                if v_isShared_5712_ == 0 {
                    v___x_5714_ = v___x_5711_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5715_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5715_, 0, v_a_5709_);
                    v___x_5714_ = v_reuseFailAlloc_5715_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5714_;
            }
            8 => {
                if v_isShared_5720_ == 0 {
                    v___x_5722_ = v___x_5719_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5723_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5723_, 0, v_a_5717_);
                    v___x_5722_ = v_reuseFailAlloc_5723_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5722_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___boxed(
    mut v_k_5725_: *mut crate::leanh::LeanObject,
    mut v___y_5726_: *mut crate::leanh::LeanObject,
    mut v___y_5727_: *mut crate::leanh::LeanObject,
    mut v___y_5728_: *mut crate::leanh::LeanObject,
    mut v___y_5729_: *mut crate::leanh::LeanObject,
    mut v___y_5730_: *mut crate::leanh::LeanObject,
    mut v___y_5731_: *mut crate::leanh::LeanObject,
    mut v___y_5732_: *mut crate::leanh::LeanObject,
    mut v___y_5733_: *mut crate::leanh::LeanObject,
    mut v___y_5734_: *mut crate::leanh::LeanObject,
    mut v___y_5735_: *mut crate::leanh::LeanObject,
    mut v___y_5736_: *mut crate::leanh::LeanObject,
    mut v___y_5737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5738_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v_k_5725_, v___y_5726_, v___y_5727_, v___y_5728_, v___y_5729_, v___y_5730_, v___y_5731_, v___y_5732_, v___y_5733_, v___y_5734_, v___y_5735_, v___y_5736_);
    crate::leanh::lean_dec(v___y_5736_);
    crate::leanh::lean_dec_ref(v___y_5735_);
    crate::leanh::lean_dec(v___y_5734_);
    crate::leanh::lean_dec_ref(v___y_5733_);
    crate::leanh::lean_dec(v___y_5732_);
    crate::leanh::lean_dec_ref(v___y_5731_);
    crate::leanh::lean_dec(v___y_5730_);
    crate::leanh::lean_dec_ref(v___y_5729_);
    crate::leanh::lean_dec(v___y_5728_);
    crate::leanh::lean_dec(v___y_5727_);
    crate::leanh::lean_dec(v___y_5726_);
    crate::leanh::lean_dec(v_k_5725_);
    return v_res_5738_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___lam__0(
    mut v_a_5739_: *mut crate::leanh::LeanObject,
    mut v_s_5740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toRing_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_5743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_5746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_5747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recheck_5755_: u8 = 0;
    let mut v_invSet_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_5757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_5759_: u8 = 0;
    let mut v___x_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5762_: u8 = 0;
    let mut v_id_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_5766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_5767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_5775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5781_: u8 = 0;
    let mut v___x_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5789_: u8 = 0;
    let mut v_unused_5790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5791_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_5741_ = crate::leanh::lean_ctor_get(v_s_5740_, 0);
                v_invFn_x3f_5742_ = crate::leanh::lean_ctor_get(v_s_5740_, 1);
                v_semiringId_x3f_5743_ = crate::leanh::lean_ctor_get(v_s_5740_, 2);
                v_commSemiringInst_5744_ = crate::leanh::lean_ctor_get(v_s_5740_, 3);
                v_commRingInst_5745_ = crate::leanh::lean_ctor_get(v_s_5740_, 4);
                v_noZeroDivInst_x3f_5746_ = crate::leanh::lean_ctor_get(v_s_5740_, 5);
                v_fieldInst_x3f_5747_ = crate::leanh::lean_ctor_get(v_s_5740_, 6);
                v_powIdentityInst_x3f_5748_ = crate::leanh::lean_ctor_get(v_s_5740_, 7);
                v_denoteEntries_5749_ = crate::leanh::lean_ctor_get(v_s_5740_, 8);
                v_nextId_5750_ = crate::leanh::lean_ctor_get(v_s_5740_, 9);
                v_steps_5751_ = crate::leanh::lean_ctor_get(v_s_5740_, 10);
                v_queue_5752_ = crate::leanh::lean_ctor_get(v_s_5740_, 11);
                v_basis_5753_ = crate::leanh::lean_ctor_get(v_s_5740_, 12);
                v_diseqs_5754_ = crate::leanh::lean_ctor_get(v_s_5740_, 13);
                v_recheck_5755_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_5740_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                );
                v_invSet_5756_ = crate::leanh::lean_ctor_get(v_s_5740_, 14);
                v_powIdentityVarCount_5757_ = crate::leanh::lean_ctor_get(v_s_5740_, 15);
                v_numEq0_x3f_5758_ = crate::leanh::lean_ctor_get(v_s_5740_, 16);
                v_numEq0Updated_5759_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_5740_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_5791_ = (!crate::leanh::lean_is_exclusive(v_s_5740_)) as u8;
                if v_isSharedCheck_5791_ == 0 {
                    v___x_5761_ = v_s_5740_;
                    v_isShared_5762_ = v_isSharedCheck_5791_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_numEq0_x3f_5758_);
                    crate::leanh::lean_inc(v_powIdentityVarCount_5757_);
                    crate::leanh::lean_inc(v_invSet_5756_);
                    crate::leanh::lean_inc(v_diseqs_5754_);
                    crate::leanh::lean_inc(v_basis_5753_);
                    crate::leanh::lean_inc(v_queue_5752_);
                    crate::leanh::lean_inc(v_steps_5751_);
                    crate::leanh::lean_inc(v_nextId_5750_);
                    crate::leanh::lean_inc(v_denoteEntries_5749_);
                    crate::leanh::lean_inc(v_powIdentityInst_x3f_5748_);
                    crate::leanh::lean_inc(v_fieldInst_x3f_5747_);
                    crate::leanh::lean_inc(v_noZeroDivInst_x3f_5746_);
                    crate::leanh::lean_inc(v_commRingInst_5745_);
                    crate::leanh::lean_inc(v_commSemiringInst_5744_);
                    crate::leanh::lean_inc(v_semiringId_x3f_5743_);
                    crate::leanh::lean_inc(v_invFn_x3f_5742_);
                    crate::leanh::lean_inc(v_toRing_5741_);
                    crate::leanh::lean_dec(v_s_5740_);
                    v___x_5761_ = crate::leanh::lean_box(0);
                    v_isShared_5762_ = v_isSharedCheck_5791_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_id_5763_ = crate::leanh::lean_ctor_get(v_toRing_5741_, 0);
                v_type_5764_ = crate::leanh::lean_ctor_get(v_toRing_5741_, 1);
                v_u_5765_ = crate::leanh::lean_ctor_get(v_toRing_5741_, 2);
                v_ringInst_5766_ = crate::leanh::lean_ctor_get(v_toRing_5741_, 3);
                v_semiringInst_5767_ = crate::leanh::lean_ctor_get(v_toRing_5741_, 4);
                v_charInst_x3f_5768_ = crate::leanh::lean_ctor_get(v_toRing_5741_, 5);
                v_addFn_x3f_5769_ = crate::leanh::lean_ctor_get(v_toRing_5741_, 6);
                v_mulFn_x3f_5770_ = crate::leanh::lean_ctor_get(v_toRing_5741_, 7);
                v_subFn_x3f_5771_ = crate::leanh::lean_ctor_get(v_toRing_5741_, 8);
                v_negFn_x3f_5772_ = crate::leanh::lean_ctor_get(v_toRing_5741_, 9);
                v_intCastFn_x3f_5773_ = crate::leanh::lean_ctor_get(v_toRing_5741_, 11);
                v_natCastFn_x3f_5774_ = crate::leanh::lean_ctor_get(v_toRing_5741_, 12);
                v_one_x3f_5775_ = crate::leanh::lean_ctor_get(v_toRing_5741_, 13);
                v_vars_5776_ = crate::leanh::lean_ctor_get(v_toRing_5741_, 14);
                v_varMap_5777_ = crate::leanh::lean_ctor_get(v_toRing_5741_, 15);
                v_denote_5778_ = crate::leanh::lean_ctor_get(v_toRing_5741_, 16);
                v_isSharedCheck_5789_ = (!crate::leanh::lean_is_exclusive(v_toRing_5741_)) as u8;
                if v_isSharedCheck_5789_ == 0 {
                    v_unused_5790_ = crate::leanh::lean_ctor_get(v_toRing_5741_, 10);
                    crate::leanh::lean_dec(v_unused_5790_);
                    v___x_5780_ = v_toRing_5741_;
                    v_isShared_5781_ = v_isSharedCheck_5789_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_denote_5778_);
                    crate::leanh::lean_inc(v_varMap_5777_);
                    crate::leanh::lean_inc(v_vars_5776_);
                    crate::leanh::lean_inc(v_one_x3f_5775_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_5774_);
                    crate::leanh::lean_inc(v_intCastFn_x3f_5773_);
                    crate::leanh::lean_inc(v_negFn_x3f_5772_);
                    crate::leanh::lean_inc(v_subFn_x3f_5771_);
                    crate::leanh::lean_inc(v_mulFn_x3f_5770_);
                    crate::leanh::lean_inc(v_addFn_x3f_5769_);
                    crate::leanh::lean_inc(v_charInst_x3f_5768_);
                    crate::leanh::lean_inc(v_semiringInst_5767_);
                    crate::leanh::lean_inc(v_ringInst_5766_);
                    crate::leanh::lean_inc(v_u_5765_);
                    crate::leanh::lean_inc(v_type_5764_);
                    crate::leanh::lean_inc(v_id_5763_);
                    crate::leanh::lean_dec(v_toRing_5741_);
                    v___x_5780_ = crate::leanh::lean_box(0);
                    v_isShared_5781_ = v_isSharedCheck_5789_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5782_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5782_, 0, v_a_5739_);
                if v_isShared_5781_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5780_, 10, v___x_5782_);
                    v___x_5784_ = v___x_5780_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5788_ = crate::leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 0, v_id_5763_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 1, v_type_5764_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 2, v_u_5765_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 3, v_ringInst_5766_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 4, v_semiringInst_5767_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 5, v_charInst_x3f_5768_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 6, v_addFn_x3f_5769_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 7, v_mulFn_x3f_5770_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 8, v_subFn_x3f_5771_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 9, v_negFn_x3f_5772_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 10, v___x_5782_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 11, v_intCastFn_x3f_5773_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 12, v_natCastFn_x3f_5774_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 13, v_one_x3f_5775_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 14, v_vars_5776_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 15, v_varMap_5777_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 16, v_denote_5778_);
                    v___x_5784_ = v_reuseFailAlloc_5788_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5762_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5761_, 0, v___x_5784_);
                    v___x_5786_ = v___x_5761_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5787_ = crate::leanh::lean_alloc_ctor(0, 17, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 0, v___x_5784_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 1, v_invFn_x3f_5742_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 2, v_semiringId_x3f_5743_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5787_,
                        3,
                        v_commSemiringInst_5744_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 4, v_commRingInst_5745_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5787_,
                        5,
                        v_noZeroDivInst_x3f_5746_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 6, v_fieldInst_x3f_5747_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5787_,
                        7,
                        v_powIdentityInst_x3f_5748_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 8, v_denoteEntries_5749_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 9, v_nextId_5750_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 10, v_steps_5751_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 11, v_queue_5752_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 12, v_basis_5753_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 13, v_diseqs_5754_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 14, v_invSet_5756_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5787_,
                        15,
                        v_powIdentityVarCount_5757_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 16, v_numEq0_x3f_5758_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5787_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                        v_recheck_5755_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5787_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                        v_numEq0Updated_5759_,
                    );
                    v___x_5786_ = v_reuseFailAlloc_5787_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5786_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5795_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5796_ = l_Lean_Level_ofNat(v___x_5795_);
    return v___x_5796_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(
    mut v_u_5807_: *mut crate::leanh::LeanObject,
    mut v_type_5808_: *mut crate::leanh::LeanObject,
    mut v_semiringInst_5809_: *mut crate::leanh::LeanObject,
    mut v___y_5810_: *mut crate::leanh::LeanObject,
    mut v___y_5811_: *mut crate::leanh::LeanObject,
    mut v___y_5812_: *mut crate::leanh::LeanObject,
    mut v___y_5813_: *mut crate::leanh::LeanObject,
    mut v___y_5814_: *mut crate::leanh::LeanObject,
    mut v___y_5815_: *mut crate::leanh::LeanObject,
    mut v___y_5816_: *mut crate::leanh::LeanObject,
    mut v___y_5817_: *mut crate::leanh::LeanObject,
    mut v___y_5818_: *mut crate::leanh::LeanObject,
    mut v___y_5819_: *mut crate::leanh::LeanObject,
    mut v___y_5820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inst_x27_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5846_: u8 = 0;
    let mut v___x_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5850_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5822_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__1;
                v___x_5823_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2_once), _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2);
                v___x_5824_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_u_5807_);
                v___x_5825_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5825_, 0, v_u_5807_);
                crate::leanh::lean_ctor_set(v___x_5825_, 1, v___x_5824_);
                crate::leanh::lean_inc_ref(v___x_5825_);
                v___x_5826_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5826_, 0, v___x_5823_);
                crate::leanh::lean_ctor_set(v___x_5826_, 1, v___x_5825_);
                v___x_5827_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5827_, 0, v_u_5807_);
                crate::leanh::lean_ctor_set(v___x_5827_, 1, v___x_5826_);
                crate::leanh::lean_inc_ref(v___x_5827_);
                v___x_5828_ = l_Lean_mkConst(v___x_5822_, v___x_5827_);
                v___x_5829_ = l_Lean_Nat_mkType;
                crate::leanh::lean_inc_ref_n(v_type_5808_, 2);
                v___x_5830_ = l_Lean_mkApp3(v___x_5828_, v_type_5808_, v___x_5829_, v_type_5808_);
                v___x_5831_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_5830_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_);
                if crate::leanh::lean_obj_tag(v___x_5831_) == 0 {
                    v_a_5832_ = crate::leanh::lean_ctor_get(v___x_5831_, 0);
                    crate::leanh::lean_inc_n(v_a_5832_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_5831_, 1);
                    v___x_5833_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4;
                    v___x_5834_ = l_Lean_mkConst(v___x_5833_, v___x_5825_);
                    crate::leanh::lean_inc_ref(v_type_5808_);
                    v_inst_x27_5835_ =
                        l_Lean_mkAppB(v___x_5834_, v_type_5808_, v_semiringInst_5809_);
                    v___x_5836_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__6;
                    v___x_5837_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(
                        v___x_5836_,
                        v_a_5832_,
                        v_inst_x27_5835_,
                        v___y_5817_,
                        v___y_5818_,
                        v___y_5819_,
                        v___y_5820_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5837_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5837_, 1);
                        v___x_5838_ = l_Lean_mkConst(v___x_5836_, v___x_5827_);
                        crate::leanh::lean_inc_ref(v_type_5808_);
                        v___x_5839_ = l_Lean_mkApp4(
                            v___x_5838_,
                            v_type_5808_,
                            v___x_5829_,
                            v_type_5808_,
                            v_a_5832_,
                        );
                        v___x_5840_ = l_Lean_Meta_Sym_canon(
                            v___x_5839_,
                            v___y_5815_,
                            v___y_5816_,
                            v___y_5817_,
                            v___y_5818_,
                            v___y_5819_,
                            v___y_5820_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5840_) == 0 {
                            v_a_5841_ = crate::leanh::lean_ctor_get(v___x_5840_, 0);
                            crate::leanh::lean_inc(v_a_5841_);
                            crate::leanh::lean_dec_ref_known(v___x_5840_, 1);
                            v___x_5842_ =
                                l_Lean_Meta_Sym_shareCommon___redArg(v_a_5841_, v___y_5816_);
                            return v___x_5842_;
                        } else {
                            return v___x_5840_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5832_);
                        crate::leanh::lean_dec_ref_known(v___x_5827_, 2);
                        crate::leanh::lean_dec_ref(v_type_5808_);
                        v_a_5843_ = crate::leanh::lean_ctor_get(v___x_5837_, 0);
                        v_isSharedCheck_5850_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5837_)) as u8;
                        if v_isSharedCheck_5850_ == 0 {
                            v___x_5845_ = v___x_5837_;
                            v_isShared_5846_ = v_isSharedCheck_5850_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5843_);
                            crate::leanh::lean_dec(v___x_5837_);
                            v___x_5845_ = crate::leanh::lean_box(0);
                            v_isShared_5846_ = v_isSharedCheck_5850_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_5827_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_5825_, 2);
                    crate::leanh::lean_dec_ref(v_semiringInst_5809_);
                    crate::leanh::lean_dec_ref(v_type_5808_);
                    return v___x_5831_;
                }
            }
            1 => {
                if v_isShared_5846_ == 0 {
                    v___x_5848_ = v___x_5845_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5849_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5849_, 0, v_a_5843_);
                    v___x_5848_ = v_reuseFailAlloc_5849_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5848_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___boxed(
    mut v_u_5851_: *mut crate::leanh::LeanObject,
    mut v_type_5852_: *mut crate::leanh::LeanObject,
    mut v_semiringInst_5853_: *mut crate::leanh::LeanObject,
    mut v___y_5854_: *mut crate::leanh::LeanObject,
    mut v___y_5855_: *mut crate::leanh::LeanObject,
    mut v___y_5856_: *mut crate::leanh::LeanObject,
    mut v___y_5857_: *mut crate::leanh::LeanObject,
    mut v___y_5858_: *mut crate::leanh::LeanObject,
    mut v___y_5859_: *mut crate::leanh::LeanObject,
    mut v___y_5860_: *mut crate::leanh::LeanObject,
    mut v___y_5861_: *mut crate::leanh::LeanObject,
    mut v___y_5862_: *mut crate::leanh::LeanObject,
    mut v___y_5863_: *mut crate::leanh::LeanObject,
    mut v___y_5864_: *mut crate::leanh::LeanObject,
    mut v___y_5865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5866_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(v_u_5851_, v_type_5852_, v_semiringInst_5853_, v___y_5854_, v___y_5855_, v___y_5856_, v___y_5857_, v___y_5858_, v___y_5859_, v___y_5860_, v___y_5861_, v___y_5862_, v___y_5863_, v___y_5864_);
    crate::leanh::lean_dec(v___y_5864_);
    crate::leanh::lean_dec_ref(v___y_5863_);
    crate::leanh::lean_dec(v___y_5862_);
    crate::leanh::lean_dec_ref(v___y_5861_);
    crate::leanh::lean_dec(v___y_5860_);
    crate::leanh::lean_dec_ref(v___y_5859_);
    crate::leanh::lean_dec(v___y_5858_);
    crate::leanh::lean_dec_ref(v___y_5857_);
    crate::leanh::lean_dec(v___y_5856_);
    crate::leanh::lean_dec(v___y_5855_);
    crate::leanh::lean_dec(v___y_5854_);
    return v_res_5866_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(
    mut v___y_5867_: *mut crate::leanh::LeanObject,
    mut v___y_5868_: *mut crate::leanh::LeanObject,
    mut v___y_5869_: *mut crate::leanh::LeanObject,
    mut v___y_5870_: *mut crate::leanh::LeanObject,
    mut v___y_5871_: *mut crate::leanh::LeanObject,
    mut v___y_5872_: *mut crate::leanh::LeanObject,
    mut v___y_5873_: *mut crate::leanh::LeanObject,
    mut v___y_5874_: *mut crate::leanh::LeanObject,
    mut v___y_5875_: *mut crate::leanh::LeanObject,
    mut v___y_5876_: *mut crate::leanh::LeanObject,
    mut v___y_5877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5883_: u8 = 0;
    let mut v_toRing_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_5885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5899_: u8 = 0;
    let mut v___x_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5903_: u8 = 0;
    let mut v_unused_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5908_: u8 = 0;
    let mut v___x_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5912_: u8 = 0;
    let mut v_isSharedCheck_5913_: u8 = 0;
    let mut v_a_5914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5917_: u8 = 0;
    let mut v___x_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5921_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5879_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(
                    v___y_5867_,
                    v___y_5868_,
                    v___y_5869_,
                    v___y_5870_,
                    v___y_5871_,
                    v___y_5872_,
                    v___y_5873_,
                    v___y_5874_,
                    v___y_5875_,
                    v___y_5876_,
                    v___y_5877_,
                );
                if crate::leanh::lean_obj_tag(v___x_5879_) == 0 {
                    v_a_5880_ = crate::leanh::lean_ctor_get(v___x_5879_, 0);
                    v_isSharedCheck_5913_ = (!crate::leanh::lean_is_exclusive(v___x_5879_)) as u8;
                    if v_isSharedCheck_5913_ == 0 {
                        v___x_5882_ = v___x_5879_;
                        v_isShared_5883_ = v_isSharedCheck_5913_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5880_);
                        crate::leanh::lean_dec(v___x_5879_);
                        v___x_5882_ = crate::leanh::lean_box(0);
                        v_isShared_5883_ = v_isSharedCheck_5913_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5914_ = crate::leanh::lean_ctor_get(v___x_5879_, 0);
                    v_isSharedCheck_5921_ = (!crate::leanh::lean_is_exclusive(v___x_5879_)) as u8;
                    if v_isSharedCheck_5921_ == 0 {
                        v___x_5916_ = v___x_5879_;
                        v_isShared_5917_ = v_isSharedCheck_5921_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5914_);
                        crate::leanh::lean_dec(v___x_5879_);
                        v___x_5916_ = crate::leanh::lean_box(0);
                        v_isShared_5917_ = v_isSharedCheck_5921_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_toRing_5884_ = crate::leanh::lean_ctor_get(v_a_5880_, 0);
                crate::leanh::lean_inc_ref(v_toRing_5884_);
                crate::leanh::lean_dec(v_a_5880_);
                v_powFn_x3f_5885_ = crate::leanh::lean_ctor_get(v_toRing_5884_, 10);
                if crate::leanh::lean_obj_tag(v_powFn_x3f_5885_) == 1 {
                    crate::leanh::lean_inc_ref(v_powFn_x3f_5885_);
                    crate::leanh::lean_dec_ref(v_toRing_5884_);
                    v_val_5886_ = crate::leanh::lean_ctor_get(v_powFn_x3f_5885_, 0);
                    crate::leanh::lean_inc(v_val_5886_);
                    crate::leanh::lean_dec_ref_known(v_powFn_x3f_5885_, 1);
                    if v_isShared_5883_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5882_, 0, v_val_5886_);
                        v___x_5888_ = v___x_5882_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5889_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5889_, 0, v_val_5886_);
                        v___x_5888_ = v_reuseFailAlloc_5889_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5882_);
                    v_type_5890_ = crate::leanh::lean_ctor_get(v_toRing_5884_, 1);
                    crate::leanh::lean_inc_ref(v_type_5890_);
                    v_u_5891_ = crate::leanh::lean_ctor_get(v_toRing_5884_, 2);
                    crate::leanh::lean_inc(v_u_5891_);
                    v_semiringInst_5892_ = crate::leanh::lean_ctor_get(v_toRing_5884_, 4);
                    crate::leanh::lean_inc_ref(v_semiringInst_5892_);
                    crate::leanh::lean_dec_ref(v_toRing_5884_);
                    v___x_5893_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(v_u_5891_, v_type_5890_, v_semiringInst_5892_, v___y_5867_, v___y_5868_, v___y_5869_, v___y_5870_, v___y_5871_, v___y_5872_, v___y_5873_, v___y_5874_, v___y_5875_, v___y_5876_, v___y_5877_);
                    if crate::leanh::lean_obj_tag(v___x_5893_) == 0 {
                        v_a_5894_ = crate::leanh::lean_ctor_get(v___x_5893_, 0);
                        crate::leanh::lean_inc_n(v_a_5894_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_5893_, 1);
                        v___f_5895_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___lam__0 as *mut core::ffi::c_void, 2, 1);
                        crate::leanh::lean_closure_set(v___f_5895_, 0, v_a_5894_);
                        v___x_5896_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(
                            v___f_5895_,
                            v___y_5867_,
                            v___y_5868_,
                            v___y_5869_,
                            v___y_5870_,
                            v___y_5871_,
                            v___y_5872_,
                            v___y_5873_,
                            v___y_5874_,
                            v___y_5875_,
                            v___y_5876_,
                            v___y_5877_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5896_) == 0 {
                            v_isSharedCheck_5903_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5896_)) as u8;
                            if v_isSharedCheck_5903_ == 0 {
                                v_unused_5904_ = crate::leanh::lean_ctor_get(v___x_5896_, 0);
                                crate::leanh::lean_dec(v_unused_5904_);
                                v___x_5898_ = v___x_5896_;
                                v_isShared_5899_ = v_isSharedCheck_5903_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_5896_);
                                v___x_5898_ = crate::leanh::lean_box(0);
                                v_isShared_5899_ = v_isSharedCheck_5903_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5894_);
                            v_a_5905_ = crate::leanh::lean_ctor_get(v___x_5896_, 0);
                            v_isSharedCheck_5912_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5896_)) as u8;
                            if v_isSharedCheck_5912_ == 0 {
                                v___x_5907_ = v___x_5896_;
                                v_isShared_5908_ = v_isSharedCheck_5912_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5905_);
                                crate::leanh::lean_dec(v___x_5896_);
                                v___x_5907_ = crate::leanh::lean_box(0);
                                v_isShared_5908_ = v_isSharedCheck_5912_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        return v___x_5893_;
                    }
                }
            }
            2 => {
                return v___x_5888_;
            }
            3 => {
                if v_isShared_5899_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5898_, 0, v_a_5894_);
                    v___x_5901_ = v___x_5898_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5902_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5902_, 0, v_a_5894_);
                    v___x_5901_ = v_reuseFailAlloc_5902_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5901_;
            }
            5 => {
                if v_isShared_5908_ == 0 {
                    v___x_5910_ = v___x_5907_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5911_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5911_, 0, v_a_5905_);
                    v___x_5910_ = v_reuseFailAlloc_5911_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5910_;
            }
            7 => {
                if v_isShared_5917_ == 0 {
                    v___x_5919_ = v___x_5916_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5920_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5920_, 0, v_a_5914_);
                    v___x_5919_ = v_reuseFailAlloc_5920_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5919_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___boxed(
    mut v___y_5922_: *mut crate::leanh::LeanObject,
    mut v___y_5923_: *mut crate::leanh::LeanObject,
    mut v___y_5924_: *mut crate::leanh::LeanObject,
    mut v___y_5925_: *mut crate::leanh::LeanObject,
    mut v___y_5926_: *mut crate::leanh::LeanObject,
    mut v___y_5927_: *mut crate::leanh::LeanObject,
    mut v___y_5928_: *mut crate::leanh::LeanObject,
    mut v___y_5929_: *mut crate::leanh::LeanObject,
    mut v___y_5930_: *mut crate::leanh::LeanObject,
    mut v___y_5931_: *mut crate::leanh::LeanObject,
    mut v___y_5932_: *mut crate::leanh::LeanObject,
    mut v___y_5933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5934_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(v___y_5922_, v___y_5923_, v___y_5924_, v___y_5925_, v___y_5926_, v___y_5927_, v___y_5928_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_);
    crate::leanh::lean_dec(v___y_5932_);
    crate::leanh::lean_dec_ref(v___y_5931_);
    crate::leanh::lean_dec(v___y_5930_);
    crate::leanh::lean_dec_ref(v___y_5929_);
    crate::leanh::lean_dec(v___y_5928_);
    crate::leanh::lean_dec_ref(v___y_5927_);
    crate::leanh::lean_dec(v___y_5926_);
    crate::leanh::lean_dec_ref(v___y_5925_);
    crate::leanh::lean_dec(v___y_5924_);
    crate::leanh::lean_dec(v___y_5923_);
    crate::leanh::lean_dec(v___y_5922_);
    return v_res_5934_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5938_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__2;
    v___x_5939_ = crate::leanh::lean_unsigned_to_nat(39);
    v___x_5940_ = crate::leanh::lean_unsigned_to_nat(159);
    v___x_5941_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__1;
    v___x_5942_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__0;
    v___x_5943_ = l_mkPanicMessageWithDecl(
        v___x_5942_,
        v___x_5941_,
        v___x_5940_,
        v___x_5939_,
        v___x_5938_,
    );
    return v___x_5943_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(
    mut v_a_5944_: *mut crate::leanh::LeanObject,
    mut v_a_5945_: *mut crate::leanh::LeanObject,
    mut v_a_5946_: *mut crate::leanh::LeanObject,
    mut v_a_5947_: *mut crate::leanh::LeanObject,
    mut v_a_5948_: *mut crate::leanh::LeanObject,
    mut v_a_5949_: *mut crate::leanh::LeanObject,
    mut v_a_5950_: *mut crate::leanh::LeanObject,
    mut v_a_5951_: *mut crate::leanh::LeanObject,
    mut v_a_5952_: *mut crate::leanh::LeanObject,
    mut v_a_5953_: *mut crate::leanh::LeanObject,
    mut v_a_5954_: *mut crate::leanh::LeanObject,
    mut v_a_5955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5969_: u8 = 0;
    let mut v___y_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSemiring_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5980_: u8 = 0;
    let mut v___x_5981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5983_: u8 = 0;
    let mut v_a_5984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5987_: u8 = 0;
    let mut v___x_5989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5991_: u8 = 0;
    let mut v_a_5992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6002_: u8 = 0;
    let mut v___x_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6007_: u8 = 0;
    let mut v_a_6008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6018_: u8 = 0;
    let mut v___x_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6023_: u8 = 0;
    let mut v_a_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6032_: u8 = 0;
    let mut v___x_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6038_: u8 = 0;
    let mut v___x_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_a_5944_) {
                0 => {
                    v_k_5957_ = crate::leanh::lean_ctor_get(v_a_5944_, 0);
                    crate::leanh::lean_inc(v_k_5957_);
                    crate::leanh::lean_dec_ref_known(v_a_5944_, 1);
                    v___x_5958_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v_k_5957_, v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_);
                    crate::leanh::lean_dec(v_k_5957_);
                    return v___x_5958_;
                }
                1 => {
                    v_k_5959_ = crate::leanh::lean_ctor_get(v_a_5944_, 0);
                    crate::leanh::lean_inc(v_k_5959_);
                    crate::leanh::lean_dec_ref_known(v_a_5944_, 1);
                    v___x_5960_ = lean_nat_to_int(v_k_5959_);
                    v___x_5961_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v___x_5960_, v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_);
                    crate::leanh::lean_dec(v___x_5960_);
                    return v___x_5961_;
                }
                3 => {
                    v_i_5962_ = crate::leanh::lean_ctor_get(v_a_5944_, 0);
                    crate::leanh::lean_inc(v_i_5962_);
                    crate::leanh::lean_dec_ref_known(v_a_5944_, 1);
                    v___x_5963_ = l_Lean_Meta_Grind_Arith_CommRing_getToQFn(
                        v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_,
                        v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5963_) == 0 {
                        v_a_5964_ = crate::leanh::lean_ctor_get(v___x_5963_, 0);
                        crate::leanh::lean_inc(v_a_5964_);
                        crate::leanh::lean_dec_ref_known(v___x_5963_, 1);
                        v___x_5965_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(
                            v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_,
                            v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5965_) == 0 {
                            v_a_5966_ = crate::leanh::lean_ctor_get(v___x_5965_, 0);
                            v_isSharedCheck_5983_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5965_)) as u8;
                            if v_isSharedCheck_5983_ == 0 {
                                v___x_5968_ = v___x_5965_;
                                v_isShared_5969_ = v_isSharedCheck_5983_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5966_);
                                crate::leanh::lean_dec(v___x_5965_);
                                v___x_5968_ = crate::leanh::lean_box(0);
                                v_isShared_5969_ = v_isSharedCheck_5983_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5964_);
                            crate::leanh::lean_dec(v_i_5962_);
                            v_a_5984_ = crate::leanh::lean_ctor_get(v___x_5965_, 0);
                            v_isSharedCheck_5991_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5965_)) as u8;
                            if v_isSharedCheck_5991_ == 0 {
                                v___x_5986_ = v___x_5965_;
                                v_isShared_5987_ = v_isSharedCheck_5991_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5984_);
                                crate::leanh::lean_dec(v___x_5965_);
                                v___x_5986_ = crate::leanh::lean_box(0);
                                v_isShared_5987_ = v_isSharedCheck_5991_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_i_5962_);
                        return v___x_5963_;
                    }
                }
                5 => {
                    v_a_5992_ = crate::leanh::lean_ctor_get(v_a_5944_, 0);
                    crate::leanh::lean_inc_ref(v_a_5992_);
                    v_b_5993_ = crate::leanh::lean_ctor_get(v_a_5944_, 1);
                    crate::leanh::lean_inc_ref(v_b_5993_);
                    crate::leanh::lean_dec_ref_known(v_a_5944_, 2);
                    v___x_5994_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_);
                    if crate::leanh::lean_obj_tag(v___x_5994_) == 0 {
                        v_a_5995_ = crate::leanh::lean_ctor_get(v___x_5994_, 0);
                        crate::leanh::lean_inc(v_a_5995_);
                        crate::leanh::lean_dec_ref_known(v___x_5994_, 1);
                        v___x_5996_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_5992_, v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_);
                        if crate::leanh::lean_obj_tag(v___x_5996_) == 0 {
                            v_a_5997_ = crate::leanh::lean_ctor_get(v___x_5996_, 0);
                            crate::leanh::lean_inc(v_a_5997_);
                            crate::leanh::lean_dec_ref_known(v___x_5996_, 1);
                            v___x_5998_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_b_5993_, v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_);
                            if crate::leanh::lean_obj_tag(v___x_5998_) == 0 {
                                v_a_5999_ = crate::leanh::lean_ctor_get(v___x_5998_, 0);
                                v_isSharedCheck_6007_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5998_)) as u8;
                                if v_isSharedCheck_6007_ == 0 {
                                    v___x_6001_ = v___x_5998_;
                                    v_isShared_6002_ = v_isSharedCheck_6007_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5999_);
                                    crate::leanh::lean_dec(v___x_5998_);
                                    v___x_6001_ = crate::leanh::lean_box(0);
                                    v_isShared_6002_ = v_isSharedCheck_6007_;
                                    state = 6;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5997_);
                                crate::leanh::lean_dec(v_a_5995_);
                                return v___x_5998_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5995_);
                            crate::leanh::lean_dec_ref(v_b_5993_);
                            return v___x_5996_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_5993_);
                        crate::leanh::lean_dec_ref(v_a_5992_);
                        return v___x_5994_;
                    }
                }
                7 => {
                    v_a_6008_ = crate::leanh::lean_ctor_get(v_a_5944_, 0);
                    crate::leanh::lean_inc_ref(v_a_6008_);
                    v_b_6009_ = crate::leanh::lean_ctor_get(v_a_5944_, 1);
                    crate::leanh::lean_inc_ref(v_b_6009_);
                    crate::leanh::lean_dec_ref_known(v_a_5944_, 2);
                    v___x_6010_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_);
                    if crate::leanh::lean_obj_tag(v___x_6010_) == 0 {
                        v_a_6011_ = crate::leanh::lean_ctor_get(v___x_6010_, 0);
                        crate::leanh::lean_inc(v_a_6011_);
                        crate::leanh::lean_dec_ref_known(v___x_6010_, 1);
                        v___x_6012_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_6008_, v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_);
                        if crate::leanh::lean_obj_tag(v___x_6012_) == 0 {
                            v_a_6013_ = crate::leanh::lean_ctor_get(v___x_6012_, 0);
                            crate::leanh::lean_inc(v_a_6013_);
                            crate::leanh::lean_dec_ref_known(v___x_6012_, 1);
                            v___x_6014_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_b_6009_, v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_);
                            if crate::leanh::lean_obj_tag(v___x_6014_) == 0 {
                                v_a_6015_ = crate::leanh::lean_ctor_get(v___x_6014_, 0);
                                v_isSharedCheck_6023_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6014_)) as u8;
                                if v_isSharedCheck_6023_ == 0 {
                                    v___x_6017_ = v___x_6014_;
                                    v_isShared_6018_ = v_isSharedCheck_6023_;
                                    state = 8;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6015_);
                                    crate::leanh::lean_dec(v___x_6014_);
                                    v___x_6017_ = crate::leanh::lean_box(0);
                                    v_isShared_6018_ = v_isSharedCheck_6023_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_6013_);
                                crate::leanh::lean_dec(v_a_6011_);
                                return v___x_6014_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_6011_);
                            crate::leanh::lean_dec_ref(v_b_6009_);
                            return v___x_6012_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_6009_);
                        crate::leanh::lean_dec_ref(v_a_6008_);
                        return v___x_6010_;
                    }
                }
                8 => {
                    v_a_6024_ = crate::leanh::lean_ctor_get(v_a_5944_, 0);
                    crate::leanh::lean_inc_ref(v_a_6024_);
                    v_k_6025_ = crate::leanh::lean_ctor_get(v_a_5944_, 1);
                    crate::leanh::lean_inc(v_k_6025_);
                    crate::leanh::lean_dec_ref_known(v_a_5944_, 2);
                    v___x_6026_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_);
                    if crate::leanh::lean_obj_tag(v___x_6026_) == 0 {
                        v_a_6027_ = crate::leanh::lean_ctor_get(v___x_6026_, 0);
                        crate::leanh::lean_inc(v_a_6027_);
                        crate::leanh::lean_dec_ref_known(v___x_6026_, 1);
                        v___x_6028_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_6024_, v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_);
                        if crate::leanh::lean_obj_tag(v___x_6028_) == 0 {
                            v_a_6029_ = crate::leanh::lean_ctor_get(v___x_6028_, 0);
                            v_isSharedCheck_6038_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6028_)) as u8;
                            if v_isSharedCheck_6038_ == 0 {
                                v___x_6031_ = v___x_6028_;
                                v_isShared_6032_ = v_isSharedCheck_6038_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6029_);
                                crate::leanh::lean_dec(v___x_6028_);
                                v___x_6031_ = crate::leanh::lean_box(0);
                                v_isShared_6032_ = v_isSharedCheck_6038_;
                                state = 10;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_6027_);
                            crate::leanh::lean_dec(v_k_6025_);
                            return v___x_6028_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_k_6025_);
                        crate::leanh::lean_dec_ref(v_a_6024_);
                        return v___x_6026_;
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_a_5944_);
                    v___x_6039_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3);
                    v___x_6040_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(v___x_6039_, v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_);
                    return v___x_6040_;
                }
            },
            1 => {
                v_toSemiring_5976_ = crate::leanh::lean_ctor_get(v_a_5966_, 0);
                crate::leanh::lean_inc_ref(v_toSemiring_5976_);
                crate::leanh::lean_dec(v_a_5966_);
                v_vars_5977_ = crate::leanh::lean_ctor_get(v_toSemiring_5976_, 9);
                crate::leanh::lean_inc_ref(v_vars_5977_);
                crate::leanh::lean_dec_ref(v_toSemiring_5976_);
                v_size_5978_ = crate::leanh::lean_ctor_get(v_vars_5977_, 2);
                v___x_5979_ = l_Lean_instInhabitedExpr;
                v___x_5980_ = lean_nat_dec_lt(v_i_5962_, v_size_5978_);
                if v___x_5980_ == 0 {
                    crate::leanh::lean_dec_ref(v_vars_5977_);
                    crate::leanh::lean_dec(v_i_5962_);
                    v___x_5981_ = l_outOfBounds___redArg(v___x_5979_);
                    v___y_5971_ = v___x_5981_;
                    state = 2;
                    continue;
                } else {
                    v___x_5982_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_5979_,
                        v_vars_5977_,
                        v_i_5962_,
                    );
                    crate::leanh::lean_dec(v_i_5962_);
                    crate::leanh::lean_dec_ref(v_vars_5977_);
                    v___y_5971_ = v___x_5982_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5972_ = l_Lean_Expr_app___override(v_a_5964_, v___y_5971_);
                if v_isShared_5969_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5968_, 0, v___x_5972_);
                    v___x_5974_ = v___x_5968_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5975_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5975_, 0, v___x_5972_);
                    v___x_5974_ = v_reuseFailAlloc_5975_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5974_;
            }
            4 => {
                if v_isShared_5987_ == 0 {
                    v___x_5989_ = v___x_5986_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5990_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5990_, 0, v_a_5984_);
                    v___x_5989_ = v_reuseFailAlloc_5990_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5989_;
            }
            6 => {
                v___x_6003_ = l_Lean_mkAppB(v_a_5995_, v_a_5997_, v_a_5999_);
                if v_isShared_6002_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6001_, 0, v___x_6003_);
                    v___x_6005_ = v___x_6001_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6006_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6006_, 0, v___x_6003_);
                    v___x_6005_ = v_reuseFailAlloc_6006_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6005_;
            }
            8 => {
                v___x_6019_ = l_Lean_mkAppB(v_a_6011_, v_a_6013_, v_a_6015_);
                if v_isShared_6018_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6017_, 0, v___x_6019_);
                    v___x_6021_ = v___x_6017_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6022_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6022_, 0, v___x_6019_);
                    v___x_6021_ = v_reuseFailAlloc_6022_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6021_;
            }
            10 => {
                v___x_6033_ = l_Lean_mkNatLit(v_k_6025_);
                v___x_6034_ = l_Lean_mkAppB(v_a_6027_, v_a_6029_, v___x_6033_);
                if v_isShared_6032_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6031_, 0, v___x_6034_);
                    v___x_6036_ = v___x_6031_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6037_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6037_, 0, v___x_6034_);
                    v___x_6036_ = v_reuseFailAlloc_6037_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6036_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___boxed(
    mut v_a_6041_: *mut crate::leanh::LeanObject,
    mut v_a_6042_: *mut crate::leanh::LeanObject,
    mut v_a_6043_: *mut crate::leanh::LeanObject,
    mut v_a_6044_: *mut crate::leanh::LeanObject,
    mut v_a_6045_: *mut crate::leanh::LeanObject,
    mut v_a_6046_: *mut crate::leanh::LeanObject,
    mut v_a_6047_: *mut crate::leanh::LeanObject,
    mut v_a_6048_: *mut crate::leanh::LeanObject,
    mut v_a_6049_: *mut crate::leanh::LeanObject,
    mut v_a_6050_: *mut crate::leanh::LeanObject,
    mut v_a_6051_: *mut crate::leanh::LeanObject,
    mut v_a_6052_: *mut crate::leanh::LeanObject,
    mut v_a_6053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6054_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_6041_, v_a_6042_, v_a_6043_, v_a_6044_, v_a_6045_, v_a_6046_, v_a_6047_, v_a_6048_, v_a_6049_, v_a_6050_, v_a_6051_, v_a_6052_);
    crate::leanh::lean_dec(v_a_6052_);
    crate::leanh::lean_dec_ref(v_a_6051_);
    crate::leanh::lean_dec(v_a_6050_);
    crate::leanh::lean_dec_ref(v_a_6049_);
    crate::leanh::lean_dec(v_a_6048_);
    crate::leanh::lean_dec_ref(v_a_6047_);
    crate::leanh::lean_dec(v_a_6046_);
    crate::leanh::lean_dec_ref(v_a_6045_);
    crate::leanh::lean_dec(v_a_6044_);
    crate::leanh::lean_dec(v_a_6043_);
    crate::leanh::lean_dec(v_a_6042_);
    return v_res_6054_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6(
    mut v_type_6055_: *mut crate::leanh::LeanObject,
    mut v___y_6056_: *mut crate::leanh::LeanObject,
    mut v___y_6057_: *mut crate::leanh::LeanObject,
    mut v___y_6058_: *mut crate::leanh::LeanObject,
    mut v___y_6059_: *mut crate::leanh::LeanObject,
    mut v___y_6060_: *mut crate::leanh::LeanObject,
    mut v___y_6061_: *mut crate::leanh::LeanObject,
    mut v___y_6062_: *mut crate::leanh::LeanObject,
    mut v___y_6063_: *mut crate::leanh::LeanObject,
    mut v___y_6064_: *mut crate::leanh::LeanObject,
    mut v___y_6065_: *mut crate::leanh::LeanObject,
    mut v___y_6066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6068_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v_type_6055_, v___y_6063_, v___y_6064_, v___y_6065_, v___y_6066_);
    return v___x_6068_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___boxed(
    mut v_type_6069_: *mut crate::leanh::LeanObject,
    mut v___y_6070_: *mut crate::leanh::LeanObject,
    mut v___y_6071_: *mut crate::leanh::LeanObject,
    mut v___y_6072_: *mut crate::leanh::LeanObject,
    mut v___y_6073_: *mut crate::leanh::LeanObject,
    mut v___y_6074_: *mut crate::leanh::LeanObject,
    mut v___y_6075_: *mut crate::leanh::LeanObject,
    mut v___y_6076_: *mut crate::leanh::LeanObject,
    mut v___y_6077_: *mut crate::leanh::LeanObject,
    mut v___y_6078_: *mut crate::leanh::LeanObject,
    mut v___y_6079_: *mut crate::leanh::LeanObject,
    mut v___y_6080_: *mut crate::leanh::LeanObject,
    mut v___y_6081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6082_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6(v_type_6069_, v___y_6070_, v___y_6071_, v___y_6072_, v___y_6073_, v___y_6074_, v___y_6075_, v___y_6076_, v___y_6077_, v___y_6078_, v___y_6079_, v___y_6080_);
    crate::leanh::lean_dec(v___y_6080_);
    crate::leanh::lean_dec_ref(v___y_6079_);
    crate::leanh::lean_dec(v___y_6078_);
    crate::leanh::lean_dec_ref(v___y_6077_);
    crate::leanh::lean_dec(v___y_6076_);
    crate::leanh::lean_dec_ref(v___y_6075_);
    crate::leanh::lean_dec(v___y_6074_);
    crate::leanh::lean_dec_ref(v___y_6073_);
    crate::leanh::lean_dec(v___y_6072_);
    crate::leanh::lean_dec(v___y_6071_);
    crate::leanh::lean_dec(v___y_6070_);
    return v_res_6082_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(
    mut v_e_6083_: *mut crate::leanh::LeanObject,
    mut v_a_6084_: *mut crate::leanh::LeanObject,
    mut v_a_6085_: *mut crate::leanh::LeanObject,
    mut v_a_6086_: *mut crate::leanh::LeanObject,
    mut v_a_6087_: *mut crate::leanh::LeanObject,
    mut v_a_6088_: *mut crate::leanh::LeanObject,
    mut v_a_6089_: *mut crate::leanh::LeanObject,
    mut v_a_6090_: *mut crate::leanh::LeanObject,
    mut v_a_6091_: *mut crate::leanh::LeanObject,
    mut v_a_6092_: *mut crate::leanh::LeanObject,
    mut v_a_6093_: *mut crate::leanh::LeanObject,
    mut v_a_6094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6096_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_e_6083_, v_a_6084_, v_a_6085_, v_a_6086_, v_a_6087_, v_a_6088_, v_a_6089_, v_a_6090_, v_a_6091_, v_a_6092_, v_a_6093_, v_a_6094_);
    if crate::leanh::lean_obj_tag(v___x_6096_) == 0 {
        let mut v_a_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_6097_ = crate::leanh::lean_ctor_get(v___x_6096_, 0);
        crate::leanh::lean_inc(v_a_6097_);
        crate::leanh::lean_dec_ref_known(v___x_6096_, 1);
        v___x_6098_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_6097_, v_a_6090_);
        return v___x_6098_;
    } else {
        return v___x_6096_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteAsRingExpr___boxed(
    mut v_e_6099_: *mut crate::leanh::LeanObject,
    mut v_a_6100_: *mut crate::leanh::LeanObject,
    mut v_a_6101_: *mut crate::leanh::LeanObject,
    mut v_a_6102_: *mut crate::leanh::LeanObject,
    mut v_a_6103_: *mut crate::leanh::LeanObject,
    mut v_a_6104_: *mut crate::leanh::LeanObject,
    mut v_a_6105_: *mut crate::leanh::LeanObject,
    mut v_a_6106_: *mut crate::leanh::LeanObject,
    mut v_a_6107_: *mut crate::leanh::LeanObject,
    mut v_a_6108_: *mut crate::leanh::LeanObject,
    mut v_a_6109_: *mut crate::leanh::LeanObject,
    mut v_a_6110_: *mut crate::leanh::LeanObject,
    mut v_a_6111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6112_ = l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(
        v_e_6099_, v_a_6100_, v_a_6101_, v_a_6102_, v_a_6103_, v_a_6104_, v_a_6105_, v_a_6106_,
        v_a_6107_, v_a_6108_, v_a_6109_, v_a_6110_,
    );
    crate::leanh::lean_dec(v_a_6110_);
    crate::leanh::lean_dec_ref(v_a_6109_);
    crate::leanh::lean_dec(v_a_6108_);
    crate::leanh::lean_dec_ref(v_a_6107_);
    crate::leanh::lean_dec(v_a_6106_);
    crate::leanh::lean_dec_ref(v_a_6105_);
    crate::leanh::lean_dec(v_a_6104_);
    crate::leanh::lean_dec_ref(v_a_6103_);
    crate::leanh::lean_dec(v_a_6102_);
    crate::leanh::lean_dec(v_a_6101_);
    crate::leanh::lean_dec(v_a_6100_);
    return v_res_6112_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadSemiring(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM =
        _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM();
    crate::leanh::lean_mark_persistent(
        l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM,
    );
    l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM =
        _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadSemiring(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(builtin);
}
