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
    m_fun: l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__1_value:
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
    m_fun: l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__2_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__0_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__1_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__0_value:
    leanh::LeanStringObject<43> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___boxed
        as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__0_value:
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
static mut l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___boxed
        as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value:
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
    m_data: [71, 114, 105, 110, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__2_value:
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
    m_data: [82, 105, 110, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__3_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__4_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__4_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value)
            as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__2_value)
            as *mut leanh::LeanObject,
        10806710915646349764 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__3_value)
            as *mut leanh::LeanObject,
        8254287559757149654 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value_aux_3)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__4_value)
            as *mut leanh::LeanObject,
        5073726620895580904 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__0_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,17313347264508353403 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__2_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [65, 100, 100, 82, 105, 103, 104, 116, 67, 97, 110, 99, 101, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__2_value) as *mut leanh::LeanObject,2425446158037902625 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__0_value:
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
    m_data: [105, 110, 115, 116, 72, 65, 100, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__0_value
        ) as *mut leanh::LeanObject,
        9594062259507646949 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__2_value:
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
    m_data: [83, 101, 109, 105, 114, 105, 110, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__3_value:
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
    m_data: [116, 111, 65, 100, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__3_value
) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value)
            as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__2_value
        ) as *mut leanh::LeanObject,
        12050285396929189622 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__3_value
        ) as *mut leanh::LeanObject,
        5442360487226035463 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__5_value:
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
    m_data: [72, 65, 100, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__6_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__5_value
        ) as *mut leanh::LeanObject,
        10393083817453678557 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__6_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__7_value:
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
    m_data: [104, 65, 100, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__7_value
) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__5_value
        ) as *mut leanh::LeanObject,
        10393083817453678557 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__7_value
        ) as *mut leanh::LeanObject,
        10680564408669940870 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__8_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__0_value:
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
    m_data: [105, 110, 115, 116, 72, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__0_value
        ) as *mut leanh::LeanObject,
        18134279130838690737 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__2_value:
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
    m_data: [116, 111, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__2_value
) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value)
            as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__2_value
        ) as *mut leanh::LeanObject,
        12050285396929189622 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__2_value
        ) as *mut leanh::LeanObject,
        7102027102192867304 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__4_value:
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
    m_data: [72, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__5_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__4_value
        ) as *mut leanh::LeanObject,
        2929883540436775422 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__6_value:
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
    m_data: [104, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__6_value
) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__4_value
        ) as *mut leanh::LeanObject,
        2929883540436775422 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__6_value
        ) as *mut leanh::LeanObject,
        1611444129324655608 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__7_value
) as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__0_value:
    leanh::LeanStringObject<38> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0_value:
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
static mut l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__1_value:
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
static mut l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__0_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 102, 105, 110, 100, 32, 105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 111, 78, 101, 103, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__0_value) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__2_value) as *mut leanh::LeanObject,10806710915646349764 as *mut leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__0_value) as *mut leanh::LeanObject,10040236838748678500 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 101, 103, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__2_value) as *mut leanh::LeanObject,9626815015619986526 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__4_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 101, 103, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__4_value) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__2_value) as *mut leanh::LeanObject,9626815015619986526 as *mut leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__4_value) as *mut leanh::LeanObject,17185717442815859305 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__0_value) as *mut leanh::LeanObject,17636616155771105671 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__2_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__2_value) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__0_value) as *mut leanh::LeanObject,17636616155771105671 as *mut leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__2_value) as *mut leanh::LeanObject,15578568367168711682 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__3_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__2_value) as *mut leanh::LeanObject,12050285396929189622 as *mut leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__2_value) as *mut leanh::LeanObject,9341924117480681831 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 80, 111, 119, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__0_value) as *mut leanh::LeanObject,12847922472053947547 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__3_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 112, 111, 119, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__3_value) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__2_value) as *mut leanh::LeanObject,12050285396929189622 as *mut leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__3_value) as *mut leanh::LeanObject,18388652353510661091 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__5_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 80, 111, 119, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__5_value) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__0_value) as *mut leanh::LeanObject,12847922472053947547 as *mut leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__5_value) as *mut leanh::LeanObject,10422657989269798688 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__0_value: leanh::LeanStringObject<48> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 48, m_capacity: 48, m_length: 47, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 67, 111, 109, 109, 82, 105, 110, 103, 46, 83, 101, 109, 105, 114, 105, 110, 103, 77, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__1_value: leanh::LeanStringObject<104> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 104, m_capacity: 104, m_length: 103, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 67, 111, 109, 109, 82, 105, 110, 103, 46, 83, 101, 109, 105, 114, 105, 110, 103, 77, 46, 48, 46, 76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 67, 111, 109, 109, 82, 105, 110, 103, 46, 69, 120, 112, 114, 46, 100, 101, 110, 111, 116, 101, 65, 115, 82, 105, 110, 103, 69, 120, 112, 114, 46, 103, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__2_value: leanh::LeanStringObject<34> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___redArg(
    mut v_semiringId_3057_: *mut leanh::LeanObject,
    mut v_x_3058_: *mut leanh::LeanObject,
    mut v_a_3059_: *mut leanh::LeanObject,
    mut v_a_3060_: *mut leanh::LeanObject,
    mut v_a_3061_: *mut leanh::LeanObject,
    mut v_a_3062_: *mut leanh::LeanObject,
    mut v_a_3063_: *mut leanh::LeanObject,
    mut v_a_3064_: *mut leanh::LeanObject,
    mut v_a_3065_: *mut leanh::LeanObject,
    mut v_a_3066_: *mut leanh::LeanObject,
    mut v_a_3067_: *mut leanh::LeanObject,
    mut v_a_3068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_3068_);
    leanh::lean_inc_ref(v_a_3067_);
    leanh::lean_inc(v_a_3066_);
    leanh::lean_inc_ref(v_a_3065_);
    leanh::lean_inc(v_a_3064_);
    leanh::lean_inc_ref(v_a_3063_);
    leanh::lean_inc(v_a_3062_);
    leanh::lean_inc_ref(v_a_3061_);
    leanh::lean_inc(v_a_3060_);
    leanh::lean_inc(v_a_3059_);
    v___x_3070_ = leanh::lean_apply_12(
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
        leanh::lean_box(0),
    );
    return v___x_3070_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___redArg___boxed(
    mut v_semiringId_3071_: *mut leanh::LeanObject,
    mut v_x_3072_: *mut leanh::LeanObject,
    mut v_a_3073_: *mut leanh::LeanObject,
    mut v_a_3074_: *mut leanh::LeanObject,
    mut v_a_3075_: *mut leanh::LeanObject,
    mut v_a_3076_: *mut leanh::LeanObject,
    mut v_a_3077_: *mut leanh::LeanObject,
    mut v_a_3078_: *mut leanh::LeanObject,
    mut v_a_3079_: *mut leanh::LeanObject,
    mut v_a_3080_: *mut leanh::LeanObject,
    mut v_a_3081_: *mut leanh::LeanObject,
    mut v_a_3082_: *mut leanh::LeanObject,
    mut v_a_3083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_3082_);
    leanh::lean_dec_ref(v_a_3081_);
    leanh::lean_dec(v_a_3080_);
    leanh::lean_dec_ref(v_a_3079_);
    leanh::lean_dec(v_a_3078_);
    leanh::lean_dec_ref(v_a_3077_);
    leanh::lean_dec(v_a_3076_);
    leanh::lean_dec_ref(v_a_3075_);
    leanh::lean_dec(v_a_3074_);
    leanh::lean_dec(v_a_3073_);
    return v_res_3084_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run(
    mut v_00_u03b1_3085_: *mut leanh::LeanObject,
    mut v_semiringId_3086_: *mut leanh::LeanObject,
    mut v_x_3087_: *mut leanh::LeanObject,
    mut v_a_3088_: *mut leanh::LeanObject,
    mut v_a_3089_: *mut leanh::LeanObject,
    mut v_a_3090_: *mut leanh::LeanObject,
    mut v_a_3091_: *mut leanh::LeanObject,
    mut v_a_3092_: *mut leanh::LeanObject,
    mut v_a_3093_: *mut leanh::LeanObject,
    mut v_a_3094_: *mut leanh::LeanObject,
    mut v_a_3095_: *mut leanh::LeanObject,
    mut v_a_3096_: *mut leanh::LeanObject,
    mut v_a_3097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_3097_);
    leanh::lean_inc_ref(v_a_3096_);
    leanh::lean_inc(v_a_3095_);
    leanh::lean_inc_ref(v_a_3094_);
    leanh::lean_inc(v_a_3093_);
    leanh::lean_inc_ref(v_a_3092_);
    leanh::lean_inc(v_a_3091_);
    leanh::lean_inc_ref(v_a_3090_);
    leanh::lean_inc(v_a_3089_);
    leanh::lean_inc(v_a_3088_);
    v___x_3099_ = leanh::lean_apply_12(
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
        leanh::lean_box(0),
    );
    return v___x_3099_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_run___boxed(
    mut v_00_u03b1_3100_: *mut leanh::LeanObject,
    mut v_semiringId_3101_: *mut leanh::LeanObject,
    mut v_x_3102_: *mut leanh::LeanObject,
    mut v_a_3103_: *mut leanh::LeanObject,
    mut v_a_3104_: *mut leanh::LeanObject,
    mut v_a_3105_: *mut leanh::LeanObject,
    mut v_a_3106_: *mut leanh::LeanObject,
    mut v_a_3107_: *mut leanh::LeanObject,
    mut v_a_3108_: *mut leanh::LeanObject,
    mut v_a_3109_: *mut leanh::LeanObject,
    mut v_a_3110_: *mut leanh::LeanObject,
    mut v_a_3111_: *mut leanh::LeanObject,
    mut v_a_3112_: *mut leanh::LeanObject,
    mut v_a_3113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_3112_);
    leanh::lean_dec_ref(v_a_3111_);
    leanh::lean_dec(v_a_3110_);
    leanh::lean_dec_ref(v_a_3109_);
    leanh::lean_dec(v_a_3108_);
    leanh::lean_dec_ref(v_a_3107_);
    leanh::lean_dec(v_a_3106_);
    leanh::lean_dec_ref(v_a_3105_);
    leanh::lean_dec(v_a_3104_);
    leanh::lean_dec(v_a_3103_);
    return v_res_3114_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___redArg(
    mut v_a_3115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_3115_);
    v___x_3117_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3117_, 0, v_a_3115_);
    return v___x_3117_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___redArg___boxed(
    mut v_a_3118_: *mut leanh::LeanObject,
    mut v_a_3119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3120_ = l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___redArg(v_a_3118_);
    leanh::lean_dec(v_a_3118_);
    return v_res_3120_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getSemiringId(
    mut v_a_3121_: *mut leanh::LeanObject,
    mut v_a_3122_: *mut leanh::LeanObject,
    mut v_a_3123_: *mut leanh::LeanObject,
    mut v_a_3124_: *mut leanh::LeanObject,
    mut v_a_3125_: *mut leanh::LeanObject,
    mut v_a_3126_: *mut leanh::LeanObject,
    mut v_a_3127_: *mut leanh::LeanObject,
    mut v_a_3128_: *mut leanh::LeanObject,
    mut v_a_3129_: *mut leanh::LeanObject,
    mut v_a_3130_: *mut leanh::LeanObject,
    mut v_a_3131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_3121_);
    v___x_3133_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3133_, 0, v_a_3121_);
    return v___x_3133_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getSemiringId___boxed(
    mut v_a_3134_: *mut leanh::LeanObject,
    mut v_a_3135_: *mut leanh::LeanObject,
    mut v_a_3136_: *mut leanh::LeanObject,
    mut v_a_3137_: *mut leanh::LeanObject,
    mut v_a_3138_: *mut leanh::LeanObject,
    mut v_a_3139_: *mut leanh::LeanObject,
    mut v_a_3140_: *mut leanh::LeanObject,
    mut v_a_3141_: *mut leanh::LeanObject,
    mut v_a_3142_: *mut leanh::LeanObject,
    mut v_a_3143_: *mut leanh::LeanObject,
    mut v_a_3144_: *mut leanh::LeanObject,
    mut v_a_3145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3146_ = l_Lean_Meta_Grind_Arith_CommRing_getSemiringId(
        v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_, v_a_3138_, v_a_3139_, v_a_3140_, v_a_3141_,
        v_a_3142_, v_a_3143_, v_a_3144_,
    );
    leanh::lean_dec(v_a_3144_);
    leanh::lean_dec_ref(v_a_3143_);
    leanh::lean_dec(v_a_3142_);
    leanh::lean_dec_ref(v_a_3141_);
    leanh::lean_dec(v_a_3140_);
    leanh::lean_dec_ref(v_a_3139_);
    leanh::lean_dec(v_a_3138_);
    leanh::lean_dec_ref(v_a_3137_);
    leanh::lean_dec(v_a_3136_);
    leanh::lean_dec(v_a_3135_);
    leanh::lean_dec(v_a_3134_);
    return v_res_3146_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0(
    mut v_e_3147_: *mut leanh::LeanObject,
    mut v___y_3148_: *mut leanh::LeanObject,
    mut v___y_3149_: *mut leanh::LeanObject,
    mut v___y_3150_: *mut leanh::LeanObject,
    mut v___y_3151_: *mut leanh::LeanObject,
    mut v___y_3152_: *mut leanh::LeanObject,
    mut v___y_3153_: *mut leanh::LeanObject,
    mut v___y_3154_: *mut leanh::LeanObject,
    mut v___y_3155_: *mut leanh::LeanObject,
    mut v___y_3156_: *mut leanh::LeanObject,
    mut v___y_3157_: *mut leanh::LeanObject,
    mut v___y_3158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3160_ = l_Lean_Meta_Sym_canon(
        v_e_3147_,
        v___y_3153_,
        v___y_3154_,
        v___y_3155_,
        v___y_3156_,
        v___y_3157_,
        v___y_3158_,
    );
    if leanh::lean_obj_tag(v___x_3160_) == 0 {
        let mut v_a_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_3161_ = leanh::lean_ctor_get(v___x_3160_, 0);
        leanh::lean_inc(v_a_3161_);
        leanh::lean_dec_ref_known(v___x_3160_, 1);
        v___x_3162_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_3161_, v___y_3154_);
        return v___x_3162_;
    } else {
        return v___x_3160_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__0___boxed(
    mut v_e_3163_: *mut leanh::LeanObject,
    mut v___y_3164_: *mut leanh::LeanObject,
    mut v___y_3165_: *mut leanh::LeanObject,
    mut v___y_3166_: *mut leanh::LeanObject,
    mut v___y_3167_: *mut leanh::LeanObject,
    mut v___y_3168_: *mut leanh::LeanObject,
    mut v___y_3169_: *mut leanh::LeanObject,
    mut v___y_3170_: *mut leanh::LeanObject,
    mut v___y_3171_: *mut leanh::LeanObject,
    mut v___y_3172_: *mut leanh::LeanObject,
    mut v___y_3173_: *mut leanh::LeanObject,
    mut v___y_3174_: *mut leanh::LeanObject,
    mut v___y_3175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_3174_);
    leanh::lean_dec_ref(v___y_3173_);
    leanh::lean_dec(v___y_3172_);
    leanh::lean_dec_ref(v___y_3171_);
    leanh::lean_dec(v___y_3170_);
    leanh::lean_dec_ref(v___y_3169_);
    leanh::lean_dec(v___y_3168_);
    leanh::lean_dec_ref(v___y_3167_);
    leanh::lean_dec(v___y_3166_);
    leanh::lean_dec(v___y_3165_);
    leanh::lean_dec(v___y_3164_);
    return v_res_3176_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonSemiringM___lam__1(
    mut v_e_3177_: *mut leanh::LeanObject,
    mut v___y_3178_: *mut leanh::LeanObject,
    mut v___y_3179_: *mut leanh::LeanObject,
    mut v___y_3180_: *mut leanh::LeanObject,
    mut v___y_3181_: *mut leanh::LeanObject,
    mut v___y_3182_: *mut leanh::LeanObject,
    mut v___y_3183_: *mut leanh::LeanObject,
    mut v___y_3184_: *mut leanh::LeanObject,
    mut v___y_3185_: *mut leanh::LeanObject,
    mut v___y_3186_: *mut leanh::LeanObject,
    mut v___y_3187_: *mut leanh::LeanObject,
    mut v___y_3188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_e_3191_: *mut leanh::LeanObject,
    mut v___y_3192_: *mut leanh::LeanObject,
    mut v___y_3193_: *mut leanh::LeanObject,
    mut v___y_3194_: *mut leanh::LeanObject,
    mut v___y_3195_: *mut leanh::LeanObject,
    mut v___y_3196_: *mut leanh::LeanObject,
    mut v___y_3197_: *mut leanh::LeanObject,
    mut v___y_3198_: *mut leanh::LeanObject,
    mut v___y_3199_: *mut leanh::LeanObject,
    mut v___y_3200_: *mut leanh::LeanObject,
    mut v___y_3201_: *mut leanh::LeanObject,
    mut v___y_3202_: *mut leanh::LeanObject,
    mut v___y_3203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_3202_);
    leanh::lean_dec_ref(v___y_3201_);
    leanh::lean_dec(v___y_3200_);
    leanh::lean_dec_ref(v___y_3199_);
    leanh::lean_dec(v___y_3198_);
    leanh::lean_dec_ref(v___y_3197_);
    leanh::lean_dec(v___y_3196_);
    leanh::lean_dec_ref(v___y_3195_);
    leanh::lean_dec(v___y_3194_);
    leanh::lean_dec(v___y_3193_);
    leanh::lean_dec(v___y_3192_);
    return v_res_3204_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0(
    mut v_msgData_3211_: *mut leanh::LeanObject,
    mut v___y_3212_: *mut leanh::LeanObject,
    mut v___y_3213_: *mut leanh::LeanObject,
    mut v___y_3214_: *mut leanh::LeanObject,
    mut v___y_3215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3217_ = lean_st_ref_get(v___y_3215_);
    v_env_3218_ = leanh::lean_ctor_get(v___x_3217_, 0);
    leanh::lean_inc_ref(v_env_3218_);
    leanh::lean_dec(v___x_3217_);
    v___x_3219_ = lean_st_ref_get(v___y_3213_);
    v_mctx_3220_ = leanh::lean_ctor_get(v___x_3219_, 0);
    leanh::lean_inc_ref(v_mctx_3220_);
    leanh::lean_dec(v___x_3219_);
    v_lctx_3221_ = leanh::lean_ctor_get(v___y_3212_, 2);
    v_options_3222_ = leanh::lean_ctor_get(v___y_3214_, 2);
    leanh::lean_inc_ref(v_options_3222_);
    leanh::lean_inc_ref(v_lctx_3221_);
    v___x_3223_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3223_, 0, v_env_3218_);
    leanh::lean_ctor_set(v___x_3223_, 1, v_mctx_3220_);
    leanh::lean_ctor_set(v___x_3223_, 2, v_lctx_3221_);
    leanh::lean_ctor_set(v___x_3223_, 3, v_options_3222_);
    v___x_3224_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3224_, 0, v___x_3223_);
    leanh::lean_ctor_set(v___x_3224_, 1, v_msgData_3211_);
    v___x_3225_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3225_, 0, v___x_3224_);
    return v___x_3225_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0___boxed(
    mut v_msgData_3226_: *mut leanh::LeanObject,
    mut v___y_3227_: *mut leanh::LeanObject,
    mut v___y_3228_: *mut leanh::LeanObject,
    mut v___y_3229_: *mut leanh::LeanObject,
    mut v___y_3230_: *mut leanh::LeanObject,
    mut v___y_3231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3232_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0(v_msgData_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
    leanh::lean_dec(v___y_3230_);
    leanh::lean_dec_ref(v___y_3229_);
    leanh::lean_dec(v___y_3228_);
    leanh::lean_dec_ref(v___y_3227_);
    return v_res_3232_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(
    mut v_msg_3233_: *mut leanh::LeanObject,
    mut v___y_3234_: *mut leanh::LeanObject,
    mut v___y_3235_: *mut leanh::LeanObject,
    mut v___y_3236_: *mut leanh::LeanObject,
    mut v___y_3237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3244_: u8 = 0;
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3249_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3239_ = leanh::lean_ctor_get(v___y_3236_, 5);
                v___x_3240_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0_spec__0(v_msg_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
                v_a_3241_ = leanh::lean_ctor_get(v___x_3240_, 0);
                v_isSharedCheck_3249_ = (!leanh::lean_is_exclusive(v___x_3240_)) as u8;
                if v_isSharedCheck_3249_ == 0 {
                    v___x_3243_ = v___x_3240_;
                    v_isShared_3244_ = v_isSharedCheck_3249_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3241_);
                    leanh::lean_dec(v___x_3240_);
                    v___x_3243_ = leanh::lean_box(0);
                    v_isShared_3244_ = v_isSharedCheck_3249_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_3239_);
                v___x_3245_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3245_, 0, v_ref_3239_);
                leanh::lean_ctor_set(v___x_3245_, 1, v_a_3241_);
                if v_isShared_3244_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3243_, 1);
                    leanh::lean_ctor_set(v___x_3243_, 0, v___x_3245_);
                    v___x_3247_ = v___x_3243_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3248_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3245_);
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
    mut v_msg_3250_: *mut leanh::LeanObject,
    mut v___y_3251_: *mut leanh::LeanObject,
    mut v___y_3252_: *mut leanh::LeanObject,
    mut v___y_3253_: *mut leanh::LeanObject,
    mut v___y_3254_: *mut leanh::LeanObject,
    mut v___y_3255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3256_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v_msg_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_);
    leanh::lean_dec(v___y_3254_);
    leanh::lean_dec_ref(v___y_3253_);
    leanh::lean_dec(v___y_3252_);
    leanh::lean_dec_ref(v___y_3251_);
    return v_res_3256_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3258_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__0;
    v___x_3259_ = l_Lean_stringToMessageData(v___x_3258_);
    return v___x_3259_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(
    mut v_a_3260_: *mut leanh::LeanObject,
    mut v_a_3261_: *mut leanh::LeanObject,
    mut v_a_3262_: *mut leanh::LeanObject,
    mut v_a_3263_: *mut leanh::LeanObject,
    mut v_a_3264_: *mut leanh::LeanObject,
    mut v_a_3265_: *mut leanh::LeanObject,
    mut v_a_3266_: *mut leanh::LeanObject,
    mut v_a_3267_: *mut leanh::LeanObject,
    mut v_a_3268_: *mut leanh::LeanObject,
    mut v_a_3269_: *mut leanh::LeanObject,
    mut v_a_3270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3276_: u8 = 0;
    let mut v_semirings_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: u8 = 0;
    let mut v___x_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3286_: u8 = 0;
    let mut v_a_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3290_: u8 = 0;
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3294_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3272_ =
                    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_3261_, v_a_3269_);
                if leanh::lean_obj_tag(v___x_3272_) == 0 {
                    v_a_3273_ = leanh::lean_ctor_get(v___x_3272_, 0);
                    v_isSharedCheck_3286_ = (!leanh::lean_is_exclusive(v___x_3272_)) as u8;
                    if v_isSharedCheck_3286_ == 0 {
                        v___x_3275_ = v___x_3272_;
                        v_isShared_3276_ = v_isSharedCheck_3286_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3273_);
                        leanh::lean_dec(v___x_3272_);
                        v___x_3275_ = leanh::lean_box(0);
                        v_isShared_3276_ = v_isSharedCheck_3286_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3287_ = leanh::lean_ctor_get(v___x_3272_, 0);
                    v_isSharedCheck_3294_ = (!leanh::lean_is_exclusive(v___x_3272_)) as u8;
                    if v_isSharedCheck_3294_ == 0 {
                        v___x_3289_ = v___x_3272_;
                        v_isShared_3290_ = v_isSharedCheck_3294_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3287_);
                        leanh::lean_dec(v___x_3272_);
                        v___x_3289_ = leanh::lean_box(0);
                        v_isShared_3290_ = v_isSharedCheck_3294_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_semirings_3277_ = leanh::lean_ctor_get(v_a_3273_, 3);
                leanh::lean_inc_ref(v_semirings_3277_);
                leanh::lean_dec(v_a_3273_);
                v___x_3278_ = lean_array_get_size(v_semirings_3277_);
                v___x_3279_ = lean_nat_dec_lt(v_a_3260_, v___x_3278_);
                if v___x_3279_ == 0 {
                    leanh::lean_dec_ref(v_semirings_3277_);
                    leanh::lean_del_object(v___x_3275_);
                    v___x_3280_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1_once), _init_l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___closed__1);
                    v___x_3281_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v___x_3280_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_);
                    return v___x_3281_;
                } else {
                    v___x_3282_ = lean_array_fget(v_semirings_3277_, v_a_3260_);
                    leanh::lean_dec_ref(v_semirings_3277_);
                    if v_isShared_3276_ == 0 {
                        leanh::lean_ctor_set(v___x_3275_, 0, v___x_3282_);
                        v___x_3284_ = v___x_3275_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3285_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3285_, 0, v___x_3282_);
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
                    v_reuseFailAlloc_3293_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_a_3287_);
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
    mut v_a_3295_: *mut leanh::LeanObject,
    mut v_a_3296_: *mut leanh::LeanObject,
    mut v_a_3297_: *mut leanh::LeanObject,
    mut v_a_3298_: *mut leanh::LeanObject,
    mut v_a_3299_: *mut leanh::LeanObject,
    mut v_a_3300_: *mut leanh::LeanObject,
    mut v_a_3301_: *mut leanh::LeanObject,
    mut v_a_3302_: *mut leanh::LeanObject,
    mut v_a_3303_: *mut leanh::LeanObject,
    mut v_a_3304_: *mut leanh::LeanObject,
    mut v_a_3305_: *mut leanh::LeanObject,
    mut v_a_3306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3307_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(
        v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_,
        v_a_3303_, v_a_3304_, v_a_3305_,
    );
    leanh::lean_dec(v_a_3305_);
    leanh::lean_dec_ref(v_a_3304_);
    leanh::lean_dec(v_a_3303_);
    leanh::lean_dec_ref(v_a_3302_);
    leanh::lean_dec(v_a_3301_);
    leanh::lean_dec_ref(v_a_3300_);
    leanh::lean_dec(v_a_3299_);
    leanh::lean_dec_ref(v_a_3298_);
    leanh::lean_dec(v_a_3297_);
    leanh::lean_dec(v_a_3296_);
    leanh::lean_dec(v_a_3295_);
    return v_res_3307_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0(
    mut v_00_u03b1_3308_: *mut leanh::LeanObject,
    mut v_msg_3309_: *mut leanh::LeanObject,
    mut v___y_3310_: *mut leanh::LeanObject,
    mut v___y_3311_: *mut leanh::LeanObject,
    mut v___y_3312_: *mut leanh::LeanObject,
    mut v___y_3313_: *mut leanh::LeanObject,
    mut v___y_3314_: *mut leanh::LeanObject,
    mut v___y_3315_: *mut leanh::LeanObject,
    mut v___y_3316_: *mut leanh::LeanObject,
    mut v___y_3317_: *mut leanh::LeanObject,
    mut v___y_3318_: *mut leanh::LeanObject,
    mut v___y_3319_: *mut leanh::LeanObject,
    mut v___y_3320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3322_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___redArg(v_msg_3309_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
    return v___x_3322_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring_spec__0___boxed(
    mut v_00_u03b1_3323_: *mut leanh::LeanObject,
    mut v_msg_3324_: *mut leanh::LeanObject,
    mut v___y_3325_: *mut leanh::LeanObject,
    mut v___y_3326_: *mut leanh::LeanObject,
    mut v___y_3327_: *mut leanh::LeanObject,
    mut v___y_3328_: *mut leanh::LeanObject,
    mut v___y_3329_: *mut leanh::LeanObject,
    mut v___y_3330_: *mut leanh::LeanObject,
    mut v___y_3331_: *mut leanh::LeanObject,
    mut v___y_3332_: *mut leanh::LeanObject,
    mut v___y_3333_: *mut leanh::LeanObject,
    mut v___y_3334_: *mut leanh::LeanObject,
    mut v___y_3335_: *mut leanh::LeanObject,
    mut v___y_3336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_3335_);
    leanh::lean_dec_ref(v___y_3334_);
    leanh::lean_dec(v___y_3333_);
    leanh::lean_dec_ref(v___y_3332_);
    leanh::lean_dec(v___y_3331_);
    leanh::lean_dec_ref(v___y_3330_);
    leanh::lean_dec(v___y_3329_);
    leanh::lean_dec_ref(v___y_3328_);
    leanh::lean_dec(v___y_3327_);
    leanh::lean_dec(v___y_3326_);
    leanh::lean_dec(v___y_3325_);
    return v_res_3337_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0(
    mut v_a_3338_: *mut leanh::LeanObject,
    mut v_f_3339_: *mut leanh::LeanObject,
    mut v_s_3340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_rings_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_3354_: u8 = 0;
    let mut v___x_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: u8 = 0;
    let mut v___x_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3359_: u8 = 0;
    let mut v_v_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3368_: u8 = 0;
    let mut v_unused_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_3341_ = leanh::lean_ctor_get(v_s_3340_, 0);
                v_typeIdOf_3342_ = leanh::lean_ctor_get(v_s_3340_, 1);
                v_exprToRingId_3343_ = leanh::lean_ctor_get(v_s_3340_, 2);
                v_semirings_3344_ = leanh::lean_ctor_get(v_s_3340_, 3);
                v_stypeIdOf_3345_ = leanh::lean_ctor_get(v_s_3340_, 4);
                v_exprToSemiringId_3346_ = leanh::lean_ctor_get(v_s_3340_, 5);
                v_ncRings_3347_ = leanh::lean_ctor_get(v_s_3340_, 6);
                v_exprToNCRingId_3348_ = leanh::lean_ctor_get(v_s_3340_, 7);
                v_nctypeIdOf_3349_ = leanh::lean_ctor_get(v_s_3340_, 8);
                v_ncSemirings_3350_ = leanh::lean_ctor_get(v_s_3340_, 9);
                v_exprToNCSemiringId_3351_ = leanh::lean_ctor_get(v_s_3340_, 10);
                v_ncstypeIdOf_3352_ = leanh::lean_ctor_get(v_s_3340_, 11);
                v_steps_3353_ = leanh::lean_ctor_get(v_s_3340_, 12);
                v_reportedMaxDegreeIssue_3354_ = leanh::lean_ctor_get_uint8(
                    v_s_3340_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v___x_3355_ = lean_array_get_size(v_semirings_3344_);
                v___x_3356_ = lean_nat_dec_lt(v_a_3338_, v___x_3355_);
                if v___x_3356_ == 0 {
                    leanh::lean_dec_ref(v_f_3339_);
                    return v_s_3340_;
                } else {
                    leanh::lean_inc(v_steps_3353_);
                    leanh::lean_inc_ref(v_ncstypeIdOf_3352_);
                    leanh::lean_inc_ref(v_exprToNCSemiringId_3351_);
                    leanh::lean_inc_ref(v_ncSemirings_3350_);
                    leanh::lean_inc_ref(v_nctypeIdOf_3349_);
                    leanh::lean_inc_ref(v_exprToNCRingId_3348_);
                    leanh::lean_inc_ref(v_ncRings_3347_);
                    leanh::lean_inc_ref(v_exprToSemiringId_3346_);
                    leanh::lean_inc_ref(v_stypeIdOf_3345_);
                    leanh::lean_inc_ref(v_semirings_3344_);
                    leanh::lean_inc_ref(v_exprToRingId_3343_);
                    leanh::lean_inc_ref(v_typeIdOf_3342_);
                    leanh::lean_inc_ref(v_rings_3341_);
                    v_isSharedCheck_3368_ = (!leanh::lean_is_exclusive(v_s_3340_)) as u8;
                    if v_isSharedCheck_3368_ == 0 {
                        v_unused_3369_ = leanh::lean_ctor_get(v_s_3340_, 12);
                        leanh::lean_dec(v_unused_3369_);
                        v_unused_3370_ = leanh::lean_ctor_get(v_s_3340_, 11);
                        leanh::lean_dec(v_unused_3370_);
                        v_unused_3371_ = leanh::lean_ctor_get(v_s_3340_, 10);
                        leanh::lean_dec(v_unused_3371_);
                        v_unused_3372_ = leanh::lean_ctor_get(v_s_3340_, 9);
                        leanh::lean_dec(v_unused_3372_);
                        v_unused_3373_ = leanh::lean_ctor_get(v_s_3340_, 8);
                        leanh::lean_dec(v_unused_3373_);
                        v_unused_3374_ = leanh::lean_ctor_get(v_s_3340_, 7);
                        leanh::lean_dec(v_unused_3374_);
                        v_unused_3375_ = leanh::lean_ctor_get(v_s_3340_, 6);
                        leanh::lean_dec(v_unused_3375_);
                        v_unused_3376_ = leanh::lean_ctor_get(v_s_3340_, 5);
                        leanh::lean_dec(v_unused_3376_);
                        v_unused_3377_ = leanh::lean_ctor_get(v_s_3340_, 4);
                        leanh::lean_dec(v_unused_3377_);
                        v_unused_3378_ = leanh::lean_ctor_get(v_s_3340_, 3);
                        leanh::lean_dec(v_unused_3378_);
                        v_unused_3379_ = leanh::lean_ctor_get(v_s_3340_, 2);
                        leanh::lean_dec(v_unused_3379_);
                        v_unused_3380_ = leanh::lean_ctor_get(v_s_3340_, 1);
                        leanh::lean_dec(v_unused_3380_);
                        v_unused_3381_ = leanh::lean_ctor_get(v_s_3340_, 0);
                        leanh::lean_dec(v_unused_3381_);
                        v___x_3358_ = v_s_3340_;
                        v_isShared_3359_ = v_isSharedCheck_3368_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_s_3340_);
                        v___x_3358_ = leanh::lean_box(0);
                        v_isShared_3359_ = v_isSharedCheck_3368_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3360_ = lean_array_fget(v_semirings_3344_, v_a_3338_);
                v___x_3361_ = leanh::lean_box(0);
                v_xs_x27_3362_ = lean_array_fset(v_semirings_3344_, v_a_3338_, v___x_3361_);
                v___x_3363_ = leanh::lean_apply_1(v_f_3339_, v_v_3360_);
                v___x_3364_ = lean_array_fset(v_xs_x27_3362_, v_a_3338_, v___x_3363_);
                if v_isShared_3359_ == 0 {
                    leanh::lean_ctor_set(v___x_3358_, 3, v___x_3364_);
                    v___x_3366_ = v___x_3358_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3367_ = leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_rings_3341_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 1, v_typeIdOf_3342_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 2, v_exprToRingId_3343_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 3, v___x_3364_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 4, v_stypeIdOf_3345_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3367_,
                        5,
                        v_exprToSemiringId_3346_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 6, v_ncRings_3347_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 7, v_exprToNCRingId_3348_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 8, v_nctypeIdOf_3349_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 9, v_ncSemirings_3350_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3367_,
                        10,
                        v_exprToNCSemiringId_3351_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 11, v_ncstypeIdOf_3352_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 12, v_steps_3353_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3367_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
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
    mut v_a_3382_: *mut leanh::LeanObject,
    mut v_f_3383_: *mut leanh::LeanObject,
    mut v_s_3384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3385_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0(
        v_a_3382_, v_f_3383_, v_s_3384_,
    );
    leanh::lean_dec(v_a_3382_);
    return v_res_3385_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg(
    mut v_f_3386_: *mut leanh::LeanObject,
    mut v_a_3387_: *mut leanh::LeanObject,
    mut v_a_3388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_3387_);
    v___f_3390_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3390_, 0, v_a_3387_);
    leanh::lean_closure_set(v___f_3390_, 1, v_f_3386_);
    v___x_3391_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
    v___x_3392_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3391_, v___f_3390_, v_a_3388_);
    return v___x_3392_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___boxed(
    mut v_f_3393_: *mut leanh::LeanObject,
    mut v_a_3394_: *mut leanh::LeanObject,
    mut v_a_3395_: *mut leanh::LeanObject,
    mut v_a_3396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3397_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg(
        v_f_3393_, v_a_3394_, v_a_3395_,
    );
    leanh::lean_dec(v_a_3395_);
    leanh::lean_dec(v_a_3394_);
    return v_res_3397_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring(
    mut v_f_3398_: *mut leanh::LeanObject,
    mut v_a_3399_: *mut leanh::LeanObject,
    mut v_a_3400_: *mut leanh::LeanObject,
    mut v_a_3401_: *mut leanh::LeanObject,
    mut v_a_3402_: *mut leanh::LeanObject,
    mut v_a_3403_: *mut leanh::LeanObject,
    mut v_a_3404_: *mut leanh::LeanObject,
    mut v_a_3405_: *mut leanh::LeanObject,
    mut v_a_3406_: *mut leanh::LeanObject,
    mut v_a_3407_: *mut leanh::LeanObject,
    mut v_a_3408_: *mut leanh::LeanObject,
    mut v_a_3409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_3399_);
    v___f_3411_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3411_, 0, v_a_3399_);
    leanh::lean_closure_set(v___f_3411_, 1, v_f_3398_);
    v___x_3412_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
    v___x_3413_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3412_, v___f_3411_, v_a_3400_);
    return v___x_3413_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring___boxed(
    mut v_f_3414_: *mut leanh::LeanObject,
    mut v_a_3415_: *mut leanh::LeanObject,
    mut v_a_3416_: *mut leanh::LeanObject,
    mut v_a_3417_: *mut leanh::LeanObject,
    mut v_a_3418_: *mut leanh::LeanObject,
    mut v_a_3419_: *mut leanh::LeanObject,
    mut v_a_3420_: *mut leanh::LeanObject,
    mut v_a_3421_: *mut leanh::LeanObject,
    mut v_a_3422_: *mut leanh::LeanObject,
    mut v_a_3423_: *mut leanh::LeanObject,
    mut v_a_3424_: *mut leanh::LeanObject,
    mut v_a_3425_: *mut leanh::LeanObject,
    mut v_a_3426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3427_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommSemiring(
        v_f_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_,
        v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_,
    );
    leanh::lean_dec(v_a_3425_);
    leanh::lean_dec_ref(v_a_3424_);
    leanh::lean_dec(v_a_3423_);
    leanh::lean_dec_ref(v_a_3422_);
    leanh::lean_dec(v_a_3421_);
    leanh::lean_dec_ref(v_a_3420_);
    leanh::lean_dec(v_a_3419_);
    leanh::lean_dec_ref(v_a_3418_);
    leanh::lean_dec(v_a_3417_);
    leanh::lean_dec(v_a_3416_);
    leanh::lean_dec(v_a_3415_);
    return v_res_3427_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3429_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM___closed__0;
    v___x_3430_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring___boxed
            as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_3431_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3431_, 0, v___x_3430_);
    leanh::lean_ctor_set(v___x_3431_, 1, v___x_3429_);
    return v___x_3431_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM()
-> *mut leanh::LeanObject {
    let mut v___x_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3432_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3434_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___closed__0;
    v___x_3435_ = l_Lean_stringToMessageData(v___x_3434_);
    return v___x_3435_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(
    mut v_a_3436_: *mut leanh::LeanObject,
    mut v_a_3437_: *mut leanh::LeanObject,
    mut v_a_3438_: *mut leanh::LeanObject,
    mut v_a_3439_: *mut leanh::LeanObject,
    mut v_a_3440_: *mut leanh::LeanObject,
    mut v_a_3441_: *mut leanh::LeanObject,
    mut v_a_3442_: *mut leanh::LeanObject,
    mut v_a_3443_: *mut leanh::LeanObject,
    mut v_a_3444_: *mut leanh::LeanObject,
    mut v_a_3445_: *mut leanh::LeanObject,
    mut v_a_3446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3454_: u8 = 0;
    let mut v_ringId_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rings_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: u8 = 0;
    let mut v___x_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3465_: u8 = 0;
    let mut v_a_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3469_: u8 = 0;
    let mut v___x_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3473_: u8 = 0;
    let mut v_a_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3477_: u8 = 0;
    let mut v___x_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3481_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3448_ =
                    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_3437_, v_a_3445_);
                if leanh::lean_obj_tag(v___x_3448_) == 0 {
                    v_a_3449_ = leanh::lean_ctor_get(v___x_3448_, 0);
                    leanh::lean_inc(v_a_3449_);
                    leanh::lean_dec_ref_known(v___x_3448_, 1);
                    v___x_3450_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(
                        v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_,
                        v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_,
                    );
                    if leanh::lean_obj_tag(v___x_3450_) == 0 {
                        v_a_3451_ = leanh::lean_ctor_get(v___x_3450_, 0);
                        v_isSharedCheck_3465_ =
                            (!leanh::lean_is_exclusive(v___x_3450_)) as u8;
                        if v_isSharedCheck_3465_ == 0 {
                            v___x_3453_ = v___x_3450_;
                            v_isShared_3454_ = v_isSharedCheck_3465_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3451_);
                            leanh::lean_dec(v___x_3450_);
                            v___x_3453_ = leanh::lean_box(0);
                            v_isShared_3454_ = v_isSharedCheck_3465_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3449_);
                        v_a_3466_ = leanh::lean_ctor_get(v___x_3450_, 0);
                        v_isSharedCheck_3473_ =
                            (!leanh::lean_is_exclusive(v___x_3450_)) as u8;
                        if v_isSharedCheck_3473_ == 0 {
                            v___x_3468_ = v___x_3450_;
                            v_isShared_3469_ = v_isSharedCheck_3473_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3466_);
                            leanh::lean_dec(v___x_3450_);
                            v___x_3468_ = leanh::lean_box(0);
                            v_isShared_3469_ = v_isSharedCheck_3473_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_3474_ = leanh::lean_ctor_get(v___x_3448_, 0);
                    v_isSharedCheck_3481_ = (!leanh::lean_is_exclusive(v___x_3448_)) as u8;
                    if v_isSharedCheck_3481_ == 0 {
                        v___x_3476_ = v___x_3448_;
                        v_isShared_3477_ = v_isSharedCheck_3481_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3474_);
                        leanh::lean_dec(v___x_3448_);
                        v___x_3476_ = leanh::lean_box(0);
                        v_isShared_3477_ = v_isSharedCheck_3481_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_ringId_3455_ = leanh::lean_ctor_get(v_a_3451_, 1);
                leanh::lean_inc(v_ringId_3455_);
                leanh::lean_dec(v_a_3451_);
                v_rings_3456_ = leanh::lean_ctor_get(v_a_3449_, 0);
                leanh::lean_inc_ref(v_rings_3456_);
                leanh::lean_dec(v_a_3449_);
                v___x_3457_ = lean_array_get_size(v_rings_3456_);
                v___x_3458_ = lean_nat_dec_lt(v_ringId_3455_, v___x_3457_);
                if v___x_3458_ == 0 {
                    leanh::lean_dec_ref(v_rings_3456_);
                    leanh::lean_dec(v_ringId_3455_);
                    leanh::lean_del_object(v___x_3453_);
                    v___x_3459_ = leanh::lean_obj_once(
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
                    leanh::lean_dec(v_ringId_3455_);
                    leanh::lean_dec_ref(v_rings_3456_);
                    if v_isShared_3454_ == 0 {
                        leanh::lean_ctor_set(v___x_3453_, 0, v___x_3461_);
                        v___x_3463_ = v___x_3453_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3464_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3461_);
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
                    v_reuseFailAlloc_3472_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_a_3466_);
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
                    v_reuseFailAlloc_3480_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3474_);
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
    mut v_a_3482_: *mut leanh::LeanObject,
    mut v_a_3483_: *mut leanh::LeanObject,
    mut v_a_3484_: *mut leanh::LeanObject,
    mut v_a_3485_: *mut leanh::LeanObject,
    mut v_a_3486_: *mut leanh::LeanObject,
    mut v_a_3487_: *mut leanh::LeanObject,
    mut v_a_3488_: *mut leanh::LeanObject,
    mut v_a_3489_: *mut leanh::LeanObject,
    mut v_a_3490_: *mut leanh::LeanObject,
    mut v_a_3491_: *mut leanh::LeanObject,
    mut v_a_3492_: *mut leanh::LeanObject,
    mut v_a_3493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3494_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing(
        v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_,
        v_a_3490_, v_a_3491_, v_a_3492_,
    );
    leanh::lean_dec(v_a_3492_);
    leanh::lean_dec_ref(v_a_3491_);
    leanh::lean_dec(v_a_3490_);
    leanh::lean_dec_ref(v_a_3489_);
    leanh::lean_dec(v_a_3488_);
    leanh::lean_dec_ref(v_a_3487_);
    leanh::lean_dec(v_a_3486_);
    leanh::lean_dec_ref(v_a_3485_);
    leanh::lean_dec(v_a_3484_);
    leanh::lean_dec(v_a_3483_);
    leanh::lean_dec(v_a_3482_);
    return v_res_3494_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0(
    mut v_ringId_3495_: *mut leanh::LeanObject,
    mut v_f_3496_: *mut leanh::LeanObject,
    mut v_s_3497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_rings_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_3511_: u8 = 0;
    let mut v___x_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: u8 = 0;
    let mut v___x_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3516_: u8 = 0;
    let mut v_v_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3525_: u8 = 0;
    let mut v_unused_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_3498_ = leanh::lean_ctor_get(v_s_3497_, 0);
                v_typeIdOf_3499_ = leanh::lean_ctor_get(v_s_3497_, 1);
                v_exprToRingId_3500_ = leanh::lean_ctor_get(v_s_3497_, 2);
                v_semirings_3501_ = leanh::lean_ctor_get(v_s_3497_, 3);
                v_stypeIdOf_3502_ = leanh::lean_ctor_get(v_s_3497_, 4);
                v_exprToSemiringId_3503_ = leanh::lean_ctor_get(v_s_3497_, 5);
                v_ncRings_3504_ = leanh::lean_ctor_get(v_s_3497_, 6);
                v_exprToNCRingId_3505_ = leanh::lean_ctor_get(v_s_3497_, 7);
                v_nctypeIdOf_3506_ = leanh::lean_ctor_get(v_s_3497_, 8);
                v_ncSemirings_3507_ = leanh::lean_ctor_get(v_s_3497_, 9);
                v_exprToNCSemiringId_3508_ = leanh::lean_ctor_get(v_s_3497_, 10);
                v_ncstypeIdOf_3509_ = leanh::lean_ctor_get(v_s_3497_, 11);
                v_steps_3510_ = leanh::lean_ctor_get(v_s_3497_, 12);
                v_reportedMaxDegreeIssue_3511_ = leanh::lean_ctor_get_uint8(
                    v_s_3497_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v___x_3512_ = lean_array_get_size(v_rings_3498_);
                v___x_3513_ = lean_nat_dec_lt(v_ringId_3495_, v___x_3512_);
                if v___x_3513_ == 0 {
                    leanh::lean_dec_ref(v_f_3496_);
                    return v_s_3497_;
                } else {
                    leanh::lean_inc(v_steps_3510_);
                    leanh::lean_inc_ref(v_ncstypeIdOf_3509_);
                    leanh::lean_inc_ref(v_exprToNCSemiringId_3508_);
                    leanh::lean_inc_ref(v_ncSemirings_3507_);
                    leanh::lean_inc_ref(v_nctypeIdOf_3506_);
                    leanh::lean_inc_ref(v_exprToNCRingId_3505_);
                    leanh::lean_inc_ref(v_ncRings_3504_);
                    leanh::lean_inc_ref(v_exprToSemiringId_3503_);
                    leanh::lean_inc_ref(v_stypeIdOf_3502_);
                    leanh::lean_inc_ref(v_semirings_3501_);
                    leanh::lean_inc_ref(v_exprToRingId_3500_);
                    leanh::lean_inc_ref(v_typeIdOf_3499_);
                    leanh::lean_inc_ref(v_rings_3498_);
                    v_isSharedCheck_3525_ = (!leanh::lean_is_exclusive(v_s_3497_)) as u8;
                    if v_isSharedCheck_3525_ == 0 {
                        v_unused_3526_ = leanh::lean_ctor_get(v_s_3497_, 12);
                        leanh::lean_dec(v_unused_3526_);
                        v_unused_3527_ = leanh::lean_ctor_get(v_s_3497_, 11);
                        leanh::lean_dec(v_unused_3527_);
                        v_unused_3528_ = leanh::lean_ctor_get(v_s_3497_, 10);
                        leanh::lean_dec(v_unused_3528_);
                        v_unused_3529_ = leanh::lean_ctor_get(v_s_3497_, 9);
                        leanh::lean_dec(v_unused_3529_);
                        v_unused_3530_ = leanh::lean_ctor_get(v_s_3497_, 8);
                        leanh::lean_dec(v_unused_3530_);
                        v_unused_3531_ = leanh::lean_ctor_get(v_s_3497_, 7);
                        leanh::lean_dec(v_unused_3531_);
                        v_unused_3532_ = leanh::lean_ctor_get(v_s_3497_, 6);
                        leanh::lean_dec(v_unused_3532_);
                        v_unused_3533_ = leanh::lean_ctor_get(v_s_3497_, 5);
                        leanh::lean_dec(v_unused_3533_);
                        v_unused_3534_ = leanh::lean_ctor_get(v_s_3497_, 4);
                        leanh::lean_dec(v_unused_3534_);
                        v_unused_3535_ = leanh::lean_ctor_get(v_s_3497_, 3);
                        leanh::lean_dec(v_unused_3535_);
                        v_unused_3536_ = leanh::lean_ctor_get(v_s_3497_, 2);
                        leanh::lean_dec(v_unused_3536_);
                        v_unused_3537_ = leanh::lean_ctor_get(v_s_3497_, 1);
                        leanh::lean_dec(v_unused_3537_);
                        v_unused_3538_ = leanh::lean_ctor_get(v_s_3497_, 0);
                        leanh::lean_dec(v_unused_3538_);
                        v___x_3515_ = v_s_3497_;
                        v_isShared_3516_ = v_isSharedCheck_3525_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_s_3497_);
                        v___x_3515_ = leanh::lean_box(0);
                        v_isShared_3516_ = v_isSharedCheck_3525_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3517_ = lean_array_fget(v_rings_3498_, v_ringId_3495_);
                v___x_3518_ = leanh::lean_box(0);
                v_xs_x27_3519_ = lean_array_fset(v_rings_3498_, v_ringId_3495_, v___x_3518_);
                v___x_3520_ = leanh::lean_apply_1(v_f_3496_, v_v_3517_);
                v___x_3521_ = lean_array_fset(v_xs_x27_3519_, v_ringId_3495_, v___x_3520_);
                if v_isShared_3516_ == 0 {
                    leanh::lean_ctor_set(v___x_3515_, 0, v___x_3521_);
                    v___x_3523_ = v___x_3515_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3524_ = leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3521_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 1, v_typeIdOf_3499_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 2, v_exprToRingId_3500_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 3, v_semirings_3501_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 4, v_stypeIdOf_3502_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3524_,
                        5,
                        v_exprToSemiringId_3503_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 6, v_ncRings_3504_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 7, v_exprToNCRingId_3505_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 8, v_nctypeIdOf_3506_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 9, v_ncSemirings_3507_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3524_,
                        10,
                        v_exprToNCSemiringId_3508_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 11, v_ncstypeIdOf_3509_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3524_, 12, v_steps_3510_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3524_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
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
    mut v_ringId_3539_: *mut leanh::LeanObject,
    mut v_f_3540_: *mut leanh::LeanObject,
    mut v_s_3541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3542_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0(
        v_ringId_3539_,
        v_f_3540_,
        v_s_3541_,
    );
    leanh::lean_dec(v_ringId_3539_);
    return v_res_3542_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(
    mut v_f_3543_: *mut leanh::LeanObject,
    mut v_a_3544_: *mut leanh::LeanObject,
    mut v_a_3545_: *mut leanh::LeanObject,
    mut v_a_3546_: *mut leanh::LeanObject,
    mut v_a_3547_: *mut leanh::LeanObject,
    mut v_a_3548_: *mut leanh::LeanObject,
    mut v_a_3549_: *mut leanh::LeanObject,
    mut v_a_3550_: *mut leanh::LeanObject,
    mut v_a_3551_: *mut leanh::LeanObject,
    mut v_a_3552_: *mut leanh::LeanObject,
    mut v_a_3553_: *mut leanh::LeanObject,
    mut v_a_3554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringId_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3565_: u8 = 0;
    let mut v___x_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3569_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3556_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(
                    v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_,
                    v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_,
                );
                if leanh::lean_obj_tag(v___x_3556_) == 0 {
                    v_a_3557_ = leanh::lean_ctor_get(v___x_3556_, 0);
                    leanh::lean_inc(v_a_3557_);
                    leanh::lean_dec_ref_known(v___x_3556_, 1);
                    v_ringId_3558_ = leanh::lean_ctor_get(v_a_3557_, 1);
                    leanh::lean_inc(v_ringId_3558_);
                    leanh::lean_dec(v_a_3557_);
                    v___f_3559_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing___lam__0___boxed
                            as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    leanh::lean_closure_set(v___f_3559_, 0, v_ringId_3558_);
                    leanh::lean_closure_set(v___f_3559_, 1, v_f_3543_);
                    v___x_3560_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                    v___x_3561_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3560_, v___f_3559_, v_a_3545_);
                    return v___x_3561_;
                } else {
                    leanh::lean_dec_ref(v_f_3543_);
                    v_a_3562_ = leanh::lean_ctor_get(v___x_3556_, 0);
                    v_isSharedCheck_3569_ = (!leanh::lean_is_exclusive(v___x_3556_)) as u8;
                    if v_isSharedCheck_3569_ == 0 {
                        v___x_3564_ = v___x_3556_;
                        v_isShared_3565_ = v_isSharedCheck_3569_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3562_);
                        leanh::lean_dec(v___x_3556_);
                        v___x_3564_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3568_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3562_);
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
    mut v_f_3570_: *mut leanh::LeanObject,
    mut v_a_3571_: *mut leanh::LeanObject,
    mut v_a_3572_: *mut leanh::LeanObject,
    mut v_a_3573_: *mut leanh::LeanObject,
    mut v_a_3574_: *mut leanh::LeanObject,
    mut v_a_3575_: *mut leanh::LeanObject,
    mut v_a_3576_: *mut leanh::LeanObject,
    mut v_a_3577_: *mut leanh::LeanObject,
    mut v_a_3578_: *mut leanh::LeanObject,
    mut v_a_3579_: *mut leanh::LeanObject,
    mut v_a_3580_: *mut leanh::LeanObject,
    mut v_a_3581_: *mut leanh::LeanObject,
    mut v_a_3582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3583_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifyCommRing(
        v_f_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_,
        v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_,
    );
    leanh::lean_dec(v_a_3581_);
    leanh::lean_dec_ref(v_a_3580_);
    leanh::lean_dec(v_a_3579_);
    leanh::lean_dec_ref(v_a_3578_);
    leanh::lean_dec(v_a_3577_);
    leanh::lean_dec_ref(v_a_3576_);
    leanh::lean_dec(v_a_3575_);
    leanh::lean_dec_ref(v_a_3574_);
    leanh::lean_dec(v_a_3573_);
    leanh::lean_dec(v_a_3572_);
    leanh::lean_dec(v_a_3571_);
    return v_res_3583_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3585_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM___closed__0;
    v___x_3586_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommRing___boxed as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_3587_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3587_, 0, v___x_3586_);
    leanh::lean_ctor_set(v___x_3587_, 1, v___x_3585_);
    return v___x_3587_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM()
-> *mut leanh::LeanObject {
    let mut v___x_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3588_ = leanh::lean_obj_once(
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
    mut v_a_3589_: *mut leanh::LeanObject,
    mut v_a_3590_: *mut leanh::LeanObject,
    mut v_s_3591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_rings_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_3605_: u8 = 0;
    let mut v___x_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: u8 = 0;
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3610_: u8 = 0;
    let mut v_v_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSemiring_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringId_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addRightCancelInst_x3f_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3618_: u8 = 0;
    let mut v___x_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3629_: u8 = 0;
    let mut v_unused_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3631_: u8 = 0;
    let mut v_unused_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_3592_ = leanh::lean_ctor_get(v_s_3591_, 0);
                v_typeIdOf_3593_ = leanh::lean_ctor_get(v_s_3591_, 1);
                v_exprToRingId_3594_ = leanh::lean_ctor_get(v_s_3591_, 2);
                v_semirings_3595_ = leanh::lean_ctor_get(v_s_3591_, 3);
                v_stypeIdOf_3596_ = leanh::lean_ctor_get(v_s_3591_, 4);
                v_exprToSemiringId_3597_ = leanh::lean_ctor_get(v_s_3591_, 5);
                v_ncRings_3598_ = leanh::lean_ctor_get(v_s_3591_, 6);
                v_exprToNCRingId_3599_ = leanh::lean_ctor_get(v_s_3591_, 7);
                v_nctypeIdOf_3600_ = leanh::lean_ctor_get(v_s_3591_, 8);
                v_ncSemirings_3601_ = leanh::lean_ctor_get(v_s_3591_, 9);
                v_exprToNCSemiringId_3602_ = leanh::lean_ctor_get(v_s_3591_, 10);
                v_ncstypeIdOf_3603_ = leanh::lean_ctor_get(v_s_3591_, 11);
                v_steps_3604_ = leanh::lean_ctor_get(v_s_3591_, 12);
                v_reportedMaxDegreeIssue_3605_ = leanh::lean_ctor_get_uint8(
                    v_s_3591_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v___x_3606_ = lean_array_get_size(v_semirings_3595_);
                v___x_3607_ = lean_nat_dec_lt(v_a_3589_, v___x_3606_);
                if v___x_3607_ == 0 {
                    leanh::lean_dec_ref(v_a_3590_);
                    return v_s_3591_;
                } else {
                    leanh::lean_inc(v_steps_3604_);
                    leanh::lean_inc_ref(v_ncstypeIdOf_3603_);
                    leanh::lean_inc_ref(v_exprToNCSemiringId_3602_);
                    leanh::lean_inc_ref(v_ncSemirings_3601_);
                    leanh::lean_inc_ref(v_nctypeIdOf_3600_);
                    leanh::lean_inc_ref(v_exprToNCRingId_3599_);
                    leanh::lean_inc_ref(v_ncRings_3598_);
                    leanh::lean_inc_ref(v_exprToSemiringId_3597_);
                    leanh::lean_inc_ref(v_stypeIdOf_3596_);
                    leanh::lean_inc_ref(v_semirings_3595_);
                    leanh::lean_inc_ref(v_exprToRingId_3594_);
                    leanh::lean_inc_ref(v_typeIdOf_3593_);
                    leanh::lean_inc_ref(v_rings_3592_);
                    v_isSharedCheck_3631_ = (!leanh::lean_is_exclusive(v_s_3591_)) as u8;
                    if v_isSharedCheck_3631_ == 0 {
                        v_unused_3632_ = leanh::lean_ctor_get(v_s_3591_, 12);
                        leanh::lean_dec(v_unused_3632_);
                        v_unused_3633_ = leanh::lean_ctor_get(v_s_3591_, 11);
                        leanh::lean_dec(v_unused_3633_);
                        v_unused_3634_ = leanh::lean_ctor_get(v_s_3591_, 10);
                        leanh::lean_dec(v_unused_3634_);
                        v_unused_3635_ = leanh::lean_ctor_get(v_s_3591_, 9);
                        leanh::lean_dec(v_unused_3635_);
                        v_unused_3636_ = leanh::lean_ctor_get(v_s_3591_, 8);
                        leanh::lean_dec(v_unused_3636_);
                        v_unused_3637_ = leanh::lean_ctor_get(v_s_3591_, 7);
                        leanh::lean_dec(v_unused_3637_);
                        v_unused_3638_ = leanh::lean_ctor_get(v_s_3591_, 6);
                        leanh::lean_dec(v_unused_3638_);
                        v_unused_3639_ = leanh::lean_ctor_get(v_s_3591_, 5);
                        leanh::lean_dec(v_unused_3639_);
                        v_unused_3640_ = leanh::lean_ctor_get(v_s_3591_, 4);
                        leanh::lean_dec(v_unused_3640_);
                        v_unused_3641_ = leanh::lean_ctor_get(v_s_3591_, 3);
                        leanh::lean_dec(v_unused_3641_);
                        v_unused_3642_ = leanh::lean_ctor_get(v_s_3591_, 2);
                        leanh::lean_dec(v_unused_3642_);
                        v_unused_3643_ = leanh::lean_ctor_get(v_s_3591_, 1);
                        leanh::lean_dec(v_unused_3643_);
                        v_unused_3644_ = leanh::lean_ctor_get(v_s_3591_, 0);
                        leanh::lean_dec(v_unused_3644_);
                        v___x_3609_ = v_s_3591_;
                        v_isShared_3610_ = v_isSharedCheck_3631_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_s_3591_);
                        v___x_3609_ = leanh::lean_box(0);
                        v_isShared_3610_ = v_isSharedCheck_3631_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3611_ = lean_array_fget(v_semirings_3595_, v_a_3589_);
                v_toSemiring_3612_ = leanh::lean_ctor_get(v_v_3611_, 0);
                v_ringId_3613_ = leanh::lean_ctor_get(v_v_3611_, 1);
                v_commSemiringInst_3614_ = leanh::lean_ctor_get(v_v_3611_, 2);
                v_addRightCancelInst_x3f_3615_ = leanh::lean_ctor_get(v_v_3611_, 3);
                v_isSharedCheck_3629_ = (!leanh::lean_is_exclusive(v_v_3611_)) as u8;
                if v_isSharedCheck_3629_ == 0 {
                    v_unused_3630_ = leanh::lean_ctor_get(v_v_3611_, 4);
                    leanh::lean_dec(v_unused_3630_);
                    v___x_3617_ = v_v_3611_;
                    v_isShared_3618_ = v_isSharedCheck_3629_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_addRightCancelInst_x3f_3615_);
                    leanh::lean_inc(v_commSemiringInst_3614_);
                    leanh::lean_inc(v_ringId_3613_);
                    leanh::lean_inc(v_toSemiring_3612_);
                    leanh::lean_dec(v_v_3611_);
                    v___x_3617_ = leanh::lean_box(0);
                    v_isShared_3618_ = v_isSharedCheck_3629_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3619_ = leanh::lean_box(0);
                v_xs_x27_3620_ = lean_array_fset(v_semirings_3595_, v_a_3589_, v___x_3619_);
                v___x_3621_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3621_, 0, v_a_3590_);
                if v_isShared_3618_ == 0 {
                    leanh::lean_ctor_set(v___x_3617_, 4, v___x_3621_);
                    v___x_3623_ = v___x_3617_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3628_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_toSemiring_3612_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3628_, 1, v_ringId_3613_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3628_,
                        2,
                        v_commSemiringInst_3614_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3628_,
                        3,
                        v_addRightCancelInst_x3f_3615_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3628_, 4, v___x_3621_);
                    v___x_3623_ = v_reuseFailAlloc_3628_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3624_ = lean_array_fset(v_xs_x27_3620_, v_a_3589_, v___x_3623_);
                if v_isShared_3610_ == 0 {
                    leanh::lean_ctor_set(v___x_3609_, 3, v___x_3624_);
                    v___x_3626_ = v___x_3609_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3627_ = leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_rings_3592_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 1, v_typeIdOf_3593_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 2, v_exprToRingId_3594_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 3, v___x_3624_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 4, v_stypeIdOf_3596_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3627_,
                        5,
                        v_exprToSemiringId_3597_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 6, v_ncRings_3598_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 7, v_exprToNCRingId_3599_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 8, v_nctypeIdOf_3600_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 9, v_ncSemirings_3601_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3627_,
                        10,
                        v_exprToNCSemiringId_3602_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 11, v_ncstypeIdOf_3603_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 12, v_steps_3604_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3627_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
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
    mut v_a_3645_: *mut leanh::LeanObject,
    mut v_a_3646_: *mut leanh::LeanObject,
    mut v_s_3647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3648_ =
        l_Lean_Meta_Grind_Arith_CommRing_getToQFn___lam__0(v_a_3645_, v_a_3646_, v_s_3647_);
    leanh::lean_dec(v_a_3645_);
    return v_res_3648_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getToQFn(
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
    let mut v___y_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3680_: u8 = 0;
    let mut v___x_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3684_: u8 = 0;
    let mut v_unused_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3689_: u8 = 0;
    let mut v___x_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3693_: u8 = 0;
    let mut v___x_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3698_: u8 = 0;
    let mut v_toQFn_x3f_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSemiring_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3716_: u8 = 0;
    let mut v_a_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3720_: u8 = 0;
    let mut v___x_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3724_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3694_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(
                    v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_,
                    v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_,
                );
                if leanh::lean_obj_tag(v___x_3694_) == 0 {
                    v_a_3695_ = leanh::lean_ctor_get(v___x_3694_, 0);
                    v_isSharedCheck_3716_ = (!leanh::lean_is_exclusive(v___x_3694_)) as u8;
                    if v_isSharedCheck_3716_ == 0 {
                        v___x_3697_ = v___x_3694_;
                        v_isShared_3698_ = v_isSharedCheck_3716_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3695_);
                        leanh::lean_dec(v___x_3694_);
                        v___x_3697_ = leanh::lean_box(0);
                        v_isShared_3698_ = v_isSharedCheck_3716_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_a_3717_ = leanh::lean_ctor_get(v___x_3694_, 0);
                    v_isSharedCheck_3724_ = (!leanh::lean_is_exclusive(v___x_3694_)) as u8;
                    if v_isSharedCheck_3724_ == 0 {
                        v___x_3719_ = v___x_3694_;
                        v_isShared_3720_ = v_isSharedCheck_3724_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3717_);
                        leanh::lean_dec(v___x_3694_);
                        v___x_3719_ = leanh::lean_box(0);
                        v_isShared_3720_ = v_isSharedCheck_3724_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_3673_) == 0 {
                    v_a_3674_ = leanh::lean_ctor_get(v___y_3673_, 0);
                    leanh::lean_inc_n(v_a_3674_, 2);
                    leanh::lean_dec_ref_known(v___y_3673_, 1);
                    leanh::lean_inc(v_a_3660_);
                    v___f_3675_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_Grind_Arith_CommRing_getToQFn___lam__0___boxed
                            as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    leanh::lean_closure_set(v___f_3675_, 0, v_a_3660_);
                    leanh::lean_closure_set(v___f_3675_, 1, v_a_3674_);
                    v___x_3676_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                    v___x_3677_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3676_, v___f_3675_, v_a_3661_);
                    if leanh::lean_obj_tag(v___x_3677_) == 0 {
                        v_isSharedCheck_3684_ =
                            (!leanh::lean_is_exclusive(v___x_3677_)) as u8;
                        if v_isSharedCheck_3684_ == 0 {
                            v_unused_3685_ = leanh::lean_ctor_get(v___x_3677_, 0);
                            leanh::lean_dec(v_unused_3685_);
                            v___x_3679_ = v___x_3677_;
                            v_isShared_3680_ = v_isSharedCheck_3684_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_3677_);
                            v___x_3679_ = leanh::lean_box(0);
                            v_isShared_3680_ = v_isSharedCheck_3684_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3674_);
                        v_a_3686_ = leanh::lean_ctor_get(v___x_3677_, 0);
                        v_isSharedCheck_3693_ =
                            (!leanh::lean_is_exclusive(v___x_3677_)) as u8;
                        if v_isSharedCheck_3693_ == 0 {
                            v___x_3688_ = v___x_3677_;
                            v_isShared_3689_ = v_isSharedCheck_3693_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3686_);
                            leanh::lean_dec(v___x_3677_);
                            v___x_3688_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_3679_, 0, v_a_3674_);
                    v___x_3682_ = v___x_3679_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3683_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3674_);
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
                    v_reuseFailAlloc_3692_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
                    v___x_3691_ = v_reuseFailAlloc_3692_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3691_;
            }
            6 => {
                v_toQFn_x3f_3699_ = leanh::lean_ctor_get(v_a_3695_, 4);
                if leanh::lean_obj_tag(v_toQFn_x3f_3699_) == 1 {
                    leanh::lean_inc_ref(v_toQFn_x3f_3699_);
                    leanh::lean_dec(v_a_3695_);
                    v_val_3700_ = leanh::lean_ctor_get(v_toQFn_x3f_3699_, 0);
                    leanh::lean_inc(v_val_3700_);
                    leanh::lean_dec_ref_known(v_toQFn_x3f_3699_, 1);
                    if v_isShared_3698_ == 0 {
                        leanh::lean_ctor_set(v___x_3697_, 0, v_val_3700_);
                        v___x_3702_ = v___x_3697_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3703_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3703_, 0, v_val_3700_);
                        v___x_3702_ = v_reuseFailAlloc_3703_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3697_);
                    v_toSemiring_3704_ = leanh::lean_ctor_get(v_a_3695_, 0);
                    leanh::lean_inc_ref(v_toSemiring_3704_);
                    leanh::lean_dec(v_a_3695_);
                    v_type_3705_ = leanh::lean_ctor_get(v_toSemiring_3704_, 1);
                    leanh::lean_inc_ref(v_type_3705_);
                    v_u_3706_ = leanh::lean_ctor_get(v_toSemiring_3704_, 2);
                    leanh::lean_inc(v_u_3706_);
                    v_semiringInst_3707_ = leanh::lean_ctor_get(v_toSemiring_3704_, 3);
                    leanh::lean_inc_ref(v_semiringInst_3707_);
                    leanh::lean_dec_ref(v_toSemiring_3704_);
                    v___x_3708_ = l_Lean_Meta_Grind_Arith_CommRing_getToQFn___closed__5;
                    v___x_3709_ = leanh::lean_box(0);
                    v___x_3710_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3710_, 0, v_u_3706_);
                    leanh::lean_ctor_set(v___x_3710_, 1, v___x_3709_);
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
                    if leanh::lean_obj_tag(v___x_3713_) == 0 {
                        v_a_3714_ = leanh::lean_ctor_get(v___x_3713_, 0);
                        leanh::lean_inc(v_a_3714_);
                        leanh::lean_dec_ref_known(v___x_3713_, 1);
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
                    v_reuseFailAlloc_3723_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_a_3717_);
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
    mut v_a_3725_: *mut leanh::LeanObject,
    mut v_a_3726_: *mut leanh::LeanObject,
    mut v_a_3727_: *mut leanh::LeanObject,
    mut v_a_3728_: *mut leanh::LeanObject,
    mut v_a_3729_: *mut leanh::LeanObject,
    mut v_a_3730_: *mut leanh::LeanObject,
    mut v_a_3731_: *mut leanh::LeanObject,
    mut v_a_3732_: *mut leanh::LeanObject,
    mut v_a_3733_: *mut leanh::LeanObject,
    mut v_a_3734_: *mut leanh::LeanObject,
    mut v_a_3735_: *mut leanh::LeanObject,
    mut v_a_3736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3737_ = l_Lean_Meta_Grind_Arith_CommRing_getToQFn(
        v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_,
        v_a_3733_, v_a_3734_, v_a_3735_,
    );
    leanh::lean_dec(v_a_3735_);
    leanh::lean_dec_ref(v_a_3734_);
    leanh::lean_dec(v_a_3733_);
    leanh::lean_dec_ref(v_a_3732_);
    leanh::lean_dec(v_a_3731_);
    leanh::lean_dec_ref(v_a_3730_);
    leanh::lean_dec(v_a_3729_);
    leanh::lean_dec_ref(v_a_3728_);
    leanh::lean_dec(v_a_3727_);
    leanh::lean_dec(v_a_3726_);
    leanh::lean_dec(v_a_3725_);
    return v_res_3737_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(
    mut v_u_3746_: *mut leanh::LeanObject,
    mut v_type_3747_: *mut leanh::LeanObject,
    mut v_a_3748_: *mut leanh::LeanObject,
    mut v_a_3749_: *mut leanh::LeanObject,
    mut v_a_3750_: *mut leanh::LeanObject,
    mut v_a_3751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_add_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3762_: u8 = 0;
    let mut v_val_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3772_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3753_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg___closed__1;
                v___x_3754_ = leanh::lean_box(0);
                v___x_3755_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3755_, 0, v_u_3746_);
                leanh::lean_ctor_set(v___x_3755_, 1, v___x_3754_);
                leanh::lean_inc_ref(v___x_3755_);
                v___x_3756_ = l_Lean_mkConst(v___x_3753_, v___x_3755_);
                leanh::lean_inc_ref(v_type_3747_);
                v_add_3757_ = l_Lean_Expr_app___override(v___x_3756_, v_type_3747_);
                v___x_3758_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                    v_add_3757_,
                    v_a_3748_,
                    v_a_3749_,
                    v_a_3750_,
                    v_a_3751_,
                );
                if leanh::lean_obj_tag(v___x_3758_) == 0 {
                    v_a_3759_ = leanh::lean_ctor_get(v___x_3758_, 0);
                    v_isSharedCheck_3772_ = (!leanh::lean_is_exclusive(v___x_3758_)) as u8;
                    if v_isSharedCheck_3772_ == 0 {
                        v___x_3761_ = v___x_3758_;
                        v_isShared_3762_ = v_isSharedCheck_3772_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3759_);
                        leanh::lean_dec(v___x_3758_);
                        v___x_3761_ = leanh::lean_box(0);
                        v_isShared_3762_ = v_isSharedCheck_3772_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_3755_, 2);
                    leanh::lean_dec_ref(v_type_3747_);
                    return v___x_3758_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3759_) == 1 {
                    leanh::lean_del_object(v___x_3761_);
                    v_val_3763_ = leanh::lean_ctor_get(v_a_3759_, 0);
                    leanh::lean_inc(v_val_3763_);
                    leanh::lean_dec_ref_known(v_a_3759_, 1);
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
                    leanh::lean_dec(v_a_3759_);
                    leanh::lean_dec_ref_known(v___x_3755_, 2);
                    leanh::lean_dec_ref(v_type_3747_);
                    v___x_3768_ = leanh::lean_box(0);
                    if v_isShared_3762_ == 0 {
                        leanh::lean_ctor_set(v___x_3761_, 0, v___x_3768_);
                        v___x_3770_ = v___x_3761_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3771_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3768_);
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
    mut v_u_3773_: *mut leanh::LeanObject,
    mut v_type_3774_: *mut leanh::LeanObject,
    mut v_a_3775_: *mut leanh::LeanObject,
    mut v_a_3776_: *mut leanh::LeanObject,
    mut v_a_3777_: *mut leanh::LeanObject,
    mut v_a_3778_: *mut leanh::LeanObject,
    mut v_a_3779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3780_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(v_u_3773_, v_type_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_);
    leanh::lean_dec(v_a_3778_);
    leanh::lean_dec_ref(v_a_3777_);
    leanh::lean_dec(v_a_3776_);
    leanh::lean_dec_ref(v_a_3775_);
    return v_res_3780_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f(
    mut v_u_3781_: *mut leanh::LeanObject,
    mut v_type_3782_: *mut leanh::LeanObject,
    mut v_a_3783_: *mut leanh::LeanObject,
    mut v_a_3784_: *mut leanh::LeanObject,
    mut v_a_3785_: *mut leanh::LeanObject,
    mut v_a_3786_: *mut leanh::LeanObject,
    mut v_a_3787_: *mut leanh::LeanObject,
    mut v_a_3788_: *mut leanh::LeanObject,
    mut v_a_3789_: *mut leanh::LeanObject,
    mut v_a_3790_: *mut leanh::LeanObject,
    mut v_a_3791_: *mut leanh::LeanObject,
    mut v_a_3792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3794_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(v_u_3781_, v_type_3782_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_);
    return v___x_3794_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___boxed(
    mut v_u_3795_: *mut leanh::LeanObject,
    mut v_type_3796_: *mut leanh::LeanObject,
    mut v_a_3797_: *mut leanh::LeanObject,
    mut v_a_3798_: *mut leanh::LeanObject,
    mut v_a_3799_: *mut leanh::LeanObject,
    mut v_a_3800_: *mut leanh::LeanObject,
    mut v_a_3801_: *mut leanh::LeanObject,
    mut v_a_3802_: *mut leanh::LeanObject,
    mut v_a_3803_: *mut leanh::LeanObject,
    mut v_a_3804_: *mut leanh::LeanObject,
    mut v_a_3805_: *mut leanh::LeanObject,
    mut v_a_3806_: *mut leanh::LeanObject,
    mut v_a_3807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3808_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f(v_u_3795_, v_type_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_, v_a_3806_);
    leanh::lean_dec(v_a_3806_);
    leanh::lean_dec_ref(v_a_3805_);
    leanh::lean_dec(v_a_3804_);
    leanh::lean_dec_ref(v_a_3803_);
    leanh::lean_dec(v_a_3802_);
    leanh::lean_dec_ref(v_a_3801_);
    leanh::lean_dec(v_a_3800_);
    leanh::lean_dec_ref(v_a_3799_);
    leanh::lean_dec(v_a_3798_);
    leanh::lean_dec(v_a_3797_);
    return v_res_3808_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0(
    mut v_a_3809_: *mut leanh::LeanObject,
    mut v_a_3810_: *mut leanh::LeanObject,
    mut v_s_3811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_rings_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_3825_: u8 = 0;
    let mut v___x_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: u8 = 0;
    let mut v___x_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3830_: u8 = 0;
    let mut v_v_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSemiring_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringId_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toQFn_x3f_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3838_: u8 = 0;
    let mut v___x_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3849_: u8 = 0;
    let mut v_unused_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3851_: u8 = 0;
    let mut v_unused_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_3812_ = leanh::lean_ctor_get(v_s_3811_, 0);
                v_typeIdOf_3813_ = leanh::lean_ctor_get(v_s_3811_, 1);
                v_exprToRingId_3814_ = leanh::lean_ctor_get(v_s_3811_, 2);
                v_semirings_3815_ = leanh::lean_ctor_get(v_s_3811_, 3);
                v_stypeIdOf_3816_ = leanh::lean_ctor_get(v_s_3811_, 4);
                v_exprToSemiringId_3817_ = leanh::lean_ctor_get(v_s_3811_, 5);
                v_ncRings_3818_ = leanh::lean_ctor_get(v_s_3811_, 6);
                v_exprToNCRingId_3819_ = leanh::lean_ctor_get(v_s_3811_, 7);
                v_nctypeIdOf_3820_ = leanh::lean_ctor_get(v_s_3811_, 8);
                v_ncSemirings_3821_ = leanh::lean_ctor_get(v_s_3811_, 9);
                v_exprToNCSemiringId_3822_ = leanh::lean_ctor_get(v_s_3811_, 10);
                v_ncstypeIdOf_3823_ = leanh::lean_ctor_get(v_s_3811_, 11);
                v_steps_3824_ = leanh::lean_ctor_get(v_s_3811_, 12);
                v_reportedMaxDegreeIssue_3825_ = leanh::lean_ctor_get_uint8(
                    v_s_3811_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v___x_3826_ = lean_array_get_size(v_semirings_3815_);
                v___x_3827_ = lean_nat_dec_lt(v_a_3809_, v___x_3826_);
                if v___x_3827_ == 0 {
                    leanh::lean_dec(v_a_3810_);
                    return v_s_3811_;
                } else {
                    leanh::lean_inc(v_steps_3824_);
                    leanh::lean_inc_ref(v_ncstypeIdOf_3823_);
                    leanh::lean_inc_ref(v_exprToNCSemiringId_3822_);
                    leanh::lean_inc_ref(v_ncSemirings_3821_);
                    leanh::lean_inc_ref(v_nctypeIdOf_3820_);
                    leanh::lean_inc_ref(v_exprToNCRingId_3819_);
                    leanh::lean_inc_ref(v_ncRings_3818_);
                    leanh::lean_inc_ref(v_exprToSemiringId_3817_);
                    leanh::lean_inc_ref(v_stypeIdOf_3816_);
                    leanh::lean_inc_ref(v_semirings_3815_);
                    leanh::lean_inc_ref(v_exprToRingId_3814_);
                    leanh::lean_inc_ref(v_typeIdOf_3813_);
                    leanh::lean_inc_ref(v_rings_3812_);
                    v_isSharedCheck_3851_ = (!leanh::lean_is_exclusive(v_s_3811_)) as u8;
                    if v_isSharedCheck_3851_ == 0 {
                        v_unused_3852_ = leanh::lean_ctor_get(v_s_3811_, 12);
                        leanh::lean_dec(v_unused_3852_);
                        v_unused_3853_ = leanh::lean_ctor_get(v_s_3811_, 11);
                        leanh::lean_dec(v_unused_3853_);
                        v_unused_3854_ = leanh::lean_ctor_get(v_s_3811_, 10);
                        leanh::lean_dec(v_unused_3854_);
                        v_unused_3855_ = leanh::lean_ctor_get(v_s_3811_, 9);
                        leanh::lean_dec(v_unused_3855_);
                        v_unused_3856_ = leanh::lean_ctor_get(v_s_3811_, 8);
                        leanh::lean_dec(v_unused_3856_);
                        v_unused_3857_ = leanh::lean_ctor_get(v_s_3811_, 7);
                        leanh::lean_dec(v_unused_3857_);
                        v_unused_3858_ = leanh::lean_ctor_get(v_s_3811_, 6);
                        leanh::lean_dec(v_unused_3858_);
                        v_unused_3859_ = leanh::lean_ctor_get(v_s_3811_, 5);
                        leanh::lean_dec(v_unused_3859_);
                        v_unused_3860_ = leanh::lean_ctor_get(v_s_3811_, 4);
                        leanh::lean_dec(v_unused_3860_);
                        v_unused_3861_ = leanh::lean_ctor_get(v_s_3811_, 3);
                        leanh::lean_dec(v_unused_3861_);
                        v_unused_3862_ = leanh::lean_ctor_get(v_s_3811_, 2);
                        leanh::lean_dec(v_unused_3862_);
                        v_unused_3863_ = leanh::lean_ctor_get(v_s_3811_, 1);
                        leanh::lean_dec(v_unused_3863_);
                        v_unused_3864_ = leanh::lean_ctor_get(v_s_3811_, 0);
                        leanh::lean_dec(v_unused_3864_);
                        v___x_3829_ = v_s_3811_;
                        v_isShared_3830_ = v_isSharedCheck_3851_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_s_3811_);
                        v___x_3829_ = leanh::lean_box(0);
                        v_isShared_3830_ = v_isSharedCheck_3851_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3831_ = lean_array_fget(v_semirings_3815_, v_a_3809_);
                v_toSemiring_3832_ = leanh::lean_ctor_get(v_v_3831_, 0);
                v_ringId_3833_ = leanh::lean_ctor_get(v_v_3831_, 1);
                v_commSemiringInst_3834_ = leanh::lean_ctor_get(v_v_3831_, 2);
                v_toQFn_x3f_3835_ = leanh::lean_ctor_get(v_v_3831_, 4);
                v_isSharedCheck_3849_ = (!leanh::lean_is_exclusive(v_v_3831_)) as u8;
                if v_isSharedCheck_3849_ == 0 {
                    v_unused_3850_ = leanh::lean_ctor_get(v_v_3831_, 3);
                    leanh::lean_dec(v_unused_3850_);
                    v___x_3837_ = v_v_3831_;
                    v_isShared_3838_ = v_isSharedCheck_3849_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toQFn_x3f_3835_);
                    leanh::lean_inc(v_commSemiringInst_3834_);
                    leanh::lean_inc(v_ringId_3833_);
                    leanh::lean_inc(v_toSemiring_3832_);
                    leanh::lean_dec(v_v_3831_);
                    v___x_3837_ = leanh::lean_box(0);
                    v_isShared_3838_ = v_isSharedCheck_3849_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3839_ = leanh::lean_box(0);
                v_xs_x27_3840_ = lean_array_fset(v_semirings_3815_, v_a_3809_, v___x_3839_);
                v___x_3841_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3841_, 0, v_a_3810_);
                if v_isShared_3838_ == 0 {
                    leanh::lean_ctor_set(v___x_3837_, 3, v___x_3841_);
                    v___x_3843_ = v___x_3837_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3848_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_toSemiring_3832_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 1, v_ringId_3833_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3848_,
                        2,
                        v_commSemiringInst_3834_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 3, v___x_3841_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 4, v_toQFn_x3f_3835_);
                    v___x_3843_ = v_reuseFailAlloc_3848_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3844_ = lean_array_fset(v_xs_x27_3840_, v_a_3809_, v___x_3843_);
                if v_isShared_3830_ == 0 {
                    leanh::lean_ctor_set(v___x_3829_, 3, v___x_3844_);
                    v___x_3846_ = v___x_3829_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3847_ = leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_rings_3812_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 1, v_typeIdOf_3813_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 2, v_exprToRingId_3814_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 3, v___x_3844_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 4, v_stypeIdOf_3816_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3847_,
                        5,
                        v_exprToSemiringId_3817_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 6, v_ncRings_3818_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 7, v_exprToNCRingId_3819_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 8, v_nctypeIdOf_3820_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 9, v_ncSemirings_3821_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3847_,
                        10,
                        v_exprToNCSemiringId_3822_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 11, v_ncstypeIdOf_3823_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 12, v_steps_3824_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3847_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
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
    mut v_a_3865_: *mut leanh::LeanObject,
    mut v_a_3866_: *mut leanh::LeanObject,
    mut v_s_3867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3868_ = l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0(
        v_a_3865_, v_a_3866_, v_s_3867_,
    );
    leanh::lean_dec(v_a_3865_);
    return v_res_3868_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f(
    mut v_a_3869_: *mut leanh::LeanObject,
    mut v_a_3870_: *mut leanh::LeanObject,
    mut v_a_3871_: *mut leanh::LeanObject,
    mut v_a_3872_: *mut leanh::LeanObject,
    mut v_a_3873_: *mut leanh::LeanObject,
    mut v_a_3874_: *mut leanh::LeanObject,
    mut v_a_3875_: *mut leanh::LeanObject,
    mut v_a_3876_: *mut leanh::LeanObject,
    mut v_a_3877_: *mut leanh::LeanObject,
    mut v_a_3878_: *mut leanh::LeanObject,
    mut v_a_3879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3885_: u8 = 0;
    let mut v_addRightCancelInst_x3f_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSemiring_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3901_: u8 = 0;
    let mut v___x_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3905_: u8 = 0;
    let mut v_unused_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3910_: u8 = 0;
    let mut v___x_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3914_: u8 = 0;
    let mut v_isSharedCheck_3915_: u8 = 0;
    let mut v_a_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3919_: u8 = 0;
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3923_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3881_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(
                    v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_,
                    v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_,
                );
                if leanh::lean_obj_tag(v___x_3881_) == 0 {
                    v_a_3882_ = leanh::lean_ctor_get(v___x_3881_, 0);
                    v_isSharedCheck_3915_ = (!leanh::lean_is_exclusive(v___x_3881_)) as u8;
                    if v_isSharedCheck_3915_ == 0 {
                        v___x_3884_ = v___x_3881_;
                        v_isShared_3885_ = v_isSharedCheck_3915_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3882_);
                        leanh::lean_dec(v___x_3881_);
                        v___x_3884_ = leanh::lean_box(0);
                        v_isShared_3885_ = v_isSharedCheck_3915_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3916_ = leanh::lean_ctor_get(v___x_3881_, 0);
                    v_isSharedCheck_3923_ = (!leanh::lean_is_exclusive(v___x_3881_)) as u8;
                    if v_isSharedCheck_3923_ == 0 {
                        v___x_3918_ = v___x_3881_;
                        v_isShared_3919_ = v_isSharedCheck_3923_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3916_);
                        leanh::lean_dec(v___x_3881_);
                        v___x_3918_ = leanh::lean_box(0);
                        v_isShared_3919_ = v_isSharedCheck_3923_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_addRightCancelInst_x3f_3886_ = leanh::lean_ctor_get(v_a_3882_, 3);
                if leanh::lean_obj_tag(v_addRightCancelInst_x3f_3886_) == 1 {
                    leanh::lean_inc_ref(v_addRightCancelInst_x3f_3886_);
                    leanh::lean_dec(v_a_3882_);
                    v_val_3887_ = leanh::lean_ctor_get(v_addRightCancelInst_x3f_3886_, 0);
                    leanh::lean_inc(v_val_3887_);
                    leanh::lean_dec_ref_known(v_addRightCancelInst_x3f_3886_, 1);
                    if v_isShared_3885_ == 0 {
                        leanh::lean_ctor_set(v___x_3884_, 0, v_val_3887_);
                        v___x_3889_ = v___x_3884_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3890_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_val_3887_);
                        v___x_3889_ = v_reuseFailAlloc_3890_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3884_);
                    v_toSemiring_3891_ = leanh::lean_ctor_get(v_a_3882_, 0);
                    leanh::lean_inc_ref(v_toSemiring_3891_);
                    leanh::lean_dec(v_a_3882_);
                    v_type_3892_ = leanh::lean_ctor_get(v_toSemiring_3891_, 1);
                    leanh::lean_inc_ref(v_type_3892_);
                    v_u_3893_ = leanh::lean_ctor_get(v_toSemiring_3891_, 2);
                    leanh::lean_inc(v_u_3893_);
                    leanh::lean_dec_ref(v_toSemiring_3891_);
                    v___x_3894_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Meta_Grind_Arith_CommRing_mkAddRightCancelInst_x3f___redArg(v_u_3893_, v_type_3892_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_);
                    if leanh::lean_obj_tag(v___x_3894_) == 0 {
                        v_a_3895_ = leanh::lean_ctor_get(v___x_3894_, 0);
                        leanh::lean_inc_n(v_a_3895_, 2);
                        leanh::lean_dec_ref_known(v___x_3894_, 1);
                        leanh::lean_inc(v_a_3869_);
                        v___f_3896_ = leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                        leanh::lean_closure_set(v___f_3896_, 0, v_a_3869_);
                        leanh::lean_closure_set(v___f_3896_, 1, v_a_3895_);
                        v___x_3897_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                        v___x_3898_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3897_, v___f_3896_, v_a_3870_);
                        if leanh::lean_obj_tag(v___x_3898_) == 0 {
                            v_isSharedCheck_3905_ =
                                (!leanh::lean_is_exclusive(v___x_3898_)) as u8;
                            if v_isSharedCheck_3905_ == 0 {
                                v_unused_3906_ = leanh::lean_ctor_get(v___x_3898_, 0);
                                leanh::lean_dec(v_unused_3906_);
                                v___x_3900_ = v___x_3898_;
                                v_isShared_3901_ = v_isSharedCheck_3905_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_3898_);
                                v___x_3900_ = leanh::lean_box(0);
                                v_isShared_3901_ = v_isSharedCheck_3905_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_3895_);
                            v_a_3907_ = leanh::lean_ctor_get(v___x_3898_, 0);
                            v_isSharedCheck_3914_ =
                                (!leanh::lean_is_exclusive(v___x_3898_)) as u8;
                            if v_isSharedCheck_3914_ == 0 {
                                v___x_3909_ = v___x_3898_;
                                v_isShared_3910_ = v_isSharedCheck_3914_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3907_);
                                leanh::lean_dec(v___x_3898_);
                                v___x_3909_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_3900_, 0, v_a_3895_);
                    v___x_3903_ = v___x_3900_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3904_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_a_3895_);
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
                    v_reuseFailAlloc_3913_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3913_, 0, v_a_3907_);
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
                    v_reuseFailAlloc_3922_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_a_3916_);
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
    mut v_a_3924_: *mut leanh::LeanObject,
    mut v_a_3925_: *mut leanh::LeanObject,
    mut v_a_3926_: *mut leanh::LeanObject,
    mut v_a_3927_: *mut leanh::LeanObject,
    mut v_a_3928_: *mut leanh::LeanObject,
    mut v_a_3929_: *mut leanh::LeanObject,
    mut v_a_3930_: *mut leanh::LeanObject,
    mut v_a_3931_: *mut leanh::LeanObject,
    mut v_a_3932_: *mut leanh::LeanObject,
    mut v_a_3933_: *mut leanh::LeanObject,
    mut v_a_3934_: *mut leanh::LeanObject,
    mut v_a_3935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3936_ = l_Lean_Meta_Grind_Arith_CommRing_getAddRightCancelInst_x3f(
        v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_,
        v_a_3932_, v_a_3933_, v_a_3934_,
    );
    leanh::lean_dec(v_a_3934_);
    leanh::lean_dec_ref(v_a_3933_);
    leanh::lean_dec(v_a_3932_);
    leanh::lean_dec_ref(v_a_3931_);
    leanh::lean_dec(v_a_3930_);
    leanh::lean_dec_ref(v_a_3929_);
    leanh::lean_dec(v_a_3928_);
    leanh::lean_dec_ref(v_a_3927_);
    leanh::lean_dec(v_a_3926_);
    leanh::lean_dec(v_a_3925_);
    leanh::lean_dec(v_a_3924_);
    return v_res_3936_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__0(
    mut v_addFn_3937_: *mut leanh::LeanObject,
    mut v_s_3938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_id_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3951_: u8 = 0;
    let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3956_: u8 = 0;
    let mut v_unused_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_3939_ = leanh::lean_ctor_get(v_s_3938_, 0);
                v_type_3940_ = leanh::lean_ctor_get(v_s_3938_, 1);
                v_u_3941_ = leanh::lean_ctor_get(v_s_3938_, 2);
                v_semiringInst_3942_ = leanh::lean_ctor_get(v_s_3938_, 3);
                v_mulFn_x3f_3943_ = leanh::lean_ctor_get(v_s_3938_, 5);
                v_powFn_x3f_3944_ = leanh::lean_ctor_get(v_s_3938_, 6);
                v_natCastFn_x3f_3945_ = leanh::lean_ctor_get(v_s_3938_, 7);
                v_denote_3946_ = leanh::lean_ctor_get(v_s_3938_, 8);
                v_vars_3947_ = leanh::lean_ctor_get(v_s_3938_, 9);
                v_varMap_3948_ = leanh::lean_ctor_get(v_s_3938_, 10);
                v_isSharedCheck_3956_ = (!leanh::lean_is_exclusive(v_s_3938_)) as u8;
                if v_isSharedCheck_3956_ == 0 {
                    v_unused_3957_ = leanh::lean_ctor_get(v_s_3938_, 4);
                    leanh::lean_dec(v_unused_3957_);
                    v___x_3950_ = v_s_3938_;
                    v_isShared_3951_ = v_isSharedCheck_3956_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_varMap_3948_);
                    leanh::lean_inc(v_vars_3947_);
                    leanh::lean_inc(v_denote_3946_);
                    leanh::lean_inc(v_natCastFn_x3f_3945_);
                    leanh::lean_inc(v_powFn_x3f_3944_);
                    leanh::lean_inc(v_mulFn_x3f_3943_);
                    leanh::lean_inc(v_semiringInst_3942_);
                    leanh::lean_inc(v_u_3941_);
                    leanh::lean_inc(v_type_3940_);
                    leanh::lean_inc(v_id_3939_);
                    leanh::lean_dec(v_s_3938_);
                    v___x_3950_ = leanh::lean_box(0);
                    v_isShared_3951_ = v_isSharedCheck_3956_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3952_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3952_, 0, v_addFn_3937_);
                if v_isShared_3951_ == 0 {
                    leanh::lean_ctor_set(v___x_3950_, 4, v___x_3952_);
                    v___x_3954_ = v___x_3950_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3955_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_id_3939_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 1, v_type_3940_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 2, v_u_3941_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 3, v_semiringInst_3942_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 4, v___x_3952_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 5, v_mulFn_x3f_3943_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 6, v_powFn_x3f_3944_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 7, v_natCastFn_x3f_3945_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 8, v_denote_3946_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 9, v_vars_3947_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3955_, 10, v_varMap_3948_);
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
    mut v_toPure_3958_: *mut leanh::LeanObject,
    mut v_addFn_3959_: *mut leanh::LeanObject,
    mut v_____r_3960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3961_ =
        leanh::lean_apply_2(v_toPure_3958_, leanh::lean_box(0), v_addFn_3959_);
    return v___x_3961_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__2(
    mut v_toPure_3962_: *mut leanh::LeanObject,
    mut v_modifySemiring_3963_: *mut leanh::LeanObject,
    mut v_toBind_3964_: *mut leanh::LeanObject,
    mut v_addFn_3965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_addFn_3965_);
    v___f_3966_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3966_, 0, v_addFn_3965_);
    v___f_3967_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3967_, 0, v_toPure_3962_);
    leanh::lean_closure_set(v___f_3967_, 1, v_addFn_3965_);
    v___x_3968_ = leanh::lean_apply_1(v_modifySemiring_3963_, v___f_3966_);
    v___x_3969_ = leanh::lean_apply_4(
        v_toBind_3964_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3968_,
        v___f_3967_,
    );
    return v___x_3969_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3(
    mut v_toPure_3987_: *mut leanh::LeanObject,
    mut v_inst_3988_: *mut leanh::LeanObject,
    mut v_inst_3989_: *mut leanh::LeanObject,
    mut v_inst_3990_: *mut leanh::LeanObject,
    mut v_inst_3991_: *mut leanh::LeanObject,
    mut v_toBind_3992_: *mut leanh::LeanObject,
    mut v___f_3993_: *mut leanh::LeanObject,
    mut v_s_3994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_addFn_x3f_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_addFn_x3f_3995_ = leanh::lean_ctor_get(v_s_3994_, 4);
    if leanh::lean_obj_tag(v_addFn_x3f_3995_) == 1 {
        let mut v_val_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_addFn_x3f_3995_);
        leanh::lean_dec_ref(v_s_3994_);
        leanh::lean_dec(v___f_3993_);
        leanh::lean_dec(v_toBind_3992_);
        leanh::lean_dec_ref(v_inst_3991_);
        leanh::lean_dec_ref(v_inst_3990_);
        leanh::lean_dec_ref(v_inst_3989_);
        leanh::lean_dec(v_inst_3988_);
        v_val_3996_ = leanh::lean_ctor_get(v_addFn_x3f_3995_, 0);
        leanh::lean_inc(v_val_3996_);
        leanh::lean_dec_ref_known(v_addFn_x3f_3995_, 1);
        v___x_3997_ =
            leanh::lean_apply_2(v_toPure_3987_, leanh::lean_box(0), v_val_3996_);
        return v___x_3997_;
    } else {
        let mut v_type_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_expectedInst_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_3987_);
        v_type_3998_ = leanh::lean_ctor_get(v_s_3994_, 1);
        leanh::lean_inc_ref_n(v_type_3998_, 3);
        v_u_3999_ = leanh::lean_ctor_get(v_s_3994_, 2);
        leanh::lean_inc_n(v_u_3999_, 2);
        v_semiringInst_4000_ = leanh::lean_ctor_get(v_s_3994_, 3);
        leanh::lean_inc_ref(v_semiringInst_4000_);
        leanh::lean_dec_ref(v_s_3994_);
        v___x_4001_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1;
        v___x_4002_ = leanh::lean_box(0);
        v___x_4003_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4003_, 0, v_u_3999_);
        leanh::lean_ctor_set(v___x_4003_, 1, v___x_4002_);
        leanh::lean_inc_ref(v___x_4003_);
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
        v___x_4012_ = leanh::lean_apply_4(
            v_toBind_3992_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4011_,
            v___f_3993_,
        );
        return v___x_4012_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg(
    mut v_inst_4013_: *mut leanh::LeanObject,
    mut v_inst_4014_: *mut leanh::LeanObject,
    mut v_inst_4015_: *mut leanh::LeanObject,
    mut v_inst_4016_: *mut leanh::LeanObject,
    mut v_inst_4017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getSemiring_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifySemiring_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4018_ = leanh::lean_ctor_get(v_inst_4015_, 0);
    v_toBind_4019_ = leanh::lean_ctor_get(v_inst_4015_, 1);
    leanh::lean_inc_n(v_toBind_4019_, 3);
    v_getSemiring_4020_ = leanh::lean_ctor_get(v_inst_4017_, 0);
    leanh::lean_inc(v_getSemiring_4020_);
    v_modifySemiring_4021_ = leanh::lean_ctor_get(v_inst_4017_, 1);
    leanh::lean_inc(v_modifySemiring_4021_);
    leanh::lean_dec_ref(v_inst_4017_);
    v_toPure_4022_ = leanh::lean_ctor_get(v_toApplicative_4018_, 1);
    leanh::lean_inc_n(v_toPure_4022_, 2);
    v___f_4023_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_4023_, 0, v_toPure_4022_);
    leanh::lean_closure_set(v___f_4023_, 1, v_modifySemiring_4021_);
    leanh::lean_closure_set(v___f_4023_, 2, v_toBind_4019_);
    v___f_4024_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_4024_, 0, v_toPure_4022_);
    leanh::lean_closure_set(v___f_4024_, 1, v_inst_4013_);
    leanh::lean_closure_set(v___f_4024_, 2, v_inst_4014_);
    leanh::lean_closure_set(v___f_4024_, 3, v_inst_4015_);
    leanh::lean_closure_set(v___f_4024_, 4, v_inst_4016_);
    leanh::lean_closure_set(v___f_4024_, 5, v_toBind_4019_);
    leanh::lean_closure_set(v___f_4024_, 6, v___f_4023_);
    v___x_4025_ = leanh::lean_apply_4(
        v_toBind_4019_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getSemiring_4020_,
        v___f_4024_,
    );
    return v___x_4025_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27(
    mut v_m_4026_: *mut leanh::LeanObject,
    mut v_inst_4027_: *mut leanh::LeanObject,
    mut v_inst_4028_: *mut leanh::LeanObject,
    mut v_inst_4029_: *mut leanh::LeanObject,
    mut v_inst_4030_: *mut leanh::LeanObject,
    mut v_inst_4031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_mulFn_4033_: *mut leanh::LeanObject,
    mut v_s_4034_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_id_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4047_: u8 = 0;
    let mut v___x_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4052_: u8 = 0;
    let mut v_unused_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_4035_ = leanh::lean_ctor_get(v_s_4034_, 0);
                v_type_4036_ = leanh::lean_ctor_get(v_s_4034_, 1);
                v_u_4037_ = leanh::lean_ctor_get(v_s_4034_, 2);
                v_semiringInst_4038_ = leanh::lean_ctor_get(v_s_4034_, 3);
                v_addFn_x3f_4039_ = leanh::lean_ctor_get(v_s_4034_, 4);
                v_powFn_x3f_4040_ = leanh::lean_ctor_get(v_s_4034_, 6);
                v_natCastFn_x3f_4041_ = leanh::lean_ctor_get(v_s_4034_, 7);
                v_denote_4042_ = leanh::lean_ctor_get(v_s_4034_, 8);
                v_vars_4043_ = leanh::lean_ctor_get(v_s_4034_, 9);
                v_varMap_4044_ = leanh::lean_ctor_get(v_s_4034_, 10);
                v_isSharedCheck_4052_ = (!leanh::lean_is_exclusive(v_s_4034_)) as u8;
                if v_isSharedCheck_4052_ == 0 {
                    v_unused_4053_ = leanh::lean_ctor_get(v_s_4034_, 5);
                    leanh::lean_dec(v_unused_4053_);
                    v___x_4046_ = v_s_4034_;
                    v_isShared_4047_ = v_isSharedCheck_4052_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_varMap_4044_);
                    leanh::lean_inc(v_vars_4043_);
                    leanh::lean_inc(v_denote_4042_);
                    leanh::lean_inc(v_natCastFn_x3f_4041_);
                    leanh::lean_inc(v_powFn_x3f_4040_);
                    leanh::lean_inc(v_addFn_x3f_4039_);
                    leanh::lean_inc(v_semiringInst_4038_);
                    leanh::lean_inc(v_u_4037_);
                    leanh::lean_inc(v_type_4036_);
                    leanh::lean_inc(v_id_4035_);
                    leanh::lean_dec(v_s_4034_);
                    v___x_4046_ = leanh::lean_box(0);
                    v_isShared_4047_ = v_isSharedCheck_4052_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4048_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4048_, 0, v_mulFn_4033_);
                if v_isShared_4047_ == 0 {
                    leanh::lean_ctor_set(v___x_4046_, 5, v___x_4048_);
                    v___x_4050_ = v___x_4046_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4051_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_id_4035_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4051_, 1, v_type_4036_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4051_, 2, v_u_4037_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4051_, 3, v_semiringInst_4038_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4051_, 4, v_addFn_x3f_4039_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4051_, 5, v___x_4048_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4051_, 6, v_powFn_x3f_4040_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4051_, 7, v_natCastFn_x3f_4041_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4051_, 8, v_denote_4042_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4051_, 9, v_vars_4043_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4051_, 10, v_varMap_4044_);
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
    mut v_toPure_4054_: *mut leanh::LeanObject,
    mut v_mulFn_4055_: *mut leanh::LeanObject,
    mut v_____r_4056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4057_ =
        leanh::lean_apply_2(v_toPure_4054_, leanh::lean_box(0), v_mulFn_4055_);
    return v___x_4057_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__2(
    mut v_toPure_4058_: *mut leanh::LeanObject,
    mut v_modifySemiring_4059_: *mut leanh::LeanObject,
    mut v_toBind_4060_: *mut leanh::LeanObject,
    mut v_mulFn_4061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_mulFn_4061_);
    v___f_4062_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_4062_, 0, v_mulFn_4061_);
    v___f_4063_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_4063_, 0, v_toPure_4058_);
    leanh::lean_closure_set(v___f_4063_, 1, v_mulFn_4061_);
    v___x_4064_ = leanh::lean_apply_1(v_modifySemiring_4059_, v___f_4062_);
    v___x_4065_ = leanh::lean_apply_4(
        v_toBind_4060_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4064_,
        v___f_4063_,
    );
    return v___x_4065_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3(
    mut v_toPure_4082_: *mut leanh::LeanObject,
    mut v_inst_4083_: *mut leanh::LeanObject,
    mut v_inst_4084_: *mut leanh::LeanObject,
    mut v_inst_4085_: *mut leanh::LeanObject,
    mut v_inst_4086_: *mut leanh::LeanObject,
    mut v_toBind_4087_: *mut leanh::LeanObject,
    mut v___f_4088_: *mut leanh::LeanObject,
    mut v_s_4089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mulFn_x3f_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mulFn_x3f_4090_ = leanh::lean_ctor_get(v_s_4089_, 5);
    if leanh::lean_obj_tag(v_mulFn_x3f_4090_) == 1 {
        let mut v_val_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_mulFn_x3f_4090_);
        leanh::lean_dec_ref(v_s_4089_);
        leanh::lean_dec(v___f_4088_);
        leanh::lean_dec(v_toBind_4087_);
        leanh::lean_dec_ref(v_inst_4086_);
        leanh::lean_dec_ref(v_inst_4085_);
        leanh::lean_dec_ref(v_inst_4084_);
        leanh::lean_dec(v_inst_4083_);
        v_val_4091_ = leanh::lean_ctor_get(v_mulFn_x3f_4090_, 0);
        leanh::lean_inc(v_val_4091_);
        leanh::lean_dec_ref_known(v_mulFn_x3f_4090_, 1);
        v___x_4092_ =
            leanh::lean_apply_2(v_toPure_4082_, leanh::lean_box(0), v_val_4091_);
        return v___x_4092_;
    } else {
        let mut v_type_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_expectedInst_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_4082_);
        v_type_4093_ = leanh::lean_ctor_get(v_s_4089_, 1);
        leanh::lean_inc_ref_n(v_type_4093_, 3);
        v_u_4094_ = leanh::lean_ctor_get(v_s_4089_, 2);
        leanh::lean_inc_n(v_u_4094_, 2);
        v_semiringInst_4095_ = leanh::lean_ctor_get(v_s_4089_, 3);
        leanh::lean_inc_ref(v_semiringInst_4095_);
        leanh::lean_dec_ref(v_s_4089_);
        v___x_4096_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1;
        v___x_4097_ = leanh::lean_box(0);
        v___x_4098_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4098_, 0, v_u_4094_);
        leanh::lean_ctor_set(v___x_4098_, 1, v___x_4097_);
        leanh::lean_inc_ref(v___x_4098_);
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
        v___x_4107_ = leanh::lean_apply_4(
            v_toBind_4087_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4106_,
            v___f_4088_,
        );
        return v___x_4107_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg(
    mut v_inst_4108_: *mut leanh::LeanObject,
    mut v_inst_4109_: *mut leanh::LeanObject,
    mut v_inst_4110_: *mut leanh::LeanObject,
    mut v_inst_4111_: *mut leanh::LeanObject,
    mut v_inst_4112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getSemiring_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifySemiring_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4113_ = leanh::lean_ctor_get(v_inst_4110_, 0);
    v_toBind_4114_ = leanh::lean_ctor_get(v_inst_4110_, 1);
    leanh::lean_inc_n(v_toBind_4114_, 3);
    v_getSemiring_4115_ = leanh::lean_ctor_get(v_inst_4112_, 0);
    leanh::lean_inc(v_getSemiring_4115_);
    v_modifySemiring_4116_ = leanh::lean_ctor_get(v_inst_4112_, 1);
    leanh::lean_inc(v_modifySemiring_4116_);
    leanh::lean_dec_ref(v_inst_4112_);
    v_toPure_4117_ = leanh::lean_ctor_get(v_toApplicative_4113_, 1);
    leanh::lean_inc_n(v_toPure_4117_, 2);
    v___f_4118_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_4118_, 0, v_toPure_4117_);
    leanh::lean_closure_set(v___f_4118_, 1, v_modifySemiring_4116_);
    leanh::lean_closure_set(v___f_4118_, 2, v_toBind_4114_);
    v___f_4119_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_4119_, 0, v_toPure_4117_);
    leanh::lean_closure_set(v___f_4119_, 1, v_inst_4108_);
    leanh::lean_closure_set(v___f_4119_, 2, v_inst_4109_);
    leanh::lean_closure_set(v___f_4119_, 3, v_inst_4110_);
    leanh::lean_closure_set(v___f_4119_, 4, v_inst_4111_);
    leanh::lean_closure_set(v___f_4119_, 5, v_toBind_4114_);
    leanh::lean_closure_set(v___f_4119_, 6, v___f_4118_);
    v___x_4120_ = leanh::lean_apply_4(
        v_toBind_4114_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getSemiring_4115_,
        v___f_4119_,
    );
    return v___x_4120_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27(
    mut v_m_4121_: *mut leanh::LeanObject,
    mut v_inst_4122_: *mut leanh::LeanObject,
    mut v_inst_4123_: *mut leanh::LeanObject,
    mut v_inst_4124_: *mut leanh::LeanObject,
    mut v_inst_4125_: *mut leanh::LeanObject,
    mut v_inst_4126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_powFn_4128_: *mut leanh::LeanObject,
    mut v_s_4129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_id_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4142_: u8 = 0;
    let mut v___x_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4147_: u8 = 0;
    let mut v_unused_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_4130_ = leanh::lean_ctor_get(v_s_4129_, 0);
                v_type_4131_ = leanh::lean_ctor_get(v_s_4129_, 1);
                v_u_4132_ = leanh::lean_ctor_get(v_s_4129_, 2);
                v_semiringInst_4133_ = leanh::lean_ctor_get(v_s_4129_, 3);
                v_addFn_x3f_4134_ = leanh::lean_ctor_get(v_s_4129_, 4);
                v_mulFn_x3f_4135_ = leanh::lean_ctor_get(v_s_4129_, 5);
                v_natCastFn_x3f_4136_ = leanh::lean_ctor_get(v_s_4129_, 7);
                v_denote_4137_ = leanh::lean_ctor_get(v_s_4129_, 8);
                v_vars_4138_ = leanh::lean_ctor_get(v_s_4129_, 9);
                v_varMap_4139_ = leanh::lean_ctor_get(v_s_4129_, 10);
                v_isSharedCheck_4147_ = (!leanh::lean_is_exclusive(v_s_4129_)) as u8;
                if v_isSharedCheck_4147_ == 0 {
                    v_unused_4148_ = leanh::lean_ctor_get(v_s_4129_, 6);
                    leanh::lean_dec(v_unused_4148_);
                    v___x_4141_ = v_s_4129_;
                    v_isShared_4142_ = v_isSharedCheck_4147_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_varMap_4139_);
                    leanh::lean_inc(v_vars_4138_);
                    leanh::lean_inc(v_denote_4137_);
                    leanh::lean_inc(v_natCastFn_x3f_4136_);
                    leanh::lean_inc(v_mulFn_x3f_4135_);
                    leanh::lean_inc(v_addFn_x3f_4134_);
                    leanh::lean_inc(v_semiringInst_4133_);
                    leanh::lean_inc(v_u_4132_);
                    leanh::lean_inc(v_type_4131_);
                    leanh::lean_inc(v_id_4130_);
                    leanh::lean_dec(v_s_4129_);
                    v___x_4141_ = leanh::lean_box(0);
                    v_isShared_4142_ = v_isSharedCheck_4147_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4143_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4143_, 0, v_powFn_4128_);
                if v_isShared_4142_ == 0 {
                    leanh::lean_ctor_set(v___x_4141_, 6, v___x_4143_);
                    v___x_4145_ = v___x_4141_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4146_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_id_4130_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 1, v_type_4131_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 2, v_u_4132_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 3, v_semiringInst_4133_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 4, v_addFn_x3f_4134_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 5, v_mulFn_x3f_4135_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 6, v___x_4143_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 7, v_natCastFn_x3f_4136_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 8, v_denote_4137_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 9, v_vars_4138_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 10, v_varMap_4139_);
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
    mut v_toPure_4149_: *mut leanh::LeanObject,
    mut v_powFn_4150_: *mut leanh::LeanObject,
    mut v_____r_4151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4152_ =
        leanh::lean_apply_2(v_toPure_4149_, leanh::lean_box(0), v_powFn_4150_);
    return v___x_4152_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__2(
    mut v_toPure_4153_: *mut leanh::LeanObject,
    mut v_modifySemiring_4154_: *mut leanh::LeanObject,
    mut v_toBind_4155_: *mut leanh::LeanObject,
    mut v_powFn_4156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_powFn_4156_);
    v___f_4157_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_4157_, 0, v_powFn_4156_);
    v___f_4158_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_4158_, 0, v_toPure_4153_);
    leanh::lean_closure_set(v___f_4158_, 1, v_powFn_4156_);
    v___x_4159_ = leanh::lean_apply_1(v_modifySemiring_4154_, v___f_4157_);
    v___x_4160_ = leanh::lean_apply_4(
        v_toBind_4155_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4159_,
        v___f_4158_,
    );
    return v___x_4160_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__3(
    mut v_toPure_4161_: *mut leanh::LeanObject,
    mut v_inst_4162_: *mut leanh::LeanObject,
    mut v_inst_4163_: *mut leanh::LeanObject,
    mut v_inst_4164_: *mut leanh::LeanObject,
    mut v_inst_4165_: *mut leanh::LeanObject,
    mut v_toBind_4166_: *mut leanh::LeanObject,
    mut v___f_4167_: *mut leanh::LeanObject,
    mut v_s_4168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_powFn_x3f_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_powFn_x3f_4169_ = leanh::lean_ctor_get(v_s_4168_, 6);
    if leanh::lean_obj_tag(v_powFn_x3f_4169_) == 1 {
        let mut v_val_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_powFn_x3f_4169_);
        leanh::lean_dec_ref(v_s_4168_);
        leanh::lean_dec(v___f_4167_);
        leanh::lean_dec(v_toBind_4166_);
        leanh::lean_dec_ref(v_inst_4165_);
        leanh::lean_dec_ref(v_inst_4164_);
        leanh::lean_dec_ref(v_inst_4163_);
        leanh::lean_dec(v_inst_4162_);
        v_val_4170_ = leanh::lean_ctor_get(v_powFn_x3f_4169_, 0);
        leanh::lean_inc(v_val_4170_);
        leanh::lean_dec_ref_known(v_powFn_x3f_4169_, 1);
        v___x_4171_ =
            leanh::lean_apply_2(v_toPure_4161_, leanh::lean_box(0), v_val_4170_);
        return v___x_4171_;
    } else {
        let mut v_type_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_4161_);
        v_type_4172_ = leanh::lean_ctor_get(v_s_4168_, 1);
        leanh::lean_inc_ref(v_type_4172_);
        v_u_4173_ = leanh::lean_ctor_get(v_s_4168_, 2);
        leanh::lean_inc(v_u_4173_);
        v_semiringInst_4174_ = leanh::lean_ctor_get(v_s_4168_, 3);
        leanh::lean_inc_ref(v_semiringInst_4174_);
        leanh::lean_dec_ref(v_s_4168_);
        v___x_4175_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg(
            v_inst_4162_,
            v_inst_4163_,
            v_inst_4164_,
            v_inst_4165_,
            v_u_4173_,
            v_type_4172_,
            v_semiringInst_4174_,
        );
        v___x_4176_ = leanh::lean_apply_4(
            v_toBind_4166_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4175_,
            v___f_4167_,
        );
        return v___x_4176_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg(
    mut v_inst_4177_: *mut leanh::LeanObject,
    mut v_inst_4178_: *mut leanh::LeanObject,
    mut v_inst_4179_: *mut leanh::LeanObject,
    mut v_inst_4180_: *mut leanh::LeanObject,
    mut v_inst_4181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getSemiring_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifySemiring_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4182_ = leanh::lean_ctor_get(v_inst_4179_, 0);
    v_toBind_4183_ = leanh::lean_ctor_get(v_inst_4179_, 1);
    leanh::lean_inc_n(v_toBind_4183_, 3);
    v_getSemiring_4184_ = leanh::lean_ctor_get(v_inst_4181_, 0);
    leanh::lean_inc(v_getSemiring_4184_);
    v_modifySemiring_4185_ = leanh::lean_ctor_get(v_inst_4181_, 1);
    leanh::lean_inc(v_modifySemiring_4185_);
    leanh::lean_dec_ref(v_inst_4181_);
    v_toPure_4186_ = leanh::lean_ctor_get(v_toApplicative_4182_, 1);
    leanh::lean_inc_n(v_toPure_4186_, 2);
    v___f_4187_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_4187_, 0, v_toPure_4186_);
    leanh::lean_closure_set(v___f_4187_, 1, v_modifySemiring_4185_);
    leanh::lean_closure_set(v___f_4187_, 2, v_toBind_4183_);
    v___f_4188_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_4188_, 0, v_toPure_4186_);
    leanh::lean_closure_set(v___f_4188_, 1, v_inst_4177_);
    leanh::lean_closure_set(v___f_4188_, 2, v_inst_4178_);
    leanh::lean_closure_set(v___f_4188_, 3, v_inst_4179_);
    leanh::lean_closure_set(v___f_4188_, 4, v_inst_4180_);
    leanh::lean_closure_set(v___f_4188_, 5, v_toBind_4183_);
    leanh::lean_closure_set(v___f_4188_, 6, v___f_4187_);
    v___x_4189_ = leanh::lean_apply_4(
        v_toBind_4183_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getSemiring_4184_,
        v___f_4188_,
    );
    return v___x_4189_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn_x27(
    mut v_m_4190_: *mut leanh::LeanObject,
    mut v_inst_4191_: *mut leanh::LeanObject,
    mut v_inst_4192_: *mut leanh::LeanObject,
    mut v_inst_4193_: *mut leanh::LeanObject,
    mut v_inst_4194_: *mut leanh::LeanObject,
    mut v_inst_4195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_natCastFn_4197_: *mut leanh::LeanObject,
    mut v_s_4198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_id_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4211_: u8 = 0;
    let mut v___x_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4216_: u8 = 0;
    let mut v_unused_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_4199_ = leanh::lean_ctor_get(v_s_4198_, 0);
                v_type_4200_ = leanh::lean_ctor_get(v_s_4198_, 1);
                v_u_4201_ = leanh::lean_ctor_get(v_s_4198_, 2);
                v_semiringInst_4202_ = leanh::lean_ctor_get(v_s_4198_, 3);
                v_addFn_x3f_4203_ = leanh::lean_ctor_get(v_s_4198_, 4);
                v_mulFn_x3f_4204_ = leanh::lean_ctor_get(v_s_4198_, 5);
                v_powFn_x3f_4205_ = leanh::lean_ctor_get(v_s_4198_, 6);
                v_denote_4206_ = leanh::lean_ctor_get(v_s_4198_, 8);
                v_vars_4207_ = leanh::lean_ctor_get(v_s_4198_, 9);
                v_varMap_4208_ = leanh::lean_ctor_get(v_s_4198_, 10);
                v_isSharedCheck_4216_ = (!leanh::lean_is_exclusive(v_s_4198_)) as u8;
                if v_isSharedCheck_4216_ == 0 {
                    v_unused_4217_ = leanh::lean_ctor_get(v_s_4198_, 7);
                    leanh::lean_dec(v_unused_4217_);
                    v___x_4210_ = v_s_4198_;
                    v_isShared_4211_ = v_isSharedCheck_4216_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_varMap_4208_);
                    leanh::lean_inc(v_vars_4207_);
                    leanh::lean_inc(v_denote_4206_);
                    leanh::lean_inc(v_powFn_x3f_4205_);
                    leanh::lean_inc(v_mulFn_x3f_4204_);
                    leanh::lean_inc(v_addFn_x3f_4203_);
                    leanh::lean_inc(v_semiringInst_4202_);
                    leanh::lean_inc(v_u_4201_);
                    leanh::lean_inc(v_type_4200_);
                    leanh::lean_inc(v_id_4199_);
                    leanh::lean_dec(v_s_4198_);
                    v___x_4210_ = leanh::lean_box(0);
                    v_isShared_4211_ = v_isSharedCheck_4216_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4212_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4212_, 0, v_natCastFn_4197_);
                if v_isShared_4211_ == 0 {
                    leanh::lean_ctor_set(v___x_4210_, 7, v___x_4212_);
                    v___x_4214_ = v___x_4210_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4215_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4215_, 0, v_id_4199_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4215_, 1, v_type_4200_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4215_, 2, v_u_4201_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4215_, 3, v_semiringInst_4202_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4215_, 4, v_addFn_x3f_4203_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4215_, 5, v_mulFn_x3f_4204_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4215_, 6, v_powFn_x3f_4205_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4215_, 7, v___x_4212_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4215_, 8, v_denote_4206_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4215_, 9, v_vars_4207_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4215_, 10, v_varMap_4208_);
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
    mut v_toPure_4218_: *mut leanh::LeanObject,
    mut v_natCastFn_4219_: *mut leanh::LeanObject,
    mut v_____r_4220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4221_ =
        leanh::lean_apply_2(v_toPure_4218_, leanh::lean_box(0), v_natCastFn_4219_);
    return v___x_4221_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__2(
    mut v_toPure_4222_: *mut leanh::LeanObject,
    mut v_modifySemiring_4223_: *mut leanh::LeanObject,
    mut v_toBind_4224_: *mut leanh::LeanObject,
    mut v_natCastFn_4225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_natCastFn_4225_);
    v___f_4226_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_4226_, 0, v_natCastFn_4225_);
    v___f_4227_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__1
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_4227_, 0, v_toPure_4222_);
    leanh::lean_closure_set(v___f_4227_, 1, v_natCastFn_4225_);
    v___x_4228_ = leanh::lean_apply_1(v_modifySemiring_4223_, v___f_4226_);
    v___x_4229_ = leanh::lean_apply_4(
        v_toBind_4224_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4228_,
        v___f_4227_,
    );
    return v___x_4229_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__3(
    mut v_toPure_4230_: *mut leanh::LeanObject,
    mut v_inst_4231_: *mut leanh::LeanObject,
    mut v_inst_4232_: *mut leanh::LeanObject,
    mut v_inst_4233_: *mut leanh::LeanObject,
    mut v_toBind_4234_: *mut leanh::LeanObject,
    mut v___f_4235_: *mut leanh::LeanObject,
    mut v_s_4236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_natCastFn_x3f_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_natCastFn_x3f_4237_ = leanh::lean_ctor_get(v_s_4236_, 7);
    if leanh::lean_obj_tag(v_natCastFn_x3f_4237_) == 1 {
        let mut v_val_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_natCastFn_x3f_4237_);
        leanh::lean_dec_ref(v_s_4236_);
        leanh::lean_dec(v___f_4235_);
        leanh::lean_dec(v_toBind_4234_);
        leanh::lean_dec_ref(v_inst_4233_);
        leanh::lean_dec_ref(v_inst_4232_);
        leanh::lean_dec(v_inst_4231_);
        v_val_4238_ = leanh::lean_ctor_get(v_natCastFn_x3f_4237_, 0);
        leanh::lean_inc(v_val_4238_);
        leanh::lean_dec_ref_known(v_natCastFn_x3f_4237_, 1);
        v___x_4239_ =
            leanh::lean_apply_2(v_toPure_4230_, leanh::lean_box(0), v_val_4238_);
        return v___x_4239_;
    } else {
        let mut v_type_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_4230_);
        v_type_4240_ = leanh::lean_ctor_get(v_s_4236_, 1);
        leanh::lean_inc_ref(v_type_4240_);
        v_u_4241_ = leanh::lean_ctor_get(v_s_4236_, 2);
        leanh::lean_inc(v_u_4241_);
        v_semiringInst_4242_ = leanh::lean_ctor_get(v_s_4236_, 3);
        leanh::lean_inc_ref(v_semiringInst_4242_);
        leanh::lean_dec_ref(v_s_4236_);
        v___x_4243_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg(
            v_inst_4231_,
            v_inst_4232_,
            v_inst_4233_,
            v_u_4241_,
            v_type_4240_,
            v_semiringInst_4242_,
        );
        v___x_4244_ = leanh::lean_apply_4(
            v_toBind_4234_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4243_,
            v___f_4235_,
        );
        return v___x_4244_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg(
    mut v_inst_4245_: *mut leanh::LeanObject,
    mut v_inst_4246_: *mut leanh::LeanObject,
    mut v_inst_4247_: *mut leanh::LeanObject,
    mut v_inst_4248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getSemiring_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifySemiring_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4249_ = leanh::lean_ctor_get(v_inst_4246_, 0);
    v_toBind_4250_ = leanh::lean_ctor_get(v_inst_4246_, 1);
    leanh::lean_inc_n(v_toBind_4250_, 3);
    v_getSemiring_4251_ = leanh::lean_ctor_get(v_inst_4248_, 0);
    leanh::lean_inc(v_getSemiring_4251_);
    v_modifySemiring_4252_ = leanh::lean_ctor_get(v_inst_4248_, 1);
    leanh::lean_inc(v_modifySemiring_4252_);
    leanh::lean_dec_ref(v_inst_4248_);
    v_toPure_4253_ = leanh::lean_ctor_get(v_toApplicative_4249_, 1);
    leanh::lean_inc_n(v_toPure_4253_, 2);
    v___f_4254_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__2
            as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_4254_, 0, v_toPure_4253_);
    leanh::lean_closure_set(v___f_4254_, 1, v_modifySemiring_4252_);
    leanh::lean_closure_set(v___f_4254_, 2, v_toBind_4250_);
    v___f_4255_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg___lam__3
            as *mut core::ffi::c_void,
        7,
        6,
    );
    leanh::lean_closure_set(v___f_4255_, 0, v_toPure_4253_);
    leanh::lean_closure_set(v___f_4255_, 1, v_inst_4245_);
    leanh::lean_closure_set(v___f_4255_, 2, v_inst_4246_);
    leanh::lean_closure_set(v___f_4255_, 3, v_inst_4247_);
    leanh::lean_closure_set(v___f_4255_, 4, v_toBind_4250_);
    leanh::lean_closure_set(v___f_4255_, 5, v___f_4254_);
    v___x_4256_ = leanh::lean_apply_4(
        v_toBind_4250_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getSemiring_4251_,
        v___f_4255_,
    );
    return v___x_4256_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27(
    mut v_m_4257_: *mut leanh::LeanObject,
    mut v_inst_4258_: *mut leanh::LeanObject,
    mut v_inst_4259_: *mut leanh::LeanObject,
    mut v_inst_4260_: *mut leanh::LeanObject,
    mut v_inst_4261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4262_ = l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn_x27___redArg(
        v_inst_4258_,
        v_inst_4259_,
        v_inst_4260_,
        v_inst_4261_,
    );
    return v___x_4262_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_keys_4263_: *mut leanh::LeanObject,
    mut v_vals_4264_: *mut leanh::LeanObject,
    mut v_i_4265_: *mut leanh::LeanObject,
    mut v_k_4266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: u8 = 0;
    let mut v___x_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: u8 = 0;
    let mut v___x_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4267_ = lean_array_get_size(v_keys_4263_);
                v___x_4268_ = lean_nat_dec_lt(v_i_4265_, v___x_4267_);
                if v___x_4268_ == 0 {
                    leanh::lean_dec(v_i_4265_);
                    v___x_4269_ = leanh::lean_box(0);
                    return v___x_4269_;
                } else {
                    v_k_x27_4270_ = lean_array_fget_borrowed(v_keys_4263_, v_i_4265_);
                    v___x_4271_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_4266_,
                            v_k_x27_4270_,
                        );
                    if v___x_4271_ == 0 {
                        v___x_4272_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4273_ = lean_nat_add(v_i_4265_, v___x_4272_);
                        leanh::lean_dec(v_i_4265_);
                        v_i_4265_ = v___x_4273_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4275_ = lean_array_fget_borrowed(v_vals_4264_, v_i_4265_);
                        leanh::lean_dec(v_i_4265_);
                        leanh::lean_inc(v___x_4275_);
                        v___x_4276_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4276_, 0, v___x_4275_);
                        return v___x_4276_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_4277_: *mut leanh::LeanObject,
    mut v_vals_4278_: *mut leanh::LeanObject,
    mut v_i_4279_: *mut leanh::LeanObject,
    mut v_k_4280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4281_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4277_, v_vals_4278_, v_i_4279_, v_k_4280_);
    leanh::lean_dec_ref(v_k_4280_);
    leanh::lean_dec_ref(v_vals_4278_);
    leanh::lean_dec_ref(v_keys_4277_);
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
    v___x_4286_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__0);
    v___x_4287_ = lean_usize_sub(v___x_4286_, v___x_4285_);
    return v___x_4287_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(
    mut v_x_4288_: *mut leanh::LeanObject,
    mut v_x_4289_: usize,
    mut v_x_4290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: usize = 0;
    let mut v___x_4294_: usize = 0;
    let mut v___x_4295_: usize = 0;
    let mut v_j_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: u8 = 0;
    let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: usize = 0;
    let mut v___x_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4288_) == 0 {
                    v_es_4291_ = leanh::lean_ctor_get(v_x_4288_, 0);
                    v___x_4292_ = leanh::lean_box(2);
                    v___x_4293_ = 5usize;
                    v___x_4294_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_4295_ = lean_usize_land(v_x_4289_, v___x_4294_);
                    v_j_4296_ = lean_usize_to_nat(v___x_4295_);
                    v___x_4297_ = lean_array_get_borrowed(v___x_4292_, v_es_4291_, v_j_4296_);
                    leanh::lean_dec(v_j_4296_);
                    match leanh::lean_obj_tag(v___x_4297_) {
                        0 => {
                            v_key_4298_ = leanh::lean_ctor_get(v___x_4297_, 0);
                            v_val_4299_ = leanh::lean_ctor_get(v___x_4297_, 1);
                            v___x_4300_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_4290_, v_key_4298_);
                            if v___x_4300_ == 0 {
                                v___x_4301_ = leanh::lean_box(0);
                                return v___x_4301_;
                            } else {
                                leanh::lean_inc(v_val_4299_);
                                v___x_4302_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_4302_, 0, v_val_4299_);
                                return v___x_4302_;
                            }
                        }
                        1 => {
                            v_node_4303_ = leanh::lean_ctor_get(v___x_4297_, 0);
                            v___x_4304_ = lean_usize_shift_right(v_x_4289_, v___x_4293_);
                            v_x_4288_ = v_node_4303_;
                            v_x_4289_ = v___x_4304_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4306_ = leanh::lean_box(0);
                            return v___x_4306_;
                        }
                    }
                } else {
                    v_ks_4307_ = leanh::lean_ctor_get(v_x_4288_, 0);
                    v_vs_4308_ = leanh::lean_ctor_get(v_x_4288_, 1);
                    v___x_4309_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4310_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_4307_, v_vs_4308_, v___x_4309_, v_x_4290_);
                    return v___x_4310_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_4311_: *mut leanh::LeanObject,
    mut v_x_4312_: *mut leanh::LeanObject,
    mut v_x_4313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_867__boxed_4314_: usize = 0;
    let mut v_res_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_867__boxed_4314_ = leanh::lean_unbox_usize(v_x_4312_);
    leanh::lean_dec(v_x_4312_);
    v_res_4315_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_4311_, v_x_867__boxed_4314_, v_x_4313_);
    leanh::lean_dec_ref(v_x_4313_);
    leanh::lean_dec_ref(v_x_4311_);
    return v_res_4315_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(
    mut v_x_4316_: *mut leanh::LeanObject,
    mut v_x_4317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4318_: u64 = 0;
    let mut v___x_4319_: usize = 0;
    let mut v___x_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4318_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_4317_);
    v___x_4319_ = lean_uint64_to_usize(v___x_4318_);
    v___x_4320_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_4316_, v___x_4319_, v_x_4317_);
    return v___x_4320_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg___boxed(
    mut v_x_4321_: *mut leanh::LeanObject,
    mut v_x_4322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4323_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_x_4321_, v_x_4322_);
    leanh::lean_dec_ref(v_x_4322_);
    leanh::lean_dec_ref(v_x_4321_);
    return v_res_4323_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(
    mut v_e_4324_: *mut leanh::LeanObject,
    mut v_a_4325_: *mut leanh::LeanObject,
    mut v_a_4326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4332_: u8 = 0;
    let mut v_exprToSemiringId_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4338_: u8 = 0;
    let mut v_a_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4342_: u8 = 0;
    let mut v___x_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4346_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4328_ =
                    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_4325_, v_a_4326_);
                if leanh::lean_obj_tag(v___x_4328_) == 0 {
                    v_a_4329_ = leanh::lean_ctor_get(v___x_4328_, 0);
                    v_isSharedCheck_4338_ = (!leanh::lean_is_exclusive(v___x_4328_)) as u8;
                    if v_isSharedCheck_4338_ == 0 {
                        v___x_4331_ = v___x_4328_;
                        v_isShared_4332_ = v_isSharedCheck_4338_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4329_);
                        leanh::lean_dec(v___x_4328_);
                        v___x_4331_ = leanh::lean_box(0);
                        v_isShared_4332_ = v_isSharedCheck_4338_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4339_ = leanh::lean_ctor_get(v___x_4328_, 0);
                    v_isSharedCheck_4346_ = (!leanh::lean_is_exclusive(v___x_4328_)) as u8;
                    if v_isSharedCheck_4346_ == 0 {
                        v___x_4341_ = v___x_4328_;
                        v_isShared_4342_ = v_isSharedCheck_4346_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4339_);
                        leanh::lean_dec(v___x_4328_);
                        v___x_4341_ = leanh::lean_box(0);
                        v_isShared_4342_ = v_isSharedCheck_4346_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_exprToSemiringId_4333_ = leanh::lean_ctor_get(v_a_4329_, 5);
                leanh::lean_inc_ref(v_exprToSemiringId_4333_);
                leanh::lean_dec(v_a_4329_);
                v___x_4334_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_exprToSemiringId_4333_, v_e_4324_);
                leanh::lean_dec_ref(v_exprToSemiringId_4333_);
                if v_isShared_4332_ == 0 {
                    leanh::lean_ctor_set(v___x_4331_, 0, v___x_4334_);
                    v___x_4336_ = v___x_4331_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4337_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4337_, 0, v___x_4334_);
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
                    v_reuseFailAlloc_4345_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_a_4339_);
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
    mut v_e_4347_: *mut leanh::LeanObject,
    mut v_a_4348_: *mut leanh::LeanObject,
    mut v_a_4349_: *mut leanh::LeanObject,
    mut v_a_4350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4351_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(
        v_e_4347_, v_a_4348_, v_a_4349_,
    );
    leanh::lean_dec_ref(v_a_4349_);
    leanh::lean_dec(v_a_4348_);
    leanh::lean_dec_ref(v_e_4347_);
    return v_res_4351_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f(
    mut v_e_4352_: *mut leanh::LeanObject,
    mut v_a_4353_: *mut leanh::LeanObject,
    mut v_a_4354_: *mut leanh::LeanObject,
    mut v_a_4355_: *mut leanh::LeanObject,
    mut v_a_4356_: *mut leanh::LeanObject,
    mut v_a_4357_: *mut leanh::LeanObject,
    mut v_a_4358_: *mut leanh::LeanObject,
    mut v_a_4359_: *mut leanh::LeanObject,
    mut v_a_4360_: *mut leanh::LeanObject,
    mut v_a_4361_: *mut leanh::LeanObject,
    mut v_a_4362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4364_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(
        v_e_4352_, v_a_4353_, v_a_4361_,
    );
    return v___x_4364_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___boxed(
    mut v_e_4365_: *mut leanh::LeanObject,
    mut v_a_4366_: *mut leanh::LeanObject,
    mut v_a_4367_: *mut leanh::LeanObject,
    mut v_a_4368_: *mut leanh::LeanObject,
    mut v_a_4369_: *mut leanh::LeanObject,
    mut v_a_4370_: *mut leanh::LeanObject,
    mut v_a_4371_: *mut leanh::LeanObject,
    mut v_a_4372_: *mut leanh::LeanObject,
    mut v_a_4373_: *mut leanh::LeanObject,
    mut v_a_4374_: *mut leanh::LeanObject,
    mut v_a_4375_: *mut leanh::LeanObject,
    mut v_a_4376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4377_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f(
        v_e_4365_, v_a_4366_, v_a_4367_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_,
        v_a_4373_, v_a_4374_, v_a_4375_,
    );
    leanh::lean_dec(v_a_4375_);
    leanh::lean_dec_ref(v_a_4374_);
    leanh::lean_dec(v_a_4373_);
    leanh::lean_dec_ref(v_a_4372_);
    leanh::lean_dec(v_a_4371_);
    leanh::lean_dec_ref(v_a_4370_);
    leanh::lean_dec(v_a_4369_);
    leanh::lean_dec_ref(v_a_4368_);
    leanh::lean_dec(v_a_4367_);
    leanh::lean_dec(v_a_4366_);
    leanh::lean_dec_ref(v_e_4365_);
    return v_res_4377_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0(
    mut v_00_u03b2_4378_: *mut leanh::LeanObject,
    mut v_x_4379_: *mut leanh::LeanObject,
    mut v_x_4380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4381_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_x_4379_, v_x_4380_);
    return v___x_4381_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___boxed(
    mut v_00_u03b2_4382_: *mut leanh::LeanObject,
    mut v_x_4383_: *mut leanh::LeanObject,
    mut v_x_4384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4385_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0(v_00_u03b2_4382_, v_x_4383_, v_x_4384_);
    leanh::lean_dec_ref(v_x_4384_);
    leanh::lean_dec_ref(v_x_4383_);
    return v_res_4385_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0(
    mut v_00_u03b2_4386_: *mut leanh::LeanObject,
    mut v_x_4387_: *mut leanh::LeanObject,
    mut v_x_4388_: usize,
    mut v_x_4389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4390_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg(v_x_4387_, v_x_4388_, v_x_4389_);
    return v___x_4390_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_4391_: *mut leanh::LeanObject,
    mut v_x_4392_: *mut leanh::LeanObject,
    mut v_x_4393_: *mut leanh::LeanObject,
    mut v_x_4394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_984__boxed_4395_: usize = 0;
    let mut v_res_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_984__boxed_4395_ = leanh::lean_unbox_usize(v_x_4393_);
    leanh::lean_dec(v_x_4393_);
    v_res_4396_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0(v_00_u03b2_4391_, v_x_4392_, v_x_984__boxed_4395_, v_x_4394_);
    leanh::lean_dec_ref(v_x_4394_);
    leanh::lean_dec_ref(v_x_4392_);
    return v_res_4396_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4397_: *mut leanh::LeanObject,
    mut v_keys_4398_: *mut leanh::LeanObject,
    mut v_vals_4399_: *mut leanh::LeanObject,
    mut v_heq_4400_: *mut leanh::LeanObject,
    mut v_i_4401_: *mut leanh::LeanObject,
    mut v_k_4402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4403_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4398_, v_vals_4399_, v_i_4401_, v_k_4402_);
    return v___x_4403_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4404_: *mut leanh::LeanObject,
    mut v_keys_4405_: *mut leanh::LeanObject,
    mut v_vals_4406_: *mut leanh::LeanObject,
    mut v_heq_4407_: *mut leanh::LeanObject,
    mut v_i_4408_: *mut leanh::LeanObject,
    mut v_k_4409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4410_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_4404_, v_keys_4405_, v_vals_4406_, v_heq_4407_, v_i_4408_, v_k_4409_);
    leanh::lean_dec_ref(v_k_4409_);
    leanh::lean_dec_ref(v_vals_4406_);
    leanh::lean_dec_ref(v_keys_4405_);
    return v_res_4410_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_x_4411_: *mut leanh::LeanObject,
    mut v_x_4412_: *mut leanh::LeanObject,
    mut v_x_4413_: *mut leanh::LeanObject,
    mut v_x_4414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4419_: u8 = 0;
    let mut v___x_4420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: u8 = 0;
    let mut v___x_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: u8 = 0;
    let mut v___x_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4440_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4415_ = leanh::lean_ctor_get(v_x_4411_, 0);
                v_vs_4416_ = leanh::lean_ctor_get(v_x_4411_, 1);
                v_isSharedCheck_4440_ = (!leanh::lean_is_exclusive(v_x_4411_)) as u8;
                if v_isSharedCheck_4440_ == 0 {
                    v___x_4418_ = v_x_4411_;
                    v_isShared_4419_ = v_isSharedCheck_4440_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_4416_);
                    leanh::lean_inc(v_ks_4415_);
                    leanh::lean_dec(v_x_4411_);
                    v___x_4418_ = leanh::lean_box(0);
                    v_isShared_4419_ = v_isSharedCheck_4440_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4420_ = lean_array_get_size(v_ks_4415_);
                v___x_4421_ = lean_nat_dec_lt(v_x_4412_, v___x_4420_);
                if v___x_4421_ == 0 {
                    leanh::lean_dec(v_x_4412_);
                    v___x_4422_ = lean_array_push(v_ks_4415_, v_x_4413_);
                    v___x_4423_ = lean_array_push(v_vs_4416_, v_x_4414_);
                    if v_isShared_4419_ == 0 {
                        leanh::lean_ctor_set(v___x_4418_, 1, v___x_4423_);
                        leanh::lean_ctor_set(v___x_4418_, 0, v___x_4422_);
                        v___x_4425_ = v___x_4418_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4426_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4426_, 0, v___x_4422_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4426_, 1, v___x_4423_);
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
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4434_, 0, v_ks_4415_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4434_, 1, v_vs_4416_);
                            v___x_4430_ = v_reuseFailAlloc_4434_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4435_ = lean_array_fset(v_ks_4415_, v_x_4412_, v_x_4413_);
                        v___x_4436_ = lean_array_fset(v_vs_4416_, v_x_4412_, v_x_4414_);
                        leanh::lean_dec(v_x_4412_);
                        if v_isShared_4419_ == 0 {
                            leanh::lean_ctor_set(v___x_4418_, 1, v___x_4436_);
                            leanh::lean_ctor_set(v___x_4418_, 0, v___x_4435_);
                            v___x_4438_ = v___x_4418_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4439_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4439_, 0, v___x_4435_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4439_, 1, v___x_4436_);
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
                v___x_4431_ = leanh::lean_unsigned_to_nat(1);
                v___x_4432_ = lean_nat_add(v_x_4412_, v___x_4431_);
                leanh::lean_dec(v_x_4412_);
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
    mut v_n_4441_: *mut leanh::LeanObject,
    mut v_k_4442_: *mut leanh::LeanObject,
    mut v_v_4443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4444_ = leanh::lean_unsigned_to_nat(0);
    v___x_4445_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_4441_, v___x_4444_, v_k_4442_, v_v_4443_);
    return v___x_4445_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4446_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4446_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(
    mut v_x_4447_: *mut leanh::LeanObject,
    mut v_x_4448_: usize,
    mut v_x_4449_: usize,
    mut v_x_4450_: *mut leanh::LeanObject,
    mut v_x_4451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: usize = 0;
    let mut v___x_4454_: usize = 0;
    let mut v___x_4455_: usize = 0;
    let mut v___x_4456_: usize = 0;
    let mut v_j_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: u8 = 0;
    let mut v___x_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4462_: u8 = 0;
    let mut v_v_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4476_: u8 = 0;
    let mut v___x_4477_: u8 = 0;
    let mut v___x_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4483_: u8 = 0;
    let mut v_node_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4487_: u8 = 0;
    let mut v___x_4488_: usize = 0;
    let mut v___x_4489_: usize = 0;
    let mut v___x_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4494_: u8 = 0;
    let mut v___x_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4496_: u8 = 0;
    let mut v_unused_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4502_: u8 = 0;
    let mut v___x_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_4505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4507_: u8 = 0;
    let mut v_ks_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: usize = 0;
    let mut v___x_4514_: u8 = 0;
    let mut v___x_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: u8 = 0;
    let mut v_reuseFailAlloc_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4519_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4447_) == 0 {
                    v_es_4452_ = leanh::lean_ctor_get(v_x_4447_, 0);
                    v___x_4453_ = 5usize;
                    v___x_4454_ = 1usize;
                    v___x_4455_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_4456_ = lean_usize_land(v_x_4448_, v___x_4455_);
                    v_j_4457_ = lean_usize_to_nat(v___x_4456_);
                    v___x_4458_ = lean_array_get_size(v_es_4452_);
                    v___x_4459_ = lean_nat_dec_lt(v_j_4457_, v___x_4458_);
                    if v___x_4459_ == 0 {
                        leanh::lean_dec(v_j_4457_);
                        leanh::lean_dec(v_x_4451_);
                        leanh::lean_dec_ref(v_x_4450_);
                        return v_x_4447_;
                    } else {
                        leanh::lean_inc_ref(v_es_4452_);
                        v_isSharedCheck_4496_ = (!leanh::lean_is_exclusive(v_x_4447_)) as u8;
                        if v_isSharedCheck_4496_ == 0 {
                            v_unused_4497_ = leanh::lean_ctor_get(v_x_4447_, 0);
                            leanh::lean_dec(v_unused_4497_);
                            v___x_4461_ = v_x_4447_;
                            v_isShared_4462_ = v_isSharedCheck_4496_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_4447_);
                            v___x_4461_ = leanh::lean_box(0);
                            v_isShared_4462_ = v_isSharedCheck_4496_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4498_ = leanh::lean_ctor_get(v_x_4447_, 0);
                    v_vs_4499_ = leanh::lean_ctor_get(v_x_4447_, 1);
                    v_isSharedCheck_4519_ = (!leanh::lean_is_exclusive(v_x_4447_)) as u8;
                    if v_isSharedCheck_4519_ == 0 {
                        v___x_4501_ = v_x_4447_;
                        v_isShared_4502_ = v_isSharedCheck_4519_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_4499_);
                        leanh::lean_inc(v_ks_4498_);
                        leanh::lean_dec(v_x_4447_);
                        v___x_4501_ = leanh::lean_box(0);
                        v_isShared_4502_ = v_isSharedCheck_4519_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4463_ = lean_array_fget(v_es_4452_, v_j_4457_);
                v___x_4464_ = leanh::lean_box(0);
                v_xs_x27_4465_ = lean_array_fset(v_es_4452_, v_j_4457_, v___x_4464_);
                match leanh::lean_obj_tag(v_v_4463_) {
                    0 => {
                        v_key_4472_ = leanh::lean_ctor_get(v_v_4463_, 0);
                        v_val_4473_ = leanh::lean_ctor_get(v_v_4463_, 1);
                        v_isSharedCheck_4483_ = (!leanh::lean_is_exclusive(v_v_4463_)) as u8;
                        if v_isSharedCheck_4483_ == 0 {
                            v___x_4475_ = v_v_4463_;
                            v_isShared_4476_ = v_isSharedCheck_4483_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_4473_);
                            leanh::lean_inc(v_key_4472_);
                            leanh::lean_dec(v_v_4463_);
                            v___x_4475_ = leanh::lean_box(0);
                            v_isShared_4476_ = v_isSharedCheck_4483_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4484_ = leanh::lean_ctor_get(v_v_4463_, 0);
                        v_isSharedCheck_4494_ = (!leanh::lean_is_exclusive(v_v_4463_)) as u8;
                        if v_isSharedCheck_4494_ == 0 {
                            v___x_4486_ = v_v_4463_;
                            v_isShared_4487_ = v_isSharedCheck_4494_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_4484_);
                            leanh::lean_dec(v_v_4463_);
                            v___x_4486_ = leanh::lean_box(0);
                            v_isShared_4487_ = v_isSharedCheck_4494_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4495_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4495_, 0, v_x_4450_);
                        leanh::lean_ctor_set(v___x_4495_, 1, v_x_4451_);
                        v___y_4467_ = v___x_4495_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4468_ = lean_array_fset(v_xs_x27_4465_, v_j_4457_, v___y_4467_);
                leanh::lean_dec(v_j_4457_);
                if v_isShared_4462_ == 0 {
                    leanh::lean_ctor_set(v___x_4461_, 0, v___x_4468_);
                    v___x_4470_ = v___x_4461_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4471_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4471_, 0, v___x_4468_);
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
                    leanh::lean_del_object(v___x_4475_);
                    v___x_4478_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4472_,
                        v_val_4473_,
                        v_x_4450_,
                        v_x_4451_,
                    );
                    v___x_4479_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4479_, 0, v___x_4478_);
                    v___y_4467_ = v___x_4479_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_4473_);
                    leanh::lean_dec(v_key_4472_);
                    if v_isShared_4476_ == 0 {
                        leanh::lean_ctor_set(v___x_4475_, 1, v_x_4451_);
                        leanh::lean_ctor_set(v___x_4475_, 0, v_x_4450_);
                        v___x_4481_ = v___x_4475_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4482_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_x_4450_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4482_, 1, v_x_4451_);
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
                    leanh::lean_ctor_set(v___x_4486_, 0, v___x_4490_);
                    v___x_4492_ = v___x_4486_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4493_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4493_, 0, v___x_4490_);
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
                    v_reuseFailAlloc_4518_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4518_, 0, v_ks_4498_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4518_, 1, v_vs_4499_);
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
                    v___x_4516_ = leanh::lean_unsigned_to_nat(4);
                    v___x_4517_ = lean_nat_dec_lt(v___x_4515_, v___x_4516_);
                    leanh::lean_dec(v___x_4515_);
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
                    v_ks_4508_ = leanh::lean_ctor_get(v_newNode_4505_, 0);
                    leanh::lean_inc_ref(v_ks_4508_);
                    v_vs_4509_ = leanh::lean_ctor_get(v_newNode_4505_, 1);
                    leanh::lean_inc_ref(v_vs_4509_);
                    leanh::lean_dec_ref(v_newNode_4505_);
                    v___x_4510_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4511_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___closed__0);
                    v___x_4512_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_x_4449_, v_ks_4508_, v_vs_4509_, v___x_4510_, v___x_4511_);
                    leanh::lean_dec_ref(v_vs_4509_);
                    leanh::lean_dec_ref(v_ks_4508_);
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
    mut v_keys_4521_: *mut leanh::LeanObject,
    mut v_vals_4522_: *mut leanh::LeanObject,
    mut v_i_4523_: *mut leanh::LeanObject,
    mut v_entries_4524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: u8 = 0;
    let mut v_k_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: u64 = 0;
    let mut v_h_4530_: usize = 0;
    let mut v___x_4531_: usize = 0;
    let mut v___x_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: usize = 0;
    let mut v___x_4534_: usize = 0;
    let mut v___x_4535_: usize = 0;
    let mut v_h_4536_: usize = 0;
    let mut v___x_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4525_ = lean_array_get_size(v_keys_4521_);
                v___x_4526_ = lean_nat_dec_lt(v_i_4523_, v___x_4525_);
                if v___x_4526_ == 0 {
                    leanh::lean_dec(v_i_4523_);
                    return v_entries_4524_;
                } else {
                    v_k_4527_ = lean_array_fget_borrowed(v_keys_4521_, v_i_4523_);
                    v_v_4528_ = lean_array_fget_borrowed(v_vals_4522_, v_i_4523_);
                    v___x_4529_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_4527_);
                    v_h_4530_ = lean_uint64_to_usize(v___x_4529_);
                    v___x_4531_ = 5usize;
                    v___x_4532_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4533_ = 1usize;
                    v___x_4534_ = lean_usize_sub(v_depth_4520_, v___x_4533_);
                    v___x_4535_ = lean_usize_mul(v___x_4531_, v___x_4534_);
                    v_h_4536_ = lean_usize_shift_right(v_h_4530_, v___x_4535_);
                    v___x_4537_ = lean_nat_add(v_i_4523_, v___x_4532_);
                    leanh::lean_dec(v_i_4523_);
                    leanh::lean_inc(v_v_4528_);
                    leanh::lean_inc(v_k_4527_);
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
    mut v_depth_4540_: *mut leanh::LeanObject,
    mut v_keys_4541_: *mut leanh::LeanObject,
    mut v_vals_4542_: *mut leanh::LeanObject,
    mut v_i_4543_: *mut leanh::LeanObject,
    mut v_entries_4544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_4545_: usize = 0;
    let mut v_res_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4545_ = leanh::lean_unbox_usize(v_depth_4540_);
    leanh::lean_dec(v_depth_4540_);
    v_res_4546_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_4545_, v_keys_4541_, v_vals_4542_, v_i_4543_, v_entries_4544_);
    leanh::lean_dec_ref(v_vals_4542_);
    leanh::lean_dec_ref(v_keys_4541_);
    return v_res_4546_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg___boxed(
    mut v_x_4547_: *mut leanh::LeanObject,
    mut v_x_4548_: *mut leanh::LeanObject,
    mut v_x_4549_: *mut leanh::LeanObject,
    mut v_x_4550_: *mut leanh::LeanObject,
    mut v_x_4551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_7240__boxed_4552_: usize = 0;
    let mut v_x_7241__boxed_4553_: usize = 0;
    let mut v_res_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_7240__boxed_4552_ = leanh::lean_unbox_usize(v_x_4548_);
    leanh::lean_dec(v_x_4548_);
    v_x_7241__boxed_4553_ = leanh::lean_unbox_usize(v_x_4549_);
    leanh::lean_dec(v_x_4549_);
    v_res_4554_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_4547_, v_x_7240__boxed_4552_, v_x_7241__boxed_4553_, v_x_4550_, v_x_4551_);
    return v_res_4554_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(
    mut v_x_4555_: *mut leanh::LeanObject,
    mut v_x_4556_: *mut leanh::LeanObject,
    mut v_x_4557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4558_: u64 = 0;
    let mut v___x_4559_: usize = 0;
    let mut v___x_4560_: usize = 0;
    let mut v___x_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4558_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_4556_);
    v___x_4559_ = lean_uint64_to_usize(v___x_4558_);
    v___x_4560_ = 1usize;
    v___x_4561_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_4555_, v___x_4559_, v___x_4560_, v_x_4556_, v_x_4557_);
    return v___x_4561_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0(
    mut v_e_4562_: *mut leanh::LeanObject,
    mut v_a_4563_: *mut leanh::LeanObject,
    mut v_s_4564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_rings_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_4578_: u8 = 0;
    let mut v___x_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4581_: u8 = 0;
    let mut v___x_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4586_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_4565_ = leanh::lean_ctor_get(v_s_4564_, 0);
                v_typeIdOf_4566_ = leanh::lean_ctor_get(v_s_4564_, 1);
                v_exprToRingId_4567_ = leanh::lean_ctor_get(v_s_4564_, 2);
                v_semirings_4568_ = leanh::lean_ctor_get(v_s_4564_, 3);
                v_stypeIdOf_4569_ = leanh::lean_ctor_get(v_s_4564_, 4);
                v_exprToSemiringId_4570_ = leanh::lean_ctor_get(v_s_4564_, 5);
                v_ncRings_4571_ = leanh::lean_ctor_get(v_s_4564_, 6);
                v_exprToNCRingId_4572_ = leanh::lean_ctor_get(v_s_4564_, 7);
                v_nctypeIdOf_4573_ = leanh::lean_ctor_get(v_s_4564_, 8);
                v_ncSemirings_4574_ = leanh::lean_ctor_get(v_s_4564_, 9);
                v_exprToNCSemiringId_4575_ = leanh::lean_ctor_get(v_s_4564_, 10);
                v_ncstypeIdOf_4576_ = leanh::lean_ctor_get(v_s_4564_, 11);
                v_steps_4577_ = leanh::lean_ctor_get(v_s_4564_, 12);
                v_reportedMaxDegreeIssue_4578_ = leanh::lean_ctor_get_uint8(
                    v_s_4564_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v_isSharedCheck_4586_ = (!leanh::lean_is_exclusive(v_s_4564_)) as u8;
                if v_isSharedCheck_4586_ == 0 {
                    v___x_4580_ = v_s_4564_;
                    v_isShared_4581_ = v_isSharedCheck_4586_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_steps_4577_);
                    leanh::lean_inc(v_ncstypeIdOf_4576_);
                    leanh::lean_inc(v_exprToNCSemiringId_4575_);
                    leanh::lean_inc(v_ncSemirings_4574_);
                    leanh::lean_inc(v_nctypeIdOf_4573_);
                    leanh::lean_inc(v_exprToNCRingId_4572_);
                    leanh::lean_inc(v_ncRings_4571_);
                    leanh::lean_inc(v_exprToSemiringId_4570_);
                    leanh::lean_inc(v_stypeIdOf_4569_);
                    leanh::lean_inc(v_semirings_4568_);
                    leanh::lean_inc(v_exprToRingId_4567_);
                    leanh::lean_inc(v_typeIdOf_4566_);
                    leanh::lean_inc(v_rings_4565_);
                    leanh::lean_dec(v_s_4564_);
                    v___x_4580_ = leanh::lean_box(0);
                    v_isShared_4581_ = v_isSharedCheck_4586_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_a_4563_);
                v___x_4582_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_exprToSemiringId_4570_, v_e_4562_, v_a_4563_);
                if v_isShared_4581_ == 0 {
                    leanh::lean_ctor_set(v___x_4580_, 5, v___x_4582_);
                    v___x_4584_ = v___x_4580_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4585_ = leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 0, v_rings_4565_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 1, v_typeIdOf_4566_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 2, v_exprToRingId_4567_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 3, v_semirings_4568_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 4, v_stypeIdOf_4569_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 5, v___x_4582_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 6, v_ncRings_4571_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 7, v_exprToNCRingId_4572_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 8, v_nctypeIdOf_4573_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 9, v_ncSemirings_4574_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4585_,
                        10,
                        v_exprToNCSemiringId_4575_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 11, v_ncstypeIdOf_4576_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 12, v_steps_4577_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4585_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
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
    mut v_e_4587_: *mut leanh::LeanObject,
    mut v_a_4588_: *mut leanh::LeanObject,
    mut v_s_4589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4590_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0(
        v_e_4587_, v_a_4588_, v_s_4589_,
    );
    leanh::lean_dec(v_a_4588_);
    return v_res_4590_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4592_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__0;
    v___x_4593_ = l_Lean_stringToMessageData(v___x_4592_);
    return v___x_4593_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(
    mut v_e_4594_: *mut leanh::LeanObject,
    mut v_a_4595_: *mut leanh::LeanObject,
    mut v_a_4596_: *mut leanh::LeanObject,
    mut v_a_4597_: *mut leanh::LeanObject,
    mut v_a_4598_: *mut leanh::LeanObject,
    mut v_a_4599_: *mut leanh::LeanObject,
    mut v_a_4600_: *mut leanh::LeanObject,
    mut v_a_4601_: *mut leanh::LeanObject,
    mut v_a_4602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: u8 = 0;
    let mut v___x_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: u8 = 0;
    let mut v___x_4614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4621_: u8 = 0;
    let mut v___x_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4625_: u8 = 0;
    let mut v___f_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4632_: u8 = 0;
    let mut v___x_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4636_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4607_ = l_Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f___redArg(
                    v_e_4594_, v_a_4596_, v_a_4601_,
                );
                if leanh::lean_obj_tag(v___x_4607_) == 0 {
                    v_a_4608_ = leanh::lean_ctor_get(v___x_4607_, 0);
                    leanh::lean_inc(v_a_4608_);
                    leanh::lean_dec_ref_known(v___x_4607_, 1);
                    if leanh::lean_obj_tag(v_a_4608_) == 1 {
                        v_val_4609_ = leanh::lean_ctor_get(v_a_4608_, 0);
                        leanh::lean_inc(v_val_4609_);
                        leanh::lean_dec_ref_known(v_a_4608_, 1);
                        v___x_4610_ = lean_nat_dec_eq(v_val_4609_, v_a_4595_);
                        leanh::lean_dec(v_val_4609_);
                        if v___x_4610_ == 0 {
                            v___x_4611_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_4597_);
                            if leanh::lean_obj_tag(v___x_4611_) == 0 {
                                v_a_4612_ = leanh::lean_ctor_get(v___x_4611_, 0);
                                leanh::lean_inc(v_a_4612_);
                                leanh::lean_dec_ref_known(v___x_4611_, 1);
                                v___x_4613_ = (leanh::lean_unbox(v_a_4612_) as u8);
                                leanh::lean_dec(v_a_4612_);
                                if v___x_4613_ == 0 {
                                    leanh::lean_dec_ref(v_e_4594_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_4614_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1_once), _init_l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___closed__1);
                                    v___x_4615_ = l_Lean_indentExpr(v_e_4594_);
                                    v___x_4616_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4616_, 0, v___x_4614_);
                                    leanh::lean_ctor_set(v___x_4616_, 1, v___x_4615_);
                                    v___x_4617_ = l_Lean_Meta_Sym_reportIssue(
                                        v___x_4616_,
                                        v_a_4597_,
                                        v_a_4598_,
                                        v_a_4599_,
                                        v_a_4600_,
                                        v_a_4601_,
                                        v_a_4602_,
                                    );
                                    if leanh::lean_obj_tag(v___x_4617_) == 0 {
                                        leanh::lean_dec_ref_known(v___x_4617_, 1);
                                        state = 1;
                                        continue;
                                    } else {
                                        return v___x_4617_;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_e_4594_);
                                v_a_4618_ = leanh::lean_ctor_get(v___x_4611_, 0);
                                v_isSharedCheck_4625_ =
                                    (!leanh::lean_is_exclusive(v___x_4611_)) as u8;
                                if v_isSharedCheck_4625_ == 0 {
                                    v___x_4620_ = v___x_4611_;
                                    v_isShared_4621_ = v_isSharedCheck_4625_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4618_);
                                    leanh::lean_dec(v___x_4611_);
                                    v___x_4620_ = leanh::lean_box(0);
                                    v_isShared_4621_ = v_isSharedCheck_4625_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_e_4594_);
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_4608_);
                        leanh::lean_inc(v_a_4595_);
                        v___f_4626_ = leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                        leanh::lean_closure_set(v___f_4626_, 0, v_e_4594_);
                        leanh::lean_closure_set(v___f_4626_, 1, v_a_4595_);
                        v___x_4627_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                        v___x_4628_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4627_, v___f_4626_, v_a_4596_);
                        return v___x_4628_;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_4594_);
                    v_a_4629_ = leanh::lean_ctor_get(v___x_4607_, 0);
                    v_isSharedCheck_4636_ = (!leanh::lean_is_exclusive(v___x_4607_)) as u8;
                    if v_isSharedCheck_4636_ == 0 {
                        v___x_4631_ = v___x_4607_;
                        v_isShared_4632_ = v_isSharedCheck_4636_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4629_);
                        leanh::lean_dec(v___x_4607_);
                        v___x_4631_ = leanh::lean_box(0);
                        v_isShared_4632_ = v_isSharedCheck_4636_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4605_ = leanh::lean_box(0);
                v___x_4606_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4606_, 0, v___x_4605_);
                return v___x_4606_;
            }
            2 => {
                if v_isShared_4621_ == 0 {
                    v___x_4623_ = v___x_4620_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4624_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4624_, 0, v_a_4618_);
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
                    v_reuseFailAlloc_4635_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4635_, 0, v_a_4629_);
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
    mut v_e_4637_: *mut leanh::LeanObject,
    mut v_a_4638_: *mut leanh::LeanObject,
    mut v_a_4639_: *mut leanh::LeanObject,
    mut v_a_4640_: *mut leanh::LeanObject,
    mut v_a_4641_: *mut leanh::LeanObject,
    mut v_a_4642_: *mut leanh::LeanObject,
    mut v_a_4643_: *mut leanh::LeanObject,
    mut v_a_4644_: *mut leanh::LeanObject,
    mut v_a_4645_: *mut leanh::LeanObject,
    mut v_a_4646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4647_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(
        v_e_4637_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_,
        v_a_4645_,
    );
    leanh::lean_dec(v_a_4645_);
    leanh::lean_dec_ref(v_a_4644_);
    leanh::lean_dec(v_a_4643_);
    leanh::lean_dec_ref(v_a_4642_);
    leanh::lean_dec(v_a_4641_);
    leanh::lean_dec_ref(v_a_4640_);
    leanh::lean_dec(v_a_4639_);
    leanh::lean_dec(v_a_4638_);
    return v_res_4647_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(
    mut v_e_4648_: *mut leanh::LeanObject,
    mut v_a_4649_: *mut leanh::LeanObject,
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
) -> *mut leanh::LeanObject {
    let mut v___x_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4661_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(
        v_e_4648_, v_a_4649_, v_a_4650_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_,
        v_a_4659_,
    );
    return v___x_4661_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___boxed(
    mut v_e_4662_: *mut leanh::LeanObject,
    mut v_a_4663_: *mut leanh::LeanObject,
    mut v_a_4664_: *mut leanh::LeanObject,
    mut v_a_4665_: *mut leanh::LeanObject,
    mut v_a_4666_: *mut leanh::LeanObject,
    mut v_a_4667_: *mut leanh::LeanObject,
    mut v_a_4668_: *mut leanh::LeanObject,
    mut v_a_4669_: *mut leanh::LeanObject,
    mut v_a_4670_: *mut leanh::LeanObject,
    mut v_a_4671_: *mut leanh::LeanObject,
    mut v_a_4672_: *mut leanh::LeanObject,
    mut v_a_4673_: *mut leanh::LeanObject,
    mut v_a_4674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4675_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(
        v_e_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_, v_a_4668_, v_a_4669_,
        v_a_4670_, v_a_4671_, v_a_4672_, v_a_4673_,
    );
    leanh::lean_dec(v_a_4673_);
    leanh::lean_dec_ref(v_a_4672_);
    leanh::lean_dec(v_a_4671_);
    leanh::lean_dec_ref(v_a_4670_);
    leanh::lean_dec(v_a_4669_);
    leanh::lean_dec_ref(v_a_4668_);
    leanh::lean_dec(v_a_4667_);
    leanh::lean_dec_ref(v_a_4666_);
    leanh::lean_dec(v_a_4665_);
    leanh::lean_dec(v_a_4664_);
    leanh::lean_dec(v_a_4663_);
    return v_res_4675_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0(
    mut v_00_u03b2_4676_: *mut leanh::LeanObject,
    mut v_x_4677_: *mut leanh::LeanObject,
    mut v_x_4678_: *mut leanh::LeanObject,
    mut v_x_4679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4680_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_x_4677_, v_x_4678_, v_x_4679_);
    return v___x_4680_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(
    mut v_00_u03b2_4681_: *mut leanh::LeanObject,
    mut v_x_4682_: *mut leanh::LeanObject,
    mut v_x_4683_: usize,
    mut v_x_4684_: usize,
    mut v_x_4685_: *mut leanh::LeanObject,
    mut v_x_4686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4687_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___redArg(v_x_4682_, v_x_4683_, v_x_4684_, v_x_4685_, v_x_4686_);
    return v___x_4687_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0___boxed(
    mut v_00_u03b2_4688_: *mut leanh::LeanObject,
    mut v_x_4689_: *mut leanh::LeanObject,
    mut v_x_4690_: *mut leanh::LeanObject,
    mut v_x_4691_: *mut leanh::LeanObject,
    mut v_x_4692_: *mut leanh::LeanObject,
    mut v_x_4693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_7519__boxed_4694_: usize = 0;
    let mut v_x_7520__boxed_4695_: usize = 0;
    let mut v_res_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_7519__boxed_4694_ = leanh::lean_unbox_usize(v_x_4690_);
    leanh::lean_dec(v_x_4690_);
    v_x_7520__boxed_4695_ = leanh::lean_unbox_usize(v_x_4691_);
    leanh::lean_dec(v_x_4691_);
    v_res_4696_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0(v_00_u03b2_4688_, v_x_4689_, v_x_7519__boxed_4694_, v_x_7520__boxed_4695_, v_x_4692_, v_x_4693_);
    return v_res_4696_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4697_: *mut leanh::LeanObject,
    mut v_n_4698_: *mut leanh::LeanObject,
    mut v_k_4699_: *mut leanh::LeanObject,
    mut v_v_4700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4701_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1___redArg(v_n_4698_, v_k_4699_, v_v_4700_);
    return v___x_4701_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(
    mut v_00_u03b2_4702_: *mut leanh::LeanObject,
    mut v_depth_4703_: usize,
    mut v_keys_4704_: *mut leanh::LeanObject,
    mut v_vals_4705_: *mut leanh::LeanObject,
    mut v_heq_4706_: *mut leanh::LeanObject,
    mut v_i_4707_: *mut leanh::LeanObject,
    mut v_entries_4708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4709_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___redArg(v_depth_4703_, v_keys_4704_, v_vals_4705_, v_i_4707_, v_entries_4708_);
    return v___x_4709_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_4710_: *mut leanh::LeanObject,
    mut v_depth_4711_: *mut leanh::LeanObject,
    mut v_keys_4712_: *mut leanh::LeanObject,
    mut v_vals_4713_: *mut leanh::LeanObject,
    mut v_heq_4714_: *mut leanh::LeanObject,
    mut v_i_4715_: *mut leanh::LeanObject,
    mut v_entries_4716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_4717_: usize = 0;
    let mut v_res_4718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4717_ = leanh::lean_unbox_usize(v_depth_4711_);
    leanh::lean_dec(v_depth_4711_);
    v_res_4718_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__2(v_00_u03b2_4710_, v_depth_boxed_4717_, v_keys_4712_, v_vals_4713_, v_heq_4714_, v_i_4715_, v_entries_4716_);
    leanh::lean_dec_ref(v_vals_4713_);
    leanh::lean_dec_ref(v_keys_4712_);
    return v_res_4718_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_4719_: *mut leanh::LeanObject,
    mut v_x_4720_: *mut leanh::LeanObject,
    mut v_x_4721_: *mut leanh::LeanObject,
    mut v_x_4722_: *mut leanh::LeanObject,
    mut v_x_4723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4724_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_4720_, v_x_4721_, v_x_4722_, v_x_4723_);
    return v___x_4724_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdSemiringM___lam__0(
    mut v_e_4725_: *mut leanh::LeanObject,
    mut v___y_4726_: *mut leanh::LeanObject,
    mut v___y_4727_: *mut leanh::LeanObject,
    mut v___y_4728_: *mut leanh::LeanObject,
    mut v___y_4729_: *mut leanh::LeanObject,
    mut v___y_4730_: *mut leanh::LeanObject,
    mut v___y_4731_: *mut leanh::LeanObject,
    mut v___y_4732_: *mut leanh::LeanObject,
    mut v___y_4733_: *mut leanh::LeanObject,
    mut v___y_4734_: *mut leanh::LeanObject,
    mut v___y_4735_: *mut leanh::LeanObject,
    mut v___y_4736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_e_4739_: *mut leanh::LeanObject,
    mut v___y_4740_: *mut leanh::LeanObject,
    mut v___y_4741_: *mut leanh::LeanObject,
    mut v___y_4742_: *mut leanh::LeanObject,
    mut v___y_4743_: *mut leanh::LeanObject,
    mut v___y_4744_: *mut leanh::LeanObject,
    mut v___y_4745_: *mut leanh::LeanObject,
    mut v___y_4746_: *mut leanh::LeanObject,
    mut v___y_4747_: *mut leanh::LeanObject,
    mut v___y_4748_: *mut leanh::LeanObject,
    mut v___y_4749_: *mut leanh::LeanObject,
    mut v___y_4750_: *mut leanh::LeanObject,
    mut v___y_4751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4752_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_4750_);
    leanh::lean_dec_ref(v___y_4749_);
    leanh::lean_dec(v___y_4748_);
    leanh::lean_dec_ref(v___y_4747_);
    leanh::lean_dec(v___y_4746_);
    leanh::lean_dec_ref(v___y_4745_);
    leanh::lean_dec(v___y_4744_);
    leanh::lean_dec_ref(v___y_4743_);
    leanh::lean_dec(v___y_4742_);
    leanh::lean_dec(v___y_4741_);
    leanh::lean_dec(v___y_4740_);
    return v_res_4752_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__0(
    mut v_e_4755_: *mut leanh::LeanObject,
    mut v___f_4756_: *mut leanh::LeanObject,
    mut v___f_4757_: *mut leanh::LeanObject,
    mut v_size_4758_: *mut leanh::LeanObject,
    mut v_s_4759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_id_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_4762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_4763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_4766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_4767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_4768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_4769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_4770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4773_: u8 = 0;
    let mut v___x_4774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_4760_ = leanh::lean_ctor_get(v_s_4759_, 0);
                v_type_4761_ = leanh::lean_ctor_get(v_s_4759_, 1);
                v_u_4762_ = leanh::lean_ctor_get(v_s_4759_, 2);
                v_semiringInst_4763_ = leanh::lean_ctor_get(v_s_4759_, 3);
                v_addFn_x3f_4764_ = leanh::lean_ctor_get(v_s_4759_, 4);
                v_mulFn_x3f_4765_ = leanh::lean_ctor_get(v_s_4759_, 5);
                v_powFn_x3f_4766_ = leanh::lean_ctor_get(v_s_4759_, 6);
                v_natCastFn_x3f_4767_ = leanh::lean_ctor_get(v_s_4759_, 7);
                v_denote_4768_ = leanh::lean_ctor_get(v_s_4759_, 8);
                v_vars_4769_ = leanh::lean_ctor_get(v_s_4759_, 9);
                v_varMap_4770_ = leanh::lean_ctor_get(v_s_4759_, 10);
                v_isSharedCheck_4779_ = (!leanh::lean_is_exclusive(v_s_4759_)) as u8;
                if v_isSharedCheck_4779_ == 0 {
                    v___x_4772_ = v_s_4759_;
                    v_isShared_4773_ = v_isSharedCheck_4779_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_varMap_4770_);
                    leanh::lean_inc(v_vars_4769_);
                    leanh::lean_inc(v_denote_4768_);
                    leanh::lean_inc(v_natCastFn_x3f_4767_);
                    leanh::lean_inc(v_powFn_x3f_4766_);
                    leanh::lean_inc(v_mulFn_x3f_4765_);
                    leanh::lean_inc(v_addFn_x3f_4764_);
                    leanh::lean_inc(v_semiringInst_4763_);
                    leanh::lean_inc(v_u_4762_);
                    leanh::lean_inc(v_type_4761_);
                    leanh::lean_inc(v_id_4760_);
                    leanh::lean_dec(v_s_4759_);
                    v___x_4772_ = leanh::lean_box(0);
                    v_isShared_4773_ = v_isSharedCheck_4779_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_e_4755_);
                v___x_4774_ = l_Lean_PersistentArray_push___redArg(v_vars_4769_, v_e_4755_);
                v___x_4775_ = l_Lean_PersistentHashMap_insert___redArg(
                    v___f_4756_,
                    v___f_4757_,
                    v_varMap_4770_,
                    v_e_4755_,
                    v_size_4758_,
                );
                if v_isShared_4773_ == 0 {
                    leanh::lean_ctor_set(v___x_4772_, 10, v___x_4775_);
                    leanh::lean_ctor_set(v___x_4772_, 9, v___x_4774_);
                    v___x_4777_ = v___x_4772_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4778_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4778_, 0, v_id_4760_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4778_, 1, v_type_4761_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4778_, 2, v_u_4762_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4778_, 3, v_semiringInst_4763_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4778_, 4, v_addFn_x3f_4764_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4778_, 5, v_mulFn_x3f_4765_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4778_, 6, v_powFn_x3f_4766_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4778_, 7, v_natCastFn_x3f_4767_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4778_, 8, v_denote_4768_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4778_, 9, v___x_4774_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4778_, 10, v___x_4775_);
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
    mut v_toPure_4780_: *mut leanh::LeanObject,
    mut v_size_4781_: *mut leanh::LeanObject,
    mut v_____r_4782_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4783_ =
        leanh::lean_apply_2(v_toPure_4780_, leanh::lean_box(0), v_size_4781_);
    return v___x_4783_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__2(
    mut v_e_4784_: *mut leanh::LeanObject,
    mut v_inst_4785_: *mut leanh::LeanObject,
    mut v_toBind_4786_: *mut leanh::LeanObject,
    mut v___f_4787_: *mut leanh::LeanObject,
    mut v_____r_4788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4789_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
    v___x_4790_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_SolverExtension_markTerm___boxed as *mut core::ffi::c_void,
        14,
        3,
    );
    leanh::lean_closure_set(v___x_4790_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_4790_, 1, v___x_4789_);
    leanh::lean_closure_set(v___x_4790_, 2, v_e_4784_);
    v___x_4791_ = leanh::lean_apply_2(v_inst_4785_, leanh::lean_box(0), v___x_4790_);
    v___x_4792_ = leanh::lean_apply_4(
        v_toBind_4786_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4791_,
        v___f_4787_,
    );
    return v___x_4792_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__3(
    mut v_inst_4793_: *mut leanh::LeanObject,
    mut v_e_4794_: *mut leanh::LeanObject,
    mut v_toBind_4795_: *mut leanh::LeanObject,
    mut v___f_4796_: *mut leanh::LeanObject,
    mut v_____r_4797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4798_ = leanh::lean_apply_1(v_inst_4793_, v_e_4794_);
    v___x_4799_ = leanh::lean_apply_4(
        v_toBind_4795_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4798_,
        v___f_4796_,
    );
    return v___x_4799_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__4(
    mut v___f_4800_: *mut leanh::LeanObject,
    mut v___f_4801_: *mut leanh::LeanObject,
    mut v_e_4802_: *mut leanh::LeanObject,
    mut v_toPure_4803_: *mut leanh::LeanObject,
    mut v_inst_4804_: *mut leanh::LeanObject,
    mut v_toBind_4805_: *mut leanh::LeanObject,
    mut v_inst_4806_: *mut leanh::LeanObject,
    mut v_modifySemiring_4807_: *mut leanh::LeanObject,
    mut v_s_4808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_vars_4809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_vars_4809_ = leanh::lean_ctor_get(v_s_4808_, 9);
    leanh::lean_inc_ref(v_vars_4809_);
    v_varMap_4810_ = leanh::lean_ctor_get(v_s_4808_, 10);
    leanh::lean_inc_ref(v_varMap_4810_);
    leanh::lean_dec_ref(v_s_4808_);
    leanh::lean_inc_ref(v_e_4802_);
    leanh::lean_inc_ref(v___f_4801_);
    leanh::lean_inc_ref(v___f_4800_);
    v___x_4811_ = l_Lean_PersistentHashMap_find_x3f___redArg(
        v___f_4800_,
        v___f_4801_,
        v_varMap_4810_,
        v_e_4802_,
    );
    leanh::lean_dec_ref(v_varMap_4810_);
    if leanh::lean_obj_tag(v___x_4811_) == 1 {
        let mut v_val_4812_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4813_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_vars_4809_);
        leanh::lean_dec(v_modifySemiring_4807_);
        leanh::lean_dec(v_inst_4806_);
        leanh::lean_dec(v_toBind_4805_);
        leanh::lean_dec(v_inst_4804_);
        leanh::lean_dec_ref(v_e_4802_);
        leanh::lean_dec_ref(v___f_4801_);
        leanh::lean_dec_ref(v___f_4800_);
        v_val_4812_ = leanh::lean_ctor_get(v___x_4811_, 0);
        leanh::lean_inc(v_val_4812_);
        leanh::lean_dec_ref_known(v___x_4811_, 1);
        v___x_4813_ =
            leanh::lean_apply_2(v_toPure_4803_, leanh::lean_box(0), v_val_4812_);
        return v___x_4813_;
    } else {
        let mut v_size_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4817_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4818_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4819_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4820_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_4811_);
        v_size_4814_ = leanh::lean_ctor_get(v_vars_4809_, 2);
        leanh::lean_inc_n(v_size_4814_, 2);
        leanh::lean_dec_ref(v_vars_4809_);
        leanh::lean_inc_ref_n(v_e_4802_, 2);
        v___f_4815_ = leanh::lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        leanh::lean_closure_set(v___f_4815_, 0, v_e_4802_);
        leanh::lean_closure_set(v___f_4815_, 1, v___f_4800_);
        leanh::lean_closure_set(v___f_4815_, 2, v___f_4801_);
        leanh::lean_closure_set(v___f_4815_, 3, v_size_4814_);
        v___f_4816_ = leanh::lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_4816_, 0, v_toPure_4803_);
        leanh::lean_closure_set(v___f_4816_, 1, v_size_4814_);
        leanh::lean_inc_n(v_toBind_4805_, 2);
        v___f_4817_ = leanh::lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__2 as *mut core::ffi::c_void,
            5,
            4,
        );
        leanh::lean_closure_set(v___f_4817_, 0, v_e_4802_);
        leanh::lean_closure_set(v___f_4817_, 1, v_inst_4804_);
        leanh::lean_closure_set(v___f_4817_, 2, v_toBind_4805_);
        leanh::lean_closure_set(v___f_4817_, 3, v___f_4816_);
        v___f_4818_ = leanh::lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__3 as *mut core::ffi::c_void,
            5,
            4,
        );
        leanh::lean_closure_set(v___f_4818_, 0, v_inst_4806_);
        leanh::lean_closure_set(v___f_4818_, 1, v_e_4802_);
        leanh::lean_closure_set(v___f_4818_, 2, v_toBind_4805_);
        leanh::lean_closure_set(v___f_4818_, 3, v___f_4817_);
        v___x_4819_ = leanh::lean_apply_1(v_modifySemiring_4807_, v___f_4815_);
        v___x_4820_ = leanh::lean_apply_4(
            v_toBind_4805_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_4819_,
            v___f_4818_,
        );
        return v___x_4820_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg(
    mut v_inst_4823_: *mut leanh::LeanObject,
    mut v_inst_4824_: *mut leanh::LeanObject,
    mut v_inst_4825_: *mut leanh::LeanObject,
    mut v_inst_4826_: *mut leanh::LeanObject,
    mut v_e_4827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getSemiring_4830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifySemiring_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4828_ = leanh::lean_ctor_get(v_inst_4824_, 0);
    leanh::lean_inc_ref(v_toApplicative_4828_);
    v_toBind_4829_ = leanh::lean_ctor_get(v_inst_4824_, 1);
    leanh::lean_inc_n(v_toBind_4829_, 2);
    leanh::lean_dec_ref(v_inst_4824_);
    v_getSemiring_4830_ = leanh::lean_ctor_get(v_inst_4825_, 0);
    leanh::lean_inc(v_getSemiring_4830_);
    v_modifySemiring_4831_ = leanh::lean_ctor_get(v_inst_4825_, 1);
    leanh::lean_inc(v_modifySemiring_4831_);
    leanh::lean_dec_ref(v_inst_4825_);
    v_toPure_4832_ = leanh::lean_ctor_get(v_toApplicative_4828_, 1);
    leanh::lean_inc(v_toPure_4832_);
    leanh::lean_dec_ref(v_toApplicative_4828_);
    v___f_4833_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__0;
    v___f_4834_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___closed__1;
    v___f_4835_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___redArg___lam__4 as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___f_4835_, 0, v___f_4833_);
    leanh::lean_closure_set(v___f_4835_, 1, v___f_4834_);
    leanh::lean_closure_set(v___f_4835_, 2, v_e_4827_);
    leanh::lean_closure_set(v___f_4835_, 3, v_toPure_4832_);
    leanh::lean_closure_set(v___f_4835_, 4, v_inst_4823_);
    leanh::lean_closure_set(v___f_4835_, 5, v_toBind_4829_);
    leanh::lean_closure_set(v___f_4835_, 6, v_inst_4826_);
    leanh::lean_closure_set(v___f_4835_, 7, v_modifySemiring_4831_);
    v___x_4836_ = leanh::lean_apply_4(
        v_toBind_4829_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getSemiring_4830_,
        v___f_4835_,
    );
    return v___x_4836_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore(
    mut v_m_4837_: *mut leanh::LeanObject,
    mut v_inst_4838_: *mut leanh::LeanObject,
    mut v_inst_4839_: *mut leanh::LeanObject,
    mut v_inst_4840_: *mut leanh::LeanObject,
    mut v_inst_4841_: *mut leanh::LeanObject,
    mut v_e_4842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v___y_4844_: *mut leanh::LeanObject,
    mut v_e_4845_: *mut leanh::LeanObject,
    mut v_size_4846_: *mut leanh::LeanObject,
    mut v_s_4847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_rings_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_4849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_4852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_4853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_4855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_4856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_4857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_4858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_4859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_4861_: u8 = 0;
    let mut v___x_4862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: u8 = 0;
    let mut v___x_4865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4866_: u8 = 0;
    let mut v_v_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSemiring_4868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringId_4869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addRightCancelInst_x3f_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toQFn_x3f_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4875_: u8 = 0;
    let mut v_id_4876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_4878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_4879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_4881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_4882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_4885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_4886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4889_: u8 = 0;
    let mut v___x_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4904_: u8 = 0;
    let mut v_isSharedCheck_4905_: u8 = 0;
    let mut v_isSharedCheck_4906_: u8 = 0;
    let mut v_unused_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_4848_ = leanh::lean_ctor_get(v_s_4847_, 0);
                v_typeIdOf_4849_ = leanh::lean_ctor_get(v_s_4847_, 1);
                v_exprToRingId_4850_ = leanh::lean_ctor_get(v_s_4847_, 2);
                v_semirings_4851_ = leanh::lean_ctor_get(v_s_4847_, 3);
                v_stypeIdOf_4852_ = leanh::lean_ctor_get(v_s_4847_, 4);
                v_exprToSemiringId_4853_ = leanh::lean_ctor_get(v_s_4847_, 5);
                v_ncRings_4854_ = leanh::lean_ctor_get(v_s_4847_, 6);
                v_exprToNCRingId_4855_ = leanh::lean_ctor_get(v_s_4847_, 7);
                v_nctypeIdOf_4856_ = leanh::lean_ctor_get(v_s_4847_, 8);
                v_ncSemirings_4857_ = leanh::lean_ctor_get(v_s_4847_, 9);
                v_exprToNCSemiringId_4858_ = leanh::lean_ctor_get(v_s_4847_, 10);
                v_ncstypeIdOf_4859_ = leanh::lean_ctor_get(v_s_4847_, 11);
                v_steps_4860_ = leanh::lean_ctor_get(v_s_4847_, 12);
                v_reportedMaxDegreeIssue_4861_ = leanh::lean_ctor_get_uint8(
                    v_s_4847_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
                );
                v___x_4862_ = lean_array_get_size(v_semirings_4851_);
                v___x_4863_ = lean_nat_dec_lt(v___y_4844_, v___x_4862_);
                if v___x_4863_ == 0 {
                    leanh::lean_dec(v_size_4846_);
                    leanh::lean_dec_ref(v_e_4845_);
                    return v_s_4847_;
                } else {
                    leanh::lean_inc(v_steps_4860_);
                    leanh::lean_inc_ref(v_ncstypeIdOf_4859_);
                    leanh::lean_inc_ref(v_exprToNCSemiringId_4858_);
                    leanh::lean_inc_ref(v_ncSemirings_4857_);
                    leanh::lean_inc_ref(v_nctypeIdOf_4856_);
                    leanh::lean_inc_ref(v_exprToNCRingId_4855_);
                    leanh::lean_inc_ref(v_ncRings_4854_);
                    leanh::lean_inc_ref(v_exprToSemiringId_4853_);
                    leanh::lean_inc_ref(v_stypeIdOf_4852_);
                    leanh::lean_inc_ref(v_semirings_4851_);
                    leanh::lean_inc_ref(v_exprToRingId_4850_);
                    leanh::lean_inc_ref(v_typeIdOf_4849_);
                    leanh::lean_inc_ref(v_rings_4848_);
                    v_isSharedCheck_4906_ = (!leanh::lean_is_exclusive(v_s_4847_)) as u8;
                    if v_isSharedCheck_4906_ == 0 {
                        v_unused_4907_ = leanh::lean_ctor_get(v_s_4847_, 12);
                        leanh::lean_dec(v_unused_4907_);
                        v_unused_4908_ = leanh::lean_ctor_get(v_s_4847_, 11);
                        leanh::lean_dec(v_unused_4908_);
                        v_unused_4909_ = leanh::lean_ctor_get(v_s_4847_, 10);
                        leanh::lean_dec(v_unused_4909_);
                        v_unused_4910_ = leanh::lean_ctor_get(v_s_4847_, 9);
                        leanh::lean_dec(v_unused_4910_);
                        v_unused_4911_ = leanh::lean_ctor_get(v_s_4847_, 8);
                        leanh::lean_dec(v_unused_4911_);
                        v_unused_4912_ = leanh::lean_ctor_get(v_s_4847_, 7);
                        leanh::lean_dec(v_unused_4912_);
                        v_unused_4913_ = leanh::lean_ctor_get(v_s_4847_, 6);
                        leanh::lean_dec(v_unused_4913_);
                        v_unused_4914_ = leanh::lean_ctor_get(v_s_4847_, 5);
                        leanh::lean_dec(v_unused_4914_);
                        v_unused_4915_ = leanh::lean_ctor_get(v_s_4847_, 4);
                        leanh::lean_dec(v_unused_4915_);
                        v_unused_4916_ = leanh::lean_ctor_get(v_s_4847_, 3);
                        leanh::lean_dec(v_unused_4916_);
                        v_unused_4917_ = leanh::lean_ctor_get(v_s_4847_, 2);
                        leanh::lean_dec(v_unused_4917_);
                        v_unused_4918_ = leanh::lean_ctor_get(v_s_4847_, 1);
                        leanh::lean_dec(v_unused_4918_);
                        v_unused_4919_ = leanh::lean_ctor_get(v_s_4847_, 0);
                        leanh::lean_dec(v_unused_4919_);
                        v___x_4865_ = v_s_4847_;
                        v_isShared_4866_ = v_isSharedCheck_4906_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_s_4847_);
                        v___x_4865_ = leanh::lean_box(0);
                        v_isShared_4866_ = v_isSharedCheck_4906_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4867_ = lean_array_fget(v_semirings_4851_, v___y_4844_);
                v_toSemiring_4868_ = leanh::lean_ctor_get(v_v_4867_, 0);
                v_ringId_4869_ = leanh::lean_ctor_get(v_v_4867_, 1);
                v_commSemiringInst_4870_ = leanh::lean_ctor_get(v_v_4867_, 2);
                v_addRightCancelInst_x3f_4871_ = leanh::lean_ctor_get(v_v_4867_, 3);
                v_toQFn_x3f_4872_ = leanh::lean_ctor_get(v_v_4867_, 4);
                v_isSharedCheck_4905_ = (!leanh::lean_is_exclusive(v_v_4867_)) as u8;
                if v_isSharedCheck_4905_ == 0 {
                    v___x_4874_ = v_v_4867_;
                    v_isShared_4875_ = v_isSharedCheck_4905_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toQFn_x3f_4872_);
                    leanh::lean_inc(v_addRightCancelInst_x3f_4871_);
                    leanh::lean_inc(v_commSemiringInst_4870_);
                    leanh::lean_inc(v_ringId_4869_);
                    leanh::lean_inc(v_toSemiring_4868_);
                    leanh::lean_dec(v_v_4867_);
                    v___x_4874_ = leanh::lean_box(0);
                    v_isShared_4875_ = v_isSharedCheck_4905_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_id_4876_ = leanh::lean_ctor_get(v_toSemiring_4868_, 0);
                v_type_4877_ = leanh::lean_ctor_get(v_toSemiring_4868_, 1);
                v_u_4878_ = leanh::lean_ctor_get(v_toSemiring_4868_, 2);
                v_semiringInst_4879_ = leanh::lean_ctor_get(v_toSemiring_4868_, 3);
                v_addFn_x3f_4880_ = leanh::lean_ctor_get(v_toSemiring_4868_, 4);
                v_mulFn_x3f_4881_ = leanh::lean_ctor_get(v_toSemiring_4868_, 5);
                v_powFn_x3f_4882_ = leanh::lean_ctor_get(v_toSemiring_4868_, 6);
                v_natCastFn_x3f_4883_ = leanh::lean_ctor_get(v_toSemiring_4868_, 7);
                v_denote_4884_ = leanh::lean_ctor_get(v_toSemiring_4868_, 8);
                v_vars_4885_ = leanh::lean_ctor_get(v_toSemiring_4868_, 9);
                v_varMap_4886_ = leanh::lean_ctor_get(v_toSemiring_4868_, 10);
                v_isSharedCheck_4904_ =
                    (!leanh::lean_is_exclusive(v_toSemiring_4868_)) as u8;
                if v_isSharedCheck_4904_ == 0 {
                    v___x_4888_ = v_toSemiring_4868_;
                    v_isShared_4889_ = v_isSharedCheck_4904_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_varMap_4886_);
                    leanh::lean_inc(v_vars_4885_);
                    leanh::lean_inc(v_denote_4884_);
                    leanh::lean_inc(v_natCastFn_x3f_4883_);
                    leanh::lean_inc(v_powFn_x3f_4882_);
                    leanh::lean_inc(v_mulFn_x3f_4881_);
                    leanh::lean_inc(v_addFn_x3f_4880_);
                    leanh::lean_inc(v_semiringInst_4879_);
                    leanh::lean_inc(v_u_4878_);
                    leanh::lean_inc(v_type_4877_);
                    leanh::lean_inc(v_id_4876_);
                    leanh::lean_dec(v_toSemiring_4868_);
                    v___x_4888_ = leanh::lean_box(0);
                    v_isShared_4889_ = v_isSharedCheck_4904_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4890_ = leanh::lean_box(0);
                v_xs_x27_4891_ = lean_array_fset(v_semirings_4851_, v___y_4844_, v___x_4890_);
                leanh::lean_inc_ref(v_e_4845_);
                v___x_4892_ = l_Lean_PersistentArray_push___redArg(v_vars_4885_, v_e_4845_);
                v___x_4893_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermSemiringId_spec__0___redArg(v_varMap_4886_, v_e_4845_, v_size_4846_);
                if v_isShared_4889_ == 0 {
                    leanh::lean_ctor_set(v___x_4888_, 10, v___x_4893_);
                    leanh::lean_ctor_set(v___x_4888_, 9, v___x_4892_);
                    v___x_4895_ = v___x_4888_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4903_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_id_4876_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4903_, 1, v_type_4877_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4903_, 2, v_u_4878_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4903_, 3, v_semiringInst_4879_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4903_, 4, v_addFn_x3f_4880_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4903_, 5, v_mulFn_x3f_4881_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4903_, 6, v_powFn_x3f_4882_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4903_, 7, v_natCastFn_x3f_4883_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4903_, 8, v_denote_4884_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4903_, 9, v___x_4892_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4903_, 10, v___x_4893_);
                    v___x_4895_ = v_reuseFailAlloc_4903_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4875_ == 0 {
                    leanh::lean_ctor_set(v___x_4874_, 0, v___x_4895_);
                    v___x_4897_ = v___x_4874_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4902_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4902_, 0, v___x_4895_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4902_, 1, v_ringId_4869_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4902_,
                        2,
                        v_commSemiringInst_4870_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4902_,
                        3,
                        v_addRightCancelInst_x3f_4871_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4902_, 4, v_toQFn_x3f_4872_);
                    v___x_4897_ = v_reuseFailAlloc_4902_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4898_ = lean_array_fset(v_xs_x27_4891_, v___y_4844_, v___x_4897_);
                if v_isShared_4866_ == 0 {
                    leanh::lean_ctor_set(v___x_4865_, 3, v___x_4898_);
                    v___x_4900_ = v___x_4865_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4901_ = leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4901_, 0, v_rings_4848_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4901_, 1, v_typeIdOf_4849_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4901_, 2, v_exprToRingId_4850_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4901_, 3, v___x_4898_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4901_, 4, v_stypeIdOf_4852_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4901_,
                        5,
                        v_exprToSemiringId_4853_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4901_, 6, v_ncRings_4854_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4901_, 7, v_exprToNCRingId_4855_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4901_, 8, v_nctypeIdOf_4856_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4901_, 9, v_ncSemirings_4857_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4901_,
                        10,
                        v_exprToNCSemiringId_4858_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4901_, 11, v_ncstypeIdOf_4859_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4901_, 12, v_steps_4860_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4901_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 13) as u32,
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
    mut v___y_4920_: *mut leanh::LeanObject,
    mut v_e_4921_: *mut leanh::LeanObject,
    mut v_size_4922_: *mut leanh::LeanObject,
    mut v_s_4923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4924_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0(v___y_4920_, v_e_4921_, v_size_4922_, v_s_4923_);
    leanh::lean_dec(v___y_4920_);
    return v_res_4924_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(
    mut v_e_4925_: *mut leanh::LeanObject,
    mut v___y_4926_: *mut leanh::LeanObject,
    mut v___y_4927_: *mut leanh::LeanObject,
    mut v___y_4928_: *mut leanh::LeanObject,
    mut v___y_4929_: *mut leanh::LeanObject,
    mut v___y_4930_: *mut leanh::LeanObject,
    mut v___y_4931_: *mut leanh::LeanObject,
    mut v___y_4932_: *mut leanh::LeanObject,
    mut v___y_4933_: *mut leanh::LeanObject,
    mut v___y_4934_: *mut leanh::LeanObject,
    mut v___y_4935_: *mut leanh::LeanObject,
    mut v___y_4936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4942_: u8 = 0;
    let mut v_toSemiring_4943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_4944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_4945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4959_: u8 = 0;
    let mut v___x_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4963_: u8 = 0;
    let mut v_unused_4964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4968_: u8 = 0;
    let mut v___x_4970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4972_: u8 = 0;
    let mut v_a_4973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4976_: u8 = 0;
    let mut v___x_4978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4980_: u8 = 0;
    let mut v_a_4981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4984_: u8 = 0;
    let mut v___x_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4988_: u8 = 0;
    let mut v_isSharedCheck_4989_: u8 = 0;
    let mut v_a_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4993_: u8 = 0;
    let mut v___x_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_4938_) == 0 {
                    v_a_4939_ = leanh::lean_ctor_get(v___x_4938_, 0);
                    v_isSharedCheck_4989_ = (!leanh::lean_is_exclusive(v___x_4938_)) as u8;
                    if v_isSharedCheck_4989_ == 0 {
                        v___x_4941_ = v___x_4938_;
                        v_isShared_4942_ = v_isSharedCheck_4989_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4939_);
                        leanh::lean_dec(v___x_4938_);
                        v___x_4941_ = leanh::lean_box(0);
                        v_isShared_4942_ = v_isSharedCheck_4989_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_4925_);
                    v_a_4990_ = leanh::lean_ctor_get(v___x_4938_, 0);
                    v_isSharedCheck_4997_ = (!leanh::lean_is_exclusive(v___x_4938_)) as u8;
                    if v_isSharedCheck_4997_ == 0 {
                        v___x_4992_ = v___x_4938_;
                        v_isShared_4993_ = v_isSharedCheck_4997_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4990_);
                        leanh::lean_dec(v___x_4938_);
                        v___x_4992_ = leanh::lean_box(0);
                        v_isShared_4993_ = v_isSharedCheck_4997_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v_toSemiring_4943_ = leanh::lean_ctor_get(v_a_4939_, 0);
                leanh::lean_inc_ref(v_toSemiring_4943_);
                leanh::lean_dec(v_a_4939_);
                v_vars_4944_ = leanh::lean_ctor_get(v_toSemiring_4943_, 9);
                leanh::lean_inc_ref(v_vars_4944_);
                v_varMap_4945_ = leanh::lean_ctor_get(v_toSemiring_4943_, 10);
                leanh::lean_inc_ref(v_varMap_4945_);
                leanh::lean_dec_ref(v_toSemiring_4943_);
                v___x_4946_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermSemiringId_x3f_spec__0___redArg(v_varMap_4945_, v_e_4925_);
                leanh::lean_dec_ref(v_varMap_4945_);
                if leanh::lean_obj_tag(v___x_4946_) == 1 {
                    leanh::lean_dec_ref(v_vars_4944_);
                    leanh::lean_dec_ref(v_e_4925_);
                    v_val_4947_ = leanh::lean_ctor_get(v___x_4946_, 0);
                    leanh::lean_inc(v_val_4947_);
                    leanh::lean_dec_ref_known(v___x_4946_, 1);
                    if v_isShared_4942_ == 0 {
                        leanh::lean_ctor_set(v___x_4941_, 0, v_val_4947_);
                        v___x_4949_ = v___x_4941_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4950_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4950_, 0, v_val_4947_);
                        v___x_4949_ = v_reuseFailAlloc_4950_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_4946_);
                    leanh::lean_del_object(v___x_4941_);
                    v_size_4951_ = leanh::lean_ctor_get(v_vars_4944_, 2);
                    leanh::lean_inc_n(v_size_4951_, 2);
                    leanh::lean_dec_ref(v_vars_4944_);
                    leanh::lean_inc_ref(v_e_4925_);
                    leanh::lean_inc(v___y_4926_);
                    v___f_4952_ = leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0___lam__0___boxed as *mut core::ffi::c_void, 4, 3);
                    leanh::lean_closure_set(v___f_4952_, 0, v___y_4926_);
                    leanh::lean_closure_set(v___f_4952_, 1, v_e_4925_);
                    leanh::lean_closure_set(v___f_4952_, 2, v_size_4951_);
                    v___x_4953_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                    v___x_4954_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4953_, v___f_4952_, v___y_4927_);
                    if leanh::lean_obj_tag(v___x_4954_) == 0 {
                        leanh::lean_dec_ref_known(v___x_4954_, 1);
                        leanh::lean_inc_ref(v_e_4925_);
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
                        if leanh::lean_obj_tag(v___x_4955_) == 0 {
                            leanh::lean_dec_ref_known(v___x_4955_, 1);
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
                            if leanh::lean_obj_tag(v___x_4956_) == 0 {
                                v_isSharedCheck_4963_ =
                                    (!leanh::lean_is_exclusive(v___x_4956_)) as u8;
                                if v_isSharedCheck_4963_ == 0 {
                                    v_unused_4964_ = leanh::lean_ctor_get(v___x_4956_, 0);
                                    leanh::lean_dec(v_unused_4964_);
                                    v___x_4958_ = v___x_4956_;
                                    v_isShared_4959_ = v_isSharedCheck_4963_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_dec(v___x_4956_);
                                    v___x_4958_ = leanh::lean_box(0);
                                    v_isShared_4959_ = v_isSharedCheck_4963_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_size_4951_);
                                v_a_4965_ = leanh::lean_ctor_get(v___x_4956_, 0);
                                v_isSharedCheck_4972_ =
                                    (!leanh::lean_is_exclusive(v___x_4956_)) as u8;
                                if v_isSharedCheck_4972_ == 0 {
                                    v___x_4967_ = v___x_4956_;
                                    v_isShared_4968_ = v_isSharedCheck_4972_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4965_);
                                    leanh::lean_dec(v___x_4956_);
                                    v___x_4967_ = leanh::lean_box(0);
                                    v_isShared_4968_ = v_isSharedCheck_4972_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_size_4951_);
                            leanh::lean_dec_ref(v_e_4925_);
                            v_a_4973_ = leanh::lean_ctor_get(v___x_4955_, 0);
                            v_isSharedCheck_4980_ =
                                (!leanh::lean_is_exclusive(v___x_4955_)) as u8;
                            if v_isSharedCheck_4980_ == 0 {
                                v___x_4975_ = v___x_4955_;
                                v_isShared_4976_ = v_isSharedCheck_4980_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4973_);
                                leanh::lean_dec(v___x_4955_);
                                v___x_4975_ = leanh::lean_box(0);
                                v_isShared_4976_ = v_isSharedCheck_4980_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_size_4951_);
                        leanh::lean_dec_ref(v_e_4925_);
                        v_a_4981_ = leanh::lean_ctor_get(v___x_4954_, 0);
                        v_isSharedCheck_4988_ =
                            (!leanh::lean_is_exclusive(v___x_4954_)) as u8;
                        if v_isSharedCheck_4988_ == 0 {
                            v___x_4983_ = v___x_4954_;
                            v_isShared_4984_ = v_isSharedCheck_4988_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4981_);
                            leanh::lean_dec(v___x_4954_);
                            v___x_4983_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_4958_, 0, v_size_4951_);
                    v___x_4961_ = v___x_4958_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4962_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4962_, 0, v_size_4951_);
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
                    v_reuseFailAlloc_4971_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4971_, 0, v_a_4965_);
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
                    v_reuseFailAlloc_4979_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4979_, 0, v_a_4973_);
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
                    v_reuseFailAlloc_4987_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4987_, 0, v_a_4981_);
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
                    v_reuseFailAlloc_4996_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4996_, 0, v_a_4990_);
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
    mut v_e_4998_: *mut leanh::LeanObject,
    mut v___y_4999_: *mut leanh::LeanObject,
    mut v___y_5000_: *mut leanh::LeanObject,
    mut v___y_5001_: *mut leanh::LeanObject,
    mut v___y_5002_: *mut leanh::LeanObject,
    mut v___y_5003_: *mut leanh::LeanObject,
    mut v___y_5004_: *mut leanh::LeanObject,
    mut v___y_5005_: *mut leanh::LeanObject,
    mut v___y_5006_: *mut leanh::LeanObject,
    mut v___y_5007_: *mut leanh::LeanObject,
    mut v___y_5008_: *mut leanh::LeanObject,
    mut v___y_5009_: *mut leanh::LeanObject,
    mut v___y_5010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5011_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(v_e_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_);
    leanh::lean_dec(v___y_5009_);
    leanh::lean_dec_ref(v___y_5008_);
    leanh::lean_dec(v___y_5007_);
    leanh::lean_dec_ref(v___y_5006_);
    leanh::lean_dec(v___y_5005_);
    leanh::lean_dec_ref(v___y_5004_);
    leanh::lean_dec(v___y_5003_);
    leanh::lean_dec_ref(v___y_5002_);
    leanh::lean_dec(v___y_5001_);
    leanh::lean_dec(v___y_5000_);
    leanh::lean_dec(v___y_4999_);
    return v_res_5011_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkSVar(
    mut v_e_5012_: *mut leanh::LeanObject,
    mut v_a_5013_: *mut leanh::LeanObject,
    mut v_a_5014_: *mut leanh::LeanObject,
    mut v_a_5015_: *mut leanh::LeanObject,
    mut v_a_5016_: *mut leanh::LeanObject,
    mut v_a_5017_: *mut leanh::LeanObject,
    mut v_a_5018_: *mut leanh::LeanObject,
    mut v_a_5019_: *mut leanh::LeanObject,
    mut v_a_5020_: *mut leanh::LeanObject,
    mut v_a_5021_: *mut leanh::LeanObject,
    mut v_a_5022_: *mut leanh::LeanObject,
    mut v_a_5023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5025_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkSVar_spec__0(v_e_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_);
    return v___x_5025_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkSVar___boxed(
    mut v_e_5026_: *mut leanh::LeanObject,
    mut v_a_5027_: *mut leanh::LeanObject,
    mut v_a_5028_: *mut leanh::LeanObject,
    mut v_a_5029_: *mut leanh::LeanObject,
    mut v_a_5030_: *mut leanh::LeanObject,
    mut v_a_5031_: *mut leanh::LeanObject,
    mut v_a_5032_: *mut leanh::LeanObject,
    mut v_a_5033_: *mut leanh::LeanObject,
    mut v_a_5034_: *mut leanh::LeanObject,
    mut v_a_5035_: *mut leanh::LeanObject,
    mut v_a_5036_: *mut leanh::LeanObject,
    mut v_a_5037_: *mut leanh::LeanObject,
    mut v_a_5038_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5039_ = l_Lean_Meta_Grind_Arith_CommRing_mkSVar(
        v_e_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_,
        v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_,
    );
    leanh::lean_dec(v_a_5037_);
    leanh::lean_dec_ref(v_a_5036_);
    leanh::lean_dec(v_a_5035_);
    leanh::lean_dec_ref(v_a_5034_);
    leanh::lean_dec(v_a_5033_);
    leanh::lean_dec_ref(v_a_5032_);
    leanh::lean_dec(v_a_5031_);
    leanh::lean_dec_ref(v_a_5030_);
    leanh::lean_dec(v_a_5029_);
    leanh::lean_dec(v_a_5028_);
    leanh::lean_dec(v_a_5027_);
    return v_res_5039_;
}
pub unsafe fn l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__1(
    mut v_a_5040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5041_ = lean_nat_to_int(v_a_5040_);
    return v___x_5041_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5042_ = l_Lean_Meta_Grind_instInhabitedGoalM(leanh::lean_box(0));
    return v___x_5042_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(
    mut v_msg_5043_: *mut leanh::LeanObject,
    mut v___y_5044_: *mut leanh::LeanObject,
    mut v___y_5045_: *mut leanh::LeanObject,
    mut v___y_5046_: *mut leanh::LeanObject,
    mut v___y_5047_: *mut leanh::LeanObject,
    mut v___y_5048_: *mut leanh::LeanObject,
    mut v___y_5049_: *mut leanh::LeanObject,
    mut v___y_5050_: *mut leanh::LeanObject,
    mut v___y_5051_: *mut leanh::LeanObject,
    mut v___y_5052_: *mut leanh::LeanObject,
    mut v___y_5053_: *mut leanh::LeanObject,
    mut v___y_5054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_40218__overap_5058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5056_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___closed__0);
    v___f_5057_ = leanh::lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_5057_, 0, v___x_5056_);
    v___x_40218__overap_5058_ = lean_panic_fn_borrowed(v___f_5057_, v_msg_5043_);
    leanh::lean_dec_ref(v___f_5057_);
    leanh::lean_inc(v___y_5054_);
    leanh::lean_inc_ref(v___y_5053_);
    leanh::lean_inc(v___y_5052_);
    leanh::lean_inc_ref(v___y_5051_);
    leanh::lean_inc(v___y_5050_);
    leanh::lean_inc_ref(v___y_5049_);
    leanh::lean_inc(v___y_5048_);
    leanh::lean_inc_ref(v___y_5047_);
    leanh::lean_inc(v___y_5046_);
    leanh::lean_inc(v___y_5045_);
    leanh::lean_inc(v___y_5044_);
    v___x_5059_ = leanh::lean_apply_12(
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
        leanh::lean_box(0),
    );
    return v___x_5059_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5___boxed(
    mut v_msg_5060_: *mut leanh::LeanObject,
    mut v___y_5061_: *mut leanh::LeanObject,
    mut v___y_5062_: *mut leanh::LeanObject,
    mut v___y_5063_: *mut leanh::LeanObject,
    mut v___y_5064_: *mut leanh::LeanObject,
    mut v___y_5065_: *mut leanh::LeanObject,
    mut v___y_5066_: *mut leanh::LeanObject,
    mut v___y_5067_: *mut leanh::LeanObject,
    mut v___y_5068_: *mut leanh::LeanObject,
    mut v___y_5069_: *mut leanh::LeanObject,
    mut v___y_5070_: *mut leanh::LeanObject,
    mut v___y_5071_: *mut leanh::LeanObject,
    mut v___y_5072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5073_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(v_msg_5060_, v___y_5061_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_, v___y_5069_, v___y_5070_, v___y_5071_);
    leanh::lean_dec(v___y_5071_);
    leanh::lean_dec_ref(v___y_5070_);
    leanh::lean_dec(v___y_5069_);
    leanh::lean_dec_ref(v___y_5068_);
    leanh::lean_dec(v___y_5067_);
    leanh::lean_dec_ref(v___y_5066_);
    leanh::lean_dec(v___y_5065_);
    leanh::lean_dec_ref(v___y_5064_);
    leanh::lean_dec(v___y_5063_);
    leanh::lean_dec(v___y_5062_);
    leanh::lean_dec(v___y_5061_);
    return v_res_5073_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5075_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__0;
    v___x_5076_ = l_Lean_stringToMessageData(v___x_5075_);
    return v___x_5076_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(
    mut v_type_5077_: *mut leanh::LeanObject,
    mut v___y_5078_: *mut leanh::LeanObject,
    mut v___y_5079_: *mut leanh::LeanObject,
    mut v___y_5080_: *mut leanh::LeanObject,
    mut v___y_5081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5087_: u8 = 0;
    let mut v_val_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5096_: u8 = 0;
    let mut v_a_5097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5100_: u8 = 0;
    let mut v___x_5102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5104_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_type_5077_);
                v___x_5083_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                    v_type_5077_,
                    v___y_5078_,
                    v___y_5079_,
                    v___y_5080_,
                    v___y_5081_,
                );
                if leanh::lean_obj_tag(v___x_5083_) == 0 {
                    v_a_5084_ = leanh::lean_ctor_get(v___x_5083_, 0);
                    v_isSharedCheck_5096_ = (!leanh::lean_is_exclusive(v___x_5083_)) as u8;
                    if v_isSharedCheck_5096_ == 0 {
                        v___x_5086_ = v___x_5083_;
                        v_isShared_5087_ = v_isSharedCheck_5096_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5084_);
                        leanh::lean_dec(v___x_5083_);
                        v___x_5086_ = leanh::lean_box(0);
                        v_isShared_5087_ = v_isSharedCheck_5096_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_type_5077_);
                    v_a_5097_ = leanh::lean_ctor_get(v___x_5083_, 0);
                    v_isSharedCheck_5104_ = (!leanh::lean_is_exclusive(v___x_5083_)) as u8;
                    if v_isSharedCheck_5104_ == 0 {
                        v___x_5099_ = v___x_5083_;
                        v_isShared_5100_ = v_isSharedCheck_5104_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5097_);
                        leanh::lean_dec(v___x_5083_);
                        v___x_5099_ = leanh::lean_box(0);
                        v_isShared_5100_ = v_isSharedCheck_5104_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_5084_) == 1 {
                    leanh::lean_dec_ref(v_type_5077_);
                    v_val_5088_ = leanh::lean_ctor_get(v_a_5084_, 0);
                    leanh::lean_inc(v_val_5088_);
                    leanh::lean_dec_ref_known(v_a_5084_, 1);
                    if v_isShared_5087_ == 0 {
                        leanh::lean_ctor_set(v___x_5086_, 0, v_val_5088_);
                        v___x_5090_ = v___x_5086_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5091_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5091_, 0, v_val_5088_);
                        v___x_5090_ = v_reuseFailAlloc_5091_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5086_);
                    leanh::lean_dec(v_a_5084_);
                    v___x_5092_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1_once), _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg___closed__1);
                    v___x_5093_ = l_Lean_indentExpr(v_type_5077_);
                    v___x_5094_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5094_, 0, v___x_5092_);
                    leanh::lean_ctor_set(v___x_5094_, 1, v___x_5093_);
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
                    v_reuseFailAlloc_5103_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5103_, 0, v_a_5097_);
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
    mut v_type_5105_: *mut leanh::LeanObject,
    mut v___y_5106_: *mut leanh::LeanObject,
    mut v___y_5107_: *mut leanh::LeanObject,
    mut v___y_5108_: *mut leanh::LeanObject,
    mut v___y_5109_: *mut leanh::LeanObject,
    mut v___y_5110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5111_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v_type_5105_, v___y_5106_, v___y_5107_, v___y_5108_, v___y_5109_);
    leanh::lean_dec(v___y_5109_);
    leanh::lean_dec_ref(v___y_5108_);
    leanh::lean_dec(v___y_5107_);
    leanh::lean_dec_ref(v___y_5106_);
    return v_res_5111_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(
    mut v_type_5112_: *mut leanh::LeanObject,
    mut v_u_5113_: *mut leanh::LeanObject,
    mut v_instDeclName_5114_: *mut leanh::LeanObject,
    mut v_declName_5115_: *mut leanh::LeanObject,
    mut v_expectedInst_5116_: *mut leanh::LeanObject,
    mut v___y_5117_: *mut leanh::LeanObject,
    mut v___y_5118_: *mut leanh::LeanObject,
    mut v___y_5119_: *mut leanh::LeanObject,
    mut v___y_5120_: *mut leanh::LeanObject,
    mut v___y_5121_: *mut leanh::LeanObject,
    mut v___y_5122_: *mut leanh::LeanObject,
    mut v___y_5123_: *mut leanh::LeanObject,
    mut v___y_5124_: *mut leanh::LeanObject,
    mut v___y_5125_: *mut leanh::LeanObject,
    mut v___y_5126_: *mut leanh::LeanObject,
    mut v___y_5127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5146_: u8 = 0;
    let mut v___x_5148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5150_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5129_ = leanh::lean_box(0);
                leanh::lean_inc_n(v_u_5113_, 2);
                v___x_5130_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5130_, 0, v_u_5113_);
                leanh::lean_ctor_set(v___x_5130_, 1, v___x_5129_);
                v___x_5131_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5131_, 0, v_u_5113_);
                leanh::lean_ctor_set(v___x_5131_, 1, v___x_5130_);
                v___x_5132_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5132_, 0, v_u_5113_);
                leanh::lean_ctor_set(v___x_5132_, 1, v___x_5131_);
                leanh::lean_inc_ref(v___x_5132_);
                v___x_5133_ = l_Lean_mkConst(v_instDeclName_5114_, v___x_5132_);
                leanh::lean_inc_ref_n(v_type_5112_, 3);
                v___x_5134_ = l_Lean_mkApp3(v___x_5133_, v_type_5112_, v_type_5112_, v_type_5112_);
                v___x_5135_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_5134_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_);
                if leanh::lean_obj_tag(v___x_5135_) == 0 {
                    v_a_5136_ = leanh::lean_ctor_get(v___x_5135_, 0);
                    leanh::lean_inc_n(v_a_5136_, 2);
                    leanh::lean_dec_ref_known(v___x_5135_, 1);
                    leanh::lean_inc(v_declName_5115_);
                    v___x_5137_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(
                        v_declName_5115_,
                        v_a_5136_,
                        v_expectedInst_5116_,
                        v___y_5124_,
                        v___y_5125_,
                        v___y_5126_,
                        v___y_5127_,
                    );
                    if leanh::lean_obj_tag(v___x_5137_) == 0 {
                        leanh::lean_dec_ref_known(v___x_5137_, 1);
                        v___x_5138_ = l_Lean_mkConst(v_declName_5115_, v___x_5132_);
                        leanh::lean_inc_ref_n(v_type_5112_, 2);
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
                        if leanh::lean_obj_tag(v___x_5140_) == 0 {
                            v_a_5141_ = leanh::lean_ctor_get(v___x_5140_, 0);
                            leanh::lean_inc(v_a_5141_);
                            leanh::lean_dec_ref_known(v___x_5140_, 1);
                            v___x_5142_ =
                                l_Lean_Meta_Sym_shareCommon___redArg(v_a_5141_, v___y_5123_);
                            return v___x_5142_;
                        } else {
                            return v___x_5140_;
                        }
                    } else {
                        leanh::lean_dec(v_a_5136_);
                        leanh::lean_dec_ref_known(v___x_5132_, 2);
                        leanh::lean_dec(v_declName_5115_);
                        leanh::lean_dec_ref(v_type_5112_);
                        v_a_5143_ = leanh::lean_ctor_get(v___x_5137_, 0);
                        v_isSharedCheck_5150_ =
                            (!leanh::lean_is_exclusive(v___x_5137_)) as u8;
                        if v_isSharedCheck_5150_ == 0 {
                            v___x_5145_ = v___x_5137_;
                            v_isShared_5146_ = v_isSharedCheck_5150_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5143_);
                            leanh::lean_dec(v___x_5137_);
                            v___x_5145_ = leanh::lean_box(0);
                            v_isShared_5146_ = v_isSharedCheck_5150_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_5132_, 2);
                    leanh::lean_dec_ref(v_expectedInst_5116_);
                    leanh::lean_dec(v_declName_5115_);
                    leanh::lean_dec_ref(v_type_5112_);
                    return v___x_5135_;
                }
            }
            1 => {
                if v_isShared_5146_ == 0 {
                    v___x_5148_ = v___x_5145_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5149_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5149_, 0, v_a_5143_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_type_5151_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_u_5152_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_instDeclName_5153_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_declName_5154_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_expectedInst_5155_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___y_5156_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_5157_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_5158_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_5159_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_5160_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_5161_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_5162_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_5163_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_5164_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_5165_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_5166_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_5167_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_res_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5168_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3(v_type_5151_, v_u_5152_, v_instDeclName_5153_, v_declName_5154_, v_expectedInst_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_, v___y_5165_, v___y_5166_);
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
    leanh::lean_dec(v___y_5156_);
    return v_res_5168_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___lam__0(
    mut v_a_5169_: *mut leanh::LeanObject,
    mut v_s_5170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toRing_5171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_5172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_5173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_5174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_5176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_5178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_5181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_5182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_5184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recheck_5185_: u8 = 0;
    let mut v_invSet_5186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_5187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_5188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_5189_: u8 = 0;
    let mut v___x_5191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5192_: u8 = 0;
    let mut v_id_5193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_5196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_5197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_5199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_5200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_5201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_5202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_5203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_5205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_5206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_5207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_5208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5211_: u8 = 0;
    let mut v___x_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5219_: u8 = 0;
    let mut v_unused_5220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5221_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_5171_ = leanh::lean_ctor_get(v_s_5170_, 0);
                v_invFn_x3f_5172_ = leanh::lean_ctor_get(v_s_5170_, 1);
                v_semiringId_x3f_5173_ = leanh::lean_ctor_get(v_s_5170_, 2);
                v_commSemiringInst_5174_ = leanh::lean_ctor_get(v_s_5170_, 3);
                v_commRingInst_5175_ = leanh::lean_ctor_get(v_s_5170_, 4);
                v_noZeroDivInst_x3f_5176_ = leanh::lean_ctor_get(v_s_5170_, 5);
                v_fieldInst_x3f_5177_ = leanh::lean_ctor_get(v_s_5170_, 6);
                v_powIdentityInst_x3f_5178_ = leanh::lean_ctor_get(v_s_5170_, 7);
                v_denoteEntries_5179_ = leanh::lean_ctor_get(v_s_5170_, 8);
                v_nextId_5180_ = leanh::lean_ctor_get(v_s_5170_, 9);
                v_steps_5181_ = leanh::lean_ctor_get(v_s_5170_, 10);
                v_queue_5182_ = leanh::lean_ctor_get(v_s_5170_, 11);
                v_basis_5183_ = leanh::lean_ctor_get(v_s_5170_, 12);
                v_diseqs_5184_ = leanh::lean_ctor_get(v_s_5170_, 13);
                v_recheck_5185_ = leanh::lean_ctor_get_uint8(
                    v_s_5170_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                );
                v_invSet_5186_ = leanh::lean_ctor_get(v_s_5170_, 14);
                v_powIdentityVarCount_5187_ = leanh::lean_ctor_get(v_s_5170_, 15);
                v_numEq0_x3f_5188_ = leanh::lean_ctor_get(v_s_5170_, 16);
                v_numEq0Updated_5189_ = leanh::lean_ctor_get_uint8(
                    v_s_5170_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_5221_ = (!leanh::lean_is_exclusive(v_s_5170_)) as u8;
                if v_isSharedCheck_5221_ == 0 {
                    v___x_5191_ = v_s_5170_;
                    v_isShared_5192_ = v_isSharedCheck_5221_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_numEq0_x3f_5188_);
                    leanh::lean_inc(v_powIdentityVarCount_5187_);
                    leanh::lean_inc(v_invSet_5186_);
                    leanh::lean_inc(v_diseqs_5184_);
                    leanh::lean_inc(v_basis_5183_);
                    leanh::lean_inc(v_queue_5182_);
                    leanh::lean_inc(v_steps_5181_);
                    leanh::lean_inc(v_nextId_5180_);
                    leanh::lean_inc(v_denoteEntries_5179_);
                    leanh::lean_inc(v_powIdentityInst_x3f_5178_);
                    leanh::lean_inc(v_fieldInst_x3f_5177_);
                    leanh::lean_inc(v_noZeroDivInst_x3f_5176_);
                    leanh::lean_inc(v_commRingInst_5175_);
                    leanh::lean_inc(v_commSemiringInst_5174_);
                    leanh::lean_inc(v_semiringId_x3f_5173_);
                    leanh::lean_inc(v_invFn_x3f_5172_);
                    leanh::lean_inc(v_toRing_5171_);
                    leanh::lean_dec(v_s_5170_);
                    v___x_5191_ = leanh::lean_box(0);
                    v_isShared_5192_ = v_isSharedCheck_5221_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_id_5193_ = leanh::lean_ctor_get(v_toRing_5171_, 0);
                v_type_5194_ = leanh::lean_ctor_get(v_toRing_5171_, 1);
                v_u_5195_ = leanh::lean_ctor_get(v_toRing_5171_, 2);
                v_ringInst_5196_ = leanh::lean_ctor_get(v_toRing_5171_, 3);
                v_semiringInst_5197_ = leanh::lean_ctor_get(v_toRing_5171_, 4);
                v_charInst_x3f_5198_ = leanh::lean_ctor_get(v_toRing_5171_, 5);
                v_addFn_x3f_5199_ = leanh::lean_ctor_get(v_toRing_5171_, 6);
                v_subFn_x3f_5200_ = leanh::lean_ctor_get(v_toRing_5171_, 8);
                v_negFn_x3f_5201_ = leanh::lean_ctor_get(v_toRing_5171_, 9);
                v_powFn_x3f_5202_ = leanh::lean_ctor_get(v_toRing_5171_, 10);
                v_intCastFn_x3f_5203_ = leanh::lean_ctor_get(v_toRing_5171_, 11);
                v_natCastFn_x3f_5204_ = leanh::lean_ctor_get(v_toRing_5171_, 12);
                v_one_x3f_5205_ = leanh::lean_ctor_get(v_toRing_5171_, 13);
                v_vars_5206_ = leanh::lean_ctor_get(v_toRing_5171_, 14);
                v_varMap_5207_ = leanh::lean_ctor_get(v_toRing_5171_, 15);
                v_denote_5208_ = leanh::lean_ctor_get(v_toRing_5171_, 16);
                v_isSharedCheck_5219_ = (!leanh::lean_is_exclusive(v_toRing_5171_)) as u8;
                if v_isSharedCheck_5219_ == 0 {
                    v_unused_5220_ = leanh::lean_ctor_get(v_toRing_5171_, 7);
                    leanh::lean_dec(v_unused_5220_);
                    v___x_5210_ = v_toRing_5171_;
                    v_isShared_5211_ = v_isSharedCheck_5219_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_denote_5208_);
                    leanh::lean_inc(v_varMap_5207_);
                    leanh::lean_inc(v_vars_5206_);
                    leanh::lean_inc(v_one_x3f_5205_);
                    leanh::lean_inc(v_natCastFn_x3f_5204_);
                    leanh::lean_inc(v_intCastFn_x3f_5203_);
                    leanh::lean_inc(v_powFn_x3f_5202_);
                    leanh::lean_inc(v_negFn_x3f_5201_);
                    leanh::lean_inc(v_subFn_x3f_5200_);
                    leanh::lean_inc(v_addFn_x3f_5199_);
                    leanh::lean_inc(v_charInst_x3f_5198_);
                    leanh::lean_inc(v_semiringInst_5197_);
                    leanh::lean_inc(v_ringInst_5196_);
                    leanh::lean_inc(v_u_5195_);
                    leanh::lean_inc(v_type_5194_);
                    leanh::lean_inc(v_id_5193_);
                    leanh::lean_dec(v_toRing_5171_);
                    v___x_5210_ = leanh::lean_box(0);
                    v_isShared_5211_ = v_isSharedCheck_5219_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5212_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5212_, 0, v_a_5169_);
                if v_isShared_5211_ == 0 {
                    leanh::lean_ctor_set(v___x_5210_, 7, v___x_5212_);
                    v___x_5214_ = v___x_5210_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5218_ = leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 0, v_id_5193_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 1, v_type_5194_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 2, v_u_5195_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 3, v_ringInst_5196_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 4, v_semiringInst_5197_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 5, v_charInst_x3f_5198_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 6, v_addFn_x3f_5199_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 7, v___x_5212_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 8, v_subFn_x3f_5200_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 9, v_negFn_x3f_5201_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 10, v_powFn_x3f_5202_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 11, v_intCastFn_x3f_5203_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 12, v_natCastFn_x3f_5204_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 13, v_one_x3f_5205_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 14, v_vars_5206_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 15, v_varMap_5207_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 16, v_denote_5208_);
                    v___x_5214_ = v_reuseFailAlloc_5218_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5192_ == 0 {
                    leanh::lean_ctor_set(v___x_5191_, 0, v___x_5214_);
                    v___x_5216_ = v___x_5191_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5217_ = leanh::lean_alloc_ctor(0, 17, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5217_, 0, v___x_5214_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5217_, 1, v_invFn_x3f_5172_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5217_, 2, v_semiringId_x3f_5173_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5217_,
                        3,
                        v_commSemiringInst_5174_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5217_, 4, v_commRingInst_5175_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5217_,
                        5,
                        v_noZeroDivInst_x3f_5176_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5217_, 6, v_fieldInst_x3f_5177_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5217_,
                        7,
                        v_powIdentityInst_x3f_5178_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5217_, 8, v_denoteEntries_5179_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5217_, 9, v_nextId_5180_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5217_, 10, v_steps_5181_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5217_, 11, v_queue_5182_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5217_, 12, v_basis_5183_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5217_, 13, v_diseqs_5184_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5217_, 14, v_invSet_5186_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5217_,
                        15,
                        v_powIdentityVarCount_5187_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5217_, 16, v_numEq0_x3f_5188_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5217_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                        v_recheck_5185_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5217_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 17 + 1) as u32,
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
    mut v___y_5222_: *mut leanh::LeanObject,
    mut v___y_5223_: *mut leanh::LeanObject,
    mut v___y_5224_: *mut leanh::LeanObject,
    mut v___y_5225_: *mut leanh::LeanObject,
    mut v___y_5226_: *mut leanh::LeanObject,
    mut v___y_5227_: *mut leanh::LeanObject,
    mut v___y_5228_: *mut leanh::LeanObject,
    mut v___y_5229_: *mut leanh::LeanObject,
    mut v___y_5230_: *mut leanh::LeanObject,
    mut v___y_5231_: *mut leanh::LeanObject,
    mut v___y_5232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5238_: u8 = 0;
    let mut v_toRing_5239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_5240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_5247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expectedInst_5255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5264_: u8 = 0;
    let mut v___x_5266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5268_: u8 = 0;
    let mut v_unused_5269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5273_: u8 = 0;
    let mut v___x_5275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5277_: u8 = 0;
    let mut v_isSharedCheck_5278_: u8 = 0;
    let mut v_a_5279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5282_: u8 = 0;
    let mut v___x_5284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5285_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_5234_) == 0 {
                    v_a_5235_ = leanh::lean_ctor_get(v___x_5234_, 0);
                    v_isSharedCheck_5278_ = (!leanh::lean_is_exclusive(v___x_5234_)) as u8;
                    if v_isSharedCheck_5278_ == 0 {
                        v___x_5237_ = v___x_5234_;
                        v_isShared_5238_ = v_isSharedCheck_5278_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5235_);
                        leanh::lean_dec(v___x_5234_);
                        v___x_5237_ = leanh::lean_box(0);
                        v_isShared_5238_ = v_isSharedCheck_5278_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5279_ = leanh::lean_ctor_get(v___x_5234_, 0);
                    v_isSharedCheck_5286_ = (!leanh::lean_is_exclusive(v___x_5234_)) as u8;
                    if v_isSharedCheck_5286_ == 0 {
                        v___x_5281_ = v___x_5234_;
                        v_isShared_5282_ = v_isSharedCheck_5286_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5279_);
                        leanh::lean_dec(v___x_5234_);
                        v___x_5281_ = leanh::lean_box(0);
                        v_isShared_5282_ = v_isSharedCheck_5286_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_toRing_5239_ = leanh::lean_ctor_get(v_a_5235_, 0);
                leanh::lean_inc_ref(v_toRing_5239_);
                leanh::lean_dec(v_a_5235_);
                v_mulFn_x3f_5240_ = leanh::lean_ctor_get(v_toRing_5239_, 7);
                if leanh::lean_obj_tag(v_mulFn_x3f_5240_) == 1 {
                    leanh::lean_inc_ref(v_mulFn_x3f_5240_);
                    leanh::lean_dec_ref(v_toRing_5239_);
                    v_val_5241_ = leanh::lean_ctor_get(v_mulFn_x3f_5240_, 0);
                    leanh::lean_inc(v_val_5241_);
                    leanh::lean_dec_ref_known(v_mulFn_x3f_5240_, 1);
                    if v_isShared_5238_ == 0 {
                        leanh::lean_ctor_set(v___x_5237_, 0, v_val_5241_);
                        v___x_5243_ = v___x_5237_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5244_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5244_, 0, v_val_5241_);
                        v___x_5243_ = v_reuseFailAlloc_5244_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5237_);
                    v_type_5245_ = leanh::lean_ctor_get(v_toRing_5239_, 1);
                    leanh::lean_inc_ref_n(v_type_5245_, 3);
                    v_u_5246_ = leanh::lean_ctor_get(v_toRing_5239_, 2);
                    leanh::lean_inc_n(v_u_5246_, 2);
                    v_semiringInst_5247_ = leanh::lean_ctor_get(v_toRing_5239_, 4);
                    leanh::lean_inc_ref(v_semiringInst_5247_);
                    leanh::lean_dec_ref(v_toRing_5239_);
                    v___x_5248_ =
                        l_Lean_Meta_Grind_Arith_CommRing_getMulFn_x27___redArg___lam__3___closed__1;
                    v___x_5249_ = leanh::lean_box(0);
                    v___x_5250_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5250_, 0, v_u_5246_);
                    leanh::lean_ctor_set(v___x_5250_, 1, v___x_5249_);
                    leanh::lean_inc_ref(v___x_5250_);
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
                    if leanh::lean_obj_tag(v___x_5258_) == 0 {
                        v_a_5259_ = leanh::lean_ctor_get(v___x_5258_, 0);
                        leanh::lean_inc_n(v_a_5259_, 2);
                        leanh::lean_dec_ref_known(v___x_5258_, 1);
                        v___f_5260_ = leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3___lam__0 as *mut core::ffi::c_void, 2, 1);
                        leanh::lean_closure_set(v___f_5260_, 0, v_a_5259_);
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
                        if leanh::lean_obj_tag(v___x_5261_) == 0 {
                            v_isSharedCheck_5268_ =
                                (!leanh::lean_is_exclusive(v___x_5261_)) as u8;
                            if v_isSharedCheck_5268_ == 0 {
                                v_unused_5269_ = leanh::lean_ctor_get(v___x_5261_, 0);
                                leanh::lean_dec(v_unused_5269_);
                                v___x_5263_ = v___x_5261_;
                                v_isShared_5264_ = v_isSharedCheck_5268_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_5261_);
                                v___x_5263_ = leanh::lean_box(0);
                                v_isShared_5264_ = v_isSharedCheck_5268_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_5259_);
                            v_a_5270_ = leanh::lean_ctor_get(v___x_5261_, 0);
                            v_isSharedCheck_5277_ =
                                (!leanh::lean_is_exclusive(v___x_5261_)) as u8;
                            if v_isSharedCheck_5277_ == 0 {
                                v___x_5272_ = v___x_5261_;
                                v_isShared_5273_ = v_isSharedCheck_5277_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5270_);
                                leanh::lean_dec(v___x_5261_);
                                v___x_5272_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_5263_, 0, v_a_5259_);
                    v___x_5266_ = v___x_5263_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5267_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5267_, 0, v_a_5259_);
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
                    v_reuseFailAlloc_5276_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5276_, 0, v_a_5270_);
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
                    v_reuseFailAlloc_5285_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5285_, 0, v_a_5279_);
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
    mut v___y_5287_: *mut leanh::LeanObject,
    mut v___y_5288_: *mut leanh::LeanObject,
    mut v___y_5289_: *mut leanh::LeanObject,
    mut v___y_5290_: *mut leanh::LeanObject,
    mut v___y_5291_: *mut leanh::LeanObject,
    mut v___y_5292_: *mut leanh::LeanObject,
    mut v___y_5293_: *mut leanh::LeanObject,
    mut v___y_5294_: *mut leanh::LeanObject,
    mut v___y_5295_: *mut leanh::LeanObject,
    mut v___y_5296_: *mut leanh::LeanObject,
    mut v___y_5297_: *mut leanh::LeanObject,
    mut v___y_5298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5299_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(v___y_5287_, v___y_5288_, v___y_5289_, v___y_5290_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_, v___y_5295_, v___y_5296_, v___y_5297_);
    leanh::lean_dec(v___y_5297_);
    leanh::lean_dec_ref(v___y_5296_);
    leanh::lean_dec(v___y_5295_);
    leanh::lean_dec_ref(v___y_5294_);
    leanh::lean_dec(v___y_5293_);
    leanh::lean_dec_ref(v___y_5292_);
    leanh::lean_dec(v___y_5291_);
    leanh::lean_dec_ref(v___y_5290_);
    leanh::lean_dec(v___y_5289_);
    leanh::lean_dec(v___y_5288_);
    leanh::lean_dec(v___y_5287_);
    return v_res_5299_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0(
    mut v_a_5300_: *mut leanh::LeanObject,
    mut v_s_5301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toRing_5302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_5303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_5304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_5305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_5306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_5309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_5310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_5311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_5312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_5313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_5314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recheck_5316_: u8 = 0;
    let mut v_invSet_5317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_5318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_5319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_5320_: u8 = 0;
    let mut v___x_5322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5323_: u8 = 0;
    let mut v_id_5324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_5327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_5328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_5329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_5330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_5331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_5333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_5334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_5335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_5337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_5338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5342_: u8 = 0;
    let mut v___x_5343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5350_: u8 = 0;
    let mut v_unused_5351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5352_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_5302_ = leanh::lean_ctor_get(v_s_5301_, 0);
                v_invFn_x3f_5303_ = leanh::lean_ctor_get(v_s_5301_, 1);
                v_semiringId_x3f_5304_ = leanh::lean_ctor_get(v_s_5301_, 2);
                v_commSemiringInst_5305_ = leanh::lean_ctor_get(v_s_5301_, 3);
                v_commRingInst_5306_ = leanh::lean_ctor_get(v_s_5301_, 4);
                v_noZeroDivInst_x3f_5307_ = leanh::lean_ctor_get(v_s_5301_, 5);
                v_fieldInst_x3f_5308_ = leanh::lean_ctor_get(v_s_5301_, 6);
                v_powIdentityInst_x3f_5309_ = leanh::lean_ctor_get(v_s_5301_, 7);
                v_denoteEntries_5310_ = leanh::lean_ctor_get(v_s_5301_, 8);
                v_nextId_5311_ = leanh::lean_ctor_get(v_s_5301_, 9);
                v_steps_5312_ = leanh::lean_ctor_get(v_s_5301_, 10);
                v_queue_5313_ = leanh::lean_ctor_get(v_s_5301_, 11);
                v_basis_5314_ = leanh::lean_ctor_get(v_s_5301_, 12);
                v_diseqs_5315_ = leanh::lean_ctor_get(v_s_5301_, 13);
                v_recheck_5316_ = leanh::lean_ctor_get_uint8(
                    v_s_5301_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                );
                v_invSet_5317_ = leanh::lean_ctor_get(v_s_5301_, 14);
                v_powIdentityVarCount_5318_ = leanh::lean_ctor_get(v_s_5301_, 15);
                v_numEq0_x3f_5319_ = leanh::lean_ctor_get(v_s_5301_, 16);
                v_numEq0Updated_5320_ = leanh::lean_ctor_get_uint8(
                    v_s_5301_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_5352_ = (!leanh::lean_is_exclusive(v_s_5301_)) as u8;
                if v_isSharedCheck_5352_ == 0 {
                    v___x_5322_ = v_s_5301_;
                    v_isShared_5323_ = v_isSharedCheck_5352_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_numEq0_x3f_5319_);
                    leanh::lean_inc(v_powIdentityVarCount_5318_);
                    leanh::lean_inc(v_invSet_5317_);
                    leanh::lean_inc(v_diseqs_5315_);
                    leanh::lean_inc(v_basis_5314_);
                    leanh::lean_inc(v_queue_5313_);
                    leanh::lean_inc(v_steps_5312_);
                    leanh::lean_inc(v_nextId_5311_);
                    leanh::lean_inc(v_denoteEntries_5310_);
                    leanh::lean_inc(v_powIdentityInst_x3f_5309_);
                    leanh::lean_inc(v_fieldInst_x3f_5308_);
                    leanh::lean_inc(v_noZeroDivInst_x3f_5307_);
                    leanh::lean_inc(v_commRingInst_5306_);
                    leanh::lean_inc(v_commSemiringInst_5305_);
                    leanh::lean_inc(v_semiringId_x3f_5304_);
                    leanh::lean_inc(v_invFn_x3f_5303_);
                    leanh::lean_inc(v_toRing_5302_);
                    leanh::lean_dec(v_s_5301_);
                    v___x_5322_ = leanh::lean_box(0);
                    v_isShared_5323_ = v_isSharedCheck_5352_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_id_5324_ = leanh::lean_ctor_get(v_toRing_5302_, 0);
                v_type_5325_ = leanh::lean_ctor_get(v_toRing_5302_, 1);
                v_u_5326_ = leanh::lean_ctor_get(v_toRing_5302_, 2);
                v_ringInst_5327_ = leanh::lean_ctor_get(v_toRing_5302_, 3);
                v_semiringInst_5328_ = leanh::lean_ctor_get(v_toRing_5302_, 4);
                v_charInst_x3f_5329_ = leanh::lean_ctor_get(v_toRing_5302_, 5);
                v_mulFn_x3f_5330_ = leanh::lean_ctor_get(v_toRing_5302_, 7);
                v_subFn_x3f_5331_ = leanh::lean_ctor_get(v_toRing_5302_, 8);
                v_negFn_x3f_5332_ = leanh::lean_ctor_get(v_toRing_5302_, 9);
                v_powFn_x3f_5333_ = leanh::lean_ctor_get(v_toRing_5302_, 10);
                v_intCastFn_x3f_5334_ = leanh::lean_ctor_get(v_toRing_5302_, 11);
                v_natCastFn_x3f_5335_ = leanh::lean_ctor_get(v_toRing_5302_, 12);
                v_one_x3f_5336_ = leanh::lean_ctor_get(v_toRing_5302_, 13);
                v_vars_5337_ = leanh::lean_ctor_get(v_toRing_5302_, 14);
                v_varMap_5338_ = leanh::lean_ctor_get(v_toRing_5302_, 15);
                v_denote_5339_ = leanh::lean_ctor_get(v_toRing_5302_, 16);
                v_isSharedCheck_5350_ = (!leanh::lean_is_exclusive(v_toRing_5302_)) as u8;
                if v_isSharedCheck_5350_ == 0 {
                    v_unused_5351_ = leanh::lean_ctor_get(v_toRing_5302_, 6);
                    leanh::lean_dec(v_unused_5351_);
                    v___x_5341_ = v_toRing_5302_;
                    v_isShared_5342_ = v_isSharedCheck_5350_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_denote_5339_);
                    leanh::lean_inc(v_varMap_5338_);
                    leanh::lean_inc(v_vars_5337_);
                    leanh::lean_inc(v_one_x3f_5336_);
                    leanh::lean_inc(v_natCastFn_x3f_5335_);
                    leanh::lean_inc(v_intCastFn_x3f_5334_);
                    leanh::lean_inc(v_powFn_x3f_5333_);
                    leanh::lean_inc(v_negFn_x3f_5332_);
                    leanh::lean_inc(v_subFn_x3f_5331_);
                    leanh::lean_inc(v_mulFn_x3f_5330_);
                    leanh::lean_inc(v_charInst_x3f_5329_);
                    leanh::lean_inc(v_semiringInst_5328_);
                    leanh::lean_inc(v_ringInst_5327_);
                    leanh::lean_inc(v_u_5326_);
                    leanh::lean_inc(v_type_5325_);
                    leanh::lean_inc(v_id_5324_);
                    leanh::lean_dec(v_toRing_5302_);
                    v___x_5341_ = leanh::lean_box(0);
                    v_isShared_5342_ = v_isSharedCheck_5350_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5343_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5343_, 0, v_a_5300_);
                if v_isShared_5342_ == 0 {
                    leanh::lean_ctor_set(v___x_5341_, 6, v___x_5343_);
                    v___x_5345_ = v___x_5341_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5349_ = leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 0, v_id_5324_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 1, v_type_5325_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 2, v_u_5326_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 3, v_ringInst_5327_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 4, v_semiringInst_5328_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 5, v_charInst_x3f_5329_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 6, v___x_5343_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 7, v_mulFn_x3f_5330_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 8, v_subFn_x3f_5331_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 9, v_negFn_x3f_5332_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 10, v_powFn_x3f_5333_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 11, v_intCastFn_x3f_5334_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 12, v_natCastFn_x3f_5335_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 13, v_one_x3f_5336_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 14, v_vars_5337_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 15, v_varMap_5338_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 16, v_denote_5339_);
                    v___x_5345_ = v_reuseFailAlloc_5349_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5323_ == 0 {
                    leanh::lean_ctor_set(v___x_5322_, 0, v___x_5345_);
                    v___x_5347_ = v___x_5322_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5348_ = leanh::lean_alloc_ctor(0, 17, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 0, v___x_5345_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 1, v_invFn_x3f_5303_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 2, v_semiringId_x3f_5304_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5348_,
                        3,
                        v_commSemiringInst_5305_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 4, v_commRingInst_5306_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5348_,
                        5,
                        v_noZeroDivInst_x3f_5307_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 6, v_fieldInst_x3f_5308_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5348_,
                        7,
                        v_powIdentityInst_x3f_5309_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 8, v_denoteEntries_5310_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 9, v_nextId_5311_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 10, v_steps_5312_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 11, v_queue_5313_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 12, v_basis_5314_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 13, v_diseqs_5315_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 14, v_invSet_5317_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5348_,
                        15,
                        v_powIdentityVarCount_5318_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 16, v_numEq0_x3f_5319_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5348_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                        v_recheck_5316_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5348_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 17 + 1) as u32,
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
    mut v___y_5353_: *mut leanh::LeanObject,
    mut v___y_5354_: *mut leanh::LeanObject,
    mut v___y_5355_: *mut leanh::LeanObject,
    mut v___y_5356_: *mut leanh::LeanObject,
    mut v___y_5357_: *mut leanh::LeanObject,
    mut v___y_5358_: *mut leanh::LeanObject,
    mut v___y_5359_: *mut leanh::LeanObject,
    mut v___y_5360_: *mut leanh::LeanObject,
    mut v___y_5361_: *mut leanh::LeanObject,
    mut v___y_5362_: *mut leanh::LeanObject,
    mut v___y_5363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5369_: u8 = 0;
    let mut v_toRing_5370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_5371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_5378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expectedInst_5386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5395_: u8 = 0;
    let mut v___x_5397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5399_: u8 = 0;
    let mut v_unused_5400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5404_: u8 = 0;
    let mut v___x_5406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5408_: u8 = 0;
    let mut v_isSharedCheck_5409_: u8 = 0;
    let mut v_a_5410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5413_: u8 = 0;
    let mut v___x_5415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5416_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_5365_) == 0 {
                    v_a_5366_ = leanh::lean_ctor_get(v___x_5365_, 0);
                    v_isSharedCheck_5409_ = (!leanh::lean_is_exclusive(v___x_5365_)) as u8;
                    if v_isSharedCheck_5409_ == 0 {
                        v___x_5368_ = v___x_5365_;
                        v_isShared_5369_ = v_isSharedCheck_5409_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5366_);
                        leanh::lean_dec(v___x_5365_);
                        v___x_5368_ = leanh::lean_box(0);
                        v_isShared_5369_ = v_isSharedCheck_5409_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5410_ = leanh::lean_ctor_get(v___x_5365_, 0);
                    v_isSharedCheck_5417_ = (!leanh::lean_is_exclusive(v___x_5365_)) as u8;
                    if v_isSharedCheck_5417_ == 0 {
                        v___x_5412_ = v___x_5365_;
                        v_isShared_5413_ = v_isSharedCheck_5417_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5410_);
                        leanh::lean_dec(v___x_5365_);
                        v___x_5412_ = leanh::lean_box(0);
                        v_isShared_5413_ = v_isSharedCheck_5417_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_toRing_5370_ = leanh::lean_ctor_get(v_a_5366_, 0);
                leanh::lean_inc_ref(v_toRing_5370_);
                leanh::lean_dec(v_a_5366_);
                v_addFn_x3f_5371_ = leanh::lean_ctor_get(v_toRing_5370_, 6);
                if leanh::lean_obj_tag(v_addFn_x3f_5371_) == 1 {
                    leanh::lean_inc_ref(v_addFn_x3f_5371_);
                    leanh::lean_dec_ref(v_toRing_5370_);
                    v_val_5372_ = leanh::lean_ctor_get(v_addFn_x3f_5371_, 0);
                    leanh::lean_inc(v_val_5372_);
                    leanh::lean_dec_ref_known(v_addFn_x3f_5371_, 1);
                    if v_isShared_5369_ == 0 {
                        leanh::lean_ctor_set(v___x_5368_, 0, v_val_5372_);
                        v___x_5374_ = v___x_5368_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5375_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5375_, 0, v_val_5372_);
                        v___x_5374_ = v_reuseFailAlloc_5375_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5368_);
                    v_type_5376_ = leanh::lean_ctor_get(v_toRing_5370_, 1);
                    leanh::lean_inc_ref_n(v_type_5376_, 3);
                    v_u_5377_ = leanh::lean_ctor_get(v_toRing_5370_, 2);
                    leanh::lean_inc_n(v_u_5377_, 2);
                    v_semiringInst_5378_ = leanh::lean_ctor_get(v_toRing_5370_, 4);
                    leanh::lean_inc_ref(v_semiringInst_5378_);
                    leanh::lean_dec_ref(v_toRing_5370_);
                    v___x_5379_ =
                        l_Lean_Meta_Grind_Arith_CommRing_getAddFn_x27___redArg___lam__3___closed__1;
                    v___x_5380_ = leanh::lean_box(0);
                    v___x_5381_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5381_, 0, v_u_5377_);
                    leanh::lean_ctor_set(v___x_5381_, 1, v___x_5380_);
                    leanh::lean_inc_ref(v___x_5381_);
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
                    if leanh::lean_obj_tag(v___x_5389_) == 0 {
                        v_a_5390_ = leanh::lean_ctor_get(v___x_5389_, 0);
                        leanh::lean_inc_n(v_a_5390_, 2);
                        leanh::lean_dec_ref_known(v___x_5389_, 1);
                        v___f_5391_ = leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2___lam__0 as *mut core::ffi::c_void, 2, 1);
                        leanh::lean_closure_set(v___f_5391_, 0, v_a_5390_);
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
                        if leanh::lean_obj_tag(v___x_5392_) == 0 {
                            v_isSharedCheck_5399_ =
                                (!leanh::lean_is_exclusive(v___x_5392_)) as u8;
                            if v_isSharedCheck_5399_ == 0 {
                                v_unused_5400_ = leanh::lean_ctor_get(v___x_5392_, 0);
                                leanh::lean_dec(v_unused_5400_);
                                v___x_5394_ = v___x_5392_;
                                v_isShared_5395_ = v_isSharedCheck_5399_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_5392_);
                                v___x_5394_ = leanh::lean_box(0);
                                v_isShared_5395_ = v_isSharedCheck_5399_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_5390_);
                            v_a_5401_ = leanh::lean_ctor_get(v___x_5392_, 0);
                            v_isSharedCheck_5408_ =
                                (!leanh::lean_is_exclusive(v___x_5392_)) as u8;
                            if v_isSharedCheck_5408_ == 0 {
                                v___x_5403_ = v___x_5392_;
                                v_isShared_5404_ = v_isSharedCheck_5408_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5401_);
                                leanh::lean_dec(v___x_5392_);
                                v___x_5403_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_5394_, 0, v_a_5390_);
                    v___x_5397_ = v___x_5394_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5398_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5398_, 0, v_a_5390_);
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
                    v_reuseFailAlloc_5407_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5407_, 0, v_a_5401_);
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
                    v_reuseFailAlloc_5416_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5416_, 0, v_a_5410_);
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
    mut v___y_5418_: *mut leanh::LeanObject,
    mut v___y_5419_: *mut leanh::LeanObject,
    mut v___y_5420_: *mut leanh::LeanObject,
    mut v___y_5421_: *mut leanh::LeanObject,
    mut v___y_5422_: *mut leanh::LeanObject,
    mut v___y_5423_: *mut leanh::LeanObject,
    mut v___y_5424_: *mut leanh::LeanObject,
    mut v___y_5425_: *mut leanh::LeanObject,
    mut v___y_5426_: *mut leanh::LeanObject,
    mut v___y_5427_: *mut leanh::LeanObject,
    mut v___y_5428_: *mut leanh::LeanObject,
    mut v___y_5429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5430_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_);
    leanh::lean_dec(v___y_5428_);
    leanh::lean_dec_ref(v___y_5427_);
    leanh::lean_dec(v___y_5426_);
    leanh::lean_dec_ref(v___y_5425_);
    leanh::lean_dec(v___y_5424_);
    leanh::lean_dec_ref(v___y_5423_);
    leanh::lean_dec(v___y_5422_);
    leanh::lean_dec_ref(v___y_5421_);
    leanh::lean_dec(v___y_5420_);
    leanh::lean_dec(v___y_5419_);
    leanh::lean_dec(v___y_5418_);
    return v_res_5430_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(
    mut v_type_5431_: *mut leanh::LeanObject,
    mut v_u_5432_: *mut leanh::LeanObject,
    mut v_instDeclName_5433_: *mut leanh::LeanObject,
    mut v_declName_5434_: *mut leanh::LeanObject,
    mut v_expectedInst_5435_: *mut leanh::LeanObject,
    mut v___y_5436_: *mut leanh::LeanObject,
    mut v___y_5437_: *mut leanh::LeanObject,
    mut v___y_5438_: *mut leanh::LeanObject,
    mut v___y_5439_: *mut leanh::LeanObject,
    mut v___y_5440_: *mut leanh::LeanObject,
    mut v___y_5441_: *mut leanh::LeanObject,
    mut v___y_5442_: *mut leanh::LeanObject,
    mut v___y_5443_: *mut leanh::LeanObject,
    mut v___y_5444_: *mut leanh::LeanObject,
    mut v___y_5445_: *mut leanh::LeanObject,
    mut v___y_5446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5463_: u8 = 0;
    let mut v___x_5465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5467_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5448_ = leanh::lean_box(0);
                v___x_5449_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5449_, 0, v_u_5432_);
                leanh::lean_ctor_set(v___x_5449_, 1, v___x_5448_);
                leanh::lean_inc_ref(v___x_5449_);
                v___x_5450_ = l_Lean_mkConst(v_instDeclName_5433_, v___x_5449_);
                leanh::lean_inc_ref(v_type_5431_);
                v___x_5451_ = l_Lean_Expr_app___override(v___x_5450_, v_type_5431_);
                v___x_5452_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_5451_, v___y_5443_, v___y_5444_, v___y_5445_, v___y_5446_);
                if leanh::lean_obj_tag(v___x_5452_) == 0 {
                    v_a_5453_ = leanh::lean_ctor_get(v___x_5452_, 0);
                    leanh::lean_inc_n(v_a_5453_, 2);
                    leanh::lean_dec_ref_known(v___x_5452_, 1);
                    leanh::lean_inc(v_declName_5434_);
                    v___x_5454_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(
                        v_declName_5434_,
                        v_a_5453_,
                        v_expectedInst_5435_,
                        v___y_5443_,
                        v___y_5444_,
                        v___y_5445_,
                        v___y_5446_,
                    );
                    if leanh::lean_obj_tag(v___x_5454_) == 0 {
                        leanh::lean_dec_ref_known(v___x_5454_, 1);
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
                        if leanh::lean_obj_tag(v___x_5457_) == 0 {
                            v_a_5458_ = leanh::lean_ctor_get(v___x_5457_, 0);
                            leanh::lean_inc(v_a_5458_);
                            leanh::lean_dec_ref_known(v___x_5457_, 1);
                            v___x_5459_ =
                                l_Lean_Meta_Sym_shareCommon___redArg(v_a_5458_, v___y_5442_);
                            return v___x_5459_;
                        } else {
                            return v___x_5457_;
                        }
                    } else {
                        leanh::lean_dec(v_a_5453_);
                        leanh::lean_dec_ref_known(v___x_5449_, 2);
                        leanh::lean_dec(v_declName_5434_);
                        leanh::lean_dec_ref(v_type_5431_);
                        v_a_5460_ = leanh::lean_ctor_get(v___x_5454_, 0);
                        v_isSharedCheck_5467_ =
                            (!leanh::lean_is_exclusive(v___x_5454_)) as u8;
                        if v_isSharedCheck_5467_ == 0 {
                            v___x_5462_ = v___x_5454_;
                            v_isShared_5463_ = v_isSharedCheck_5467_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5460_);
                            leanh::lean_dec(v___x_5454_);
                            v___x_5462_ = leanh::lean_box(0);
                            v_isShared_5463_ = v_isSharedCheck_5467_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_5449_, 2);
                    leanh::lean_dec_ref(v_expectedInst_5435_);
                    leanh::lean_dec(v_declName_5434_);
                    leanh::lean_dec_ref(v_type_5431_);
                    return v___x_5452_;
                }
            }
            1 => {
                if v_isShared_5463_ == 0 {
                    v___x_5465_ = v___x_5462_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5466_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5466_, 0, v_a_5460_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_type_5468_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_u_5469_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_instDeclName_5470_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_declName_5471_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_expectedInst_5472_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___y_5473_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_5474_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_5475_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_5476_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_5477_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_5478_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_5479_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_5480_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_5481_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_5482_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_5483_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_5484_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_res_5485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5485_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(v_type_5468_, v_u_5469_, v_instDeclName_5470_, v_declName_5471_, v_expectedInst_5472_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_, v___y_5477_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_);
    leanh::lean_dec(v___y_5483_);
    leanh::lean_dec_ref(v___y_5482_);
    leanh::lean_dec(v___y_5481_);
    leanh::lean_dec_ref(v___y_5480_);
    leanh::lean_dec(v___y_5479_);
    leanh::lean_dec_ref(v___y_5478_);
    leanh::lean_dec(v___y_5477_);
    leanh::lean_dec_ref(v___y_5476_);
    leanh::lean_dec(v___y_5475_);
    leanh::lean_dec(v___y_5474_);
    leanh::lean_dec(v___y_5473_);
    return v_res_5485_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___lam__0(
    mut v_a_5486_: *mut leanh::LeanObject,
    mut v_s_5487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toRing_5488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_5489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_5490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_5491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_5492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_5493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_5494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_5495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_5496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_5497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_5498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_5499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_5500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_5501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recheck_5502_: u8 = 0;
    let mut v_invSet_5503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_5504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_5505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_5506_: u8 = 0;
    let mut v___x_5508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5509_: u8 = 0;
    let mut v_id_5510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_5513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_5514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_5515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_5517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_5518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_5519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_5520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_5521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_5522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_5523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_5524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_5525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5528_: u8 = 0;
    let mut v___x_5529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5536_: u8 = 0;
    let mut v_unused_5537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5538_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_5488_ = leanh::lean_ctor_get(v_s_5487_, 0);
                v_invFn_x3f_5489_ = leanh::lean_ctor_get(v_s_5487_, 1);
                v_semiringId_x3f_5490_ = leanh::lean_ctor_get(v_s_5487_, 2);
                v_commSemiringInst_5491_ = leanh::lean_ctor_get(v_s_5487_, 3);
                v_commRingInst_5492_ = leanh::lean_ctor_get(v_s_5487_, 4);
                v_noZeroDivInst_x3f_5493_ = leanh::lean_ctor_get(v_s_5487_, 5);
                v_fieldInst_x3f_5494_ = leanh::lean_ctor_get(v_s_5487_, 6);
                v_powIdentityInst_x3f_5495_ = leanh::lean_ctor_get(v_s_5487_, 7);
                v_denoteEntries_5496_ = leanh::lean_ctor_get(v_s_5487_, 8);
                v_nextId_5497_ = leanh::lean_ctor_get(v_s_5487_, 9);
                v_steps_5498_ = leanh::lean_ctor_get(v_s_5487_, 10);
                v_queue_5499_ = leanh::lean_ctor_get(v_s_5487_, 11);
                v_basis_5500_ = leanh::lean_ctor_get(v_s_5487_, 12);
                v_diseqs_5501_ = leanh::lean_ctor_get(v_s_5487_, 13);
                v_recheck_5502_ = leanh::lean_ctor_get_uint8(
                    v_s_5487_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                );
                v_invSet_5503_ = leanh::lean_ctor_get(v_s_5487_, 14);
                v_powIdentityVarCount_5504_ = leanh::lean_ctor_get(v_s_5487_, 15);
                v_numEq0_x3f_5505_ = leanh::lean_ctor_get(v_s_5487_, 16);
                v_numEq0Updated_5506_ = leanh::lean_ctor_get_uint8(
                    v_s_5487_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_5538_ = (!leanh::lean_is_exclusive(v_s_5487_)) as u8;
                if v_isSharedCheck_5538_ == 0 {
                    v___x_5508_ = v_s_5487_;
                    v_isShared_5509_ = v_isSharedCheck_5538_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_numEq0_x3f_5505_);
                    leanh::lean_inc(v_powIdentityVarCount_5504_);
                    leanh::lean_inc(v_invSet_5503_);
                    leanh::lean_inc(v_diseqs_5501_);
                    leanh::lean_inc(v_basis_5500_);
                    leanh::lean_inc(v_queue_5499_);
                    leanh::lean_inc(v_steps_5498_);
                    leanh::lean_inc(v_nextId_5497_);
                    leanh::lean_inc(v_denoteEntries_5496_);
                    leanh::lean_inc(v_powIdentityInst_x3f_5495_);
                    leanh::lean_inc(v_fieldInst_x3f_5494_);
                    leanh::lean_inc(v_noZeroDivInst_x3f_5493_);
                    leanh::lean_inc(v_commRingInst_5492_);
                    leanh::lean_inc(v_commSemiringInst_5491_);
                    leanh::lean_inc(v_semiringId_x3f_5490_);
                    leanh::lean_inc(v_invFn_x3f_5489_);
                    leanh::lean_inc(v_toRing_5488_);
                    leanh::lean_dec(v_s_5487_);
                    v___x_5508_ = leanh::lean_box(0);
                    v_isShared_5509_ = v_isSharedCheck_5538_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_id_5510_ = leanh::lean_ctor_get(v_toRing_5488_, 0);
                v_type_5511_ = leanh::lean_ctor_get(v_toRing_5488_, 1);
                v_u_5512_ = leanh::lean_ctor_get(v_toRing_5488_, 2);
                v_ringInst_5513_ = leanh::lean_ctor_get(v_toRing_5488_, 3);
                v_semiringInst_5514_ = leanh::lean_ctor_get(v_toRing_5488_, 4);
                v_charInst_x3f_5515_ = leanh::lean_ctor_get(v_toRing_5488_, 5);
                v_addFn_x3f_5516_ = leanh::lean_ctor_get(v_toRing_5488_, 6);
                v_mulFn_x3f_5517_ = leanh::lean_ctor_get(v_toRing_5488_, 7);
                v_subFn_x3f_5518_ = leanh::lean_ctor_get(v_toRing_5488_, 8);
                v_powFn_x3f_5519_ = leanh::lean_ctor_get(v_toRing_5488_, 10);
                v_intCastFn_x3f_5520_ = leanh::lean_ctor_get(v_toRing_5488_, 11);
                v_natCastFn_x3f_5521_ = leanh::lean_ctor_get(v_toRing_5488_, 12);
                v_one_x3f_5522_ = leanh::lean_ctor_get(v_toRing_5488_, 13);
                v_vars_5523_ = leanh::lean_ctor_get(v_toRing_5488_, 14);
                v_varMap_5524_ = leanh::lean_ctor_get(v_toRing_5488_, 15);
                v_denote_5525_ = leanh::lean_ctor_get(v_toRing_5488_, 16);
                v_isSharedCheck_5536_ = (!leanh::lean_is_exclusive(v_toRing_5488_)) as u8;
                if v_isSharedCheck_5536_ == 0 {
                    v_unused_5537_ = leanh::lean_ctor_get(v_toRing_5488_, 9);
                    leanh::lean_dec(v_unused_5537_);
                    v___x_5527_ = v_toRing_5488_;
                    v_isShared_5528_ = v_isSharedCheck_5536_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_denote_5525_);
                    leanh::lean_inc(v_varMap_5524_);
                    leanh::lean_inc(v_vars_5523_);
                    leanh::lean_inc(v_one_x3f_5522_);
                    leanh::lean_inc(v_natCastFn_x3f_5521_);
                    leanh::lean_inc(v_intCastFn_x3f_5520_);
                    leanh::lean_inc(v_powFn_x3f_5519_);
                    leanh::lean_inc(v_subFn_x3f_5518_);
                    leanh::lean_inc(v_mulFn_x3f_5517_);
                    leanh::lean_inc(v_addFn_x3f_5516_);
                    leanh::lean_inc(v_charInst_x3f_5515_);
                    leanh::lean_inc(v_semiringInst_5514_);
                    leanh::lean_inc(v_ringInst_5513_);
                    leanh::lean_inc(v_u_5512_);
                    leanh::lean_inc(v_type_5511_);
                    leanh::lean_inc(v_id_5510_);
                    leanh::lean_dec(v_toRing_5488_);
                    v___x_5527_ = leanh::lean_box(0);
                    v_isShared_5528_ = v_isSharedCheck_5536_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5529_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5529_, 0, v_a_5486_);
                if v_isShared_5528_ == 0 {
                    leanh::lean_ctor_set(v___x_5527_, 9, v___x_5529_);
                    v___x_5531_ = v___x_5527_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5535_ = leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 0, v_id_5510_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 1, v_type_5511_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 2, v_u_5512_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 3, v_ringInst_5513_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 4, v_semiringInst_5514_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 5, v_charInst_x3f_5515_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 6, v_addFn_x3f_5516_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 7, v_mulFn_x3f_5517_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 8, v_subFn_x3f_5518_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 9, v___x_5529_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 10, v_powFn_x3f_5519_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 11, v_intCastFn_x3f_5520_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 12, v_natCastFn_x3f_5521_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 13, v_one_x3f_5522_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 14, v_vars_5523_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 15, v_varMap_5524_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 16, v_denote_5525_);
                    v___x_5531_ = v_reuseFailAlloc_5535_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5509_ == 0 {
                    leanh::lean_ctor_set(v___x_5508_, 0, v___x_5531_);
                    v___x_5533_ = v___x_5508_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5534_ = leanh::lean_alloc_ctor(0, 17, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5534_, 0, v___x_5531_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5534_, 1, v_invFn_x3f_5489_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5534_, 2, v_semiringId_x3f_5490_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5534_,
                        3,
                        v_commSemiringInst_5491_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5534_, 4, v_commRingInst_5492_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5534_,
                        5,
                        v_noZeroDivInst_x3f_5493_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5534_, 6, v_fieldInst_x3f_5494_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5534_,
                        7,
                        v_powIdentityInst_x3f_5495_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5534_, 8, v_denoteEntries_5496_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5534_, 9, v_nextId_5497_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5534_, 10, v_steps_5498_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5534_, 11, v_queue_5499_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5534_, 12, v_basis_5500_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5534_, 13, v_diseqs_5501_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5534_, 14, v_invSet_5503_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5534_,
                        15,
                        v_powIdentityVarCount_5504_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5534_, 16, v_numEq0_x3f_5505_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5534_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                        v_recheck_5502_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5534_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 17 + 1) as u32,
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
    mut v___y_5552_: *mut leanh::LeanObject,
    mut v___y_5553_: *mut leanh::LeanObject,
    mut v___y_5554_: *mut leanh::LeanObject,
    mut v___y_5555_: *mut leanh::LeanObject,
    mut v___y_5556_: *mut leanh::LeanObject,
    mut v___y_5557_: *mut leanh::LeanObject,
    mut v___y_5558_: *mut leanh::LeanObject,
    mut v___y_5559_: *mut leanh::LeanObject,
    mut v___y_5560_: *mut leanh::LeanObject,
    mut v___y_5561_: *mut leanh::LeanObject,
    mut v___y_5562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5568_: u8 = 0;
    let mut v_toRing_5569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_5570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_5577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expectedInst_5582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5591_: u8 = 0;
    let mut v___x_5593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5595_: u8 = 0;
    let mut v_unused_5596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5600_: u8 = 0;
    let mut v___x_5602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5604_: u8 = 0;
    let mut v_isSharedCheck_5605_: u8 = 0;
    let mut v_a_5606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5609_: u8 = 0;
    let mut v___x_5611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5612_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_5564_) == 0 {
                    v_a_5565_ = leanh::lean_ctor_get(v___x_5564_, 0);
                    v_isSharedCheck_5605_ = (!leanh::lean_is_exclusive(v___x_5564_)) as u8;
                    if v_isSharedCheck_5605_ == 0 {
                        v___x_5567_ = v___x_5564_;
                        v_isShared_5568_ = v_isSharedCheck_5605_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5565_);
                        leanh::lean_dec(v___x_5564_);
                        v___x_5567_ = leanh::lean_box(0);
                        v_isShared_5568_ = v_isSharedCheck_5605_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5606_ = leanh::lean_ctor_get(v___x_5564_, 0);
                    v_isSharedCheck_5613_ = (!leanh::lean_is_exclusive(v___x_5564_)) as u8;
                    if v_isSharedCheck_5613_ == 0 {
                        v___x_5608_ = v___x_5564_;
                        v_isShared_5609_ = v_isSharedCheck_5613_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5606_);
                        leanh::lean_dec(v___x_5564_);
                        v___x_5608_ = leanh::lean_box(0);
                        v_isShared_5609_ = v_isSharedCheck_5613_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_toRing_5569_ = leanh::lean_ctor_get(v_a_5565_, 0);
                leanh::lean_inc_ref(v_toRing_5569_);
                leanh::lean_dec(v_a_5565_);
                v_negFn_x3f_5570_ = leanh::lean_ctor_get(v_toRing_5569_, 9);
                if leanh::lean_obj_tag(v_negFn_x3f_5570_) == 1 {
                    leanh::lean_inc_ref(v_negFn_x3f_5570_);
                    leanh::lean_dec_ref(v_toRing_5569_);
                    v_val_5571_ = leanh::lean_ctor_get(v_negFn_x3f_5570_, 0);
                    leanh::lean_inc(v_val_5571_);
                    leanh::lean_dec_ref_known(v_negFn_x3f_5570_, 1);
                    if v_isShared_5568_ == 0 {
                        leanh::lean_ctor_set(v___x_5567_, 0, v_val_5571_);
                        v___x_5573_ = v___x_5567_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5574_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5574_, 0, v_val_5571_);
                        v___x_5573_ = v_reuseFailAlloc_5574_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5567_);
                    v_type_5575_ = leanh::lean_ctor_get(v_toRing_5569_, 1);
                    leanh::lean_inc_ref_n(v_type_5575_, 2);
                    v_u_5576_ = leanh::lean_ctor_get(v_toRing_5569_, 2);
                    leanh::lean_inc_n(v_u_5576_, 2);
                    v_ringInst_5577_ = leanh::lean_ctor_get(v_toRing_5569_, 3);
                    leanh::lean_inc_ref(v_ringInst_5577_);
                    leanh::lean_dec_ref(v_toRing_5569_);
                    v___x_5578_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__1;
                    v___x_5579_ = leanh::lean_box(0);
                    v___x_5580_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5580_, 0, v_u_5576_);
                    leanh::lean_ctor_set(v___x_5580_, 1, v___x_5579_);
                    v___x_5581_ = l_Lean_mkConst(v___x_5578_, v___x_5580_);
                    v_expectedInst_5582_ =
                        l_Lean_mkAppB(v___x_5581_, v_type_5575_, v_ringInst_5577_);
                    v___x_5583_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__3;
                    v___x_5584_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___closed__5;
                    v___x_5585_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0_spec__3(v_type_5575_, v_u_5576_, v___x_5583_, v___x_5584_, v_expectedInst_5582_, v___y_5552_, v___y_5553_, v___y_5554_, v___y_5555_, v___y_5556_, v___y_5557_, v___y_5558_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_);
                    if leanh::lean_obj_tag(v___x_5585_) == 0 {
                        v_a_5586_ = leanh::lean_ctor_get(v___x_5585_, 0);
                        leanh::lean_inc_n(v_a_5586_, 2);
                        leanh::lean_dec_ref_known(v___x_5585_, 1);
                        v___f_5587_ = leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0___lam__0 as *mut core::ffi::c_void, 2, 1);
                        leanh::lean_closure_set(v___f_5587_, 0, v_a_5586_);
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
                        if leanh::lean_obj_tag(v___x_5588_) == 0 {
                            v_isSharedCheck_5595_ =
                                (!leanh::lean_is_exclusive(v___x_5588_)) as u8;
                            if v_isSharedCheck_5595_ == 0 {
                                v_unused_5596_ = leanh::lean_ctor_get(v___x_5588_, 0);
                                leanh::lean_dec(v_unused_5596_);
                                v___x_5590_ = v___x_5588_;
                                v_isShared_5591_ = v_isSharedCheck_5595_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_5588_);
                                v___x_5590_ = leanh::lean_box(0);
                                v_isShared_5591_ = v_isSharedCheck_5595_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_5586_);
                            v_a_5597_ = leanh::lean_ctor_get(v___x_5588_, 0);
                            v_isSharedCheck_5604_ =
                                (!leanh::lean_is_exclusive(v___x_5588_)) as u8;
                            if v_isSharedCheck_5604_ == 0 {
                                v___x_5599_ = v___x_5588_;
                                v_isShared_5600_ = v_isSharedCheck_5604_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5597_);
                                leanh::lean_dec(v___x_5588_);
                                v___x_5599_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_5590_, 0, v_a_5586_);
                    v___x_5593_ = v___x_5590_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5594_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5594_, 0, v_a_5586_);
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
                    v_reuseFailAlloc_5603_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5603_, 0, v_a_5597_);
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
                    v_reuseFailAlloc_5612_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5612_, 0, v_a_5606_);
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
    mut v___y_5614_: *mut leanh::LeanObject,
    mut v___y_5615_: *mut leanh::LeanObject,
    mut v___y_5616_: *mut leanh::LeanObject,
    mut v___y_5617_: *mut leanh::LeanObject,
    mut v___y_5618_: *mut leanh::LeanObject,
    mut v___y_5619_: *mut leanh::LeanObject,
    mut v___y_5620_: *mut leanh::LeanObject,
    mut v___y_5621_: *mut leanh::LeanObject,
    mut v___y_5622_: *mut leanh::LeanObject,
    mut v___y_5623_: *mut leanh::LeanObject,
    mut v___y_5624_: *mut leanh::LeanObject,
    mut v___y_5625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5626_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(v___y_5614_, v___y_5615_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_, v___y_5622_, v___y_5623_, v___y_5624_);
    leanh::lean_dec(v___y_5624_);
    leanh::lean_dec_ref(v___y_5623_);
    leanh::lean_dec(v___y_5622_);
    leanh::lean_dec_ref(v___y_5621_);
    leanh::lean_dec(v___y_5620_);
    leanh::lean_dec_ref(v___y_5619_);
    leanh::lean_dec(v___y_5618_);
    leanh::lean_dec_ref(v___y_5617_);
    leanh::lean_dec(v___y_5616_);
    leanh::lean_dec(v___y_5615_);
    leanh::lean_dec(v___y_5614_);
    return v_res_5626_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_5634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5634_ = leanh::lean_unsigned_to_nat(0);
    v___x_5635_ = lean_nat_to_int(v___x_5634_);
    return v___x_5635_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(
    mut v_k_5641_: *mut leanh::LeanObject,
    mut v___y_5642_: *mut leanh::LeanObject,
    mut v___y_5643_: *mut leanh::LeanObject,
    mut v___y_5644_: *mut leanh::LeanObject,
    mut v___y_5645_: *mut leanh::LeanObject,
    mut v___y_5646_: *mut leanh::LeanObject,
    mut v___y_5647_: *mut leanh::LeanObject,
    mut v___y_5648_: *mut leanh::LeanObject,
    mut v___y_5649_: *mut leanh::LeanObject,
    mut v___y_5650_: *mut leanh::LeanObject,
    mut v___y_5651_: *mut leanh::LeanObject,
    mut v___y_5652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toRing_5656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_5659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5672_: u8 = 0;
    let mut v_ofNatInst_5674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5690_: u8 = 0;
    let mut v___x_5692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5698_: u8 = 0;
    let mut v___x_5699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5703_: u8 = 0;
    let mut v_val_5704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5708_: u8 = 0;
    let mut v_a_5709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5712_: u8 = 0;
    let mut v___x_5714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5716_: u8 = 0;
    let mut v_a_5717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5720_: u8 = 0;
    let mut v___x_5722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5723_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_5654_) == 0 {
                    v_a_5655_ = leanh::lean_ctor_get(v___x_5654_, 0);
                    leanh::lean_inc(v_a_5655_);
                    leanh::lean_dec_ref_known(v___x_5654_, 1);
                    v_toRing_5656_ = leanh::lean_ctor_get(v_a_5655_, 0);
                    leanh::lean_inc_ref(v_toRing_5656_);
                    leanh::lean_dec(v_a_5655_);
                    v_type_5657_ = leanh::lean_ctor_get(v_toRing_5656_, 1);
                    leanh::lean_inc_ref_n(v_type_5657_, 2);
                    v_u_5658_ = leanh::lean_ctor_get(v_toRing_5656_, 2);
                    leanh::lean_inc(v_u_5658_);
                    v_semiringInst_5659_ = leanh::lean_ctor_get(v_toRing_5656_, 4);
                    leanh::lean_inc_ref(v_semiringInst_5659_);
                    leanh::lean_dec_ref(v_toRing_5656_);
                    v___x_5660_ = lean_nat_abs(v_k_5641_);
                    v_n_5661_ = l_Lean_mkRawNatLit(v___x_5660_);
                    v___x_5662_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__1;
                    v___x_5663_ = leanh::lean_box(0);
                    v___x_5664_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5664_, 0, v_u_5658_);
                    leanh::lean_ctor_set(v___x_5664_, 1, v___x_5663_);
                    leanh::lean_inc_ref(v___x_5664_);
                    v___x_5665_ = l_Lean_mkConst(v___x_5662_, v___x_5664_);
                    leanh::lean_inc_ref(v_n_5661_);
                    v___x_5666_ = l_Lean_mkAppB(v___x_5665_, v_type_5657_, v_n_5661_);
                    v___x_5667_ = leanh::lean_box(0);
                    v___x_5668_ = l_Lean_Meta_synthInstance_x3f(
                        v___x_5666_,
                        v___x_5667_,
                        v___y_5649_,
                        v___y_5650_,
                        v___y_5651_,
                        v___y_5652_,
                    );
                    if leanh::lean_obj_tag(v___x_5668_) == 0 {
                        v_a_5669_ = leanh::lean_ctor_get(v___x_5668_, 0);
                        v_isSharedCheck_5708_ =
                            (!leanh::lean_is_exclusive(v___x_5668_)) as u8;
                        if v_isSharedCheck_5708_ == 0 {
                            v___x_5671_ = v___x_5668_;
                            v_isShared_5672_ = v_isSharedCheck_5708_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5669_);
                            leanh::lean_dec(v___x_5668_);
                            v___x_5671_ = leanh::lean_box(0);
                            v_isShared_5672_ = v_isSharedCheck_5708_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___x_5664_, 2);
                        leanh::lean_dec_ref(v_n_5661_);
                        leanh::lean_dec_ref(v_semiringInst_5659_);
                        leanh::lean_dec_ref(v_type_5657_);
                        v_a_5709_ = leanh::lean_ctor_get(v___x_5668_, 0);
                        v_isSharedCheck_5716_ =
                            (!leanh::lean_is_exclusive(v___x_5668_)) as u8;
                        if v_isSharedCheck_5716_ == 0 {
                            v___x_5711_ = v___x_5668_;
                            v_isShared_5712_ = v_isSharedCheck_5716_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5709_);
                            leanh::lean_dec(v___x_5668_);
                            v___x_5711_ = leanh::lean_box(0);
                            v_isShared_5712_ = v_isSharedCheck_5716_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v_a_5717_ = leanh::lean_ctor_get(v___x_5654_, 0);
                    v_isSharedCheck_5724_ = (!leanh::lean_is_exclusive(v___x_5654_)) as u8;
                    if v_isSharedCheck_5724_ == 0 {
                        v___x_5719_ = v___x_5654_;
                        v_isShared_5720_ = v_isSharedCheck_5724_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5717_);
                        leanh::lean_dec(v___x_5654_);
                        v___x_5719_ = leanh::lean_box(0);
                        v_isShared_5720_ = v_isSharedCheck_5724_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_5669_) == 1 {
                    leanh::lean_dec_ref(v_semiringInst_5659_);
                    v_val_5704_ = leanh::lean_ctor_get(v_a_5669_, 0);
                    leanh::lean_inc(v_val_5704_);
                    leanh::lean_dec_ref_known(v_a_5669_, 1);
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
                    leanh::lean_dec(v_a_5669_);
                    v___x_5705_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__5;
                    leanh::lean_inc_ref(v___x_5664_);
                    v___x_5706_ = l_Lean_mkConst(v___x_5705_, v___x_5664_);
                    leanh::lean_inc_ref(v_n_5661_);
                    leanh::lean_inc_ref(v_type_5657_);
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
                v___x_5689_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4_once), _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0___closed__4);
                v___x_5690_ = lean_int_dec_lt(v_k_5641_, v___x_5689_);
                if v___x_5690_ == 0 {
                    if v_isShared_5672_ == 0 {
                        leanh::lean_ctor_set(v___x_5671_, 0, v_n_5688_);
                        v___x_5692_ = v___x_5671_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5693_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5693_, 0, v_n_5688_);
                        v___x_5692_ = v_reuseFailAlloc_5693_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5671_);
                    v___x_5694_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0_spec__0(v___y_5675_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_, v___y_5682_, v___y_5683_, v___y_5684_, v___y_5685_);
                    if leanh::lean_obj_tag(v___x_5694_) == 0 {
                        v_a_5695_ = leanh::lean_ctor_get(v___x_5694_, 0);
                        v_isSharedCheck_5703_ =
                            (!leanh::lean_is_exclusive(v___x_5694_)) as u8;
                        if v_isSharedCheck_5703_ == 0 {
                            v___x_5697_ = v___x_5694_;
                            v_isShared_5698_ = v_isSharedCheck_5703_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5695_);
                            leanh::lean_dec(v___x_5694_);
                            v___x_5697_ = leanh::lean_box(0);
                            v_isShared_5698_ = v_isSharedCheck_5703_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_n_5688_);
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
                    leanh::lean_ctor_set(v___x_5697_, 0, v___x_5699_);
                    v___x_5701_ = v___x_5697_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5702_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5702_, 0, v___x_5699_);
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
                    v_reuseFailAlloc_5715_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5715_, 0, v_a_5709_);
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
                    v_reuseFailAlloc_5723_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5723_, 0, v_a_5717_);
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
    mut v_k_5725_: *mut leanh::LeanObject,
    mut v___y_5726_: *mut leanh::LeanObject,
    mut v___y_5727_: *mut leanh::LeanObject,
    mut v___y_5728_: *mut leanh::LeanObject,
    mut v___y_5729_: *mut leanh::LeanObject,
    mut v___y_5730_: *mut leanh::LeanObject,
    mut v___y_5731_: *mut leanh::LeanObject,
    mut v___y_5732_: *mut leanh::LeanObject,
    mut v___y_5733_: *mut leanh::LeanObject,
    mut v___y_5734_: *mut leanh::LeanObject,
    mut v___y_5735_: *mut leanh::LeanObject,
    mut v___y_5736_: *mut leanh::LeanObject,
    mut v___y_5737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5738_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v_k_5725_, v___y_5726_, v___y_5727_, v___y_5728_, v___y_5729_, v___y_5730_, v___y_5731_, v___y_5732_, v___y_5733_, v___y_5734_, v___y_5735_, v___y_5736_);
    leanh::lean_dec(v___y_5736_);
    leanh::lean_dec_ref(v___y_5735_);
    leanh::lean_dec(v___y_5734_);
    leanh::lean_dec_ref(v___y_5733_);
    leanh::lean_dec(v___y_5732_);
    leanh::lean_dec_ref(v___y_5731_);
    leanh::lean_dec(v___y_5730_);
    leanh::lean_dec_ref(v___y_5729_);
    leanh::lean_dec(v___y_5728_);
    leanh::lean_dec(v___y_5727_);
    leanh::lean_dec(v___y_5726_);
    leanh::lean_dec(v_k_5725_);
    return v_res_5738_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___lam__0(
    mut v_a_5739_: *mut leanh::LeanObject,
    mut v_s_5740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toRing_5741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_5742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_5743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_5744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_5745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_5746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_5747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_5748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_5749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_5750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_5751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_5752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_5753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_5754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recheck_5755_: u8 = 0;
    let mut v_invSet_5756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_5757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_5758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_5759_: u8 = 0;
    let mut v___x_5761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5762_: u8 = 0;
    let mut v_id_5763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_5766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_5767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_5768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_5769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_5770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_5771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_5772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_5773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_5774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_5775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_5776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_5777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_5778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5781_: u8 = 0;
    let mut v___x_5782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5789_: u8 = 0;
    let mut v_unused_5790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5791_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_5741_ = leanh::lean_ctor_get(v_s_5740_, 0);
                v_invFn_x3f_5742_ = leanh::lean_ctor_get(v_s_5740_, 1);
                v_semiringId_x3f_5743_ = leanh::lean_ctor_get(v_s_5740_, 2);
                v_commSemiringInst_5744_ = leanh::lean_ctor_get(v_s_5740_, 3);
                v_commRingInst_5745_ = leanh::lean_ctor_get(v_s_5740_, 4);
                v_noZeroDivInst_x3f_5746_ = leanh::lean_ctor_get(v_s_5740_, 5);
                v_fieldInst_x3f_5747_ = leanh::lean_ctor_get(v_s_5740_, 6);
                v_powIdentityInst_x3f_5748_ = leanh::lean_ctor_get(v_s_5740_, 7);
                v_denoteEntries_5749_ = leanh::lean_ctor_get(v_s_5740_, 8);
                v_nextId_5750_ = leanh::lean_ctor_get(v_s_5740_, 9);
                v_steps_5751_ = leanh::lean_ctor_get(v_s_5740_, 10);
                v_queue_5752_ = leanh::lean_ctor_get(v_s_5740_, 11);
                v_basis_5753_ = leanh::lean_ctor_get(v_s_5740_, 12);
                v_diseqs_5754_ = leanh::lean_ctor_get(v_s_5740_, 13);
                v_recheck_5755_ = leanh::lean_ctor_get_uint8(
                    v_s_5740_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                );
                v_invSet_5756_ = leanh::lean_ctor_get(v_s_5740_, 14);
                v_powIdentityVarCount_5757_ = leanh::lean_ctor_get(v_s_5740_, 15);
                v_numEq0_x3f_5758_ = leanh::lean_ctor_get(v_s_5740_, 16);
                v_numEq0Updated_5759_ = leanh::lean_ctor_get_uint8(
                    v_s_5740_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_5791_ = (!leanh::lean_is_exclusive(v_s_5740_)) as u8;
                if v_isSharedCheck_5791_ == 0 {
                    v___x_5761_ = v_s_5740_;
                    v_isShared_5762_ = v_isSharedCheck_5791_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_numEq0_x3f_5758_);
                    leanh::lean_inc(v_powIdentityVarCount_5757_);
                    leanh::lean_inc(v_invSet_5756_);
                    leanh::lean_inc(v_diseqs_5754_);
                    leanh::lean_inc(v_basis_5753_);
                    leanh::lean_inc(v_queue_5752_);
                    leanh::lean_inc(v_steps_5751_);
                    leanh::lean_inc(v_nextId_5750_);
                    leanh::lean_inc(v_denoteEntries_5749_);
                    leanh::lean_inc(v_powIdentityInst_x3f_5748_);
                    leanh::lean_inc(v_fieldInst_x3f_5747_);
                    leanh::lean_inc(v_noZeroDivInst_x3f_5746_);
                    leanh::lean_inc(v_commRingInst_5745_);
                    leanh::lean_inc(v_commSemiringInst_5744_);
                    leanh::lean_inc(v_semiringId_x3f_5743_);
                    leanh::lean_inc(v_invFn_x3f_5742_);
                    leanh::lean_inc(v_toRing_5741_);
                    leanh::lean_dec(v_s_5740_);
                    v___x_5761_ = leanh::lean_box(0);
                    v_isShared_5762_ = v_isSharedCheck_5791_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_id_5763_ = leanh::lean_ctor_get(v_toRing_5741_, 0);
                v_type_5764_ = leanh::lean_ctor_get(v_toRing_5741_, 1);
                v_u_5765_ = leanh::lean_ctor_get(v_toRing_5741_, 2);
                v_ringInst_5766_ = leanh::lean_ctor_get(v_toRing_5741_, 3);
                v_semiringInst_5767_ = leanh::lean_ctor_get(v_toRing_5741_, 4);
                v_charInst_x3f_5768_ = leanh::lean_ctor_get(v_toRing_5741_, 5);
                v_addFn_x3f_5769_ = leanh::lean_ctor_get(v_toRing_5741_, 6);
                v_mulFn_x3f_5770_ = leanh::lean_ctor_get(v_toRing_5741_, 7);
                v_subFn_x3f_5771_ = leanh::lean_ctor_get(v_toRing_5741_, 8);
                v_negFn_x3f_5772_ = leanh::lean_ctor_get(v_toRing_5741_, 9);
                v_intCastFn_x3f_5773_ = leanh::lean_ctor_get(v_toRing_5741_, 11);
                v_natCastFn_x3f_5774_ = leanh::lean_ctor_get(v_toRing_5741_, 12);
                v_one_x3f_5775_ = leanh::lean_ctor_get(v_toRing_5741_, 13);
                v_vars_5776_ = leanh::lean_ctor_get(v_toRing_5741_, 14);
                v_varMap_5777_ = leanh::lean_ctor_get(v_toRing_5741_, 15);
                v_denote_5778_ = leanh::lean_ctor_get(v_toRing_5741_, 16);
                v_isSharedCheck_5789_ = (!leanh::lean_is_exclusive(v_toRing_5741_)) as u8;
                if v_isSharedCheck_5789_ == 0 {
                    v_unused_5790_ = leanh::lean_ctor_get(v_toRing_5741_, 10);
                    leanh::lean_dec(v_unused_5790_);
                    v___x_5780_ = v_toRing_5741_;
                    v_isShared_5781_ = v_isSharedCheck_5789_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_denote_5778_);
                    leanh::lean_inc(v_varMap_5777_);
                    leanh::lean_inc(v_vars_5776_);
                    leanh::lean_inc(v_one_x3f_5775_);
                    leanh::lean_inc(v_natCastFn_x3f_5774_);
                    leanh::lean_inc(v_intCastFn_x3f_5773_);
                    leanh::lean_inc(v_negFn_x3f_5772_);
                    leanh::lean_inc(v_subFn_x3f_5771_);
                    leanh::lean_inc(v_mulFn_x3f_5770_);
                    leanh::lean_inc(v_addFn_x3f_5769_);
                    leanh::lean_inc(v_charInst_x3f_5768_);
                    leanh::lean_inc(v_semiringInst_5767_);
                    leanh::lean_inc(v_ringInst_5766_);
                    leanh::lean_inc(v_u_5765_);
                    leanh::lean_inc(v_type_5764_);
                    leanh::lean_inc(v_id_5763_);
                    leanh::lean_dec(v_toRing_5741_);
                    v___x_5780_ = leanh::lean_box(0);
                    v_isShared_5781_ = v_isSharedCheck_5789_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5782_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5782_, 0, v_a_5739_);
                if v_isShared_5781_ == 0 {
                    leanh::lean_ctor_set(v___x_5780_, 10, v___x_5782_);
                    v___x_5784_ = v___x_5780_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5788_ = leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 0, v_id_5763_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 1, v_type_5764_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 2, v_u_5765_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 3, v_ringInst_5766_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 4, v_semiringInst_5767_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 5, v_charInst_x3f_5768_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 6, v_addFn_x3f_5769_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 7, v_mulFn_x3f_5770_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 8, v_subFn_x3f_5771_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 9, v_negFn_x3f_5772_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 10, v___x_5782_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 11, v_intCastFn_x3f_5773_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 12, v_natCastFn_x3f_5774_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 13, v_one_x3f_5775_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 14, v_vars_5776_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 15, v_varMap_5777_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 16, v_denote_5778_);
                    v___x_5784_ = v_reuseFailAlloc_5788_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5762_ == 0 {
                    leanh::lean_ctor_set(v___x_5761_, 0, v___x_5784_);
                    v___x_5786_ = v___x_5761_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5787_ = leanh::lean_alloc_ctor(0, 17, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 0, v___x_5784_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 1, v_invFn_x3f_5742_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 2, v_semiringId_x3f_5743_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5787_,
                        3,
                        v_commSemiringInst_5744_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 4, v_commRingInst_5745_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5787_,
                        5,
                        v_noZeroDivInst_x3f_5746_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 6, v_fieldInst_x3f_5747_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5787_,
                        7,
                        v_powIdentityInst_x3f_5748_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 8, v_denoteEntries_5749_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 9, v_nextId_5750_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 10, v_steps_5751_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 11, v_queue_5752_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 12, v_basis_5753_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 13, v_diseqs_5754_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 14, v_invSet_5756_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5787_,
                        15,
                        v_powIdentityVarCount_5757_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 16, v_numEq0_x3f_5758_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5787_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                        v_recheck_5755_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5787_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 17 + 1) as u32,
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
-> *mut leanh::LeanObject {
    let mut v___x_5795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5795_ = leanh::lean_unsigned_to_nat(0);
    v___x_5796_ = l_Lean_Level_ofNat(v___x_5795_);
    return v___x_5796_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(
    mut v_u_5807_: *mut leanh::LeanObject,
    mut v_type_5808_: *mut leanh::LeanObject,
    mut v_semiringInst_5809_: *mut leanh::LeanObject,
    mut v___y_5810_: *mut leanh::LeanObject,
    mut v___y_5811_: *mut leanh::LeanObject,
    mut v___y_5812_: *mut leanh::LeanObject,
    mut v___y_5813_: *mut leanh::LeanObject,
    mut v___y_5814_: *mut leanh::LeanObject,
    mut v___y_5815_: *mut leanh::LeanObject,
    mut v___y_5816_: *mut leanh::LeanObject,
    mut v___y_5817_: *mut leanh::LeanObject,
    mut v___y_5818_: *mut leanh::LeanObject,
    mut v___y_5819_: *mut leanh::LeanObject,
    mut v___y_5820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inst_x27_5835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5842_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                v___x_5822_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__1;
                v___x_5823_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2_once), _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__2);
                v___x_5824_ = leanh::lean_box(0);
                leanh::lean_inc(v_u_5807_);
                v___x_5825_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5825_, 0, v_u_5807_);
                leanh::lean_ctor_set(v___x_5825_, 1, v___x_5824_);
                leanh::lean_inc_ref(v___x_5825_);
                v___x_5826_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5826_, 0, v___x_5823_);
                leanh::lean_ctor_set(v___x_5826_, 1, v___x_5825_);
                v___x_5827_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5827_, 0, v_u_5807_);
                leanh::lean_ctor_set(v___x_5827_, 1, v___x_5826_);
                leanh::lean_inc_ref(v___x_5827_);
                v___x_5828_ = l_Lean_mkConst(v___x_5822_, v___x_5827_);
                v___x_5829_ = l_Lean_Nat_mkType;
                leanh::lean_inc_ref_n(v_type_5808_, 2);
                v___x_5830_ = l_Lean_mkApp3(v___x_5828_, v_type_5808_, v___x_5829_, v_type_5808_);
                v___x_5831_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v___x_5830_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_);
                if leanh::lean_obj_tag(v___x_5831_) == 0 {
                    v_a_5832_ = leanh::lean_ctor_get(v___x_5831_, 0);
                    leanh::lean_inc_n(v_a_5832_, 2);
                    leanh::lean_dec_ref_known(v___x_5831_, 1);
                    v___x_5833_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6___closed__4;
                    v___x_5834_ = l_Lean_mkConst(v___x_5833_, v___x_5825_);
                    leanh::lean_inc_ref(v_type_5808_);
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
                    if leanh::lean_obj_tag(v___x_5837_) == 0 {
                        leanh::lean_dec_ref_known(v___x_5837_, 1);
                        v___x_5838_ = l_Lean_mkConst(v___x_5836_, v___x_5827_);
                        leanh::lean_inc_ref(v_type_5808_);
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
                        if leanh::lean_obj_tag(v___x_5840_) == 0 {
                            v_a_5841_ = leanh::lean_ctor_get(v___x_5840_, 0);
                            leanh::lean_inc(v_a_5841_);
                            leanh::lean_dec_ref_known(v___x_5840_, 1);
                            v___x_5842_ =
                                l_Lean_Meta_Sym_shareCommon___redArg(v_a_5841_, v___y_5816_);
                            return v___x_5842_;
                        } else {
                            return v___x_5840_;
                        }
                    } else {
                        leanh::lean_dec(v_a_5832_);
                        leanh::lean_dec_ref_known(v___x_5827_, 2);
                        leanh::lean_dec_ref(v_type_5808_);
                        v_a_5843_ = leanh::lean_ctor_get(v___x_5837_, 0);
                        v_isSharedCheck_5850_ =
                            (!leanh::lean_is_exclusive(v___x_5837_)) as u8;
                        if v_isSharedCheck_5850_ == 0 {
                            v___x_5845_ = v___x_5837_;
                            v_isShared_5846_ = v_isSharedCheck_5850_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5843_);
                            leanh::lean_dec(v___x_5837_);
                            v___x_5845_ = leanh::lean_box(0);
                            v_isShared_5846_ = v_isSharedCheck_5850_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_5827_, 2);
                    leanh::lean_dec_ref_known(v___x_5825_, 2);
                    leanh::lean_dec_ref(v_semiringInst_5809_);
                    leanh::lean_dec_ref(v_type_5808_);
                    return v___x_5831_;
                }
            }
            1 => {
                if v_isShared_5846_ == 0 {
                    v___x_5848_ = v___x_5845_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5849_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5849_, 0, v_a_5843_);
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
    mut v_u_5851_: *mut leanh::LeanObject,
    mut v_type_5852_: *mut leanh::LeanObject,
    mut v_semiringInst_5853_: *mut leanh::LeanObject,
    mut v___y_5854_: *mut leanh::LeanObject,
    mut v___y_5855_: *mut leanh::LeanObject,
    mut v___y_5856_: *mut leanh::LeanObject,
    mut v___y_5857_: *mut leanh::LeanObject,
    mut v___y_5858_: *mut leanh::LeanObject,
    mut v___y_5859_: *mut leanh::LeanObject,
    mut v___y_5860_: *mut leanh::LeanObject,
    mut v___y_5861_: *mut leanh::LeanObject,
    mut v___y_5862_: *mut leanh::LeanObject,
    mut v___y_5863_: *mut leanh::LeanObject,
    mut v___y_5864_: *mut leanh::LeanObject,
    mut v___y_5865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5866_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(v_u_5851_, v_type_5852_, v_semiringInst_5853_, v___y_5854_, v___y_5855_, v___y_5856_, v___y_5857_, v___y_5858_, v___y_5859_, v___y_5860_, v___y_5861_, v___y_5862_, v___y_5863_, v___y_5864_);
    leanh::lean_dec(v___y_5864_);
    leanh::lean_dec_ref(v___y_5863_);
    leanh::lean_dec(v___y_5862_);
    leanh::lean_dec_ref(v___y_5861_);
    leanh::lean_dec(v___y_5860_);
    leanh::lean_dec_ref(v___y_5859_);
    leanh::lean_dec(v___y_5858_);
    leanh::lean_dec_ref(v___y_5857_);
    leanh::lean_dec(v___y_5856_);
    leanh::lean_dec(v___y_5855_);
    leanh::lean_dec(v___y_5854_);
    return v_res_5866_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(
    mut v___y_5867_: *mut leanh::LeanObject,
    mut v___y_5868_: *mut leanh::LeanObject,
    mut v___y_5869_: *mut leanh::LeanObject,
    mut v___y_5870_: *mut leanh::LeanObject,
    mut v___y_5871_: *mut leanh::LeanObject,
    mut v___y_5872_: *mut leanh::LeanObject,
    mut v___y_5873_: *mut leanh::LeanObject,
    mut v___y_5874_: *mut leanh::LeanObject,
    mut v___y_5875_: *mut leanh::LeanObject,
    mut v___y_5876_: *mut leanh::LeanObject,
    mut v___y_5877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5883_: u8 = 0;
    let mut v_toRing_5884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_5885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_5892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5899_: u8 = 0;
    let mut v___x_5901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5903_: u8 = 0;
    let mut v_unused_5904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5908_: u8 = 0;
    let mut v___x_5910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5912_: u8 = 0;
    let mut v_isSharedCheck_5913_: u8 = 0;
    let mut v_a_5914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5917_: u8 = 0;
    let mut v___x_5919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5920_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_5879_) == 0 {
                    v_a_5880_ = leanh::lean_ctor_get(v___x_5879_, 0);
                    v_isSharedCheck_5913_ = (!leanh::lean_is_exclusive(v___x_5879_)) as u8;
                    if v_isSharedCheck_5913_ == 0 {
                        v___x_5882_ = v___x_5879_;
                        v_isShared_5883_ = v_isSharedCheck_5913_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5880_);
                        leanh::lean_dec(v___x_5879_);
                        v___x_5882_ = leanh::lean_box(0);
                        v_isShared_5883_ = v_isSharedCheck_5913_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5914_ = leanh::lean_ctor_get(v___x_5879_, 0);
                    v_isSharedCheck_5921_ = (!leanh::lean_is_exclusive(v___x_5879_)) as u8;
                    if v_isSharedCheck_5921_ == 0 {
                        v___x_5916_ = v___x_5879_;
                        v_isShared_5917_ = v_isSharedCheck_5921_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5914_);
                        leanh::lean_dec(v___x_5879_);
                        v___x_5916_ = leanh::lean_box(0);
                        v_isShared_5917_ = v_isSharedCheck_5921_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_toRing_5884_ = leanh::lean_ctor_get(v_a_5880_, 0);
                leanh::lean_inc_ref(v_toRing_5884_);
                leanh::lean_dec(v_a_5880_);
                v_powFn_x3f_5885_ = leanh::lean_ctor_get(v_toRing_5884_, 10);
                if leanh::lean_obj_tag(v_powFn_x3f_5885_) == 1 {
                    leanh::lean_inc_ref(v_powFn_x3f_5885_);
                    leanh::lean_dec_ref(v_toRing_5884_);
                    v_val_5886_ = leanh::lean_ctor_get(v_powFn_x3f_5885_, 0);
                    leanh::lean_inc(v_val_5886_);
                    leanh::lean_dec_ref_known(v_powFn_x3f_5885_, 1);
                    if v_isShared_5883_ == 0 {
                        leanh::lean_ctor_set(v___x_5882_, 0, v_val_5886_);
                        v___x_5888_ = v___x_5882_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5889_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5889_, 0, v_val_5886_);
                        v___x_5888_ = v_reuseFailAlloc_5889_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5882_);
                    v_type_5890_ = leanh::lean_ctor_get(v_toRing_5884_, 1);
                    leanh::lean_inc_ref(v_type_5890_);
                    v_u_5891_ = leanh::lean_ctor_get(v_toRing_5884_, 2);
                    leanh::lean_inc(v_u_5891_);
                    v_semiringInst_5892_ = leanh::lean_ctor_get(v_toRing_5884_, 4);
                    leanh::lean_inc_ref(v_semiringInst_5892_);
                    leanh::lean_dec_ref(v_toRing_5884_);
                    v___x_5893_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4_spec__6(v_u_5891_, v_type_5890_, v_semiringInst_5892_, v___y_5867_, v___y_5868_, v___y_5869_, v___y_5870_, v___y_5871_, v___y_5872_, v___y_5873_, v___y_5874_, v___y_5875_, v___y_5876_, v___y_5877_);
                    if leanh::lean_obj_tag(v___x_5893_) == 0 {
                        v_a_5894_ = leanh::lean_ctor_get(v___x_5893_, 0);
                        leanh::lean_inc_n(v_a_5894_, 2);
                        leanh::lean_dec_ref_known(v___x_5893_, 1);
                        v___f_5895_ = leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4___lam__0 as *mut core::ffi::c_void, 2, 1);
                        leanh::lean_closure_set(v___f_5895_, 0, v_a_5894_);
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
                        if leanh::lean_obj_tag(v___x_5896_) == 0 {
                            v_isSharedCheck_5903_ =
                                (!leanh::lean_is_exclusive(v___x_5896_)) as u8;
                            if v_isSharedCheck_5903_ == 0 {
                                v_unused_5904_ = leanh::lean_ctor_get(v___x_5896_, 0);
                                leanh::lean_dec(v_unused_5904_);
                                v___x_5898_ = v___x_5896_;
                                v_isShared_5899_ = v_isSharedCheck_5903_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_5896_);
                                v___x_5898_ = leanh::lean_box(0);
                                v_isShared_5899_ = v_isSharedCheck_5903_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_5894_);
                            v_a_5905_ = leanh::lean_ctor_get(v___x_5896_, 0);
                            v_isSharedCheck_5912_ =
                                (!leanh::lean_is_exclusive(v___x_5896_)) as u8;
                            if v_isSharedCheck_5912_ == 0 {
                                v___x_5907_ = v___x_5896_;
                                v_isShared_5908_ = v_isSharedCheck_5912_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5905_);
                                leanh::lean_dec(v___x_5896_);
                                v___x_5907_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_5898_, 0, v_a_5894_);
                    v___x_5901_ = v___x_5898_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5902_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5902_, 0, v_a_5894_);
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
                    v_reuseFailAlloc_5911_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5911_, 0, v_a_5905_);
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
                    v_reuseFailAlloc_5920_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5920_, 0, v_a_5914_);
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
    mut v___y_5922_: *mut leanh::LeanObject,
    mut v___y_5923_: *mut leanh::LeanObject,
    mut v___y_5924_: *mut leanh::LeanObject,
    mut v___y_5925_: *mut leanh::LeanObject,
    mut v___y_5926_: *mut leanh::LeanObject,
    mut v___y_5927_: *mut leanh::LeanObject,
    mut v___y_5928_: *mut leanh::LeanObject,
    mut v___y_5929_: *mut leanh::LeanObject,
    mut v___y_5930_: *mut leanh::LeanObject,
    mut v___y_5931_: *mut leanh::LeanObject,
    mut v___y_5932_: *mut leanh::LeanObject,
    mut v___y_5933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5934_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(v___y_5922_, v___y_5923_, v___y_5924_, v___y_5925_, v___y_5926_, v___y_5927_, v___y_5928_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_);
    leanh::lean_dec(v___y_5932_);
    leanh::lean_dec_ref(v___y_5931_);
    leanh::lean_dec(v___y_5930_);
    leanh::lean_dec_ref(v___y_5929_);
    leanh::lean_dec(v___y_5928_);
    leanh::lean_dec_ref(v___y_5927_);
    leanh::lean_dec(v___y_5926_);
    leanh::lean_dec_ref(v___y_5925_);
    leanh::lean_dec(v___y_5924_);
    leanh::lean_dec(v___y_5923_);
    leanh::lean_dec(v___y_5922_);
    return v_res_5934_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5938_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__2;
    v___x_5939_ = leanh::lean_unsigned_to_nat(39);
    v___x_5940_ = leanh::lean_unsigned_to_nat(159);
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
    mut v_a_5944_: *mut leanh::LeanObject,
    mut v_a_5945_: *mut leanh::LeanObject,
    mut v_a_5946_: *mut leanh::LeanObject,
    mut v_a_5947_: *mut leanh::LeanObject,
    mut v_a_5948_: *mut leanh::LeanObject,
    mut v_a_5949_: *mut leanh::LeanObject,
    mut v_a_5950_: *mut leanh::LeanObject,
    mut v_a_5951_: *mut leanh::LeanObject,
    mut v_a_5952_: *mut leanh::LeanObject,
    mut v_a_5953_: *mut leanh::LeanObject,
    mut v_a_5954_: *mut leanh::LeanObject,
    mut v_a_5955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_5957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_5962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5969_: u8 = 0;
    let mut v___y_5971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSemiring_5976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_5977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5980_: u8 = 0;
    let mut v___x_5981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5983_: u8 = 0;
    let mut v_a_5984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5987_: u8 = 0;
    let mut v___x_5989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5991_: u8 = 0;
    let mut v_a_5992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6002_: u8 = 0;
    let mut v___x_6003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6007_: u8 = 0;
    let mut v_a_6008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_6009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6018_: u8 = 0;
    let mut v___x_6019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6023_: u8 = 0;
    let mut v_a_6024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6032_: u8 = 0;
    let mut v___x_6033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6038_: u8 = 0;
    let mut v___x_6039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_a_5944_) {
                0 => {
                    v_k_5957_ = leanh::lean_ctor_get(v_a_5944_, 0);
                    leanh::lean_inc(v_k_5957_);
                    leanh::lean_dec_ref_known(v_a_5944_, 1);
                    v___x_5958_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v_k_5957_, v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_);
                    leanh::lean_dec(v_k_5957_);
                    return v___x_5958_;
                }
                1 => {
                    v_k_5959_ = leanh::lean_ctor_get(v_a_5944_, 0);
                    leanh::lean_inc(v_k_5959_);
                    leanh::lean_dec_ref_known(v_a_5944_, 1);
                    v___x_5960_ = lean_nat_to_int(v_k_5959_);
                    v___x_5961_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__0(v___x_5960_, v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_);
                    leanh::lean_dec(v___x_5960_);
                    return v___x_5961_;
                }
                3 => {
                    v_i_5962_ = leanh::lean_ctor_get(v_a_5944_, 0);
                    leanh::lean_inc(v_i_5962_);
                    leanh::lean_dec_ref_known(v_a_5944_, 1);
                    v___x_5963_ = l_Lean_Meta_Grind_Arith_CommRing_getToQFn(
                        v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_,
                        v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_,
                    );
                    if leanh::lean_obj_tag(v___x_5963_) == 0 {
                        v_a_5964_ = leanh::lean_ctor_get(v___x_5963_, 0);
                        leanh::lean_inc(v_a_5964_);
                        leanh::lean_dec_ref_known(v___x_5963_, 1);
                        v___x_5965_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(
                            v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_,
                            v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_,
                        );
                        if leanh::lean_obj_tag(v___x_5965_) == 0 {
                            v_a_5966_ = leanh::lean_ctor_get(v___x_5965_, 0);
                            v_isSharedCheck_5983_ =
                                (!leanh::lean_is_exclusive(v___x_5965_)) as u8;
                            if v_isSharedCheck_5983_ == 0 {
                                v___x_5968_ = v___x_5965_;
                                v_isShared_5969_ = v_isSharedCheck_5983_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5966_);
                                leanh::lean_dec(v___x_5965_);
                                v___x_5968_ = leanh::lean_box(0);
                                v_isShared_5969_ = v_isSharedCheck_5983_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_5964_);
                            leanh::lean_dec(v_i_5962_);
                            v_a_5984_ = leanh::lean_ctor_get(v___x_5965_, 0);
                            v_isSharedCheck_5991_ =
                                (!leanh::lean_is_exclusive(v___x_5965_)) as u8;
                            if v_isSharedCheck_5991_ == 0 {
                                v___x_5986_ = v___x_5965_;
                                v_isShared_5987_ = v_isSharedCheck_5991_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5984_);
                                leanh::lean_dec(v___x_5965_);
                                v___x_5986_ = leanh::lean_box(0);
                                v_isShared_5987_ = v_isSharedCheck_5991_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_i_5962_);
                        return v___x_5963_;
                    }
                }
                5 => {
                    v_a_5992_ = leanh::lean_ctor_get(v_a_5944_, 0);
                    leanh::lean_inc_ref(v_a_5992_);
                    v_b_5993_ = leanh::lean_ctor_get(v_a_5944_, 1);
                    leanh::lean_inc_ref(v_b_5993_);
                    leanh::lean_dec_ref_known(v_a_5944_, 2);
                    v___x_5994_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2(v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_);
                    if leanh::lean_obj_tag(v___x_5994_) == 0 {
                        v_a_5995_ = leanh::lean_ctor_get(v___x_5994_, 0);
                        leanh::lean_inc(v_a_5995_);
                        leanh::lean_dec_ref_known(v___x_5994_, 1);
                        v___x_5996_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_5992_, v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_);
                        if leanh::lean_obj_tag(v___x_5996_) == 0 {
                            v_a_5997_ = leanh::lean_ctor_get(v___x_5996_, 0);
                            leanh::lean_inc(v_a_5997_);
                            leanh::lean_dec_ref_known(v___x_5996_, 1);
                            v___x_5998_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_b_5993_, v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_);
                            if leanh::lean_obj_tag(v___x_5998_) == 0 {
                                v_a_5999_ = leanh::lean_ctor_get(v___x_5998_, 0);
                                v_isSharedCheck_6007_ =
                                    (!leanh::lean_is_exclusive(v___x_5998_)) as u8;
                                if v_isSharedCheck_6007_ == 0 {
                                    v___x_6001_ = v___x_5998_;
                                    v_isShared_6002_ = v_isSharedCheck_6007_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5999_);
                                    leanh::lean_dec(v___x_5998_);
                                    v___x_6001_ = leanh::lean_box(0);
                                    v_isShared_6002_ = v_isSharedCheck_6007_;
                                    state = 6;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_5997_);
                                leanh::lean_dec(v_a_5995_);
                                return v___x_5998_;
                            }
                        } else {
                            leanh::lean_dec(v_a_5995_);
                            leanh::lean_dec_ref(v_b_5993_);
                            return v___x_5996_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_5993_);
                        leanh::lean_dec_ref(v_a_5992_);
                        return v___x_5994_;
                    }
                }
                7 => {
                    v_a_6008_ = leanh::lean_ctor_get(v_a_5944_, 0);
                    leanh::lean_inc_ref(v_a_6008_);
                    v_b_6009_ = leanh::lean_ctor_get(v_a_5944_, 1);
                    leanh::lean_inc_ref(v_b_6009_);
                    leanh::lean_dec_ref_known(v_a_5944_, 2);
                    v___x_6010_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__3(v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_);
                    if leanh::lean_obj_tag(v___x_6010_) == 0 {
                        v_a_6011_ = leanh::lean_ctor_get(v___x_6010_, 0);
                        leanh::lean_inc(v_a_6011_);
                        leanh::lean_dec_ref_known(v___x_6010_, 1);
                        v___x_6012_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_6008_, v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_);
                        if leanh::lean_obj_tag(v___x_6012_) == 0 {
                            v_a_6013_ = leanh::lean_ctor_get(v___x_6012_, 0);
                            leanh::lean_inc(v_a_6013_);
                            leanh::lean_dec_ref_known(v___x_6012_, 1);
                            v___x_6014_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_b_6009_, v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_);
                            if leanh::lean_obj_tag(v___x_6014_) == 0 {
                                v_a_6015_ = leanh::lean_ctor_get(v___x_6014_, 0);
                                v_isSharedCheck_6023_ =
                                    (!leanh::lean_is_exclusive(v___x_6014_)) as u8;
                                if v_isSharedCheck_6023_ == 0 {
                                    v___x_6017_ = v___x_6014_;
                                    v_isShared_6018_ = v_isSharedCheck_6023_;
                                    state = 8;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6015_);
                                    leanh::lean_dec(v___x_6014_);
                                    v___x_6017_ = leanh::lean_box(0);
                                    v_isShared_6018_ = v_isSharedCheck_6023_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_6013_);
                                leanh::lean_dec(v_a_6011_);
                                return v___x_6014_;
                            }
                        } else {
                            leanh::lean_dec(v_a_6011_);
                            leanh::lean_dec_ref(v_b_6009_);
                            return v___x_6012_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_6009_);
                        leanh::lean_dec_ref(v_a_6008_);
                        return v___x_6010_;
                    }
                }
                8 => {
                    v_a_6024_ = leanh::lean_ctor_get(v_a_5944_, 0);
                    leanh::lean_inc_ref(v_a_6024_);
                    v_k_6025_ = leanh::lean_ctor_get(v_a_5944_, 1);
                    leanh::lean_inc(v_k_6025_);
                    leanh::lean_dec_ref_known(v_a_5944_, 2);
                    v___x_6026_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__4(v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_);
                    if leanh::lean_obj_tag(v___x_6026_) == 0 {
                        v_a_6027_ = leanh::lean_ctor_get(v___x_6026_, 0);
                        leanh::lean_inc(v_a_6027_);
                        leanh::lean_dec_ref_known(v___x_6026_, 1);
                        v___x_6028_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_6024_, v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_);
                        if leanh::lean_obj_tag(v___x_6028_) == 0 {
                            v_a_6029_ = leanh::lean_ctor_get(v___x_6028_, 0);
                            v_isSharedCheck_6038_ =
                                (!leanh::lean_is_exclusive(v___x_6028_)) as u8;
                            if v_isSharedCheck_6038_ == 0 {
                                v___x_6031_ = v___x_6028_;
                                v_isShared_6032_ = v_isSharedCheck_6038_;
                                state = 10;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6029_);
                                leanh::lean_dec(v___x_6028_);
                                v___x_6031_ = leanh::lean_box(0);
                                v_isShared_6032_ = v_isSharedCheck_6038_;
                                state = 10;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_6027_);
                            leanh::lean_dec(v_k_6025_);
                            return v___x_6028_;
                        }
                    } else {
                        leanh::lean_dec(v_k_6025_);
                        leanh::lean_dec_ref(v_a_6024_);
                        return v___x_6026_;
                    }
                }
                _ => {
                    leanh::lean_dec_ref(v_a_5944_);
                    v___x_6039_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go___closed__3);
                    v___x_6040_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__5(v___x_6039_, v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_, v_a_5952_, v_a_5953_, v_a_5954_, v_a_5955_);
                    return v___x_6040_;
                }
            },
            1 => {
                v_toSemiring_5976_ = leanh::lean_ctor_get(v_a_5966_, 0);
                leanh::lean_inc_ref(v_toSemiring_5976_);
                leanh::lean_dec(v_a_5966_);
                v_vars_5977_ = leanh::lean_ctor_get(v_toSemiring_5976_, 9);
                leanh::lean_inc_ref(v_vars_5977_);
                leanh::lean_dec_ref(v_toSemiring_5976_);
                v_size_5978_ = leanh::lean_ctor_get(v_vars_5977_, 2);
                v___x_5979_ = l_Lean_instInhabitedExpr;
                v___x_5980_ = lean_nat_dec_lt(v_i_5962_, v_size_5978_);
                if v___x_5980_ == 0 {
                    leanh::lean_dec_ref(v_vars_5977_);
                    leanh::lean_dec(v_i_5962_);
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
                    leanh::lean_dec(v_i_5962_);
                    leanh::lean_dec_ref(v_vars_5977_);
                    v___y_5971_ = v___x_5982_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5972_ = l_Lean_Expr_app___override(v_a_5964_, v___y_5971_);
                if v_isShared_5969_ == 0 {
                    leanh::lean_ctor_set(v___x_5968_, 0, v___x_5972_);
                    v___x_5974_ = v___x_5968_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5975_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5975_, 0, v___x_5972_);
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
                    v_reuseFailAlloc_5990_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5990_, 0, v_a_5984_);
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
                    leanh::lean_ctor_set(v___x_6001_, 0, v___x_6003_);
                    v___x_6005_ = v___x_6001_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6006_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6006_, 0, v___x_6003_);
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
                    leanh::lean_ctor_set(v___x_6017_, 0, v___x_6019_);
                    v___x_6021_ = v___x_6017_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6022_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6022_, 0, v___x_6019_);
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
                    leanh::lean_ctor_set(v___x_6031_, 0, v___x_6034_);
                    v___x_6036_ = v___x_6031_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6037_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6037_, 0, v___x_6034_);
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
    mut v_a_6041_: *mut leanh::LeanObject,
    mut v_a_6042_: *mut leanh::LeanObject,
    mut v_a_6043_: *mut leanh::LeanObject,
    mut v_a_6044_: *mut leanh::LeanObject,
    mut v_a_6045_: *mut leanh::LeanObject,
    mut v_a_6046_: *mut leanh::LeanObject,
    mut v_a_6047_: *mut leanh::LeanObject,
    mut v_a_6048_: *mut leanh::LeanObject,
    mut v_a_6049_: *mut leanh::LeanObject,
    mut v_a_6050_: *mut leanh::LeanObject,
    mut v_a_6051_: *mut leanh::LeanObject,
    mut v_a_6052_: *mut leanh::LeanObject,
    mut v_a_6053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6054_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_a_6041_, v_a_6042_, v_a_6043_, v_a_6044_, v_a_6045_, v_a_6046_, v_a_6047_, v_a_6048_, v_a_6049_, v_a_6050_, v_a_6051_, v_a_6052_);
    leanh::lean_dec(v_a_6052_);
    leanh::lean_dec_ref(v_a_6051_);
    leanh::lean_dec(v_a_6050_);
    leanh::lean_dec_ref(v_a_6049_);
    leanh::lean_dec(v_a_6048_);
    leanh::lean_dec_ref(v_a_6047_);
    leanh::lean_dec(v_a_6046_);
    leanh::lean_dec_ref(v_a_6045_);
    leanh::lean_dec(v_a_6044_);
    leanh::lean_dec(v_a_6043_);
    leanh::lean_dec(v_a_6042_);
    return v_res_6054_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6(
    mut v_type_6055_: *mut leanh::LeanObject,
    mut v___y_6056_: *mut leanh::LeanObject,
    mut v___y_6057_: *mut leanh::LeanObject,
    mut v___y_6058_: *mut leanh::LeanObject,
    mut v___y_6059_: *mut leanh::LeanObject,
    mut v___y_6060_: *mut leanh::LeanObject,
    mut v___y_6061_: *mut leanh::LeanObject,
    mut v___y_6062_: *mut leanh::LeanObject,
    mut v___y_6063_: *mut leanh::LeanObject,
    mut v___y_6064_: *mut leanh::LeanObject,
    mut v___y_6065_: *mut leanh::LeanObject,
    mut v___y_6066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6068_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___redArg(v_type_6055_, v___y_6063_, v___y_6064_, v___y_6065_, v___y_6066_);
    return v___x_6068_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6___boxed(
    mut v_type_6069_: *mut leanh::LeanObject,
    mut v___y_6070_: *mut leanh::LeanObject,
    mut v___y_6071_: *mut leanh::LeanObject,
    mut v___y_6072_: *mut leanh::LeanObject,
    mut v___y_6073_: *mut leanh::LeanObject,
    mut v___y_6074_: *mut leanh::LeanObject,
    mut v___y_6075_: *mut leanh::LeanObject,
    mut v___y_6076_: *mut leanh::LeanObject,
    mut v___y_6077_: *mut leanh::LeanObject,
    mut v___y_6078_: *mut leanh::LeanObject,
    mut v___y_6079_: *mut leanh::LeanObject,
    mut v___y_6080_: *mut leanh::LeanObject,
    mut v___y_6081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6082_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go_spec__2_spec__3_spec__6(v_type_6069_, v___y_6070_, v___y_6071_, v___y_6072_, v___y_6073_, v___y_6074_, v___y_6075_, v___y_6076_, v___y_6077_, v___y_6078_, v___y_6079_, v___y_6080_);
    leanh::lean_dec(v___y_6080_);
    leanh::lean_dec_ref(v___y_6079_);
    leanh::lean_dec(v___y_6078_);
    leanh::lean_dec_ref(v___y_6077_);
    leanh::lean_dec(v___y_6076_);
    leanh::lean_dec_ref(v___y_6075_);
    leanh::lean_dec(v___y_6074_);
    leanh::lean_dec_ref(v___y_6073_);
    leanh::lean_dec(v___y_6072_);
    leanh::lean_dec(v___y_6071_);
    leanh::lean_dec(v___y_6070_);
    return v_res_6082_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(
    mut v_e_6083_: *mut leanh::LeanObject,
    mut v_a_6084_: *mut leanh::LeanObject,
    mut v_a_6085_: *mut leanh::LeanObject,
    mut v_a_6086_: *mut leanh::LeanObject,
    mut v_a_6087_: *mut leanh::LeanObject,
    mut v_a_6088_: *mut leanh::LeanObject,
    mut v_a_6089_: *mut leanh::LeanObject,
    mut v_a_6090_: *mut leanh::LeanObject,
    mut v_a_6091_: *mut leanh::LeanObject,
    mut v_a_6092_: *mut leanh::LeanObject,
    mut v_a_6093_: *mut leanh::LeanObject,
    mut v_a_6094_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6096_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM_0__Lean_Grind_CommRing_Expr_denoteAsRingExpr_go(v_e_6083_, v_a_6084_, v_a_6085_, v_a_6086_, v_a_6087_, v_a_6088_, v_a_6089_, v_a_6090_, v_a_6091_, v_a_6092_, v_a_6093_, v_a_6094_);
    if leanh::lean_obj_tag(v___x_6096_) == 0 {
        let mut v_a_6097_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6098_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_6097_ = leanh::lean_ctor_get(v___x_6096_, 0);
        leanh::lean_inc(v_a_6097_);
        leanh::lean_dec_ref_known(v___x_6096_, 1);
        v___x_6098_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_6097_, v_a_6090_);
        return v___x_6098_;
    } else {
        return v___x_6096_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteAsRingExpr___boxed(
    mut v_e_6099_: *mut leanh::LeanObject,
    mut v_a_6100_: *mut leanh::LeanObject,
    mut v_a_6101_: *mut leanh::LeanObject,
    mut v_a_6102_: *mut leanh::LeanObject,
    mut v_a_6103_: *mut leanh::LeanObject,
    mut v_a_6104_: *mut leanh::LeanObject,
    mut v_a_6105_: *mut leanh::LeanObject,
    mut v_a_6106_: *mut leanh::LeanObject,
    mut v_a_6107_: *mut leanh::LeanObject,
    mut v_a_6108_: *mut leanh::LeanObject,
    mut v_a_6109_: *mut leanh::LeanObject,
    mut v_a_6110_: *mut leanh::LeanObject,
    mut v_a_6111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6112_ = l_Lean_Grind_CommRing_Expr_denoteAsRingExpr(
        v_e_6099_, v_a_6100_, v_a_6101_, v_a_6102_, v_a_6103_, v_a_6104_, v_a_6105_, v_a_6106_,
        v_a_6107_, v_a_6108_, v_a_6109_, v_a_6110_,
    );
    leanh::lean_dec(v_a_6110_);
    leanh::lean_dec_ref(v_a_6109_);
    leanh::lean_dec(v_a_6108_);
    leanh::lean_dec_ref(v_a_6107_);
    leanh::lean_dec(v_a_6106_);
    leanh::lean_dec_ref(v_a_6105_);
    leanh::lean_dec(v_a_6104_);
    leanh::lean_dec_ref(v_a_6103_);
    leanh::lean_dec(v_a_6102_);
    leanh::lean_dec(v_a_6101_);
    leanh::lean_dec(v_a_6100_);
    return v_res_6112_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadSemiring(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM =
        _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM();
    leanh::lean_mark_persistent(
        l_Lean_Meta_Grind_Arith_CommRing_instMonadCommSemiringSemiringM,
    );
    l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM =
        _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingSemiringM);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadSemiring(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SemiringM(builtin);
}