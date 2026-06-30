// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.Util
// Imports: Lean.Meta.Tactic.Grind.Arith.Linear.LinearM Lean.Meta.Tactic.Grind.Arith.Util Init.Data.Int.Gcd
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_int_dec_eq, lean_int_ediv, lean_int_neg,
    lean_nat_abs, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul,
    lean_nat_sub, lean_nat_to_int, lean_st_ref_get, lean_uint64_to_usize, lean_usize_add,
    lean_usize_dec_le, lean_usize_land, lean_usize_mul, lean_usize_of_nat, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Int::Gcd::{
    initialize_Init_Data_Int_Gcd, l_Int_gcd, runtime_initialize_Init_Data_Int_Gcd,
};
use crate::r#gen::Init::Data::Rat::Basic::{
    l_Rat_add, l_Rat_blt, l_Rat_instDecidableLe, l_Rat_mul, l_Rat_ofInt,
    l_instDecidableEqRat_decEq, l_instInhabitedRat,
};
use crate::r#gen::Init::GetElem::l_outOfBounds___redArg;
use crate::r#gen::Lean::Data::LBool::l_Bool_toLBool;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_get_x21___redArg, l_Lean_PersistentArray_push___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Exception::l_Lean_throwError___redArg;
use crate::r#gen::Lean::Expr::l_Lean_instInhabitedExpr;
use crate::r#gen::Lean::Message::{l_Lean_indentExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    l_Lean_Meta_Sym_getConfig___redArg, l_Lean_Meta_Sym_reportIssue,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::LinearM::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM,
    l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct,
    l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg,
    l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Types::l_Lean_Meta_Grind_Arith_Linear_linearExt;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Util::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Util, l_Lean_Meta_Grind_Arith_shrink,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg,
    l_Lean_Meta_Grind_isInconsistent___redArg,
};
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__0_value:
    leanh::LeanStringObject<57> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 57,
    m_capacity: 57,
    m_length: 56,
    m_data: [
        101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 105, 110, 32, 116, 119, 111, 32, 100,
        105, 102, 102, 101, 114, 101, 110, 116, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 32,
        105, 110, 32, 108, 105, 110, 97, 114, 105, 116, 104, 32, 109, 111, 100, 117, 108, 101, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__0_value:
    leanh::LeanStringObject<82> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 82,
    m_capacity: 82,
    m_length: 81,
    m_data: [
        96, 103, 114, 105, 110, 100, 32, 108, 105, 110, 97, 114, 105, 116, 104, 96, 32, 105, 110,
        116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 44, 32, 115, 116, 114, 117, 99,
        116, 117, 114, 101, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 105, 109, 112, 108, 101,
        109, 101, 110, 116, 32, 96, 78, 111, 78, 97, 116, 90, 101, 114, 111, 68, 105, 118, 105,
        115, 111, 114, 115, 96, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__0_value:
    leanh::LeanStringObject<63> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 63,
    m_capacity: 63,
    m_length: 62,
    m_data: [
        96, 103, 114, 105, 110, 100, 32, 108, 105, 110, 97, 114, 105, 116, 104, 96, 32, 105, 110,
        116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 44, 32, 115, 116, 114, 117, 99,
        116, 117, 114, 101, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 115, 117, 112, 112, 111,
        114, 116, 32, 76, 69, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__0_value:
    leanh::LeanStringObject<63> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 63,
    m_capacity: 63,
    m_length: 62,
    m_data: [
        96, 103, 114, 105, 110, 100, 32, 108, 105, 110, 97, 114, 105, 116, 104, 96, 32, 105, 110,
        116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 44, 32, 115, 116, 114, 117, 99,
        116, 117, 114, 101, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 115, 117, 112, 112, 111,
        114, 116, 32, 76, 84, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__0_value:
    leanh::LeanStringObject<78> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 78,
    m_capacity: 78,
    m_length: 77,
    m_data: [
        96, 103, 114, 105, 110, 100, 32, 108, 105, 110, 97, 114, 105, 116, 104, 96, 32, 105, 110,
        116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 44, 32, 115, 116, 114, 117, 99,
        116, 117, 114, 101, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 104, 97, 118, 101, 32,
        97, 32, 108, 97, 119, 102, 117, 108, 32, 76, 84, 32, 105, 110, 115, 116, 97, 110, 99, 101,
        0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__0_value:
    leanh::LeanStringObject<61> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 61,
    m_capacity: 61,
    m_length: 60,
    m_data: [
        96, 103, 114, 105, 110, 100, 32, 108, 105, 110, 97, 114, 105, 116, 104, 96, 32, 105, 110,
        116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 44, 32, 115, 116, 114, 117, 99,
        116, 117, 114, 101, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 112, 114, 101, 111, 114,
        100, 101, 114, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__0_value:
    leanh::LeanStringObject<68> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 68,
    m_capacity: 68,
    m_length: 67,
    m_data: [
        96, 103, 114, 105, 110, 100, 32, 108, 105, 110, 97, 114, 105, 116, 104, 96, 32, 105, 110,
        116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 44, 32, 115, 116, 114, 117, 99,
        116, 117, 114, 101, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 111, 114, 100, 101,
        114, 101, 100, 32, 109, 111, 100, 117, 108, 101, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__0_value:
    leanh::LeanStringObject<72> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 72,
    m_capacity: 72,
    m_length: 71,
    m_data: [
        96, 103, 114, 105, 110, 100, 32, 108, 105, 110, 97, 114, 105, 116, 104, 96, 32, 105, 110,
        116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 44, 32, 115, 116, 114, 117, 99,
        116, 117, 114, 101, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 111, 114, 100, 101,
        114, 101, 100, 32, 105, 110, 116, 32, 109, 111, 100, 117, 108, 101, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__0_value:
    leanh::LeanStringObject<65> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 65,
    m_capacity: 65,
    m_length: 64,
    m_data: [
        96, 103, 114, 105, 110, 100, 32, 108, 105, 110, 97, 114, 105, 116, 104, 96, 32, 105, 110,
        116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 44, 32, 115, 116, 114, 117, 99,
        116, 117, 114, 101, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 108, 105, 110, 101, 97,
        114, 32, 111, 114, 100, 101, 114, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__0_value:
    leanh::LeanStringObject<57> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 57,
    m_capacity: 57,
    m_length: 56,
    m_data: [
        96, 103, 114, 105, 110, 100, 32, 108, 105, 110, 97, 114, 105, 116, 104, 96, 32, 105, 110,
        116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 44, 32, 115, 116, 114, 117, 99,
        116, 117, 114, 101, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 114, 105, 110, 103, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__0_value:
    leanh::LeanStringObject<69> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 69,
    m_capacity: 69,
    m_length: 68,
    m_data: [
        96, 103, 114, 105, 110, 100, 32, 108, 105, 110, 97, 114, 105, 116, 104, 96, 32, 105, 110,
        116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 44, 32, 115, 116, 114, 117, 99,
        116, 117, 114, 101, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 109, 109, 117,
        116, 97, 116, 105, 118, 101, 32, 114, 105, 110, 103, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__0_value:
    leanh::LeanStringObject<66> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 66,
    m_capacity: 66,
    m_length: 65,
    m_data: [
        96, 103, 114, 105, 110, 100, 32, 108, 105, 110, 97, 114, 105, 116, 104, 96, 32, 105, 110,
        116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 44, 32, 115, 116, 114, 117, 99,
        116, 117, 114, 101, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 111, 114, 100, 101,
        114, 101, 100, 32, 114, 105, 110, 103, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Grind_Linarith_Poly_updateOccs___closed__0_value: leanh::LeanStringObject<
    64,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 64,
    m_capacity: 64,
    m_length: 63,
    m_data: [
        96, 103, 114, 105, 110, 100, 32, 108, 105, 110, 97, 114, 105, 116, 104, 96, 32, 105, 110,
        116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 44, 32, 117, 110, 101, 120, 112,
        101, 99, 116, 101, 100, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 112, 111, 108, 121,
        110, 111, 109, 105, 97, 108, 0,
    ],
};
static mut l_Lean_Grind_Linarith_Poly_updateOccs___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_Linarith_Poly_updateOccs___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Grind_Linarith_Poly_updateOccs___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_Linarith_Poly_updateOccs___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getZero(
    mut v_a_2716_: *mut leanh::LeanObject,
    mut v_a_2717_: *mut leanh::LeanObject,
    mut v_a_2718_: *mut leanh::LeanObject,
    mut v_a_2719_: *mut leanh::LeanObject,
    mut v_a_2720_: *mut leanh::LeanObject,
    mut v_a_2721_: *mut leanh::LeanObject,
    mut v_a_2722_: *mut leanh::LeanObject,
    mut v_a_2723_: *mut leanh::LeanObject,
    mut v_a_2724_: *mut leanh::LeanObject,
    mut v_a_2725_: *mut leanh::LeanObject,
    mut v_a_2726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2732_: u8 = 0;
    let mut v_zero_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2737_: u8 = 0;
    let mut v_a_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2741_: u8 = 0;
    let mut v___x_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2745_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2728_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_,
                    v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_,
                );
                if leanh::lean_obj_tag(v___x_2728_) == 0 {
                    v_a_2729_ = leanh::lean_ctor_get(v___x_2728_, 0);
                    v_isSharedCheck_2737_ = (!leanh::lean_is_exclusive(v___x_2728_)) as u8;
                    if v_isSharedCheck_2737_ == 0 {
                        v___x_2731_ = v___x_2728_;
                        v_isShared_2732_ = v_isSharedCheck_2737_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2729_);
                        leanh::lean_dec(v___x_2728_);
                        v___x_2731_ = leanh::lean_box(0);
                        v_isShared_2732_ = v_isSharedCheck_2737_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2738_ = leanh::lean_ctor_get(v___x_2728_, 0);
                    v_isSharedCheck_2745_ = (!leanh::lean_is_exclusive(v___x_2728_)) as u8;
                    if v_isSharedCheck_2745_ == 0 {
                        v___x_2740_ = v___x_2728_;
                        v_isShared_2741_ = v_isSharedCheck_2745_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2738_);
                        leanh::lean_dec(v___x_2728_);
                        v___x_2740_ = leanh::lean_box(0);
                        v_isShared_2741_ = v_isSharedCheck_2745_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_zero_2733_ = leanh::lean_ctor_get(v_a_2729_, 17);
                leanh::lean_inc_ref(v_zero_2733_);
                leanh::lean_dec(v_a_2729_);
                if v_isShared_2732_ == 0 {
                    leanh::lean_ctor_set(v___x_2731_, 0, v_zero_2733_);
                    v___x_2735_ = v___x_2731_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2736_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_zero_2733_);
                    v___x_2735_ = v_reuseFailAlloc_2736_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2735_;
            }
            3 => {
                if v_isShared_2741_ == 0 {
                    v___x_2743_ = v___x_2740_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2744_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
                    v___x_2743_ = v_reuseFailAlloc_2744_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2743_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getZero___boxed(
    mut v_a_2746_: *mut leanh::LeanObject,
    mut v_a_2747_: *mut leanh::LeanObject,
    mut v_a_2748_: *mut leanh::LeanObject,
    mut v_a_2749_: *mut leanh::LeanObject,
    mut v_a_2750_: *mut leanh::LeanObject,
    mut v_a_2751_: *mut leanh::LeanObject,
    mut v_a_2752_: *mut leanh::LeanObject,
    mut v_a_2753_: *mut leanh::LeanObject,
    mut v_a_2754_: *mut leanh::LeanObject,
    mut v_a_2755_: *mut leanh::LeanObject,
    mut v_a_2756_: *mut leanh::LeanObject,
    mut v_a_2757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2758_ = l_Lean_Meta_Grind_Arith_Linear_getZero(
        v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_,
        v_a_2754_, v_a_2755_, v_a_2756_,
    );
    leanh::lean_dec(v_a_2756_);
    leanh::lean_dec_ref(v_a_2755_);
    leanh::lean_dec(v_a_2754_);
    leanh::lean_dec_ref(v_a_2753_);
    leanh::lean_dec(v_a_2752_);
    leanh::lean_dec_ref(v_a_2751_);
    leanh::lean_dec(v_a_2750_);
    leanh::lean_dec_ref(v_a_2749_);
    leanh::lean_dec(v_a_2748_);
    leanh::lean_dec(v_a_2747_);
    leanh::lean_dec(v_a_2746_);
    return v_res_2758_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getOne(
    mut v_a_2759_: *mut leanh::LeanObject,
    mut v_a_2760_: *mut leanh::LeanObject,
    mut v_a_2761_: *mut leanh::LeanObject,
    mut v_a_2762_: *mut leanh::LeanObject,
    mut v_a_2763_: *mut leanh::LeanObject,
    mut v_a_2764_: *mut leanh::LeanObject,
    mut v_a_2765_: *mut leanh::LeanObject,
    mut v_a_2766_: *mut leanh::LeanObject,
    mut v_a_2767_: *mut leanh::LeanObject,
    mut v_a_2768_: *mut leanh::LeanObject,
    mut v_a_2769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2775_: u8 = 0;
    let mut v_one_x3f_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2782_: u8 = 0;
    let mut v_a_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2786_: u8 = 0;
    let mut v___x_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2790_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2771_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_, v_a_2765_,
                    v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_,
                );
                if leanh::lean_obj_tag(v___x_2771_) == 0 {
                    v_a_2772_ = leanh::lean_ctor_get(v___x_2771_, 0);
                    v_isSharedCheck_2782_ = (!leanh::lean_is_exclusive(v___x_2771_)) as u8;
                    if v_isSharedCheck_2782_ == 0 {
                        v___x_2774_ = v___x_2771_;
                        v_isShared_2775_ = v_isSharedCheck_2782_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2772_);
                        leanh::lean_dec(v___x_2771_);
                        v___x_2774_ = leanh::lean_box(0);
                        v_isShared_2775_ = v_isSharedCheck_2782_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2783_ = leanh::lean_ctor_get(v___x_2771_, 0);
                    v_isSharedCheck_2790_ = (!leanh::lean_is_exclusive(v___x_2771_)) as u8;
                    if v_isSharedCheck_2790_ == 0 {
                        v___x_2785_ = v___x_2771_;
                        v_isShared_2786_ = v_isSharedCheck_2790_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2783_);
                        leanh::lean_dec(v___x_2771_);
                        v___x_2785_ = leanh::lean_box(0);
                        v_isShared_2786_ = v_isSharedCheck_2790_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_one_x3f_2776_ = leanh::lean_ctor_get(v_a_2772_, 19);
                leanh::lean_inc(v_one_x3f_2776_);
                leanh::lean_dec(v_a_2772_);
                if leanh::lean_obj_tag(v_one_x3f_2776_) == 1 {
                    v_val_2777_ = leanh::lean_ctor_get(v_one_x3f_2776_, 0);
                    leanh::lean_inc(v_val_2777_);
                    leanh::lean_dec_ref_known(v_one_x3f_2776_, 1);
                    if v_isShared_2775_ == 0 {
                        leanh::lean_ctor_set(v___x_2774_, 0, v_val_2777_);
                        v___x_2779_ = v___x_2774_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2780_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_val_2777_);
                        v___x_2779_ = v_reuseFailAlloc_2780_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_one_x3f_2776_);
                    leanh::lean_del_object(v___x_2774_);
                    v___x_2781_ = l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(
                        v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_,
                    );
                    return v___x_2781_;
                }
            }
            2 => {
                return v___x_2779_;
            }
            3 => {
                if v_isShared_2786_ == 0 {
                    v___x_2788_ = v___x_2785_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2789_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_a_2783_);
                    v___x_2788_ = v_reuseFailAlloc_2789_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2788_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getOne___boxed(
    mut v_a_2791_: *mut leanh::LeanObject,
    mut v_a_2792_: *mut leanh::LeanObject,
    mut v_a_2793_: *mut leanh::LeanObject,
    mut v_a_2794_: *mut leanh::LeanObject,
    mut v_a_2795_: *mut leanh::LeanObject,
    mut v_a_2796_: *mut leanh::LeanObject,
    mut v_a_2797_: *mut leanh::LeanObject,
    mut v_a_2798_: *mut leanh::LeanObject,
    mut v_a_2799_: *mut leanh::LeanObject,
    mut v_a_2800_: *mut leanh::LeanObject,
    mut v_a_2801_: *mut leanh::LeanObject,
    mut v_a_2802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2803_ = l_Lean_Meta_Grind_Arith_Linear_getOne(
        v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_,
        v_a_2799_, v_a_2800_, v_a_2801_,
    );
    leanh::lean_dec(v_a_2801_);
    leanh::lean_dec_ref(v_a_2800_);
    leanh::lean_dec(v_a_2799_);
    leanh::lean_dec_ref(v_a_2798_);
    leanh::lean_dec(v_a_2797_);
    leanh::lean_dec_ref(v_a_2796_);
    leanh::lean_dec(v_a_2795_);
    leanh::lean_dec_ref(v_a_2794_);
    leanh::lean_dec(v_a_2793_);
    leanh::lean_dec(v_a_2792_);
    leanh::lean_dec(v_a_2791_);
    return v_res_2803_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isCommRing(
    mut v_a_2804_: *mut leanh::LeanObject,
    mut v_a_2805_: *mut leanh::LeanObject,
    mut v_a_2806_: *mut leanh::LeanObject,
    mut v_a_2807_: *mut leanh::LeanObject,
    mut v_a_2808_: *mut leanh::LeanObject,
    mut v_a_2809_: *mut leanh::LeanObject,
    mut v_a_2810_: *mut leanh::LeanObject,
    mut v_a_2811_: *mut leanh::LeanObject,
    mut v_a_2812_: *mut leanh::LeanObject,
    mut v_a_2813_: *mut leanh::LeanObject,
    mut v_a_2814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2820_: u8 = 0;
    let mut v_ringId_x3f_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: u8 = 0;
    let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: u8 = 0;
    let mut v___x_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2832_: u8 = 0;
    let mut v_a_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2836_: u8 = 0;
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2840_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2816_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_,
                    v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_,
                );
                if leanh::lean_obj_tag(v___x_2816_) == 0 {
                    v_a_2817_ = leanh::lean_ctor_get(v___x_2816_, 0);
                    v_isSharedCheck_2832_ = (!leanh::lean_is_exclusive(v___x_2816_)) as u8;
                    if v_isSharedCheck_2832_ == 0 {
                        v___x_2819_ = v___x_2816_;
                        v_isShared_2820_ = v_isSharedCheck_2832_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2817_);
                        leanh::lean_dec(v___x_2816_);
                        v___x_2819_ = leanh::lean_box(0);
                        v_isShared_2820_ = v_isSharedCheck_2832_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2833_ = leanh::lean_ctor_get(v___x_2816_, 0);
                    v_isSharedCheck_2840_ = (!leanh::lean_is_exclusive(v___x_2816_)) as u8;
                    if v_isSharedCheck_2840_ == 0 {
                        v___x_2835_ = v___x_2816_;
                        v_isShared_2836_ = v_isSharedCheck_2840_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2833_);
                        leanh::lean_dec(v___x_2816_);
                        v___x_2835_ = leanh::lean_box(0);
                        v_isShared_2836_ = v_isSharedCheck_2840_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_ringId_x3f_2821_ = leanh::lean_ctor_get(v_a_2817_, 1);
                leanh::lean_inc(v_ringId_x3f_2821_);
                leanh::lean_dec(v_a_2817_);
                if leanh::lean_obj_tag(v_ringId_x3f_2821_) == 0 {
                    v___x_2822_ = 0;
                    v___x_2823_ = leanh::lean_box((v___x_2822_) as usize);
                    if v_isShared_2820_ == 0 {
                        leanh::lean_ctor_set(v___x_2819_, 0, v___x_2823_);
                        v___x_2825_ = v___x_2819_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2826_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2823_);
                        v___x_2825_ = v_reuseFailAlloc_2826_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_ringId_x3f_2821_, 1);
                    v___x_2827_ = 1;
                    v___x_2828_ = leanh::lean_box((v___x_2827_) as usize);
                    if v_isShared_2820_ == 0 {
                        leanh::lean_ctor_set(v___x_2819_, 0, v___x_2828_);
                        v___x_2830_ = v___x_2819_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2831_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2831_, 0, v___x_2828_);
                        v___x_2830_ = v_reuseFailAlloc_2831_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2825_;
            }
            3 => {
                return v___x_2830_;
            }
            4 => {
                if v_isShared_2836_ == 0 {
                    v___x_2838_ = v___x_2835_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2839_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2833_);
                    v___x_2838_ = v_reuseFailAlloc_2839_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2838_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isCommRing___boxed(
    mut v_a_2841_: *mut leanh::LeanObject,
    mut v_a_2842_: *mut leanh::LeanObject,
    mut v_a_2843_: *mut leanh::LeanObject,
    mut v_a_2844_: *mut leanh::LeanObject,
    mut v_a_2845_: *mut leanh::LeanObject,
    mut v_a_2846_: *mut leanh::LeanObject,
    mut v_a_2847_: *mut leanh::LeanObject,
    mut v_a_2848_: *mut leanh::LeanObject,
    mut v_a_2849_: *mut leanh::LeanObject,
    mut v_a_2850_: *mut leanh::LeanObject,
    mut v_a_2851_: *mut leanh::LeanObject,
    mut v_a_2852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2853_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(
        v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_,
        v_a_2849_, v_a_2850_, v_a_2851_,
    );
    leanh::lean_dec(v_a_2851_);
    leanh::lean_dec_ref(v_a_2850_);
    leanh::lean_dec(v_a_2849_);
    leanh::lean_dec_ref(v_a_2848_);
    leanh::lean_dec(v_a_2847_);
    leanh::lean_dec_ref(v_a_2846_);
    leanh::lean_dec(v_a_2845_);
    leanh::lean_dec_ref(v_a_2844_);
    leanh::lean_dec(v_a_2843_);
    leanh::lean_dec(v_a_2842_);
    leanh::lean_dec(v_a_2841_);
    return v_res_2853_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing(
    mut v_a_2854_: *mut leanh::LeanObject,
    mut v_a_2855_: *mut leanh::LeanObject,
    mut v_a_2856_: *mut leanh::LeanObject,
    mut v_a_2857_: *mut leanh::LeanObject,
    mut v_a_2858_: *mut leanh::LeanObject,
    mut v_a_2859_: *mut leanh::LeanObject,
    mut v_a_2860_: *mut leanh::LeanObject,
    mut v_a_2861_: *mut leanh::LeanObject,
    mut v_a_2862_: *mut leanh::LeanObject,
    mut v_a_2863_: *mut leanh::LeanObject,
    mut v_a_2864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: u8 = 0;
    let mut v___x_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2872_: u8 = 0;
    let mut v___x_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2876_: u8 = 0;
    let mut v_unused_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2881_: u8 = 0;
    let mut v_orderedRingInst_x3f_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: u8 = 0;
    let mut v___x_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2891_: u8 = 0;
    let mut v_a_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2895_: u8 = 0;
    let mut v___x_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2899_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2866_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(
                    v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_,
                    v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_,
                );
                if leanh::lean_obj_tag(v___x_2866_) == 0 {
                    v_a_2867_ = leanh::lean_ctor_get(v___x_2866_, 0);
                    leanh::lean_inc(v_a_2867_);
                    leanh::lean_dec_ref_known(v___x_2866_, 1);
                    v___x_2868_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                        v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_,
                        v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_,
                    );
                    if leanh::lean_obj_tag(v___x_2868_) == 0 {
                        v___x_2869_ = (leanh::lean_unbox(v_a_2867_) as u8);
                        if v___x_2869_ == 0 {
                            v_isSharedCheck_2876_ =
                                (!leanh::lean_is_exclusive(v___x_2868_)) as u8;
                            if v_isSharedCheck_2876_ == 0 {
                                v_unused_2877_ = leanh::lean_ctor_get(v___x_2868_, 0);
                                leanh::lean_dec(v_unused_2877_);
                                v___x_2871_ = v___x_2868_;
                                v_isShared_2872_ = v_isSharedCheck_2876_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_2868_);
                                v___x_2871_ = leanh::lean_box(0);
                                v_isShared_2872_ = v_isSharedCheck_2876_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_2878_ = leanh::lean_ctor_get(v___x_2868_, 0);
                            v_isSharedCheck_2891_ =
                                (!leanh::lean_is_exclusive(v___x_2868_)) as u8;
                            if v_isSharedCheck_2891_ == 0 {
                                v___x_2880_ = v___x_2868_;
                                v_isShared_2881_ = v_isSharedCheck_2891_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2878_);
                                leanh::lean_dec(v___x_2868_);
                                v___x_2880_ = leanh::lean_box(0);
                                v_isShared_2881_ = v_isSharedCheck_2891_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_2867_);
                        v_a_2892_ = leanh::lean_ctor_get(v___x_2868_, 0);
                        v_isSharedCheck_2899_ =
                            (!leanh::lean_is_exclusive(v___x_2868_)) as u8;
                        if v_isSharedCheck_2899_ == 0 {
                            v___x_2894_ = v___x_2868_;
                            v_isShared_2895_ = v_isSharedCheck_2899_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2892_);
                            leanh::lean_dec(v___x_2868_);
                            v___x_2894_ = leanh::lean_box(0);
                            v_isShared_2895_ = v_isSharedCheck_2899_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    return v___x_2866_;
                }
            }
            1 => {
                if v_isShared_2872_ == 0 {
                    leanh::lean_ctor_set(v___x_2871_, 0, v_a_2867_);
                    v___x_2874_ = v___x_2871_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2875_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2867_);
                    v___x_2874_ = v_reuseFailAlloc_2875_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2874_;
            }
            3 => {
                v_orderedRingInst_x3f_2882_ = leanh::lean_ctor_get(v_a_2878_, 14);
                leanh::lean_inc(v_orderedRingInst_x3f_2882_);
                leanh::lean_dec(v_a_2878_);
                if leanh::lean_obj_tag(v_orderedRingInst_x3f_2882_) == 0 {
                    leanh::lean_dec(v_a_2867_);
                    v___x_2883_ = 0;
                    v___x_2884_ = leanh::lean_box((v___x_2883_) as usize);
                    if v_isShared_2881_ == 0 {
                        leanh::lean_ctor_set(v___x_2880_, 0, v___x_2884_);
                        v___x_2886_ = v___x_2880_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2887_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2887_, 0, v___x_2884_);
                        v___x_2886_ = v_reuseFailAlloc_2887_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_orderedRingInst_x3f_2882_, 1);
                    if v_isShared_2881_ == 0 {
                        leanh::lean_ctor_set(v___x_2880_, 0, v_a_2867_);
                        v___x_2889_ = v___x_2880_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2890_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2867_);
                        v___x_2889_ = v_reuseFailAlloc_2890_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_2886_;
            }
            5 => {
                return v___x_2889_;
            }
            6 => {
                if v_isShared_2895_ == 0 {
                    v___x_2897_ = v___x_2894_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2898_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2892_);
                    v___x_2897_ = v_reuseFailAlloc_2898_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2897_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing___boxed(
    mut v_a_2900_: *mut leanh::LeanObject,
    mut v_a_2901_: *mut leanh::LeanObject,
    mut v_a_2902_: *mut leanh::LeanObject,
    mut v_a_2903_: *mut leanh::LeanObject,
    mut v_a_2904_: *mut leanh::LeanObject,
    mut v_a_2905_: *mut leanh::LeanObject,
    mut v_a_2906_: *mut leanh::LeanObject,
    mut v_a_2907_: *mut leanh::LeanObject,
    mut v_a_2908_: *mut leanh::LeanObject,
    mut v_a_2909_: *mut leanh::LeanObject,
    mut v_a_2910_: *mut leanh::LeanObject,
    mut v_a_2911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2912_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing(
        v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_,
        v_a_2908_, v_a_2909_, v_a_2910_,
    );
    leanh::lean_dec(v_a_2910_);
    leanh::lean_dec_ref(v_a_2909_);
    leanh::lean_dec(v_a_2908_);
    leanh::lean_dec_ref(v_a_2907_);
    leanh::lean_dec(v_a_2906_);
    leanh::lean_dec_ref(v_a_2905_);
    leanh::lean_dec(v_a_2904_);
    leanh::lean_dec_ref(v_a_2903_);
    leanh::lean_dec(v_a_2902_);
    leanh::lean_dec(v_a_2901_);
    leanh::lean_dec(v_a_2900_);
    return v_res_2912_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(
    mut v_a_2913_: *mut leanh::LeanObject,
    mut v_a_2914_: *mut leanh::LeanObject,
    mut v_a_2915_: *mut leanh::LeanObject,
    mut v_a_2916_: *mut leanh::LeanObject,
    mut v_a_2917_: *mut leanh::LeanObject,
    mut v_a_2918_: *mut leanh::LeanObject,
    mut v_a_2919_: *mut leanh::LeanObject,
    mut v_a_2920_: *mut leanh::LeanObject,
    mut v_a_2921_: *mut leanh::LeanObject,
    mut v_a_2922_: *mut leanh::LeanObject,
    mut v_a_2923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2929_: u8 = 0;
    let mut v_isLinearInst_x3f_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: u8 = 0;
    let mut v___x_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: u8 = 0;
    let mut v___x_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2941_: u8 = 0;
    let mut v_a_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2945_: u8 = 0;
    let mut v___x_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2949_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2925_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_,
                    v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_,
                );
                if leanh::lean_obj_tag(v___x_2925_) == 0 {
                    v_a_2926_ = leanh::lean_ctor_get(v___x_2925_, 0);
                    v_isSharedCheck_2941_ = (!leanh::lean_is_exclusive(v___x_2925_)) as u8;
                    if v_isSharedCheck_2941_ == 0 {
                        v___x_2928_ = v___x_2925_;
                        v_isShared_2929_ = v_isSharedCheck_2941_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2926_);
                        leanh::lean_dec(v___x_2925_);
                        v___x_2928_ = leanh::lean_box(0);
                        v_isShared_2929_ = v_isSharedCheck_2941_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2942_ = leanh::lean_ctor_get(v___x_2925_, 0);
                    v_isSharedCheck_2949_ = (!leanh::lean_is_exclusive(v___x_2925_)) as u8;
                    if v_isSharedCheck_2949_ == 0 {
                        v___x_2944_ = v___x_2925_;
                        v_isShared_2945_ = v_isSharedCheck_2949_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2942_);
                        leanh::lean_dec(v___x_2925_);
                        v___x_2944_ = leanh::lean_box(0);
                        v_isShared_2945_ = v_isSharedCheck_2949_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_isLinearInst_x3f_2930_ = leanh::lean_ctor_get(v_a_2926_, 10);
                leanh::lean_inc(v_isLinearInst_x3f_2930_);
                leanh::lean_dec(v_a_2926_);
                if leanh::lean_obj_tag(v_isLinearInst_x3f_2930_) == 0 {
                    v___x_2931_ = 0;
                    v___x_2932_ = leanh::lean_box((v___x_2931_) as usize);
                    if v_isShared_2929_ == 0 {
                        leanh::lean_ctor_set(v___x_2928_, 0, v___x_2932_);
                        v___x_2934_ = v___x_2928_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2935_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2935_, 0, v___x_2932_);
                        v___x_2934_ = v_reuseFailAlloc_2935_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_isLinearInst_x3f_2930_, 1);
                    v___x_2936_ = 1;
                    v___x_2937_ = leanh::lean_box((v___x_2936_) as usize);
                    if v_isShared_2929_ == 0 {
                        leanh::lean_ctor_set(v___x_2928_, 0, v___x_2937_);
                        v___x_2939_ = v___x_2928_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2940_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2940_, 0, v___x_2937_);
                        v___x_2939_ = v_reuseFailAlloc_2940_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2934_;
            }
            3 => {
                return v___x_2939_;
            }
            4 => {
                if v_isShared_2945_ == 0 {
                    v___x_2947_ = v___x_2944_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2948_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2942_);
                    v___x_2947_ = v_reuseFailAlloc_2948_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2947_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isLinearOrder___boxed(
    mut v_a_2950_: *mut leanh::LeanObject,
    mut v_a_2951_: *mut leanh::LeanObject,
    mut v_a_2952_: *mut leanh::LeanObject,
    mut v_a_2953_: *mut leanh::LeanObject,
    mut v_a_2954_: *mut leanh::LeanObject,
    mut v_a_2955_: *mut leanh::LeanObject,
    mut v_a_2956_: *mut leanh::LeanObject,
    mut v_a_2957_: *mut leanh::LeanObject,
    mut v_a_2958_: *mut leanh::LeanObject,
    mut v_a_2959_: *mut leanh::LeanObject,
    mut v_a_2960_: *mut leanh::LeanObject,
    mut v_a_2961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2962_ = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(
        v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_,
        v_a_2958_, v_a_2959_, v_a_2960_,
    );
    leanh::lean_dec(v_a_2960_);
    leanh::lean_dec_ref(v_a_2959_);
    leanh::lean_dec(v_a_2958_);
    leanh::lean_dec_ref(v_a_2957_);
    leanh::lean_dec(v_a_2956_);
    leanh::lean_dec_ref(v_a_2955_);
    leanh::lean_dec(v_a_2954_);
    leanh::lean_dec_ref(v_a_2953_);
    leanh::lean_dec(v_a_2952_);
    leanh::lean_dec(v_a_2951_);
    leanh::lean_dec(v_a_2950_);
    return v_res_2962_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(
    mut v_a_2963_: *mut leanh::LeanObject,
    mut v_a_2964_: *mut leanh::LeanObject,
    mut v_a_2965_: *mut leanh::LeanObject,
    mut v_a_2966_: *mut leanh::LeanObject,
    mut v_a_2967_: *mut leanh::LeanObject,
    mut v_a_2968_: *mut leanh::LeanObject,
    mut v_a_2969_: *mut leanh::LeanObject,
    mut v_a_2970_: *mut leanh::LeanObject,
    mut v_a_2971_: *mut leanh::LeanObject,
    mut v_a_2972_: *mut leanh::LeanObject,
    mut v_a_2973_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2979_: u8 = 0;
    let mut v_noNatDivInst_x3f_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: u8 = 0;
    let mut v___x_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: u8 = 0;
    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2991_: u8 = 0;
    let mut v_a_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2995_: u8 = 0;
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2999_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2975_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_2963_, v_a_2964_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_,
                    v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_,
                );
                if leanh::lean_obj_tag(v___x_2975_) == 0 {
                    v_a_2976_ = leanh::lean_ctor_get(v___x_2975_, 0);
                    v_isSharedCheck_2991_ = (!leanh::lean_is_exclusive(v___x_2975_)) as u8;
                    if v_isSharedCheck_2991_ == 0 {
                        v___x_2978_ = v___x_2975_;
                        v_isShared_2979_ = v_isSharedCheck_2991_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2976_);
                        leanh::lean_dec(v___x_2975_);
                        v___x_2978_ = leanh::lean_box(0);
                        v_isShared_2979_ = v_isSharedCheck_2991_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2992_ = leanh::lean_ctor_get(v___x_2975_, 0);
                    v_isSharedCheck_2999_ = (!leanh::lean_is_exclusive(v___x_2975_)) as u8;
                    if v_isSharedCheck_2999_ == 0 {
                        v___x_2994_ = v___x_2975_;
                        v_isShared_2995_ = v_isSharedCheck_2999_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2992_);
                        leanh::lean_dec(v___x_2975_);
                        v___x_2994_ = leanh::lean_box(0);
                        v_isShared_2995_ = v_isSharedCheck_2999_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_noNatDivInst_x3f_2980_ = leanh::lean_ctor_get(v_a_2976_, 11);
                leanh::lean_inc(v_noNatDivInst_x3f_2980_);
                leanh::lean_dec(v_a_2976_);
                if leanh::lean_obj_tag(v_noNatDivInst_x3f_2980_) == 0 {
                    v___x_2981_ = 0;
                    v___x_2982_ = leanh::lean_box((v___x_2981_) as usize);
                    if v_isShared_2979_ == 0 {
                        leanh::lean_ctor_set(v___x_2978_, 0, v___x_2982_);
                        v___x_2984_ = v___x_2978_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2985_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 0, v___x_2982_);
                        v___x_2984_ = v_reuseFailAlloc_2985_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_noNatDivInst_x3f_2980_, 1);
                    v___x_2986_ = 1;
                    v___x_2987_ = leanh::lean_box((v___x_2986_) as usize);
                    if v_isShared_2979_ == 0 {
                        leanh::lean_ctor_set(v___x_2978_, 0, v___x_2987_);
                        v___x_2989_ = v___x_2978_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2990_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2987_);
                        v___x_2989_ = v_reuseFailAlloc_2990_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2984_;
            }
            3 => {
                return v___x_2989_;
            }
            4 => {
                if v_isShared_2995_ == 0 {
                    v___x_2997_ = v___x_2994_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2998_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_a_2992_);
                    v___x_2997_ = v_reuseFailAlloc_2998_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2997_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors___boxed(
    mut v_a_3000_: *mut leanh::LeanObject,
    mut v_a_3001_: *mut leanh::LeanObject,
    mut v_a_3002_: *mut leanh::LeanObject,
    mut v_a_3003_: *mut leanh::LeanObject,
    mut v_a_3004_: *mut leanh::LeanObject,
    mut v_a_3005_: *mut leanh::LeanObject,
    mut v_a_3006_: *mut leanh::LeanObject,
    mut v_a_3007_: *mut leanh::LeanObject,
    mut v_a_3008_: *mut leanh::LeanObject,
    mut v_a_3009_: *mut leanh::LeanObject,
    mut v_a_3010_: *mut leanh::LeanObject,
    mut v_a_3011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3012_ = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(
        v_a_3000_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_,
        v_a_3008_, v_a_3009_, v_a_3010_,
    );
    leanh::lean_dec(v_a_3010_);
    leanh::lean_dec_ref(v_a_3009_);
    leanh::lean_dec(v_a_3008_);
    leanh::lean_dec_ref(v_a_3007_);
    leanh::lean_dec(v_a_3006_);
    leanh::lean_dec_ref(v_a_3005_);
    leanh::lean_dec(v_a_3004_);
    leanh::lean_dec_ref(v_a_3003_);
    leanh::lean_dec(v_a_3002_);
    leanh::lean_dec(v_a_3001_);
    leanh::lean_dec(v_a_3000_);
    return v_res_3012_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_keys_3013_: *mut leanh::LeanObject,
    mut v_vals_3014_: *mut leanh::LeanObject,
    mut v_i_3015_: *mut leanh::LeanObject,
    mut v_k_3016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: u8 = 0;
    let mut v___x_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: u8 = 0;
    let mut v___x_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3017_ = lean_array_get_size(v_keys_3013_);
                v___x_3018_ = lean_nat_dec_lt(v_i_3015_, v___x_3017_);
                if v___x_3018_ == 0 {
                    leanh::lean_dec(v_i_3015_);
                    v___x_3019_ = leanh::lean_box(0);
                    return v___x_3019_;
                } else {
                    v_k_x27_3020_ = lean_array_fget_borrowed(v_keys_3013_, v_i_3015_);
                    v___x_3021_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_3016_,
                            v_k_x27_3020_,
                        );
                    if v___x_3021_ == 0 {
                        v___x_3022_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3023_ = lean_nat_add(v_i_3015_, v___x_3022_);
                        leanh::lean_dec(v_i_3015_);
                        v_i_3015_ = v___x_3023_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3025_ = lean_array_fget_borrowed(v_vals_3014_, v_i_3015_);
                        leanh::lean_dec(v_i_3015_);
                        leanh::lean_inc(v___x_3025_);
                        v___x_3026_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3026_, 0, v___x_3025_);
                        return v___x_3026_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_3027_: *mut leanh::LeanObject,
    mut v_vals_3028_: *mut leanh::LeanObject,
    mut v_i_3029_: *mut leanh::LeanObject,
    mut v_k_3030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3031_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_3027_, v_vals_3028_, v_i_3029_, v_k_3030_);
    leanh::lean_dec_ref(v_k_3030_);
    leanh::lean_dec_ref(v_vals_3028_);
    leanh::lean_dec_ref(v_keys_3027_);
    return v_res_3031_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_3032_: usize = 0;
    let mut v___x_3033_: usize = 0;
    let mut v___x_3034_: usize = 0;
    v___x_3032_ = 5usize;
    v___x_3033_ = 1usize;
    v___x_3034_ = lean_usize_shift_left(v___x_3033_, v___x_3032_);
    return v___x_3034_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_3035_: usize = 0;
    let mut v___x_3036_: usize = 0;
    let mut v___x_3037_: usize = 0;
    v___x_3035_ = 1usize;
    v___x_3036_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__0);
    v___x_3037_ = lean_usize_sub(v___x_3036_, v___x_3035_);
    return v___x_3037_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(
    mut v_x_3038_: *mut leanh::LeanObject,
    mut v_x_3039_: usize,
    mut v_x_3040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: usize = 0;
    let mut v___x_3044_: usize = 0;
    let mut v___x_3045_: usize = 0;
    let mut v_j_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: u8 = 0;
    let mut v___x_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: usize = 0;
    let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3038_) == 0 {
                    v_es_3041_ = leanh::lean_ctor_get(v_x_3038_, 0);
                    v___x_3042_ = leanh::lean_box(2);
                    v___x_3043_ = 5usize;
                    v___x_3044_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_3045_ = lean_usize_land(v_x_3039_, v___x_3044_);
                    v_j_3046_ = lean_usize_to_nat(v___x_3045_);
                    v___x_3047_ = lean_array_get_borrowed(v___x_3042_, v_es_3041_, v_j_3046_);
                    leanh::lean_dec(v_j_3046_);
                    match leanh::lean_obj_tag(v___x_3047_) {
                        0 => {
                            v_key_3048_ = leanh::lean_ctor_get(v___x_3047_, 0);
                            v_val_3049_ = leanh::lean_ctor_get(v___x_3047_, 1);
                            v___x_3050_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_3040_, v_key_3048_);
                            if v___x_3050_ == 0 {
                                v___x_3051_ = leanh::lean_box(0);
                                return v___x_3051_;
                            } else {
                                leanh::lean_inc(v_val_3049_);
                                v___x_3052_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3052_, 0, v_val_3049_);
                                return v___x_3052_;
                            }
                        }
                        1 => {
                            v_node_3053_ = leanh::lean_ctor_get(v___x_3047_, 0);
                            v___x_3054_ = lean_usize_shift_right(v_x_3039_, v___x_3043_);
                            v_x_3038_ = v_node_3053_;
                            v_x_3039_ = v___x_3054_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3056_ = leanh::lean_box(0);
                            return v___x_3056_;
                        }
                    }
                } else {
                    v_ks_3057_ = leanh::lean_ctor_get(v_x_3038_, 0);
                    v_vs_3058_ = leanh::lean_ctor_get(v_x_3038_, 1);
                    v___x_3059_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3060_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_3057_, v_vs_3058_, v___x_3059_, v_x_3040_);
                    return v___x_3060_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_3061_: *mut leanh::LeanObject,
    mut v_x_3062_: *mut leanh::LeanObject,
    mut v_x_3063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_867__boxed_3064_: usize = 0;
    let mut v_res_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_867__boxed_3064_ = leanh::lean_unbox_usize(v_x_3062_);
    leanh::lean_dec(v_x_3062_);
    v_res_3065_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(v_x_3061_, v_x_867__boxed_3064_, v_x_3063_);
    leanh::lean_dec_ref(v_x_3063_);
    leanh::lean_dec_ref(v_x_3061_);
    return v_res_3065_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(
    mut v_x_3066_: *mut leanh::LeanObject,
    mut v_x_3067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3068_: u64 = 0;
    let mut v___x_3069_: usize = 0;
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3068_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_3067_);
    v___x_3069_ = lean_uint64_to_usize(v___x_3068_);
    v___x_3070_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(v_x_3066_, v___x_3069_, v_x_3067_);
    return v___x_3070_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg___boxed(
    mut v_x_3071_: *mut leanh::LeanObject,
    mut v_x_3072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3073_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(v_x_3071_, v_x_3072_);
    leanh::lean_dec_ref(v_x_3072_);
    leanh::lean_dec_ref(v_x_3071_);
    return v_res_3073_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(
    mut v_e_3074_: *mut leanh::LeanObject,
    mut v_a_3075_: *mut leanh::LeanObject,
    mut v_a_3076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3082_: u8 = 0;
    let mut v_exprToStructId_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3088_: u8 = 0;
    let mut v_a_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3092_: u8 = 0;
    let mut v___x_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3096_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3078_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_3075_, v_a_3076_);
                if leanh::lean_obj_tag(v___x_3078_) == 0 {
                    v_a_3079_ = leanh::lean_ctor_get(v___x_3078_, 0);
                    v_isSharedCheck_3088_ = (!leanh::lean_is_exclusive(v___x_3078_)) as u8;
                    if v_isSharedCheck_3088_ == 0 {
                        v___x_3081_ = v___x_3078_;
                        v_isShared_3082_ = v_isSharedCheck_3088_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3079_);
                        leanh::lean_dec(v___x_3078_);
                        v___x_3081_ = leanh::lean_box(0);
                        v_isShared_3082_ = v_isSharedCheck_3088_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3089_ = leanh::lean_ctor_get(v___x_3078_, 0);
                    v_isSharedCheck_3096_ = (!leanh::lean_is_exclusive(v___x_3078_)) as u8;
                    if v_isSharedCheck_3096_ == 0 {
                        v___x_3091_ = v___x_3078_;
                        v_isShared_3092_ = v_isSharedCheck_3096_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3089_);
                        leanh::lean_dec(v___x_3078_);
                        v___x_3091_ = leanh::lean_box(0);
                        v_isShared_3092_ = v_isSharedCheck_3096_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_exprToStructId_3083_ = leanh::lean_ctor_get(v_a_3079_, 2);
                leanh::lean_inc_ref(v_exprToStructId_3083_);
                leanh::lean_dec(v_a_3079_);
                v___x_3084_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(v_exprToStructId_3083_, v_e_3074_);
                leanh::lean_dec_ref(v_exprToStructId_3083_);
                if v_isShared_3082_ == 0 {
                    leanh::lean_ctor_set(v___x_3081_, 0, v___x_3084_);
                    v___x_3086_ = v___x_3081_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3087_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3087_, 0, v___x_3084_);
                    v___x_3086_ = v_reuseFailAlloc_3087_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3086_;
            }
            3 => {
                if v_isShared_3092_ == 0 {
                    v___x_3094_ = v___x_3091_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3095_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3089_);
                    v___x_3094_ = v_reuseFailAlloc_3095_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3094_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg___boxed(
    mut v_e_3097_: *mut leanh::LeanObject,
    mut v_a_3098_: *mut leanh::LeanObject,
    mut v_a_3099_: *mut leanh::LeanObject,
    mut v_a_3100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3101_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(
        v_e_3097_, v_a_3098_, v_a_3099_,
    );
    leanh::lean_dec_ref(v_a_3099_);
    leanh::lean_dec(v_a_3098_);
    leanh::lean_dec_ref(v_e_3097_);
    return v_res_3101_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f(
    mut v_e_3102_: *mut leanh::LeanObject,
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
) -> *mut leanh::LeanObject {
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3114_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(
        v_e_3102_, v_a_3103_, v_a_3111_,
    );
    return v___x_3114_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___boxed(
    mut v_e_3115_: *mut leanh::LeanObject,
    mut v_a_3116_: *mut leanh::LeanObject,
    mut v_a_3117_: *mut leanh::LeanObject,
    mut v_a_3118_: *mut leanh::LeanObject,
    mut v_a_3119_: *mut leanh::LeanObject,
    mut v_a_3120_: *mut leanh::LeanObject,
    mut v_a_3121_: *mut leanh::LeanObject,
    mut v_a_3122_: *mut leanh::LeanObject,
    mut v_a_3123_: *mut leanh::LeanObject,
    mut v_a_3124_: *mut leanh::LeanObject,
    mut v_a_3125_: *mut leanh::LeanObject,
    mut v_a_3126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3127_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f(
        v_e_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_,
        v_a_3123_, v_a_3124_, v_a_3125_,
    );
    leanh::lean_dec(v_a_3125_);
    leanh::lean_dec_ref(v_a_3124_);
    leanh::lean_dec(v_a_3123_);
    leanh::lean_dec_ref(v_a_3122_);
    leanh::lean_dec(v_a_3121_);
    leanh::lean_dec_ref(v_a_3120_);
    leanh::lean_dec(v_a_3119_);
    leanh::lean_dec_ref(v_a_3118_);
    leanh::lean_dec(v_a_3117_);
    leanh::lean_dec(v_a_3116_);
    leanh::lean_dec_ref(v_e_3115_);
    return v_res_3127_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0(
    mut v_00_u03b2_3128_: *mut leanh::LeanObject,
    mut v_x_3129_: *mut leanh::LeanObject,
    mut v_x_3130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3131_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(v_x_3129_, v_x_3130_);
    return v___x_3131_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___boxed(
    mut v_00_u03b2_3132_: *mut leanh::LeanObject,
    mut v_x_3133_: *mut leanh::LeanObject,
    mut v_x_3134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3135_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0(v_00_u03b2_3132_, v_x_3133_, v_x_3134_);
    leanh::lean_dec_ref(v_x_3134_);
    leanh::lean_dec_ref(v_x_3133_);
    return v_res_3135_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0(
    mut v_00_u03b2_3136_: *mut leanh::LeanObject,
    mut v_x_3137_: *mut leanh::LeanObject,
    mut v_x_3138_: usize,
    mut v_x_3139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3140_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(v_x_3137_, v_x_3138_, v_x_3139_);
    return v___x_3140_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_3141_: *mut leanh::LeanObject,
    mut v_x_3142_: *mut leanh::LeanObject,
    mut v_x_3143_: *mut leanh::LeanObject,
    mut v_x_3144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_984__boxed_3145_: usize = 0;
    let mut v_res_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_984__boxed_3145_ = leanh::lean_unbox_usize(v_x_3143_);
    leanh::lean_dec(v_x_3143_);
    v_res_3146_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0(v_00_u03b2_3141_, v_x_3142_, v_x_984__boxed_3145_, v_x_3144_);
    leanh::lean_dec_ref(v_x_3144_);
    leanh::lean_dec_ref(v_x_3142_);
    return v_res_3146_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3147_: *mut leanh::LeanObject,
    mut v_keys_3148_: *mut leanh::LeanObject,
    mut v_vals_3149_: *mut leanh::LeanObject,
    mut v_heq_3150_: *mut leanh::LeanObject,
    mut v_i_3151_: *mut leanh::LeanObject,
    mut v_k_3152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3153_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_3148_, v_vals_3149_, v_i_3151_, v_k_3152_);
    return v___x_3153_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_3154_: *mut leanh::LeanObject,
    mut v_keys_3155_: *mut leanh::LeanObject,
    mut v_vals_3156_: *mut leanh::LeanObject,
    mut v_heq_3157_: *mut leanh::LeanObject,
    mut v_i_3158_: *mut leanh::LeanObject,
    mut v_k_3159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3160_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_3154_, v_keys_3155_, v_vals_3156_, v_heq_3157_, v_i_3158_, v_k_3159_);
    leanh::lean_dec_ref(v_k_3159_);
    leanh::lean_dec_ref(v_vals_3156_);
    leanh::lean_dec_ref(v_keys_3155_);
    return v_res_3160_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_x_3161_: *mut leanh::LeanObject,
    mut v_x_3162_: *mut leanh::LeanObject,
    mut v_x_3163_: *mut leanh::LeanObject,
    mut v_x_3164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3169_: u8 = 0;
    let mut v___x_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: u8 = 0;
    let mut v___x_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: u8 = 0;
    let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3190_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3165_ = leanh::lean_ctor_get(v_x_3161_, 0);
                v_vs_3166_ = leanh::lean_ctor_get(v_x_3161_, 1);
                v_isSharedCheck_3190_ = (!leanh::lean_is_exclusive(v_x_3161_)) as u8;
                if v_isSharedCheck_3190_ == 0 {
                    v___x_3168_ = v_x_3161_;
                    v_isShared_3169_ = v_isSharedCheck_3190_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_3166_);
                    leanh::lean_inc(v_ks_3165_);
                    leanh::lean_dec(v_x_3161_);
                    v___x_3168_ = leanh::lean_box(0);
                    v_isShared_3169_ = v_isSharedCheck_3190_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3170_ = lean_array_get_size(v_ks_3165_);
                v___x_3171_ = lean_nat_dec_lt(v_x_3162_, v___x_3170_);
                if v___x_3171_ == 0 {
                    leanh::lean_dec(v_x_3162_);
                    v___x_3172_ = lean_array_push(v_ks_3165_, v_x_3163_);
                    v___x_3173_ = lean_array_push(v_vs_3166_, v_x_3164_);
                    if v_isShared_3169_ == 0 {
                        leanh::lean_ctor_set(v___x_3168_, 1, v___x_3173_);
                        leanh::lean_ctor_set(v___x_3168_, 0, v___x_3172_);
                        v___x_3175_ = v___x_3168_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3176_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3176_, 0, v___x_3172_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3176_, 1, v___x_3173_);
                        v___x_3175_ = v_reuseFailAlloc_3176_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3177_ = lean_array_fget_borrowed(v_ks_3165_, v_x_3162_);
                    v___x_3178_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_x_3163_,
                            v_k_x27_3177_,
                        );
                    if v___x_3178_ == 0 {
                        if v_isShared_3169_ == 0 {
                            v___x_3180_ = v___x_3168_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3184_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_ks_3165_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3184_, 1, v_vs_3166_);
                            v___x_3180_ = v_reuseFailAlloc_3184_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3185_ = lean_array_fset(v_ks_3165_, v_x_3162_, v_x_3163_);
                        v___x_3186_ = lean_array_fset(v_vs_3166_, v_x_3162_, v_x_3164_);
                        leanh::lean_dec(v_x_3162_);
                        if v_isShared_3169_ == 0 {
                            leanh::lean_ctor_set(v___x_3168_, 1, v___x_3186_);
                            leanh::lean_ctor_set(v___x_3168_, 0, v___x_3185_);
                            v___x_3188_ = v___x_3168_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3189_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3189_, 0, v___x_3185_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3189_, 1, v___x_3186_);
                            v___x_3188_ = v_reuseFailAlloc_3189_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3175_;
            }
            3 => {
                v___x_3181_ = leanh::lean_unsigned_to_nat(1);
                v___x_3182_ = lean_nat_add(v_x_3162_, v___x_3181_);
                leanh::lean_dec(v_x_3162_);
                v_x_3161_ = v___x_3180_;
                v_x_3162_ = v___x_3182_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3188_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(
    mut v_n_3191_: *mut leanh::LeanObject,
    mut v_k_3192_: *mut leanh::LeanObject,
    mut v_v_3193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3194_ = leanh::lean_unsigned_to_nat(0);
    v___x_3195_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_3191_, v___x_3194_, v_k_3192_, v_v_3193_);
    return v___x_3195_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3196_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3196_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(
    mut v_x_3197_: *mut leanh::LeanObject,
    mut v_x_3198_: usize,
    mut v_x_3199_: usize,
    mut v_x_3200_: *mut leanh::LeanObject,
    mut v_x_3201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: usize = 0;
    let mut v___x_3204_: usize = 0;
    let mut v___x_3205_: usize = 0;
    let mut v___x_3206_: usize = 0;
    let mut v_j_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: u8 = 0;
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3212_: u8 = 0;
    let mut v_v_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3226_: u8 = 0;
    let mut v___x_3227_: u8 = 0;
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3233_: u8 = 0;
    let mut v_node_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3237_: u8 = 0;
    let mut v___x_3238_: usize = 0;
    let mut v___x_3239_: usize = 0;
    let mut v___x_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3244_: u8 = 0;
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3246_: u8 = 0;
    let mut v_unused_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3252_: u8 = 0;
    let mut v___x_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3257_: u8 = 0;
    let mut v_ks_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: usize = 0;
    let mut v___x_3264_: u8 = 0;
    let mut v___x_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: u8 = 0;
    let mut v_reuseFailAlloc_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3269_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3197_) == 0 {
                    v_es_3202_ = leanh::lean_ctor_get(v_x_3197_, 0);
                    v___x_3203_ = 5usize;
                    v___x_3204_ = 1usize;
                    v___x_3205_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_3206_ = lean_usize_land(v_x_3198_, v___x_3205_);
                    v_j_3207_ = lean_usize_to_nat(v___x_3206_);
                    v___x_3208_ = lean_array_get_size(v_es_3202_);
                    v___x_3209_ = lean_nat_dec_lt(v_j_3207_, v___x_3208_);
                    if v___x_3209_ == 0 {
                        leanh::lean_dec(v_j_3207_);
                        leanh::lean_dec(v_x_3201_);
                        leanh::lean_dec_ref(v_x_3200_);
                        return v_x_3197_;
                    } else {
                        leanh::lean_inc_ref(v_es_3202_);
                        v_isSharedCheck_3246_ = (!leanh::lean_is_exclusive(v_x_3197_)) as u8;
                        if v_isSharedCheck_3246_ == 0 {
                            v_unused_3247_ = leanh::lean_ctor_get(v_x_3197_, 0);
                            leanh::lean_dec(v_unused_3247_);
                            v___x_3211_ = v_x_3197_;
                            v_isShared_3212_ = v_isSharedCheck_3246_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_3197_);
                            v___x_3211_ = leanh::lean_box(0);
                            v_isShared_3212_ = v_isSharedCheck_3246_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3248_ = leanh::lean_ctor_get(v_x_3197_, 0);
                    v_vs_3249_ = leanh::lean_ctor_get(v_x_3197_, 1);
                    v_isSharedCheck_3269_ = (!leanh::lean_is_exclusive(v_x_3197_)) as u8;
                    if v_isSharedCheck_3269_ == 0 {
                        v___x_3251_ = v_x_3197_;
                        v_isShared_3252_ = v_isSharedCheck_3269_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_3249_);
                        leanh::lean_inc(v_ks_3248_);
                        leanh::lean_dec(v_x_3197_);
                        v___x_3251_ = leanh::lean_box(0);
                        v_isShared_3252_ = v_isSharedCheck_3269_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3213_ = lean_array_fget(v_es_3202_, v_j_3207_);
                v___x_3214_ = leanh::lean_box(0);
                v_xs_x27_3215_ = lean_array_fset(v_es_3202_, v_j_3207_, v___x_3214_);
                match leanh::lean_obj_tag(v_v_3213_) {
                    0 => {
                        v_key_3222_ = leanh::lean_ctor_get(v_v_3213_, 0);
                        v_val_3223_ = leanh::lean_ctor_get(v_v_3213_, 1);
                        v_isSharedCheck_3233_ = (!leanh::lean_is_exclusive(v_v_3213_)) as u8;
                        if v_isSharedCheck_3233_ == 0 {
                            v___x_3225_ = v_v_3213_;
                            v_isShared_3226_ = v_isSharedCheck_3233_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3223_);
                            leanh::lean_inc(v_key_3222_);
                            leanh::lean_dec(v_v_3213_);
                            v___x_3225_ = leanh::lean_box(0);
                            v_isShared_3226_ = v_isSharedCheck_3233_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3234_ = leanh::lean_ctor_get(v_v_3213_, 0);
                        v_isSharedCheck_3244_ = (!leanh::lean_is_exclusive(v_v_3213_)) as u8;
                        if v_isSharedCheck_3244_ == 0 {
                            v___x_3236_ = v_v_3213_;
                            v_isShared_3237_ = v_isSharedCheck_3244_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_3234_);
                            leanh::lean_dec(v_v_3213_);
                            v___x_3236_ = leanh::lean_box(0);
                            v_isShared_3237_ = v_isSharedCheck_3244_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3245_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3245_, 0, v_x_3200_);
                        leanh::lean_ctor_set(v___x_3245_, 1, v_x_3201_);
                        v___y_3217_ = v___x_3245_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3218_ = lean_array_fset(v_xs_x27_3215_, v_j_3207_, v___y_3217_);
                leanh::lean_dec(v_j_3207_);
                if v_isShared_3212_ == 0 {
                    leanh::lean_ctor_set(v___x_3211_, 0, v___x_3218_);
                    v___x_3220_ = v___x_3211_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3221_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3218_);
                    v___x_3220_ = v_reuseFailAlloc_3221_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3220_;
            }
            4 => {
                v___x_3227_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_x_3200_,
                        v_key_3222_,
                    );
                if v___x_3227_ == 0 {
                    leanh::lean_del_object(v___x_3225_);
                    v___x_3228_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3222_,
                        v_val_3223_,
                        v_x_3200_,
                        v_x_3201_,
                    );
                    v___x_3229_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3229_, 0, v___x_3228_);
                    v___y_3217_ = v___x_3229_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_3223_);
                    leanh::lean_dec(v_key_3222_);
                    if v_isShared_3226_ == 0 {
                        leanh::lean_ctor_set(v___x_3225_, 1, v_x_3201_);
                        leanh::lean_ctor_set(v___x_3225_, 0, v_x_3200_);
                        v___x_3231_ = v___x_3225_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3232_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_x_3200_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3232_, 1, v_x_3201_);
                        v___x_3231_ = v_reuseFailAlloc_3232_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3217_ = v___x_3231_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3238_ = lean_usize_shift_right(v_x_3198_, v___x_3203_);
                v___x_3239_ = lean_usize_add(v_x_3199_, v___x_3204_);
                v___x_3240_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_node_3234_, v___x_3238_, v___x_3239_, v_x_3200_, v_x_3201_);
                if v_isShared_3237_ == 0 {
                    leanh::lean_ctor_set(v___x_3236_, 0, v___x_3240_);
                    v___x_3242_ = v___x_3236_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3243_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3243_, 0, v___x_3240_);
                    v___x_3242_ = v_reuseFailAlloc_3243_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3217_ = v___x_3242_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3252_ == 0 {
                    v___x_3254_ = v___x_3251_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3268_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_ks_3248_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3268_, 1, v_vs_3249_);
                    v___x_3254_ = v_reuseFailAlloc_3268_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3255_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(v___x_3254_, v_x_3200_, v_x_3201_);
                v___x_3263_ = 7usize;
                v___x_3264_ = lean_usize_dec_le(v___x_3263_, v_x_3199_);
                if v___x_3264_ == 0 {
                    v___x_3265_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3255_);
                    v___x_3266_ = leanh::lean_unsigned_to_nat(4);
                    v___x_3267_ = lean_nat_dec_lt(v___x_3265_, v___x_3266_);
                    leanh::lean_dec(v___x_3265_);
                    v___y_3257_ = v___x_3267_;
                    state = 10;
                    continue;
                } else {
                    v___y_3257_ = v___x_3264_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3257_ == 0 {
                    v_ks_3258_ = leanh::lean_ctor_get(v_newNode_3255_, 0);
                    leanh::lean_inc_ref(v_ks_3258_);
                    v_vs_3259_ = leanh::lean_ctor_get(v_newNode_3255_, 1);
                    leanh::lean_inc_ref(v_vs_3259_);
                    leanh::lean_dec_ref(v_newNode_3255_);
                    v___x_3260_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3261_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0);
                    v___x_3262_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(v_x_3199_, v_ks_3258_, v_vs_3259_, v___x_3260_, v___x_3261_);
                    leanh::lean_dec_ref(v_vs_3259_);
                    leanh::lean_dec_ref(v_ks_3258_);
                    return v___x_3262_;
                } else {
                    return v_newNode_3255_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(
    mut v_depth_3270_: usize,
    mut v_keys_3271_: *mut leanh::LeanObject,
    mut v_vals_3272_: *mut leanh::LeanObject,
    mut v_i_3273_: *mut leanh::LeanObject,
    mut v_entries_3274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: u8 = 0;
    let mut v_k_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: u64 = 0;
    let mut v_h_3280_: usize = 0;
    let mut v___x_3281_: usize = 0;
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: usize = 0;
    let mut v___x_3284_: usize = 0;
    let mut v___x_3285_: usize = 0;
    let mut v_h_3286_: usize = 0;
    let mut v___x_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3275_ = lean_array_get_size(v_keys_3271_);
                v___x_3276_ = lean_nat_dec_lt(v_i_3273_, v___x_3275_);
                if v___x_3276_ == 0 {
                    leanh::lean_dec(v_i_3273_);
                    return v_entries_3274_;
                } else {
                    v_k_3277_ = lean_array_fget_borrowed(v_keys_3271_, v_i_3273_);
                    v_v_3278_ = lean_array_fget_borrowed(v_vals_3272_, v_i_3273_);
                    v___x_3279_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_3277_);
                    v_h_3280_ = lean_uint64_to_usize(v___x_3279_);
                    v___x_3281_ = 5usize;
                    v___x_3282_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3283_ = 1usize;
                    v___x_3284_ = lean_usize_sub(v_depth_3270_, v___x_3283_);
                    v___x_3285_ = lean_usize_mul(v___x_3281_, v___x_3284_);
                    v_h_3286_ = lean_usize_shift_right(v_h_3280_, v___x_3285_);
                    v___x_3287_ = lean_nat_add(v_i_3273_, v___x_3282_);
                    leanh::lean_dec(v_i_3273_);
                    leanh::lean_inc(v_v_3278_);
                    leanh::lean_inc(v_k_3277_);
                    v___x_3288_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_entries_3274_, v_h_3286_, v_depth_3270_, v_k_3277_, v_v_3278_);
                    v_i_3273_ = v___x_3287_;
                    v_entries_3274_ = v___x_3288_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_depth_3290_: *mut leanh::LeanObject,
    mut v_keys_3291_: *mut leanh::LeanObject,
    mut v_vals_3292_: *mut leanh::LeanObject,
    mut v_i_3293_: *mut leanh::LeanObject,
    mut v_entries_3294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_3295_: usize = 0;
    let mut v_res_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3295_ = leanh::lean_unbox_usize(v_depth_3290_);
    leanh::lean_dec(v_depth_3290_);
    v_res_3296_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_3295_, v_keys_3291_, v_vals_3292_, v_i_3293_, v_entries_3294_);
    leanh::lean_dec_ref(v_vals_3292_);
    leanh::lean_dec_ref(v_keys_3291_);
    return v_res_3296_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___boxed(
    mut v_x_3297_: *mut leanh::LeanObject,
    mut v_x_3298_: *mut leanh::LeanObject,
    mut v_x_3299_: *mut leanh::LeanObject,
    mut v_x_3300_: *mut leanh::LeanObject,
    mut v_x_3301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_7030__boxed_3302_: usize = 0;
    let mut v_x_7031__boxed_3303_: usize = 0;
    let mut v_res_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_7030__boxed_3302_ = leanh::lean_unbox_usize(v_x_3298_);
    leanh::lean_dec(v_x_3298_);
    v_x_7031__boxed_3303_ = leanh::lean_unbox_usize(v_x_3299_);
    leanh::lean_dec(v_x_3299_);
    v_res_3304_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_3297_, v_x_7030__boxed_3302_, v_x_7031__boxed_3303_, v_x_3300_, v_x_3301_);
    return v_res_3304_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(
    mut v_x_3305_: *mut leanh::LeanObject,
    mut v_x_3306_: *mut leanh::LeanObject,
    mut v_x_3307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3308_: u64 = 0;
    let mut v___x_3309_: usize = 0;
    let mut v___x_3310_: usize = 0;
    let mut v___x_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3308_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_3306_);
    v___x_3309_ = lean_uint64_to_usize(v___x_3308_);
    v___x_3310_ = 1usize;
    v___x_3311_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_3305_, v___x_3309_, v___x_3310_, v_x_3306_, v_x_3307_);
    return v___x_3311_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0(
    mut v_e_3312_: *mut leanh::LeanObject,
    mut v_a_3313_: *mut leanh::LeanObject,
    mut v_s_3314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_structs_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToStructId_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToStructIdEntries_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_forbiddenNatModules_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natStructs_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natTypeIdOf_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNatStructId_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3325_: u8 = 0;
    let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3332_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_3315_ = leanh::lean_ctor_get(v_s_3314_, 0);
                v_typeIdOf_3316_ = leanh::lean_ctor_get(v_s_3314_, 1);
                v_exprToStructId_3317_ = leanh::lean_ctor_get(v_s_3314_, 2);
                v_exprToStructIdEntries_3318_ = leanh::lean_ctor_get(v_s_3314_, 3);
                v_forbiddenNatModules_3319_ = leanh::lean_ctor_get(v_s_3314_, 4);
                v_natStructs_3320_ = leanh::lean_ctor_get(v_s_3314_, 5);
                v_natTypeIdOf_3321_ = leanh::lean_ctor_get(v_s_3314_, 6);
                v_exprToNatStructId_3322_ = leanh::lean_ctor_get(v_s_3314_, 7);
                v_isSharedCheck_3332_ = (!leanh::lean_is_exclusive(v_s_3314_)) as u8;
                if v_isSharedCheck_3332_ == 0 {
                    v___x_3324_ = v_s_3314_;
                    v_isShared_3325_ = v_isSharedCheck_3332_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_exprToNatStructId_3322_);
                    leanh::lean_inc(v_natTypeIdOf_3321_);
                    leanh::lean_inc(v_natStructs_3320_);
                    leanh::lean_inc(v_forbiddenNatModules_3319_);
                    leanh::lean_inc(v_exprToStructIdEntries_3318_);
                    leanh::lean_inc(v_exprToStructId_3317_);
                    leanh::lean_inc(v_typeIdOf_3316_);
                    leanh::lean_inc(v_structs_3315_);
                    leanh::lean_dec(v_s_3314_);
                    v___x_3324_ = leanh::lean_box(0);
                    v_isShared_3325_ = v_isSharedCheck_3332_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_n(v_a_3313_, 2);
                leanh::lean_inc_ref(v_e_3312_);
                v___x_3326_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(v_exprToStructId_3317_, v_e_3312_, v_a_3313_);
                v___x_3327_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3327_, 0, v_e_3312_);
                leanh::lean_ctor_set(v___x_3327_, 1, v_a_3313_);
                v___x_3328_ = l_Lean_PersistentArray_push___redArg(
                    v_exprToStructIdEntries_3318_,
                    v___x_3327_,
                );
                if v_isShared_3325_ == 0 {
                    leanh::lean_ctor_set(v___x_3324_, 3, v___x_3328_);
                    leanh::lean_ctor_set(v___x_3324_, 2, v___x_3326_);
                    v___x_3330_ = v___x_3324_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3331_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_structs_3315_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3331_, 1, v_typeIdOf_3316_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3331_, 2, v___x_3326_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3331_, 3, v___x_3328_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3331_,
                        4,
                        v_forbiddenNatModules_3319_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3331_, 5, v_natStructs_3320_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3331_, 6, v_natTypeIdOf_3321_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3331_,
                        7,
                        v_exprToNatStructId_3322_,
                    );
                    v___x_3330_ = v_reuseFailAlloc_3331_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3330_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0___boxed(
    mut v_e_3333_: *mut leanh::LeanObject,
    mut v_a_3334_: *mut leanh::LeanObject,
    mut v_s_3335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3336_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0(
        v_e_3333_, v_a_3334_, v_s_3335_,
    );
    leanh::lean_dec(v_a_3334_);
    return v_res_3336_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3338_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__0;
    v___x_3339_ = l_Lean_stringToMessageData(v___x_3338_);
    return v___x_3339_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(
    mut v_e_3340_: *mut leanh::LeanObject,
    mut v_a_3341_: *mut leanh::LeanObject,
    mut v_a_3342_: *mut leanh::LeanObject,
    mut v_a_3343_: *mut leanh::LeanObject,
    mut v_a_3344_: *mut leanh::LeanObject,
    mut v_a_3345_: *mut leanh::LeanObject,
    mut v_a_3346_: *mut leanh::LeanObject,
    mut v_a_3347_: *mut leanh::LeanObject,
    mut v_a_3348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: u8 = 0;
    let mut v___x_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: u8 = 0;
    let mut v___x_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3367_: u8 = 0;
    let mut v___x_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3371_: u8 = 0;
    let mut v___f_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3378_: u8 = 0;
    let mut v___x_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3382_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3353_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(
                    v_e_3340_, v_a_3342_, v_a_3347_,
                );
                if leanh::lean_obj_tag(v___x_3353_) == 0 {
                    v_a_3354_ = leanh::lean_ctor_get(v___x_3353_, 0);
                    leanh::lean_inc(v_a_3354_);
                    leanh::lean_dec_ref_known(v___x_3353_, 1);
                    if leanh::lean_obj_tag(v_a_3354_) == 1 {
                        v_val_3355_ = leanh::lean_ctor_get(v_a_3354_, 0);
                        leanh::lean_inc(v_val_3355_);
                        leanh::lean_dec_ref_known(v_a_3354_, 1);
                        v___x_3356_ = lean_nat_dec_eq(v_val_3355_, v_a_3341_);
                        leanh::lean_dec(v_val_3355_);
                        if v___x_3356_ == 0 {
                            v___x_3357_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3343_);
                            if leanh::lean_obj_tag(v___x_3357_) == 0 {
                                v_a_3358_ = leanh::lean_ctor_get(v___x_3357_, 0);
                                leanh::lean_inc(v_a_3358_);
                                leanh::lean_dec_ref_known(v___x_3357_, 1);
                                v___x_3359_ = (leanh::lean_unbox(v_a_3358_) as u8);
                                leanh::lean_dec(v_a_3358_);
                                if v___x_3359_ == 0 {
                                    leanh::lean_dec_ref(v_e_3340_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_3360_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1_once), _init_l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1);
                                    v___x_3361_ = l_Lean_indentExpr(v_e_3340_);
                                    v___x_3362_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3362_, 0, v___x_3360_);
                                    leanh::lean_ctor_set(v___x_3362_, 1, v___x_3361_);
                                    v___x_3363_ = l_Lean_Meta_Sym_reportIssue(
                                        v___x_3362_,
                                        v_a_3343_,
                                        v_a_3344_,
                                        v_a_3345_,
                                        v_a_3346_,
                                        v_a_3347_,
                                        v_a_3348_,
                                    );
                                    if leanh::lean_obj_tag(v___x_3363_) == 0 {
                                        leanh::lean_dec_ref_known(v___x_3363_, 1);
                                        state = 1;
                                        continue;
                                    } else {
                                        return v___x_3363_;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_e_3340_);
                                v_a_3364_ = leanh::lean_ctor_get(v___x_3357_, 0);
                                v_isSharedCheck_3371_ =
                                    (!leanh::lean_is_exclusive(v___x_3357_)) as u8;
                                if v_isSharedCheck_3371_ == 0 {
                                    v___x_3366_ = v___x_3357_;
                                    v_isShared_3367_ = v_isSharedCheck_3371_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3364_);
                                    leanh::lean_dec(v___x_3357_);
                                    v___x_3366_ = leanh::lean_box(0);
                                    v_isShared_3367_ = v_isSharedCheck_3371_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_e_3340_);
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3354_);
                        leanh::lean_inc(v_a_3341_);
                        v___f_3372_ = leanh::lean_alloc_closure(
                            l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0___boxed
                                as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        leanh::lean_closure_set(v___f_3372_, 0, v_e_3340_);
                        leanh::lean_closure_set(v___f_3372_, 1, v_a_3341_);
                        v___x_3373_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
                        v___x_3374_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3373_, v___f_3372_, v_a_3342_);
                        return v___x_3374_;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_3340_);
                    v_a_3375_ = leanh::lean_ctor_get(v___x_3353_, 0);
                    v_isSharedCheck_3382_ = (!leanh::lean_is_exclusive(v___x_3353_)) as u8;
                    if v_isSharedCheck_3382_ == 0 {
                        v___x_3377_ = v___x_3353_;
                        v_isShared_3378_ = v_isSharedCheck_3382_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3375_);
                        leanh::lean_dec(v___x_3353_);
                        v___x_3377_ = leanh::lean_box(0);
                        v_isShared_3378_ = v_isSharedCheck_3382_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3351_ = leanh::lean_box(0);
                v___x_3352_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3352_, 0, v___x_3351_);
                return v___x_3352_;
            }
            2 => {
                if v_isShared_3367_ == 0 {
                    v___x_3369_ = v___x_3366_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3370_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_a_3364_);
                    v___x_3369_ = v_reuseFailAlloc_3370_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3369_;
            }
            4 => {
                if v_isShared_3378_ == 0 {
                    v___x_3380_ = v___x_3377_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3381_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_a_3375_);
                    v___x_3380_ = v_reuseFailAlloc_3381_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3380_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___boxed(
    mut v_e_3383_: *mut leanh::LeanObject,
    mut v_a_3384_: *mut leanh::LeanObject,
    mut v_a_3385_: *mut leanh::LeanObject,
    mut v_a_3386_: *mut leanh::LeanObject,
    mut v_a_3387_: *mut leanh::LeanObject,
    mut v_a_3388_: *mut leanh::LeanObject,
    mut v_a_3389_: *mut leanh::LeanObject,
    mut v_a_3390_: *mut leanh::LeanObject,
    mut v_a_3391_: *mut leanh::LeanObject,
    mut v_a_3392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3393_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(
        v_e_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_,
        v_a_3391_,
    );
    leanh::lean_dec(v_a_3391_);
    leanh::lean_dec_ref(v_a_3390_);
    leanh::lean_dec(v_a_3389_);
    leanh::lean_dec_ref(v_a_3388_);
    leanh::lean_dec(v_a_3387_);
    leanh::lean_dec_ref(v_a_3386_);
    leanh::lean_dec(v_a_3385_);
    leanh::lean_dec(v_a_3384_);
    return v_res_3393_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_setTermStructId(
    mut v_e_3394_: *mut leanh::LeanObject,
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
    mut v_a_3405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3407_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(
        v_e_3394_, v_a_3395_, v_a_3396_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_,
        v_a_3405_,
    );
    return v___x_3407_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_setTermStructId___boxed(
    mut v_e_3408_: *mut leanh::LeanObject,
    mut v_a_3409_: *mut leanh::LeanObject,
    mut v_a_3410_: *mut leanh::LeanObject,
    mut v_a_3411_: *mut leanh::LeanObject,
    mut v_a_3412_: *mut leanh::LeanObject,
    mut v_a_3413_: *mut leanh::LeanObject,
    mut v_a_3414_: *mut leanh::LeanObject,
    mut v_a_3415_: *mut leanh::LeanObject,
    mut v_a_3416_: *mut leanh::LeanObject,
    mut v_a_3417_: *mut leanh::LeanObject,
    mut v_a_3418_: *mut leanh::LeanObject,
    mut v_a_3419_: *mut leanh::LeanObject,
    mut v_a_3420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3421_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId(
        v_e_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_,
        v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_,
    );
    leanh::lean_dec(v_a_3419_);
    leanh::lean_dec_ref(v_a_3418_);
    leanh::lean_dec(v_a_3417_);
    leanh::lean_dec_ref(v_a_3416_);
    leanh::lean_dec(v_a_3415_);
    leanh::lean_dec_ref(v_a_3414_);
    leanh::lean_dec(v_a_3413_);
    leanh::lean_dec_ref(v_a_3412_);
    leanh::lean_dec(v_a_3411_);
    leanh::lean_dec(v_a_3410_);
    leanh::lean_dec(v_a_3409_);
    return v_res_3421_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0(
    mut v_00_u03b2_3422_: *mut leanh::LeanObject,
    mut v_x_3423_: *mut leanh::LeanObject,
    mut v_x_3424_: *mut leanh::LeanObject,
    mut v_x_3425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3426_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(v_x_3423_, v_x_3424_, v_x_3425_);
    return v___x_3426_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0(
    mut v_00_u03b2_3427_: *mut leanh::LeanObject,
    mut v_x_3428_: *mut leanh::LeanObject,
    mut v_x_3429_: usize,
    mut v_x_3430_: usize,
    mut v_x_3431_: *mut leanh::LeanObject,
    mut v_x_3432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3433_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_3428_, v_x_3429_, v_x_3430_, v_x_3431_, v_x_3432_);
    return v___x_3433_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___boxed(
    mut v_00_u03b2_3434_: *mut leanh::LeanObject,
    mut v_x_3435_: *mut leanh::LeanObject,
    mut v_x_3436_: *mut leanh::LeanObject,
    mut v_x_3437_: *mut leanh::LeanObject,
    mut v_x_3438_: *mut leanh::LeanObject,
    mut v_x_3439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_7313__boxed_3440_: usize = 0;
    let mut v_x_7314__boxed_3441_: usize = 0;
    let mut v_res_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_7313__boxed_3440_ = leanh::lean_unbox_usize(v_x_3436_);
    leanh::lean_dec(v_x_3436_);
    v_x_7314__boxed_3441_ = leanh::lean_unbox_usize(v_x_3437_);
    leanh::lean_dec(v_x_3437_);
    v_res_3442_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0(v_00_u03b2_3434_, v_x_3435_, v_x_7313__boxed_3440_, v_x_7314__boxed_3441_, v_x_3438_, v_x_3439_);
    return v_res_3442_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3443_: *mut leanh::LeanObject,
    mut v_n_3444_: *mut leanh::LeanObject,
    mut v_k_3445_: *mut leanh::LeanObject,
    mut v_v_3446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3447_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(v_n_3444_, v_k_3445_, v_v_3446_);
    return v___x_3447_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2(
    mut v_00_u03b2_3448_: *mut leanh::LeanObject,
    mut v_depth_3449_: usize,
    mut v_keys_3450_: *mut leanh::LeanObject,
    mut v_vals_3451_: *mut leanh::LeanObject,
    mut v_heq_3452_: *mut leanh::LeanObject,
    mut v_i_3453_: *mut leanh::LeanObject,
    mut v_entries_3454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3455_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(v_depth_3449_, v_keys_3450_, v_vals_3451_, v_i_3453_, v_entries_3454_);
    return v___x_3455_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_3456_: *mut leanh::LeanObject,
    mut v_depth_3457_: *mut leanh::LeanObject,
    mut v_keys_3458_: *mut leanh::LeanObject,
    mut v_vals_3459_: *mut leanh::LeanObject,
    mut v_heq_3460_: *mut leanh::LeanObject,
    mut v_i_3461_: *mut leanh::LeanObject,
    mut v_entries_3462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_3463_: usize = 0;
    let mut v_res_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3463_ = leanh::lean_unbox_usize(v_depth_3457_);
    leanh::lean_dec(v_depth_3457_);
    v_res_3464_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2(v_00_u03b2_3456_, v_depth_boxed_3463_, v_keys_3458_, v_vals_3459_, v_heq_3460_, v_i_3461_, v_entries_3462_);
    leanh::lean_dec_ref(v_vals_3459_);
    leanh::lean_dec_ref(v_keys_3458_);
    return v_res_3464_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_3465_: *mut leanh::LeanObject,
    mut v_x_3466_: *mut leanh::LeanObject,
    mut v_x_3467_: *mut leanh::LeanObject,
    mut v_x_3468_: *mut leanh::LeanObject,
    mut v_x_3469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3470_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_3466_, v_x_3467_, v_x_3468_, v_x_3469_);
    return v___x_3470_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(
    mut v_msgData_3471_: *mut leanh::LeanObject,
    mut v___y_3472_: *mut leanh::LeanObject,
    mut v___y_3473_: *mut leanh::LeanObject,
    mut v___y_3474_: *mut leanh::LeanObject,
    mut v___y_3475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3477_ = lean_st_ref_get(v___y_3475_);
    v_env_3478_ = leanh::lean_ctor_get(v___x_3477_, 0);
    leanh::lean_inc_ref(v_env_3478_);
    leanh::lean_dec(v___x_3477_);
    v___x_3479_ = lean_st_ref_get(v___y_3473_);
    v_mctx_3480_ = leanh::lean_ctor_get(v___x_3479_, 0);
    leanh::lean_inc_ref(v_mctx_3480_);
    leanh::lean_dec(v___x_3479_);
    v_lctx_3481_ = leanh::lean_ctor_get(v___y_3472_, 2);
    v_options_3482_ = leanh::lean_ctor_get(v___y_3474_, 2);
    leanh::lean_inc_ref(v_options_3482_);
    leanh::lean_inc_ref(v_lctx_3481_);
    v___x_3483_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3483_, 0, v_env_3478_);
    leanh::lean_ctor_set(v___x_3483_, 1, v_mctx_3480_);
    leanh::lean_ctor_set(v___x_3483_, 2, v_lctx_3481_);
    leanh::lean_ctor_set(v___x_3483_, 3, v_options_3482_);
    v___x_3484_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3484_, 0, v___x_3483_);
    leanh::lean_ctor_set(v___x_3484_, 1, v_msgData_3471_);
    v___x_3485_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3485_, 0, v___x_3484_);
    return v___x_3485_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0___boxed(
    mut v_msgData_3486_: *mut leanh::LeanObject,
    mut v___y_3487_: *mut leanh::LeanObject,
    mut v___y_3488_: *mut leanh::LeanObject,
    mut v___y_3489_: *mut leanh::LeanObject,
    mut v___y_3490_: *mut leanh::LeanObject,
    mut v___y_3491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3492_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(v_msgData_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
    leanh::lean_dec(v___y_3490_);
    leanh::lean_dec_ref(v___y_3489_);
    leanh::lean_dec(v___y_3488_);
    leanh::lean_dec_ref(v___y_3487_);
    return v_res_3492_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(
    mut v_msg_3493_: *mut leanh::LeanObject,
    mut v___y_3494_: *mut leanh::LeanObject,
    mut v___y_3495_: *mut leanh::LeanObject,
    mut v___y_3496_: *mut leanh::LeanObject,
    mut v___y_3497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3504_: u8 = 0;
    let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3509_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3499_ = leanh::lean_ctor_get(v___y_3496_, 5);
                v___x_3500_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(v_msg_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_);
                v_a_3501_ = leanh::lean_ctor_get(v___x_3500_, 0);
                v_isSharedCheck_3509_ = (!leanh::lean_is_exclusive(v___x_3500_)) as u8;
                if v_isSharedCheck_3509_ == 0 {
                    v___x_3503_ = v___x_3500_;
                    v_isShared_3504_ = v_isSharedCheck_3509_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3501_);
                    leanh::lean_dec(v___x_3500_);
                    v___x_3503_ = leanh::lean_box(0);
                    v_isShared_3504_ = v_isSharedCheck_3509_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_3499_);
                v___x_3505_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3505_, 0, v_ref_3499_);
                leanh::lean_ctor_set(v___x_3505_, 1, v_a_3501_);
                if v_isShared_3504_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3503_, 1);
                    leanh::lean_ctor_set(v___x_3503_, 0, v___x_3505_);
                    v___x_3507_ = v___x_3503_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3508_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3505_);
                    v___x_3507_ = v_reuseFailAlloc_3508_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3507_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg___boxed(
    mut v_msg_3510_: *mut leanh::LeanObject,
    mut v___y_3511_: *mut leanh::LeanObject,
    mut v___y_3512_: *mut leanh::LeanObject,
    mut v___y_3513_: *mut leanh::LeanObject,
    mut v___y_3514_: *mut leanh::LeanObject,
    mut v___y_3515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3516_ =
        l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(
            v_msg_3510_,
            v___y_3511_,
            v___y_3512_,
            v___y_3513_,
            v___y_3514_,
        );
    leanh::lean_dec(v___y_3514_);
    leanh::lean_dec_ref(v___y_3513_);
    leanh::lean_dec(v___y_3512_);
    leanh::lean_dec_ref(v___y_3511_);
    return v_res_3516_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3518_ = l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__0;
    v___x_3519_ = l_Lean_stringToMessageData(v___x_3518_);
    return v___x_3519_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst(
    mut v_a_3520_: *mut leanh::LeanObject,
    mut v_a_3521_: *mut leanh::LeanObject,
    mut v_a_3522_: *mut leanh::LeanObject,
    mut v_a_3523_: *mut leanh::LeanObject,
    mut v_a_3524_: *mut leanh::LeanObject,
    mut v_a_3525_: *mut leanh::LeanObject,
    mut v_a_3526_: *mut leanh::LeanObject,
    mut v_a_3527_: *mut leanh::LeanObject,
    mut v_a_3528_: *mut leanh::LeanObject,
    mut v_a_3529_: *mut leanh::LeanObject,
    mut v_a_3530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3536_: u8 = 0;
    let mut v_noNatDivInst_x3f_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3544_: u8 = 0;
    let mut v_a_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3548_: u8 = 0;
    let mut v___x_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3552_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3532_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_3520_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_,
                    v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_,
                );
                if leanh::lean_obj_tag(v___x_3532_) == 0 {
                    v_a_3533_ = leanh::lean_ctor_get(v___x_3532_, 0);
                    v_isSharedCheck_3544_ = (!leanh::lean_is_exclusive(v___x_3532_)) as u8;
                    if v_isSharedCheck_3544_ == 0 {
                        v___x_3535_ = v___x_3532_;
                        v_isShared_3536_ = v_isSharedCheck_3544_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3533_);
                        leanh::lean_dec(v___x_3532_);
                        v___x_3535_ = leanh::lean_box(0);
                        v_isShared_3536_ = v_isSharedCheck_3544_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3545_ = leanh::lean_ctor_get(v___x_3532_, 0);
                    v_isSharedCheck_3552_ = (!leanh::lean_is_exclusive(v___x_3532_)) as u8;
                    if v_isSharedCheck_3552_ == 0 {
                        v___x_3547_ = v___x_3532_;
                        v_isShared_3548_ = v_isSharedCheck_3552_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3545_);
                        leanh::lean_dec(v___x_3532_);
                        v___x_3547_ = leanh::lean_box(0);
                        v_isShared_3548_ = v_isSharedCheck_3552_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_noNatDivInst_x3f_3537_ = leanh::lean_ctor_get(v_a_3533_, 11);
                leanh::lean_inc(v_noNatDivInst_x3f_3537_);
                leanh::lean_dec(v_a_3533_);
                if leanh::lean_obj_tag(v_noNatDivInst_x3f_3537_) == 1 {
                    v_val_3538_ = leanh::lean_ctor_get(v_noNatDivInst_x3f_3537_, 0);
                    leanh::lean_inc(v_val_3538_);
                    leanh::lean_dec_ref_known(v_noNatDivInst_x3f_3537_, 1);
                    if v_isShared_3536_ == 0 {
                        leanh::lean_ctor_set(v___x_3535_, 0, v_val_3538_);
                        v___x_3540_ = v___x_3535_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3541_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_val_3538_);
                        v___x_3540_ = v_reuseFailAlloc_3541_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_noNatDivInst_x3f_3537_);
                    leanh::lean_del_object(v___x_3535_);
                    v___x_3542_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1,
                    );
                    v___x_3543_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_3542_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_);
                    return v___x_3543_;
                }
            }
            2 => {
                return v___x_3540_;
            }
            3 => {
                if v_isShared_3548_ == 0 {
                    v___x_3550_ = v___x_3547_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3551_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_a_3545_);
                    v___x_3550_ = v_reuseFailAlloc_3551_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3550_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___boxed(
    mut v_a_3553_: *mut leanh::LeanObject,
    mut v_a_3554_: *mut leanh::LeanObject,
    mut v_a_3555_: *mut leanh::LeanObject,
    mut v_a_3556_: *mut leanh::LeanObject,
    mut v_a_3557_: *mut leanh::LeanObject,
    mut v_a_3558_: *mut leanh::LeanObject,
    mut v_a_3559_: *mut leanh::LeanObject,
    mut v_a_3560_: *mut leanh::LeanObject,
    mut v_a_3561_: *mut leanh::LeanObject,
    mut v_a_3562_: *mut leanh::LeanObject,
    mut v_a_3563_: *mut leanh::LeanObject,
    mut v_a_3564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3565_ = l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst(
        v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_,
        v_a_3561_, v_a_3562_, v_a_3563_,
    );
    leanh::lean_dec(v_a_3563_);
    leanh::lean_dec_ref(v_a_3562_);
    leanh::lean_dec(v_a_3561_);
    leanh::lean_dec_ref(v_a_3560_);
    leanh::lean_dec(v_a_3559_);
    leanh::lean_dec_ref(v_a_3558_);
    leanh::lean_dec(v_a_3557_);
    leanh::lean_dec_ref(v_a_3556_);
    leanh::lean_dec(v_a_3555_);
    leanh::lean_dec(v_a_3554_);
    leanh::lean_dec(v_a_3553_);
    return v_res_3565_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0(
    mut v_00_u03b1_3566_: *mut leanh::LeanObject,
    mut v_msg_3567_: *mut leanh::LeanObject,
    mut v___y_3568_: *mut leanh::LeanObject,
    mut v___y_3569_: *mut leanh::LeanObject,
    mut v___y_3570_: *mut leanh::LeanObject,
    mut v___y_3571_: *mut leanh::LeanObject,
    mut v___y_3572_: *mut leanh::LeanObject,
    mut v___y_3573_: *mut leanh::LeanObject,
    mut v___y_3574_: *mut leanh::LeanObject,
    mut v___y_3575_: *mut leanh::LeanObject,
    mut v___y_3576_: *mut leanh::LeanObject,
    mut v___y_3577_: *mut leanh::LeanObject,
    mut v___y_3578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3580_ =
        l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(
            v_msg_3567_,
            v___y_3575_,
            v___y_3576_,
            v___y_3577_,
            v___y_3578_,
        );
    return v___x_3580_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___boxed(
    mut v_00_u03b1_3581_: *mut leanh::LeanObject,
    mut v_msg_3582_: *mut leanh::LeanObject,
    mut v___y_3583_: *mut leanh::LeanObject,
    mut v___y_3584_: *mut leanh::LeanObject,
    mut v___y_3585_: *mut leanh::LeanObject,
    mut v___y_3586_: *mut leanh::LeanObject,
    mut v___y_3587_: *mut leanh::LeanObject,
    mut v___y_3588_: *mut leanh::LeanObject,
    mut v___y_3589_: *mut leanh::LeanObject,
    mut v___y_3590_: *mut leanh::LeanObject,
    mut v___y_3591_: *mut leanh::LeanObject,
    mut v___y_3592_: *mut leanh::LeanObject,
    mut v___y_3593_: *mut leanh::LeanObject,
    mut v___y_3594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3595_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0(
        v_00_u03b1_3581_,
        v_msg_3582_,
        v___y_3583_,
        v___y_3584_,
        v___y_3585_,
        v___y_3586_,
        v___y_3587_,
        v___y_3588_,
        v___y_3589_,
        v___y_3590_,
        v___y_3591_,
        v___y_3592_,
        v___y_3593_,
    );
    leanh::lean_dec(v___y_3593_);
    leanh::lean_dec_ref(v___y_3592_);
    leanh::lean_dec(v___y_3591_);
    leanh::lean_dec_ref(v___y_3590_);
    leanh::lean_dec(v___y_3589_);
    leanh::lean_dec_ref(v___y_3588_);
    leanh::lean_dec(v___y_3587_);
    leanh::lean_dec_ref(v___y_3586_);
    leanh::lean_dec(v___y_3585_);
    leanh::lean_dec(v___y_3584_);
    leanh::lean_dec(v___y_3583_);
    return v_res_3595_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3597_ = l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__0;
    v___x_3598_ = l_Lean_stringToMessageData(v___x_3597_);
    return v___x_3598_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getLEInst(
    mut v_a_3599_: *mut leanh::LeanObject,
    mut v_a_3600_: *mut leanh::LeanObject,
    mut v_a_3601_: *mut leanh::LeanObject,
    mut v_a_3602_: *mut leanh::LeanObject,
    mut v_a_3603_: *mut leanh::LeanObject,
    mut v_a_3604_: *mut leanh::LeanObject,
    mut v_a_3605_: *mut leanh::LeanObject,
    mut v_a_3606_: *mut leanh::LeanObject,
    mut v_a_3607_: *mut leanh::LeanObject,
    mut v_a_3608_: *mut leanh::LeanObject,
    mut v_a_3609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3615_: u8 = 0;
    let mut v_leInst_x3f_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3623_: u8 = 0;
    let mut v_a_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3627_: u8 = 0;
    let mut v___x_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3631_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3611_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_,
                    v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_,
                );
                if leanh::lean_obj_tag(v___x_3611_) == 0 {
                    v_a_3612_ = leanh::lean_ctor_get(v___x_3611_, 0);
                    v_isSharedCheck_3623_ = (!leanh::lean_is_exclusive(v___x_3611_)) as u8;
                    if v_isSharedCheck_3623_ == 0 {
                        v___x_3614_ = v___x_3611_;
                        v_isShared_3615_ = v_isSharedCheck_3623_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3612_);
                        leanh::lean_dec(v___x_3611_);
                        v___x_3614_ = leanh::lean_box(0);
                        v_isShared_3615_ = v_isSharedCheck_3623_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3624_ = leanh::lean_ctor_get(v___x_3611_, 0);
                    v_isSharedCheck_3631_ = (!leanh::lean_is_exclusive(v___x_3611_)) as u8;
                    if v_isSharedCheck_3631_ == 0 {
                        v___x_3626_ = v___x_3611_;
                        v_isShared_3627_ = v_isSharedCheck_3631_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3624_);
                        leanh::lean_dec(v___x_3611_);
                        v___x_3626_ = leanh::lean_box(0);
                        v_isShared_3627_ = v_isSharedCheck_3631_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_leInst_x3f_3616_ = leanh::lean_ctor_get(v_a_3612_, 5);
                leanh::lean_inc(v_leInst_x3f_3616_);
                leanh::lean_dec(v_a_3612_);
                if leanh::lean_obj_tag(v_leInst_x3f_3616_) == 1 {
                    v_val_3617_ = leanh::lean_ctor_get(v_leInst_x3f_3616_, 0);
                    leanh::lean_inc(v_val_3617_);
                    leanh::lean_dec_ref_known(v_leInst_x3f_3616_, 1);
                    if v_isShared_3615_ == 0 {
                        leanh::lean_ctor_set(v___x_3614_, 0, v_val_3617_);
                        v___x_3619_ = v___x_3614_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3620_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_val_3617_);
                        v___x_3619_ = v_reuseFailAlloc_3620_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_leInst_x3f_3616_);
                    leanh::lean_del_object(v___x_3614_);
                    v___x_3621_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1,
                    );
                    v___x_3622_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_3621_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_);
                    return v___x_3622_;
                }
            }
            2 => {
                return v___x_3619_;
            }
            3 => {
                if v_isShared_3627_ == 0 {
                    v___x_3629_ = v___x_3626_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3630_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3624_);
                    v___x_3629_ = v_reuseFailAlloc_3630_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3629_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getLEInst___boxed(
    mut v_a_3632_: *mut leanh::LeanObject,
    mut v_a_3633_: *mut leanh::LeanObject,
    mut v_a_3634_: *mut leanh::LeanObject,
    mut v_a_3635_: *mut leanh::LeanObject,
    mut v_a_3636_: *mut leanh::LeanObject,
    mut v_a_3637_: *mut leanh::LeanObject,
    mut v_a_3638_: *mut leanh::LeanObject,
    mut v_a_3639_: *mut leanh::LeanObject,
    mut v_a_3640_: *mut leanh::LeanObject,
    mut v_a_3641_: *mut leanh::LeanObject,
    mut v_a_3642_: *mut leanh::LeanObject,
    mut v_a_3643_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3644_ = l_Lean_Meta_Grind_Arith_Linear_getLEInst(
        v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_,
        v_a_3640_, v_a_3641_, v_a_3642_,
    );
    leanh::lean_dec(v_a_3642_);
    leanh::lean_dec_ref(v_a_3641_);
    leanh::lean_dec(v_a_3640_);
    leanh::lean_dec_ref(v_a_3639_);
    leanh::lean_dec(v_a_3638_);
    leanh::lean_dec_ref(v_a_3637_);
    leanh::lean_dec(v_a_3636_);
    leanh::lean_dec_ref(v_a_3635_);
    leanh::lean_dec(v_a_3634_);
    leanh::lean_dec(v_a_3633_);
    leanh::lean_dec(v_a_3632_);
    return v_res_3644_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3646_ = l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__0;
    v___x_3647_ = l_Lean_stringToMessageData(v___x_3646_);
    return v___x_3647_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getLTInst(
    mut v_a_3648_: *mut leanh::LeanObject,
    mut v_a_3649_: *mut leanh::LeanObject,
    mut v_a_3650_: *mut leanh::LeanObject,
    mut v_a_3651_: *mut leanh::LeanObject,
    mut v_a_3652_: *mut leanh::LeanObject,
    mut v_a_3653_: *mut leanh::LeanObject,
    mut v_a_3654_: *mut leanh::LeanObject,
    mut v_a_3655_: *mut leanh::LeanObject,
    mut v_a_3656_: *mut leanh::LeanObject,
    mut v_a_3657_: *mut leanh::LeanObject,
    mut v_a_3658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3664_: u8 = 0;
    let mut v_ltInst_x3f_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3672_: u8 = 0;
    let mut v_a_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3676_: u8 = 0;
    let mut v___x_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3680_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3660_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_,
                    v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_,
                );
                if leanh::lean_obj_tag(v___x_3660_) == 0 {
                    v_a_3661_ = leanh::lean_ctor_get(v___x_3660_, 0);
                    v_isSharedCheck_3672_ = (!leanh::lean_is_exclusive(v___x_3660_)) as u8;
                    if v_isSharedCheck_3672_ == 0 {
                        v___x_3663_ = v___x_3660_;
                        v_isShared_3664_ = v_isSharedCheck_3672_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3661_);
                        leanh::lean_dec(v___x_3660_);
                        v___x_3663_ = leanh::lean_box(0);
                        v_isShared_3664_ = v_isSharedCheck_3672_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3673_ = leanh::lean_ctor_get(v___x_3660_, 0);
                    v_isSharedCheck_3680_ = (!leanh::lean_is_exclusive(v___x_3660_)) as u8;
                    if v_isSharedCheck_3680_ == 0 {
                        v___x_3675_ = v___x_3660_;
                        v_isShared_3676_ = v_isSharedCheck_3680_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3673_);
                        leanh::lean_dec(v___x_3660_);
                        v___x_3675_ = leanh::lean_box(0);
                        v_isShared_3676_ = v_isSharedCheck_3680_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_ltInst_x3f_3665_ = leanh::lean_ctor_get(v_a_3661_, 6);
                leanh::lean_inc(v_ltInst_x3f_3665_);
                leanh::lean_dec(v_a_3661_);
                if leanh::lean_obj_tag(v_ltInst_x3f_3665_) == 1 {
                    v_val_3666_ = leanh::lean_ctor_get(v_ltInst_x3f_3665_, 0);
                    leanh::lean_inc(v_val_3666_);
                    leanh::lean_dec_ref_known(v_ltInst_x3f_3665_, 1);
                    if v_isShared_3664_ == 0 {
                        leanh::lean_ctor_set(v___x_3663_, 0, v_val_3666_);
                        v___x_3668_ = v___x_3663_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3669_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_val_3666_);
                        v___x_3668_ = v_reuseFailAlloc_3669_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_ltInst_x3f_3665_);
                    leanh::lean_del_object(v___x_3663_);
                    v___x_3670_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1,
                    );
                    v___x_3671_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_3670_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_);
                    return v___x_3671_;
                }
            }
            2 => {
                return v___x_3668_;
            }
            3 => {
                if v_isShared_3676_ == 0 {
                    v___x_3678_ = v___x_3675_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3679_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_a_3673_);
                    v___x_3678_ = v_reuseFailAlloc_3679_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3678_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getLTInst___boxed(
    mut v_a_3681_: *mut leanh::LeanObject,
    mut v_a_3682_: *mut leanh::LeanObject,
    mut v_a_3683_: *mut leanh::LeanObject,
    mut v_a_3684_: *mut leanh::LeanObject,
    mut v_a_3685_: *mut leanh::LeanObject,
    mut v_a_3686_: *mut leanh::LeanObject,
    mut v_a_3687_: *mut leanh::LeanObject,
    mut v_a_3688_: *mut leanh::LeanObject,
    mut v_a_3689_: *mut leanh::LeanObject,
    mut v_a_3690_: *mut leanh::LeanObject,
    mut v_a_3691_: *mut leanh::LeanObject,
    mut v_a_3692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3693_ = l_Lean_Meta_Grind_Arith_Linear_getLTInst(
        v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_, v_a_3685_, v_a_3686_, v_a_3687_, v_a_3688_,
        v_a_3689_, v_a_3690_, v_a_3691_,
    );
    leanh::lean_dec(v_a_3691_);
    leanh::lean_dec_ref(v_a_3690_);
    leanh::lean_dec(v_a_3689_);
    leanh::lean_dec_ref(v_a_3688_);
    leanh::lean_dec(v_a_3687_);
    leanh::lean_dec_ref(v_a_3686_);
    leanh::lean_dec(v_a_3685_);
    leanh::lean_dec_ref(v_a_3684_);
    leanh::lean_dec(v_a_3683_);
    leanh::lean_dec(v_a_3682_);
    leanh::lean_dec(v_a_3681_);
    return v_res_3693_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3695_ = l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__0;
    v___x_3696_ = l_Lean_stringToMessageData(v___x_3695_);
    return v___x_3696_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst(
    mut v_a_3697_: *mut leanh::LeanObject,
    mut v_a_3698_: *mut leanh::LeanObject,
    mut v_a_3699_: *mut leanh::LeanObject,
    mut v_a_3700_: *mut leanh::LeanObject,
    mut v_a_3701_: *mut leanh::LeanObject,
    mut v_a_3702_: *mut leanh::LeanObject,
    mut v_a_3703_: *mut leanh::LeanObject,
    mut v_a_3704_: *mut leanh::LeanObject,
    mut v_a_3705_: *mut leanh::LeanObject,
    mut v_a_3706_: *mut leanh::LeanObject,
    mut v_a_3707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3713_: u8 = 0;
    let mut v_lawfulOrderLTInst_x3f_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3721_: u8 = 0;
    let mut v_a_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3725_: u8 = 0;
    let mut v___x_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3729_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3709_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_,
                    v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_,
                );
                if leanh::lean_obj_tag(v___x_3709_) == 0 {
                    v_a_3710_ = leanh::lean_ctor_get(v___x_3709_, 0);
                    v_isSharedCheck_3721_ = (!leanh::lean_is_exclusive(v___x_3709_)) as u8;
                    if v_isSharedCheck_3721_ == 0 {
                        v___x_3712_ = v___x_3709_;
                        v_isShared_3713_ = v_isSharedCheck_3721_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3710_);
                        leanh::lean_dec(v___x_3709_);
                        v___x_3712_ = leanh::lean_box(0);
                        v_isShared_3713_ = v_isSharedCheck_3721_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3722_ = leanh::lean_ctor_get(v___x_3709_, 0);
                    v_isSharedCheck_3729_ = (!leanh::lean_is_exclusive(v___x_3709_)) as u8;
                    if v_isSharedCheck_3729_ == 0 {
                        v___x_3724_ = v___x_3709_;
                        v_isShared_3725_ = v_isSharedCheck_3729_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3722_);
                        leanh::lean_dec(v___x_3709_);
                        v___x_3724_ = leanh::lean_box(0);
                        v_isShared_3725_ = v_isSharedCheck_3729_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_lawfulOrderLTInst_x3f_3714_ = leanh::lean_ctor_get(v_a_3710_, 7);
                leanh::lean_inc(v_lawfulOrderLTInst_x3f_3714_);
                leanh::lean_dec(v_a_3710_);
                if leanh::lean_obj_tag(v_lawfulOrderLTInst_x3f_3714_) == 1 {
                    v_val_3715_ = leanh::lean_ctor_get(v_lawfulOrderLTInst_x3f_3714_, 0);
                    leanh::lean_inc(v_val_3715_);
                    leanh::lean_dec_ref_known(v_lawfulOrderLTInst_x3f_3714_, 1);
                    if v_isShared_3713_ == 0 {
                        leanh::lean_ctor_set(v___x_3712_, 0, v_val_3715_);
                        v___x_3717_ = v___x_3712_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3718_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_val_3715_);
                        v___x_3717_ = v_reuseFailAlloc_3718_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_lawfulOrderLTInst_x3f_3714_);
                    leanh::lean_del_object(v___x_3712_);
                    v___x_3719_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1,
                    );
                    v___x_3720_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_3719_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_);
                    return v___x_3720_;
                }
            }
            2 => {
                return v___x_3717_;
            }
            3 => {
                if v_isShared_3725_ == 0 {
                    v___x_3727_ = v___x_3724_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3728_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_a_3722_);
                    v___x_3727_ = v_reuseFailAlloc_3728_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3727_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___boxed(
    mut v_a_3730_: *mut leanh::LeanObject,
    mut v_a_3731_: *mut leanh::LeanObject,
    mut v_a_3732_: *mut leanh::LeanObject,
    mut v_a_3733_: *mut leanh::LeanObject,
    mut v_a_3734_: *mut leanh::LeanObject,
    mut v_a_3735_: *mut leanh::LeanObject,
    mut v_a_3736_: *mut leanh::LeanObject,
    mut v_a_3737_: *mut leanh::LeanObject,
    mut v_a_3738_: *mut leanh::LeanObject,
    mut v_a_3739_: *mut leanh::LeanObject,
    mut v_a_3740_: *mut leanh::LeanObject,
    mut v_a_3741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3742_ = l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst(
        v_a_3730_, v_a_3731_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_,
        v_a_3738_, v_a_3739_, v_a_3740_,
    );
    leanh::lean_dec(v_a_3740_);
    leanh::lean_dec_ref(v_a_3739_);
    leanh::lean_dec(v_a_3738_);
    leanh::lean_dec_ref(v_a_3737_);
    leanh::lean_dec(v_a_3736_);
    leanh::lean_dec_ref(v_a_3735_);
    leanh::lean_dec(v_a_3734_);
    leanh::lean_dec_ref(v_a_3733_);
    leanh::lean_dec(v_a_3732_);
    leanh::lean_dec(v_a_3731_);
    leanh::lean_dec(v_a_3730_);
    return v_res_3742_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3744_ = l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__0;
    v___x_3745_ = l_Lean_stringToMessageData(v___x_3744_);
    return v___x_3745_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst(
    mut v_a_3746_: *mut leanh::LeanObject,
    mut v_a_3747_: *mut leanh::LeanObject,
    mut v_a_3748_: *mut leanh::LeanObject,
    mut v_a_3749_: *mut leanh::LeanObject,
    mut v_a_3750_: *mut leanh::LeanObject,
    mut v_a_3751_: *mut leanh::LeanObject,
    mut v_a_3752_: *mut leanh::LeanObject,
    mut v_a_3753_: *mut leanh::LeanObject,
    mut v_a_3754_: *mut leanh::LeanObject,
    mut v_a_3755_: *mut leanh::LeanObject,
    mut v_a_3756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3762_: u8 = 0;
    let mut v_isPreorderInst_x3f_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3770_: u8 = 0;
    let mut v_a_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3774_: u8 = 0;
    let mut v___x_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3778_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3758_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_,
                    v_a_3753_, v_a_3754_, v_a_3755_, v_a_3756_,
                );
                if leanh::lean_obj_tag(v___x_3758_) == 0 {
                    v_a_3759_ = leanh::lean_ctor_get(v___x_3758_, 0);
                    v_isSharedCheck_3770_ = (!leanh::lean_is_exclusive(v___x_3758_)) as u8;
                    if v_isSharedCheck_3770_ == 0 {
                        v___x_3761_ = v___x_3758_;
                        v_isShared_3762_ = v_isSharedCheck_3770_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3759_);
                        leanh::lean_dec(v___x_3758_);
                        v___x_3761_ = leanh::lean_box(0);
                        v_isShared_3762_ = v_isSharedCheck_3770_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3771_ = leanh::lean_ctor_get(v___x_3758_, 0);
                    v_isSharedCheck_3778_ = (!leanh::lean_is_exclusive(v___x_3758_)) as u8;
                    if v_isSharedCheck_3778_ == 0 {
                        v___x_3773_ = v___x_3758_;
                        v_isShared_3774_ = v_isSharedCheck_3778_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3771_);
                        leanh::lean_dec(v___x_3758_);
                        v___x_3773_ = leanh::lean_box(0);
                        v_isShared_3774_ = v_isSharedCheck_3778_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_isPreorderInst_x3f_3763_ = leanh::lean_ctor_get(v_a_3759_, 8);
                leanh::lean_inc(v_isPreorderInst_x3f_3763_);
                leanh::lean_dec(v_a_3759_);
                if leanh::lean_obj_tag(v_isPreorderInst_x3f_3763_) == 1 {
                    v_val_3764_ = leanh::lean_ctor_get(v_isPreorderInst_x3f_3763_, 0);
                    leanh::lean_inc(v_val_3764_);
                    leanh::lean_dec_ref_known(v_isPreorderInst_x3f_3763_, 1);
                    if v_isShared_3762_ == 0 {
                        leanh::lean_ctor_set(v___x_3761_, 0, v_val_3764_);
                        v___x_3766_ = v___x_3761_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3767_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_val_3764_);
                        v___x_3766_ = v_reuseFailAlloc_3767_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_isPreorderInst_x3f_3763_);
                    leanh::lean_del_object(v___x_3761_);
                    v___x_3768_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1,
                    );
                    v___x_3769_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_3768_, v_a_3753_, v_a_3754_, v_a_3755_, v_a_3756_);
                    return v___x_3769_;
                }
            }
            2 => {
                return v___x_3766_;
            }
            3 => {
                if v_isShared_3774_ == 0 {
                    v___x_3776_ = v___x_3773_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3777_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_a_3771_);
                    v___x_3776_ = v_reuseFailAlloc_3777_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3776_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___boxed(
    mut v_a_3779_: *mut leanh::LeanObject,
    mut v_a_3780_: *mut leanh::LeanObject,
    mut v_a_3781_: *mut leanh::LeanObject,
    mut v_a_3782_: *mut leanh::LeanObject,
    mut v_a_3783_: *mut leanh::LeanObject,
    mut v_a_3784_: *mut leanh::LeanObject,
    mut v_a_3785_: *mut leanh::LeanObject,
    mut v_a_3786_: *mut leanh::LeanObject,
    mut v_a_3787_: *mut leanh::LeanObject,
    mut v_a_3788_: *mut leanh::LeanObject,
    mut v_a_3789_: *mut leanh::LeanObject,
    mut v_a_3790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3791_ = l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst(
        v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_, v_a_3784_, v_a_3785_, v_a_3786_,
        v_a_3787_, v_a_3788_, v_a_3789_,
    );
    leanh::lean_dec(v_a_3789_);
    leanh::lean_dec_ref(v_a_3788_);
    leanh::lean_dec(v_a_3787_);
    leanh::lean_dec_ref(v_a_3786_);
    leanh::lean_dec(v_a_3785_);
    leanh::lean_dec_ref(v_a_3784_);
    leanh::lean_dec(v_a_3783_);
    leanh::lean_dec_ref(v_a_3782_);
    leanh::lean_dec(v_a_3781_);
    leanh::lean_dec(v_a_3780_);
    leanh::lean_dec(v_a_3779_);
    return v_res_3791_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3793_ = l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__0;
    v___x_3794_ = l_Lean_stringToMessageData(v___x_3793_);
    return v___x_3794_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst(
    mut v_a_3795_: *mut leanh::LeanObject,
    mut v_a_3796_: *mut leanh::LeanObject,
    mut v_a_3797_: *mut leanh::LeanObject,
    mut v_a_3798_: *mut leanh::LeanObject,
    mut v_a_3799_: *mut leanh::LeanObject,
    mut v_a_3800_: *mut leanh::LeanObject,
    mut v_a_3801_: *mut leanh::LeanObject,
    mut v_a_3802_: *mut leanh::LeanObject,
    mut v_a_3803_: *mut leanh::LeanObject,
    mut v_a_3804_: *mut leanh::LeanObject,
    mut v_a_3805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3811_: u8 = 0;
    let mut v_orderedAddInst_x3f_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3819_: u8 = 0;
    let mut v_a_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3823_: u8 = 0;
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3827_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3807_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_,
                    v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_,
                );
                if leanh::lean_obj_tag(v___x_3807_) == 0 {
                    v_a_3808_ = leanh::lean_ctor_get(v___x_3807_, 0);
                    v_isSharedCheck_3819_ = (!leanh::lean_is_exclusive(v___x_3807_)) as u8;
                    if v_isSharedCheck_3819_ == 0 {
                        v___x_3810_ = v___x_3807_;
                        v_isShared_3811_ = v_isSharedCheck_3819_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3808_);
                        leanh::lean_dec(v___x_3807_);
                        v___x_3810_ = leanh::lean_box(0);
                        v_isShared_3811_ = v_isSharedCheck_3819_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3820_ = leanh::lean_ctor_get(v___x_3807_, 0);
                    v_isSharedCheck_3827_ = (!leanh::lean_is_exclusive(v___x_3807_)) as u8;
                    if v_isSharedCheck_3827_ == 0 {
                        v___x_3822_ = v___x_3807_;
                        v_isShared_3823_ = v_isSharedCheck_3827_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3820_);
                        leanh::lean_dec(v___x_3807_);
                        v___x_3822_ = leanh::lean_box(0);
                        v_isShared_3823_ = v_isSharedCheck_3827_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_orderedAddInst_x3f_3812_ = leanh::lean_ctor_get(v_a_3808_, 9);
                leanh::lean_inc(v_orderedAddInst_x3f_3812_);
                leanh::lean_dec(v_a_3808_);
                if leanh::lean_obj_tag(v_orderedAddInst_x3f_3812_) == 1 {
                    v_val_3813_ = leanh::lean_ctor_get(v_orderedAddInst_x3f_3812_, 0);
                    leanh::lean_inc(v_val_3813_);
                    leanh::lean_dec_ref_known(v_orderedAddInst_x3f_3812_, 1);
                    if v_isShared_3811_ == 0 {
                        leanh::lean_ctor_set(v___x_3810_, 0, v_val_3813_);
                        v___x_3815_ = v___x_3810_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3816_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_val_3813_);
                        v___x_3815_ = v_reuseFailAlloc_3816_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_orderedAddInst_x3f_3812_);
                    leanh::lean_del_object(v___x_3810_);
                    v___x_3817_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1,
                    );
                    v___x_3818_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_3817_, v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_);
                    return v___x_3818_;
                }
            }
            2 => {
                return v___x_3815_;
            }
            3 => {
                if v_isShared_3823_ == 0 {
                    v___x_3825_ = v___x_3822_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3826_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_a_3820_);
                    v___x_3825_ = v_reuseFailAlloc_3826_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3825_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___boxed(
    mut v_a_3828_: *mut leanh::LeanObject,
    mut v_a_3829_: *mut leanh::LeanObject,
    mut v_a_3830_: *mut leanh::LeanObject,
    mut v_a_3831_: *mut leanh::LeanObject,
    mut v_a_3832_: *mut leanh::LeanObject,
    mut v_a_3833_: *mut leanh::LeanObject,
    mut v_a_3834_: *mut leanh::LeanObject,
    mut v_a_3835_: *mut leanh::LeanObject,
    mut v_a_3836_: *mut leanh::LeanObject,
    mut v_a_3837_: *mut leanh::LeanObject,
    mut v_a_3838_: *mut leanh::LeanObject,
    mut v_a_3839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3840_ = l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst(
        v_a_3828_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_,
        v_a_3836_, v_a_3837_, v_a_3838_,
    );
    leanh::lean_dec(v_a_3838_);
    leanh::lean_dec_ref(v_a_3837_);
    leanh::lean_dec(v_a_3836_);
    leanh::lean_dec_ref(v_a_3835_);
    leanh::lean_dec(v_a_3834_);
    leanh::lean_dec_ref(v_a_3833_);
    leanh::lean_dec(v_a_3832_);
    leanh::lean_dec_ref(v_a_3831_);
    leanh::lean_dec(v_a_3830_);
    leanh::lean_dec(v_a_3829_);
    leanh::lean_dec(v_a_3828_);
    return v_res_3840_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(
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
) -> *mut leanh::LeanObject {
    let mut v___x_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3857_: u8 = 0;
    let mut v_orderedAddInst_x3f_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: u8 = 0;
    let mut v___x_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: u8 = 0;
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3869_: u8 = 0;
    let mut v_a_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3873_: u8 = 0;
    let mut v___x_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3877_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3853_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_,
                    v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_,
                );
                if leanh::lean_obj_tag(v___x_3853_) == 0 {
                    v_a_3854_ = leanh::lean_ctor_get(v___x_3853_, 0);
                    v_isSharedCheck_3869_ = (!leanh::lean_is_exclusive(v___x_3853_)) as u8;
                    if v_isSharedCheck_3869_ == 0 {
                        v___x_3856_ = v___x_3853_;
                        v_isShared_3857_ = v_isSharedCheck_3869_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3854_);
                        leanh::lean_dec(v___x_3853_);
                        v___x_3856_ = leanh::lean_box(0);
                        v_isShared_3857_ = v_isSharedCheck_3869_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3870_ = leanh::lean_ctor_get(v___x_3853_, 0);
                    v_isSharedCheck_3877_ = (!leanh::lean_is_exclusive(v___x_3853_)) as u8;
                    if v_isSharedCheck_3877_ == 0 {
                        v___x_3872_ = v___x_3853_;
                        v_isShared_3873_ = v_isSharedCheck_3877_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3870_);
                        leanh::lean_dec(v___x_3853_);
                        v___x_3872_ = leanh::lean_box(0);
                        v_isShared_3873_ = v_isSharedCheck_3877_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_orderedAddInst_x3f_3858_ = leanh::lean_ctor_get(v_a_3854_, 9);
                leanh::lean_inc(v_orderedAddInst_x3f_3858_);
                leanh::lean_dec(v_a_3854_);
                if leanh::lean_obj_tag(v_orderedAddInst_x3f_3858_) == 0 {
                    v___x_3859_ = 0;
                    v___x_3860_ = leanh::lean_box((v___x_3859_) as usize);
                    if v_isShared_3857_ == 0 {
                        leanh::lean_ctor_set(v___x_3856_, 0, v___x_3860_);
                        v___x_3862_ = v___x_3856_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3863_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3863_, 0, v___x_3860_);
                        v___x_3862_ = v_reuseFailAlloc_3863_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_orderedAddInst_x3f_3858_, 1);
                    v___x_3864_ = 1;
                    v___x_3865_ = leanh::lean_box((v___x_3864_) as usize);
                    if v_isShared_3857_ == 0 {
                        leanh::lean_ctor_set(v___x_3856_, 0, v___x_3865_);
                        v___x_3867_ = v___x_3856_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3868_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3868_, 0, v___x_3865_);
                        v___x_3867_ = v_reuseFailAlloc_3868_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3862_;
            }
            3 => {
                return v___x_3867_;
            }
            4 => {
                if v_isShared_3873_ == 0 {
                    v___x_3875_ = v___x_3872_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3876_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_a_3870_);
                    v___x_3875_ = v_reuseFailAlloc_3876_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3875_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd___boxed(
    mut v_a_3878_: *mut leanh::LeanObject,
    mut v_a_3879_: *mut leanh::LeanObject,
    mut v_a_3880_: *mut leanh::LeanObject,
    mut v_a_3881_: *mut leanh::LeanObject,
    mut v_a_3882_: *mut leanh::LeanObject,
    mut v_a_3883_: *mut leanh::LeanObject,
    mut v_a_3884_: *mut leanh::LeanObject,
    mut v_a_3885_: *mut leanh::LeanObject,
    mut v_a_3886_: *mut leanh::LeanObject,
    mut v_a_3887_: *mut leanh::LeanObject,
    mut v_a_3888_: *mut leanh::LeanObject,
    mut v_a_3889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3890_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(
        v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_,
        v_a_3886_, v_a_3887_, v_a_3888_,
    );
    leanh::lean_dec(v_a_3888_);
    leanh::lean_dec_ref(v_a_3887_);
    leanh::lean_dec(v_a_3886_);
    leanh::lean_dec_ref(v_a_3885_);
    leanh::lean_dec(v_a_3884_);
    leanh::lean_dec_ref(v_a_3883_);
    leanh::lean_dec(v_a_3882_);
    leanh::lean_dec_ref(v_a_3881_);
    leanh::lean_dec(v_a_3880_);
    leanh::lean_dec(v_a_3879_);
    leanh::lean_dec(v_a_3878_);
    return v_res_3890_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg___lam__0(
    mut v_toPure_3891_: *mut leanh::LeanObject,
    mut v_inst_3892_: *mut leanh::LeanObject,
    mut v_inst_3893_: *mut leanh::LeanObject,
    mut v_____do__lift_3894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ltFn_x3f_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ltFn_x3f_3895_ = leanh::lean_ctor_get(v_____do__lift_3894_, 21);
    leanh::lean_inc(v_ltFn_x3f_3895_);
    leanh::lean_dec_ref(v_____do__lift_3894_);
    if leanh::lean_obj_tag(v_ltFn_x3f_3895_) == 1 {
        let mut v_val_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_3893_);
        leanh::lean_dec_ref(v_inst_3892_);
        v_val_3896_ = leanh::lean_ctor_get(v_ltFn_x3f_3895_, 0);
        leanh::lean_inc(v_val_3896_);
        leanh::lean_dec_ref_known(v_ltFn_x3f_3895_, 1);
        v___x_3897_ =
            leanh::lean_apply_2(v_toPure_3891_, leanh::lean_box(0), v_val_3896_);
        return v___x_3897_;
    } else {
        let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_ltFn_x3f_3895_);
        leanh::lean_dec(v_toPure_3891_);
        v___x_3898_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1),
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1_once
            ),
            _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1,
        );
        v___x_3899_ = l_Lean_throwError___redArg(v_inst_3892_, v_inst_3893_, v___x_3898_);
        return v___x_3899_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg(
    mut v_inst_3900_: *mut leanh::LeanObject,
    mut v_inst_3901_: *mut leanh::LeanObject,
    mut v_inst_3902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3903_ = leanh::lean_ctor_get(v_inst_3900_, 0);
    v_toBind_3904_ = leanh::lean_ctor_get(v_inst_3900_, 1);
    leanh::lean_inc(v_toBind_3904_);
    v_toPure_3905_ = leanh::lean_ctor_get(v_toApplicative_3903_, 1);
    leanh::lean_inc(v_toPure_3905_);
    v___f_3906_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_3906_, 0, v_toPure_3905_);
    leanh::lean_closure_set(v___f_3906_, 1, v_inst_3900_);
    leanh::lean_closure_set(v___f_3906_, 2, v_inst_3901_);
    v___x_3907_ = leanh::lean_apply_4(
        v_toBind_3904_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_3902_,
        v___f_3906_,
    );
    return v___x_3907_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getLtFn(
    mut v_m_3908_: *mut leanh::LeanObject,
    mut v_inst_3909_: *mut leanh::LeanObject,
    mut v_inst_3910_: *mut leanh::LeanObject,
    mut v_inst_3911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3912_ =
        l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg(v_inst_3909_, v_inst_3910_, v_inst_3911_);
    return v___x_3912_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3914_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__0;
    v___x_3915_ = l_Lean_stringToMessageData(v___x_3914_);
    return v___x_3915_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0(
    mut v_toPure_3916_: *mut leanh::LeanObject,
    mut v_inst_3917_: *mut leanh::LeanObject,
    mut v_inst_3918_: *mut leanh::LeanObject,
    mut v_____do__lift_3919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_leFn_x3f_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_leFn_x3f_3920_ = leanh::lean_ctor_get(v_____do__lift_3919_, 20);
    leanh::lean_inc(v_leFn_x3f_3920_);
    leanh::lean_dec_ref(v_____do__lift_3919_);
    if leanh::lean_obj_tag(v_leFn_x3f_3920_) == 1 {
        let mut v_val_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_3918_);
        leanh::lean_dec_ref(v_inst_3917_);
        v_val_3921_ = leanh::lean_ctor_get(v_leFn_x3f_3920_, 0);
        leanh::lean_inc(v_val_3921_);
        leanh::lean_dec_ref_known(v_leFn_x3f_3920_, 1);
        v___x_3922_ =
            leanh::lean_apply_2(v_toPure_3916_, leanh::lean_box(0), v_val_3921_);
        return v___x_3922_;
    } else {
        let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_leFn_x3f_3920_);
        leanh::lean_dec(v_toPure_3916_);
        v___x_3923_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1_once
            ),
            _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1,
        );
        v___x_3924_ = l_Lean_throwError___redArg(v_inst_3917_, v_inst_3918_, v___x_3923_);
        return v___x_3924_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg(
    mut v_inst_3925_: *mut leanh::LeanObject,
    mut v_inst_3926_: *mut leanh::LeanObject,
    mut v_inst_3927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3928_ = leanh::lean_ctor_get(v_inst_3925_, 0);
    v_toBind_3929_ = leanh::lean_ctor_get(v_inst_3925_, 1);
    leanh::lean_inc(v_toBind_3929_);
    v_toPure_3930_ = leanh::lean_ctor_get(v_toApplicative_3928_, 1);
    leanh::lean_inc(v_toPure_3930_);
    v___f_3931_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_3931_, 0, v_toPure_3930_);
    leanh::lean_closure_set(v___f_3931_, 1, v_inst_3925_);
    leanh::lean_closure_set(v___f_3931_, 2, v_inst_3926_);
    v___x_3932_ = leanh::lean_apply_4(
        v_toBind_3929_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_3927_,
        v___f_3931_,
    );
    return v___x_3932_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getLeFn(
    mut v_m_3933_: *mut leanh::LeanObject,
    mut v_inst_3934_: *mut leanh::LeanObject,
    mut v_inst_3935_: *mut leanh::LeanObject,
    mut v_inst_3936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3937_ =
        l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg(v_inst_3934_, v_inst_3935_, v_inst_3936_);
    return v___x_3937_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3939_ = l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__0;
    v___x_3940_ = l_Lean_stringToMessageData(v___x_3939_);
    return v___x_3940_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst(
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
) -> *mut leanh::LeanObject {
    let mut v___x_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3957_: u8 = 0;
    let mut v_isLinearInst_x3f_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3965_: u8 = 0;
    let mut v_a_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3969_: u8 = 0;
    let mut v___x_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3973_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3953_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_,
                    v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_,
                );
                if leanh::lean_obj_tag(v___x_3953_) == 0 {
                    v_a_3954_ = leanh::lean_ctor_get(v___x_3953_, 0);
                    v_isSharedCheck_3965_ = (!leanh::lean_is_exclusive(v___x_3953_)) as u8;
                    if v_isSharedCheck_3965_ == 0 {
                        v___x_3956_ = v___x_3953_;
                        v_isShared_3957_ = v_isSharedCheck_3965_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3954_);
                        leanh::lean_dec(v___x_3953_);
                        v___x_3956_ = leanh::lean_box(0);
                        v_isShared_3957_ = v_isSharedCheck_3965_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3966_ = leanh::lean_ctor_get(v___x_3953_, 0);
                    v_isSharedCheck_3973_ = (!leanh::lean_is_exclusive(v___x_3953_)) as u8;
                    if v_isSharedCheck_3973_ == 0 {
                        v___x_3968_ = v___x_3953_;
                        v_isShared_3969_ = v_isSharedCheck_3973_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3966_);
                        leanh::lean_dec(v___x_3953_);
                        v___x_3968_ = leanh::lean_box(0);
                        v_isShared_3969_ = v_isSharedCheck_3973_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_isLinearInst_x3f_3958_ = leanh::lean_ctor_get(v_a_3954_, 10);
                leanh::lean_inc(v_isLinearInst_x3f_3958_);
                leanh::lean_dec(v_a_3954_);
                if leanh::lean_obj_tag(v_isLinearInst_x3f_3958_) == 1 {
                    v_val_3959_ = leanh::lean_ctor_get(v_isLinearInst_x3f_3958_, 0);
                    leanh::lean_inc(v_val_3959_);
                    leanh::lean_dec_ref_known(v_isLinearInst_x3f_3958_, 1);
                    if v_isShared_3957_ == 0 {
                        leanh::lean_ctor_set(v___x_3956_, 0, v_val_3959_);
                        v___x_3961_ = v___x_3956_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3962_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_val_3959_);
                        v___x_3961_ = v_reuseFailAlloc_3962_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_isLinearInst_x3f_3958_);
                    leanh::lean_del_object(v___x_3956_);
                    v___x_3963_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1,
                    );
                    v___x_3964_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_3963_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_);
                    return v___x_3964_;
                }
            }
            2 => {
                return v___x_3961_;
            }
            3 => {
                if v_isShared_3969_ == 0 {
                    v___x_3971_ = v___x_3968_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3972_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3972_, 0, v_a_3966_);
                    v___x_3971_ = v_reuseFailAlloc_3972_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3971_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___boxed(
    mut v_a_3974_: *mut leanh::LeanObject,
    mut v_a_3975_: *mut leanh::LeanObject,
    mut v_a_3976_: *mut leanh::LeanObject,
    mut v_a_3977_: *mut leanh::LeanObject,
    mut v_a_3978_: *mut leanh::LeanObject,
    mut v_a_3979_: *mut leanh::LeanObject,
    mut v_a_3980_: *mut leanh::LeanObject,
    mut v_a_3981_: *mut leanh::LeanObject,
    mut v_a_3982_: *mut leanh::LeanObject,
    mut v_a_3983_: *mut leanh::LeanObject,
    mut v_a_3984_: *mut leanh::LeanObject,
    mut v_a_3985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3986_ = l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst(
        v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_,
        v_a_3982_, v_a_3983_, v_a_3984_,
    );
    leanh::lean_dec(v_a_3984_);
    leanh::lean_dec_ref(v_a_3983_);
    leanh::lean_dec(v_a_3982_);
    leanh::lean_dec_ref(v_a_3981_);
    leanh::lean_dec(v_a_3980_);
    leanh::lean_dec_ref(v_a_3979_);
    leanh::lean_dec(v_a_3978_);
    leanh::lean_dec_ref(v_a_3977_);
    leanh::lean_dec(v_a_3976_);
    leanh::lean_dec(v_a_3975_);
    leanh::lean_dec(v_a_3974_);
    return v_res_3986_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3988_ = l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__0;
    v___x_3989_ = l_Lean_stringToMessageData(v___x_3988_);
    return v___x_3989_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getRingInst(
    mut v_a_3990_: *mut leanh::LeanObject,
    mut v_a_3991_: *mut leanh::LeanObject,
    mut v_a_3992_: *mut leanh::LeanObject,
    mut v_a_3993_: *mut leanh::LeanObject,
    mut v_a_3994_: *mut leanh::LeanObject,
    mut v_a_3995_: *mut leanh::LeanObject,
    mut v_a_3996_: *mut leanh::LeanObject,
    mut v_a_3997_: *mut leanh::LeanObject,
    mut v_a_3998_: *mut leanh::LeanObject,
    mut v_a_3999_: *mut leanh::LeanObject,
    mut v_a_4000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4006_: u8 = 0;
    let mut v_ringInst_x3f_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4014_: u8 = 0;
    let mut v_a_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4018_: u8 = 0;
    let mut v___x_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4022_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4002_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_3990_, v_a_3991_, v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_, v_a_3996_,
                    v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_,
                );
                if leanh::lean_obj_tag(v___x_4002_) == 0 {
                    v_a_4003_ = leanh::lean_ctor_get(v___x_4002_, 0);
                    v_isSharedCheck_4014_ = (!leanh::lean_is_exclusive(v___x_4002_)) as u8;
                    if v_isSharedCheck_4014_ == 0 {
                        v___x_4005_ = v___x_4002_;
                        v_isShared_4006_ = v_isSharedCheck_4014_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4003_);
                        leanh::lean_dec(v___x_4002_);
                        v___x_4005_ = leanh::lean_box(0);
                        v_isShared_4006_ = v_isSharedCheck_4014_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4015_ = leanh::lean_ctor_get(v___x_4002_, 0);
                    v_isSharedCheck_4022_ = (!leanh::lean_is_exclusive(v___x_4002_)) as u8;
                    if v_isSharedCheck_4022_ == 0 {
                        v___x_4017_ = v___x_4002_;
                        v_isShared_4018_ = v_isSharedCheck_4022_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4015_);
                        leanh::lean_dec(v___x_4002_);
                        v___x_4017_ = leanh::lean_box(0);
                        v_isShared_4018_ = v_isSharedCheck_4022_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_ringInst_x3f_4007_ = leanh::lean_ctor_get(v_a_4003_, 12);
                leanh::lean_inc(v_ringInst_x3f_4007_);
                leanh::lean_dec(v_a_4003_);
                if leanh::lean_obj_tag(v_ringInst_x3f_4007_) == 1 {
                    v_val_4008_ = leanh::lean_ctor_get(v_ringInst_x3f_4007_, 0);
                    leanh::lean_inc(v_val_4008_);
                    leanh::lean_dec_ref_known(v_ringInst_x3f_4007_, 1);
                    if v_isShared_4006_ == 0 {
                        leanh::lean_ctor_set(v___x_4005_, 0, v_val_4008_);
                        v___x_4010_ = v___x_4005_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4011_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_val_4008_);
                        v___x_4010_ = v_reuseFailAlloc_4011_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_ringInst_x3f_4007_);
                    leanh::lean_del_object(v___x_4005_);
                    v___x_4012_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1,
                    );
                    v___x_4013_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_4012_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_);
                    return v___x_4013_;
                }
            }
            2 => {
                return v___x_4010_;
            }
            3 => {
                if v_isShared_4018_ == 0 {
                    v___x_4020_ = v___x_4017_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4021_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_a_4015_);
                    v___x_4020_ = v_reuseFailAlloc_4021_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4020_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getRingInst___boxed(
    mut v_a_4023_: *mut leanh::LeanObject,
    mut v_a_4024_: *mut leanh::LeanObject,
    mut v_a_4025_: *mut leanh::LeanObject,
    mut v_a_4026_: *mut leanh::LeanObject,
    mut v_a_4027_: *mut leanh::LeanObject,
    mut v_a_4028_: *mut leanh::LeanObject,
    mut v_a_4029_: *mut leanh::LeanObject,
    mut v_a_4030_: *mut leanh::LeanObject,
    mut v_a_4031_: *mut leanh::LeanObject,
    mut v_a_4032_: *mut leanh::LeanObject,
    mut v_a_4033_: *mut leanh::LeanObject,
    mut v_a_4034_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4035_ = l_Lean_Meta_Grind_Arith_Linear_getRingInst(
        v_a_4023_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_,
        v_a_4031_, v_a_4032_, v_a_4033_,
    );
    leanh::lean_dec(v_a_4033_);
    leanh::lean_dec_ref(v_a_4032_);
    leanh::lean_dec(v_a_4031_);
    leanh::lean_dec_ref(v_a_4030_);
    leanh::lean_dec(v_a_4029_);
    leanh::lean_dec_ref(v_a_4028_);
    leanh::lean_dec(v_a_4027_);
    leanh::lean_dec_ref(v_a_4026_);
    leanh::lean_dec(v_a_4025_);
    leanh::lean_dec(v_a_4024_);
    leanh::lean_dec(v_a_4023_);
    return v_res_4035_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4037_ = l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__0;
    v___x_4038_ = l_Lean_stringToMessageData(v___x_4037_);
    return v___x_4038_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getCommRingInst(
    mut v_a_4039_: *mut leanh::LeanObject,
    mut v_a_4040_: *mut leanh::LeanObject,
    mut v_a_4041_: *mut leanh::LeanObject,
    mut v_a_4042_: *mut leanh::LeanObject,
    mut v_a_4043_: *mut leanh::LeanObject,
    mut v_a_4044_: *mut leanh::LeanObject,
    mut v_a_4045_: *mut leanh::LeanObject,
    mut v_a_4046_: *mut leanh::LeanObject,
    mut v_a_4047_: *mut leanh::LeanObject,
    mut v_a_4048_: *mut leanh::LeanObject,
    mut v_a_4049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4055_: u8 = 0;
    let mut v_commRingInst_x3f_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4063_: u8 = 0;
    let mut v_a_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4067_: u8 = 0;
    let mut v___x_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4071_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4051_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_,
                    v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_,
                );
                if leanh::lean_obj_tag(v___x_4051_) == 0 {
                    v_a_4052_ = leanh::lean_ctor_get(v___x_4051_, 0);
                    v_isSharedCheck_4063_ = (!leanh::lean_is_exclusive(v___x_4051_)) as u8;
                    if v_isSharedCheck_4063_ == 0 {
                        v___x_4054_ = v___x_4051_;
                        v_isShared_4055_ = v_isSharedCheck_4063_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4052_);
                        leanh::lean_dec(v___x_4051_);
                        v___x_4054_ = leanh::lean_box(0);
                        v_isShared_4055_ = v_isSharedCheck_4063_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4064_ = leanh::lean_ctor_get(v___x_4051_, 0);
                    v_isSharedCheck_4071_ = (!leanh::lean_is_exclusive(v___x_4051_)) as u8;
                    if v_isSharedCheck_4071_ == 0 {
                        v___x_4066_ = v___x_4051_;
                        v_isShared_4067_ = v_isSharedCheck_4071_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4064_);
                        leanh::lean_dec(v___x_4051_);
                        v___x_4066_ = leanh::lean_box(0);
                        v_isShared_4067_ = v_isSharedCheck_4071_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_commRingInst_x3f_4056_ = leanh::lean_ctor_get(v_a_4052_, 13);
                leanh::lean_inc(v_commRingInst_x3f_4056_);
                leanh::lean_dec(v_a_4052_);
                if leanh::lean_obj_tag(v_commRingInst_x3f_4056_) == 1 {
                    v_val_4057_ = leanh::lean_ctor_get(v_commRingInst_x3f_4056_, 0);
                    leanh::lean_inc(v_val_4057_);
                    leanh::lean_dec_ref_known(v_commRingInst_x3f_4056_, 1);
                    if v_isShared_4055_ == 0 {
                        leanh::lean_ctor_set(v___x_4054_, 0, v_val_4057_);
                        v___x_4059_ = v___x_4054_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4060_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_val_4057_);
                        v___x_4059_ = v_reuseFailAlloc_4060_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_commRingInst_x3f_4056_);
                    leanh::lean_del_object(v___x_4054_);
                    v___x_4061_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1,
                    );
                    v___x_4062_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_4061_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_);
                    return v___x_4062_;
                }
            }
            2 => {
                return v___x_4059_;
            }
            3 => {
                if v_isShared_4067_ == 0 {
                    v___x_4069_ = v___x_4066_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4070_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_4064_);
                    v___x_4069_ = v_reuseFailAlloc_4070_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4069_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___boxed(
    mut v_a_4072_: *mut leanh::LeanObject,
    mut v_a_4073_: *mut leanh::LeanObject,
    mut v_a_4074_: *mut leanh::LeanObject,
    mut v_a_4075_: *mut leanh::LeanObject,
    mut v_a_4076_: *mut leanh::LeanObject,
    mut v_a_4077_: *mut leanh::LeanObject,
    mut v_a_4078_: *mut leanh::LeanObject,
    mut v_a_4079_: *mut leanh::LeanObject,
    mut v_a_4080_: *mut leanh::LeanObject,
    mut v_a_4081_: *mut leanh::LeanObject,
    mut v_a_4082_: *mut leanh::LeanObject,
    mut v_a_4083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4084_ = l_Lean_Meta_Grind_Arith_Linear_getCommRingInst(
        v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_, v_a_4078_, v_a_4079_,
        v_a_4080_, v_a_4081_, v_a_4082_,
    );
    leanh::lean_dec(v_a_4082_);
    leanh::lean_dec_ref(v_a_4081_);
    leanh::lean_dec(v_a_4080_);
    leanh::lean_dec_ref(v_a_4079_);
    leanh::lean_dec(v_a_4078_);
    leanh::lean_dec_ref(v_a_4077_);
    leanh::lean_dec(v_a_4076_);
    leanh::lean_dec_ref(v_a_4075_);
    leanh::lean_dec(v_a_4074_);
    leanh::lean_dec(v_a_4073_);
    leanh::lean_dec(v_a_4072_);
    return v_res_4084_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4086_ = l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__0;
    v___x_4087_ = l_Lean_stringToMessageData(v___x_4086_);
    return v___x_4087_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst(
    mut v_a_4088_: *mut leanh::LeanObject,
    mut v_a_4089_: *mut leanh::LeanObject,
    mut v_a_4090_: *mut leanh::LeanObject,
    mut v_a_4091_: *mut leanh::LeanObject,
    mut v_a_4092_: *mut leanh::LeanObject,
    mut v_a_4093_: *mut leanh::LeanObject,
    mut v_a_4094_: *mut leanh::LeanObject,
    mut v_a_4095_: *mut leanh::LeanObject,
    mut v_a_4096_: *mut leanh::LeanObject,
    mut v_a_4097_: *mut leanh::LeanObject,
    mut v_a_4098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4104_: u8 = 0;
    let mut v_orderedRingInst_x3f_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4112_: u8 = 0;
    let mut v_a_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4116_: u8 = 0;
    let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4120_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4100_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_, v_a_4092_, v_a_4093_, v_a_4094_,
                    v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_,
                );
                if leanh::lean_obj_tag(v___x_4100_) == 0 {
                    v_a_4101_ = leanh::lean_ctor_get(v___x_4100_, 0);
                    v_isSharedCheck_4112_ = (!leanh::lean_is_exclusive(v___x_4100_)) as u8;
                    if v_isSharedCheck_4112_ == 0 {
                        v___x_4103_ = v___x_4100_;
                        v_isShared_4104_ = v_isSharedCheck_4112_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4101_);
                        leanh::lean_dec(v___x_4100_);
                        v___x_4103_ = leanh::lean_box(0);
                        v_isShared_4104_ = v_isSharedCheck_4112_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4113_ = leanh::lean_ctor_get(v___x_4100_, 0);
                    v_isSharedCheck_4120_ = (!leanh::lean_is_exclusive(v___x_4100_)) as u8;
                    if v_isSharedCheck_4120_ == 0 {
                        v___x_4115_ = v___x_4100_;
                        v_isShared_4116_ = v_isSharedCheck_4120_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4113_);
                        leanh::lean_dec(v___x_4100_);
                        v___x_4115_ = leanh::lean_box(0);
                        v_isShared_4116_ = v_isSharedCheck_4120_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_orderedRingInst_x3f_4105_ = leanh::lean_ctor_get(v_a_4101_, 14);
                leanh::lean_inc(v_orderedRingInst_x3f_4105_);
                leanh::lean_dec(v_a_4101_);
                if leanh::lean_obj_tag(v_orderedRingInst_x3f_4105_) == 1 {
                    v_val_4106_ = leanh::lean_ctor_get(v_orderedRingInst_x3f_4105_, 0);
                    leanh::lean_inc(v_val_4106_);
                    leanh::lean_dec_ref_known(v_orderedRingInst_x3f_4105_, 1);
                    if v_isShared_4104_ == 0 {
                        leanh::lean_ctor_set(v___x_4103_, 0, v_val_4106_);
                        v___x_4108_ = v___x_4103_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4109_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_val_4106_);
                        v___x_4108_ = v_reuseFailAlloc_4109_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_orderedRingInst_x3f_4105_);
                    leanh::lean_del_object(v___x_4103_);
                    v___x_4110_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1,
                    );
                    v___x_4111_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_4110_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_);
                    return v___x_4111_;
                }
            }
            2 => {
                return v___x_4108_;
            }
            3 => {
                if v_isShared_4116_ == 0 {
                    v___x_4118_ = v___x_4115_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4119_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4119_, 0, v_a_4113_);
                    v___x_4118_ = v_reuseFailAlloc_4119_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4118_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___boxed(
    mut v_a_4121_: *mut leanh::LeanObject,
    mut v_a_4122_: *mut leanh::LeanObject,
    mut v_a_4123_: *mut leanh::LeanObject,
    mut v_a_4124_: *mut leanh::LeanObject,
    mut v_a_4125_: *mut leanh::LeanObject,
    mut v_a_4126_: *mut leanh::LeanObject,
    mut v_a_4127_: *mut leanh::LeanObject,
    mut v_a_4128_: *mut leanh::LeanObject,
    mut v_a_4129_: *mut leanh::LeanObject,
    mut v_a_4130_: *mut leanh::LeanObject,
    mut v_a_4131_: *mut leanh::LeanObject,
    mut v_a_4132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4133_ = l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst(
        v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_,
        v_a_4129_, v_a_4130_, v_a_4131_,
    );
    leanh::lean_dec(v_a_4131_);
    leanh::lean_dec_ref(v_a_4130_);
    leanh::lean_dec(v_a_4129_);
    leanh::lean_dec_ref(v_a_4128_);
    leanh::lean_dec(v_a_4127_);
    leanh::lean_dec_ref(v_a_4126_);
    leanh::lean_dec(v_a_4125_);
    leanh::lean_dec_ref(v_a_4124_);
    leanh::lean_dec(v_a_4123_);
    leanh::lean_dec(v_a_4122_);
    leanh::lean_dec(v_a_4121_);
    return v_res_4133_;
}
pub unsafe fn l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go_spec__0(
    mut v_a_4134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4135_ = l_Rat_ofInt(v_a_4134_);
    return v___x_4135_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(
    mut v_a_4136_: *mut leanh::LeanObject,
    mut v_v_4137_: *mut leanh::LeanObject,
    mut v_a_4138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: u8 = 0;
    let mut v___x_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_4138_) == 0 {
                    v___x_4139_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4139_, 0, v_v_4137_);
                    return v___x_4139_;
                } else {
                    v_k_4140_ = leanh::lean_ctor_get(v_a_4138_, 0);
                    leanh::lean_inc(v_k_4140_);
                    v_v_4141_ = leanh::lean_ctor_get(v_a_4138_, 1);
                    leanh::lean_inc(v_v_4141_);
                    v_p_4142_ = leanh::lean_ctor_get(v_a_4138_, 2);
                    leanh::lean_inc(v_p_4142_);
                    leanh::lean_dec_ref_known(v_a_4138_, 3);
                    v_size_4143_ = leanh::lean_ctor_get(v_a_4136_, 2);
                    v___x_4144_ = lean_nat_dec_lt(v_v_4141_, v_size_4143_);
                    if v___x_4144_ == 0 {
                        leanh::lean_dec(v_p_4142_);
                        leanh::lean_dec(v_v_4141_);
                        leanh::lean_dec(v_k_4140_);
                        leanh::lean_dec_ref(v_v_4137_);
                        v___x_4145_ = leanh::lean_box(0);
                        return v___x_4145_;
                    } else {
                        v___x_4146_ = l_Rat_ofInt(v_k_4140_);
                        v___x_4147_ = l_instInhabitedRat;
                        v___x_4148_ = l_Lean_PersistentArray_get_x21___redArg(
                            v___x_4147_,
                            v_a_4136_,
                            v_v_4141_,
                        );
                        leanh::lean_dec(v_v_4141_);
                        v___x_4149_ = l_Rat_mul(v___x_4146_, v___x_4148_);
                        leanh::lean_dec_ref(v___x_4146_);
                        v___x_4150_ = l_Rat_add(v_v_4137_, v___x_4149_);
                        v_v_4137_ = v___x_4150_;
                        v_a_4138_ = v_p_4142_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go___boxed(
    mut v_a_4152_: *mut leanh::LeanObject,
    mut v_v_4153_: *mut leanh::LeanObject,
    mut v_a_4154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4155_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(v_a_4152_, v_v_4153_, v_a_4154_);
    leanh::lean_dec_ref(v_a_4152_);
    return v_res_4155_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0(
    mut v_a_4156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4157_ = lean_nat_to_int(v_a_4156_);
    v___x_4158_ = l_Rat_ofInt(v___x_4157_);
    return v___x_4158_;
}
pub unsafe fn _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4159_ = leanh::lean_unsigned_to_nat(0);
    v___x_4160_ = l_Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0(v___x_4159_);
    return v___x_4160_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_eval_x3f(
    mut v_p_4161_: *mut leanh::LeanObject,
    mut v_a_4162_: *mut leanh::LeanObject,
    mut v_a_4163_: *mut leanh::LeanObject,
    mut v_a_4164_: *mut leanh::LeanObject,
    mut v_a_4165_: *mut leanh::LeanObject,
    mut v_a_4166_: *mut leanh::LeanObject,
    mut v_a_4167_: *mut leanh::LeanObject,
    mut v_a_4168_: *mut leanh::LeanObject,
    mut v_a_4169_: *mut leanh::LeanObject,
    mut v_a_4170_: *mut leanh::LeanObject,
    mut v_a_4171_: *mut leanh::LeanObject,
    mut v_a_4172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4178_: u8 = 0;
    let mut v_assignment_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4185_: u8 = 0;
    let mut v_a_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4189_: u8 = 0;
    let mut v___x_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4193_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4174_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_,
                    v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_,
                );
                if leanh::lean_obj_tag(v___x_4174_) == 0 {
                    v_a_4175_ = leanh::lean_ctor_get(v___x_4174_, 0);
                    v_isSharedCheck_4185_ = (!leanh::lean_is_exclusive(v___x_4174_)) as u8;
                    if v_isSharedCheck_4185_ == 0 {
                        v___x_4177_ = v___x_4174_;
                        v_isShared_4178_ = v_isSharedCheck_4185_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4175_);
                        leanh::lean_dec(v___x_4174_);
                        v___x_4177_ = leanh::lean_box(0);
                        v_isShared_4178_ = v_isSharedCheck_4185_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_p_4161_);
                    v_a_4186_ = leanh::lean_ctor_get(v___x_4174_, 0);
                    v_isSharedCheck_4193_ = (!leanh::lean_is_exclusive(v___x_4174_)) as u8;
                    if v_isSharedCheck_4193_ == 0 {
                        v___x_4188_ = v___x_4174_;
                        v_isShared_4189_ = v_isSharedCheck_4193_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4186_);
                        leanh::lean_dec(v___x_4174_);
                        v___x_4188_ = leanh::lean_box(0);
                        v_isShared_4189_ = v_isSharedCheck_4193_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_assignment_4179_ = leanh::lean_ctor_get(v_a_4175_, 35);
                leanh::lean_inc_ref(v_assignment_4179_);
                leanh::lean_dec(v_a_4175_);
                v___x_4180_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once),
                    _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0,
                );
                v___x_4181_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(v_assignment_4179_, v___x_4180_, v_p_4161_);
                leanh::lean_dec_ref(v_assignment_4179_);
                if v_isShared_4178_ == 0 {
                    leanh::lean_ctor_set(v___x_4177_, 0, v___x_4181_);
                    v___x_4183_ = v___x_4177_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4184_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4184_, 0, v___x_4181_);
                    v___x_4183_ = v_reuseFailAlloc_4184_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4183_;
            }
            3 => {
                if v_isShared_4189_ == 0 {
                    v___x_4191_ = v___x_4188_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4192_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4192_, 0, v_a_4186_);
                    v___x_4191_ = v_reuseFailAlloc_4192_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4191_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_eval_x3f___boxed(
    mut v_p_4194_: *mut leanh::LeanObject,
    mut v_a_4195_: *mut leanh::LeanObject,
    mut v_a_4196_: *mut leanh::LeanObject,
    mut v_a_4197_: *mut leanh::LeanObject,
    mut v_a_4198_: *mut leanh::LeanObject,
    mut v_a_4199_: *mut leanh::LeanObject,
    mut v_a_4200_: *mut leanh::LeanObject,
    mut v_a_4201_: *mut leanh::LeanObject,
    mut v_a_4202_: *mut leanh::LeanObject,
    mut v_a_4203_: *mut leanh::LeanObject,
    mut v_a_4204_: *mut leanh::LeanObject,
    mut v_a_4205_: *mut leanh::LeanObject,
    mut v_a_4206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4207_ = l_Lean_Grind_Linarith_Poly_eval_x3f(
        v_p_4194_, v_a_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_,
        v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_,
    );
    leanh::lean_dec(v_a_4205_);
    leanh::lean_dec_ref(v_a_4204_);
    leanh::lean_dec(v_a_4203_);
    leanh::lean_dec_ref(v_a_4202_);
    leanh::lean_dec(v_a_4201_);
    leanh::lean_dec_ref(v_a_4200_);
    leanh::lean_dec(v_a_4199_);
    leanh::lean_dec_ref(v_a_4198_);
    leanh::lean_dec(v_a_4197_);
    leanh::lean_dec(v_a_4196_);
    leanh::lean_dec(v_a_4195_);
    return v_res_4207_;
}
pub unsafe fn l_Nat_cast___at___00Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0_spec__0(
    mut v_a_4208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4209_ = lean_nat_to_int(v_a_4208_);
    return v___x_4209_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(
    mut v_c_4210_: *mut leanh::LeanObject,
    mut v_a_4211_: *mut leanh::LeanObject,
    mut v_a_4212_: *mut leanh::LeanObject,
    mut v_a_4213_: *mut leanh::LeanObject,
    mut v_a_4214_: *mut leanh::LeanObject,
    mut v_a_4215_: *mut leanh::LeanObject,
    mut v_a_4216_: *mut leanh::LeanObject,
    mut v_a_4217_: *mut leanh::LeanObject,
    mut v_a_4218_: *mut leanh::LeanObject,
    mut v_a_4219_: *mut leanh::LeanObject,
    mut v_a_4220_: *mut leanh::LeanObject,
    mut v_a_4221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_p_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_4224_: u8 = 0;
    let mut v___x_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4229_: u8 = 0;
    let mut v_val_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: u8 = 0;
    let mut v___x_4233_: u8 = 0;
    let mut v___x_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: u8 = 0;
    let mut v___x_4241_: u8 = 0;
    let mut v___x_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: u8 = 0;
    let mut v___x_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4251_: u8 = 0;
    let mut v_a_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4255_: u8 = 0;
    let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4259_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_p_4223_ = leanh::lean_ctor_get(v_c_4210_, 0);
                leanh::lean_inc(v_p_4223_);
                v_strict_4224_ = leanh::lean_ctor_get_uint8(
                    v_c_4210_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                leanh::lean_dec_ref(v_c_4210_);
                v___x_4225_ = l_Lean_Grind_Linarith_Poly_eval_x3f(
                    v_p_4223_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_,
                    v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_, v_a_4221_,
                );
                if leanh::lean_obj_tag(v___x_4225_) == 0 {
                    v_a_4226_ = leanh::lean_ctor_get(v___x_4225_, 0);
                    v_isSharedCheck_4251_ = (!leanh::lean_is_exclusive(v___x_4225_)) as u8;
                    if v_isSharedCheck_4251_ == 0 {
                        v___x_4228_ = v___x_4225_;
                        v_isShared_4229_ = v_isSharedCheck_4251_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4226_);
                        leanh::lean_dec(v___x_4225_);
                        v___x_4228_ = leanh::lean_box(0);
                        v_isShared_4229_ = v_isSharedCheck_4251_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4252_ = leanh::lean_ctor_get(v___x_4225_, 0);
                    v_isSharedCheck_4259_ = (!leanh::lean_is_exclusive(v___x_4225_)) as u8;
                    if v_isSharedCheck_4259_ == 0 {
                        v___x_4254_ = v___x_4225_;
                        v_isShared_4255_ = v_isSharedCheck_4259_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4252_);
                        leanh::lean_dec(v___x_4225_);
                        v___x_4254_ = leanh::lean_box(0);
                        v_isShared_4255_ = v_isSharedCheck_4259_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4226_) == 1 {
                    if v_strict_4224_ == 0 {
                        v_val_4230_ = leanh::lean_ctor_get(v_a_4226_, 0);
                        leanh::lean_inc(v_val_4230_);
                        leanh::lean_dec_ref_known(v_a_4226_, 1);
                        v___x_4231_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once
                            ),
                            _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0,
                        );
                        v___x_4232_ = l_Rat_instDecidableLe(v_val_4230_, v___x_4231_);
                        v___x_4233_ = l_Bool_toLBool(v___x_4232_);
                        v___x_4234_ = leanh::lean_box((v___x_4233_) as usize);
                        if v_isShared_4229_ == 0 {
                            leanh::lean_ctor_set(v___x_4228_, 0, v___x_4234_);
                            v___x_4236_ = v___x_4228_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4237_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4237_, 0, v___x_4234_);
                            v___x_4236_ = v_reuseFailAlloc_4237_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_val_4238_ = leanh::lean_ctor_get(v_a_4226_, 0);
                        leanh::lean_inc(v_val_4238_);
                        leanh::lean_dec_ref_known(v_a_4226_, 1);
                        v___x_4239_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once
                            ),
                            _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0,
                        );
                        v___x_4240_ = l_Rat_blt(v_val_4238_, v___x_4239_);
                        v___x_4241_ = l_Bool_toLBool(v___x_4240_);
                        v___x_4242_ = leanh::lean_box((v___x_4241_) as usize);
                        if v_isShared_4229_ == 0 {
                            leanh::lean_ctor_set(v___x_4228_, 0, v___x_4242_);
                            v___x_4244_ = v___x_4228_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4245_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4245_, 0, v___x_4242_);
                            v___x_4244_ = v_reuseFailAlloc_4245_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_4226_);
                    v___x_4246_ = 2;
                    v___x_4247_ = leanh::lean_box((v___x_4246_) as usize);
                    if v_isShared_4229_ == 0 {
                        leanh::lean_ctor_set(v___x_4228_, 0, v___x_4247_);
                        v___x_4249_ = v___x_4228_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4250_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4250_, 0, v___x_4247_);
                        v___x_4249_ = v_reuseFailAlloc_4250_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4236_;
            }
            3 => {
                return v___x_4244_;
            }
            4 => {
                return v___x_4249_;
            }
            5 => {
                if v_isShared_4255_ == 0 {
                    v___x_4257_ = v___x_4254_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4258_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_a_4252_);
                    v___x_4257_ = v_reuseFailAlloc_4258_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4257_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied___boxed(
    mut v_c_4260_: *mut leanh::LeanObject,
    mut v_a_4261_: *mut leanh::LeanObject,
    mut v_a_4262_: *mut leanh::LeanObject,
    mut v_a_4263_: *mut leanh::LeanObject,
    mut v_a_4264_: *mut leanh::LeanObject,
    mut v_a_4265_: *mut leanh::LeanObject,
    mut v_a_4266_: *mut leanh::LeanObject,
    mut v_a_4267_: *mut leanh::LeanObject,
    mut v_a_4268_: *mut leanh::LeanObject,
    mut v_a_4269_: *mut leanh::LeanObject,
    mut v_a_4270_: *mut leanh::LeanObject,
    mut v_a_4271_: *mut leanh::LeanObject,
    mut v_a_4272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4273_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(
        v_c_4260_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_, v_a_4265_, v_a_4266_, v_a_4267_,
        v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_,
    );
    leanh::lean_dec(v_a_4271_);
    leanh::lean_dec_ref(v_a_4270_);
    leanh::lean_dec(v_a_4269_);
    leanh::lean_dec_ref(v_a_4268_);
    leanh::lean_dec(v_a_4267_);
    leanh::lean_dec_ref(v_a_4266_);
    leanh::lean_dec(v_a_4265_);
    leanh::lean_dec_ref(v_a_4264_);
    leanh::lean_dec(v_a_4263_);
    leanh::lean_dec(v_a_4262_);
    leanh::lean_dec(v_a_4261_);
    return v_res_4273_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(
    mut v_c_4274_: *mut leanh::LeanObject,
    mut v_a_4275_: *mut leanh::LeanObject,
    mut v_a_4276_: *mut leanh::LeanObject,
    mut v_a_4277_: *mut leanh::LeanObject,
    mut v_a_4278_: *mut leanh::LeanObject,
    mut v_a_4279_: *mut leanh::LeanObject,
    mut v_a_4280_: *mut leanh::LeanObject,
    mut v_a_4281_: *mut leanh::LeanObject,
    mut v_a_4282_: *mut leanh::LeanObject,
    mut v_a_4283_: *mut leanh::LeanObject,
    mut v_a_4284_: *mut leanh::LeanObject,
    mut v_a_4285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_p_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4292_: u8 = 0;
    let mut v___y_4294_: u8 = 0;
    let mut v___x_4295_: u8 = 0;
    let mut v___x_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: u8 = 0;
    let mut v___x_4303_: u8 = 0;
    let mut v___x_4304_: u8 = 0;
    let mut v___x_4305_: u8 = 0;
    let mut v___x_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4308_: u8 = 0;
    let mut v_a_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4312_: u8 = 0;
    let mut v___x_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4316_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_p_4287_ = leanh::lean_ctor_get(v_c_4274_, 0);
                leanh::lean_inc(v_p_4287_);
                leanh::lean_dec_ref(v_c_4274_);
                v___x_4288_ = l_Lean_Grind_Linarith_Poly_eval_x3f(
                    v_p_4287_, v_a_4275_, v_a_4276_, v_a_4277_, v_a_4278_, v_a_4279_, v_a_4280_,
                    v_a_4281_, v_a_4282_, v_a_4283_, v_a_4284_, v_a_4285_,
                );
                if leanh::lean_obj_tag(v___x_4288_) == 0 {
                    v_a_4289_ = leanh::lean_ctor_get(v___x_4288_, 0);
                    v_isSharedCheck_4308_ = (!leanh::lean_is_exclusive(v___x_4288_)) as u8;
                    if v_isSharedCheck_4308_ == 0 {
                        v___x_4291_ = v___x_4288_;
                        v_isShared_4292_ = v_isSharedCheck_4308_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4289_);
                        leanh::lean_dec(v___x_4288_);
                        v___x_4291_ = leanh::lean_box(0);
                        v_isShared_4292_ = v_isSharedCheck_4308_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4309_ = leanh::lean_ctor_get(v___x_4288_, 0);
                    v_isSharedCheck_4316_ = (!leanh::lean_is_exclusive(v___x_4288_)) as u8;
                    if v_isSharedCheck_4316_ == 0 {
                        v___x_4311_ = v___x_4288_;
                        v_isShared_4312_ = v_isSharedCheck_4316_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4309_);
                        leanh::lean_dec(v___x_4288_);
                        v___x_4311_ = leanh::lean_box(0);
                        v_isShared_4312_ = v_isSharedCheck_4316_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4289_) == 1 {
                    v_val_4300_ = leanh::lean_ctor_get(v_a_4289_, 0);
                    leanh::lean_inc(v_val_4300_);
                    leanh::lean_dec_ref_known(v_a_4289_, 1);
                    v___x_4301_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once
                        ),
                        _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0,
                    );
                    v___x_4302_ = l_instDecidableEqRat_decEq(v_val_4300_, v___x_4301_);
                    leanh::lean_dec(v_val_4300_);
                    if v___x_4302_ == 0 {
                        v___x_4303_ = 1;
                        v___y_4294_ = v___x_4303_;
                        state = 2;
                        continue;
                    } else {
                        v___x_4304_ = 0;
                        v___y_4294_ = v___x_4304_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4291_);
                    leanh::lean_dec(v_a_4289_);
                    v___x_4305_ = 2;
                    v___x_4306_ = leanh::lean_box((v___x_4305_) as usize);
                    v___x_4307_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4307_, 0, v___x_4306_);
                    return v___x_4307_;
                }
            }
            2 => {
                v___x_4295_ = l_Bool_toLBool(v___y_4294_);
                v___x_4296_ = leanh::lean_box((v___x_4295_) as usize);
                if v_isShared_4292_ == 0 {
                    leanh::lean_ctor_set(v___x_4291_, 0, v___x_4296_);
                    v___x_4298_ = v___x_4291_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4299_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4299_, 0, v___x_4296_);
                    v___x_4298_ = v_reuseFailAlloc_4299_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4298_;
            }
            4 => {
                if v_isShared_4312_ == 0 {
                    v___x_4314_ = v___x_4311_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4315_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4315_, 0, v_a_4309_);
                    v___x_4314_ = v_reuseFailAlloc_4315_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4314_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied___boxed(
    mut v_c_4317_: *mut leanh::LeanObject,
    mut v_a_4318_: *mut leanh::LeanObject,
    mut v_a_4319_: *mut leanh::LeanObject,
    mut v_a_4320_: *mut leanh::LeanObject,
    mut v_a_4321_: *mut leanh::LeanObject,
    mut v_a_4322_: *mut leanh::LeanObject,
    mut v_a_4323_: *mut leanh::LeanObject,
    mut v_a_4324_: *mut leanh::LeanObject,
    mut v_a_4325_: *mut leanh::LeanObject,
    mut v_a_4326_: *mut leanh::LeanObject,
    mut v_a_4327_: *mut leanh::LeanObject,
    mut v_a_4328_: *mut leanh::LeanObject,
    mut v_a_4329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4330_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(
        v_c_4317_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_, v_a_4324_,
        v_a_4325_, v_a_4326_, v_a_4327_, v_a_4328_,
    );
    leanh::lean_dec(v_a_4328_);
    leanh::lean_dec_ref(v_a_4327_);
    leanh::lean_dec(v_a_4326_);
    leanh::lean_dec_ref(v_a_4325_);
    leanh::lean_dec(v_a_4324_);
    leanh::lean_dec_ref(v_a_4323_);
    leanh::lean_dec(v_a_4322_);
    leanh::lean_dec_ref(v_a_4321_);
    leanh::lean_dec(v_a_4320_);
    leanh::lean_dec(v_a_4319_);
    leanh::lean_dec(v_a_4318_);
    return v_res_4330_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0(
    mut v_a_4331_: *mut leanh::LeanObject,
    mut v_x_4332_: *mut leanh::LeanObject,
    mut v_s_4333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_structs_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToStructId_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToStructIdEntries_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_forbiddenNatModules_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natStructs_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natTypeIdOf_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNatStructId_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: u8 = 0;
    let mut v___x_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4346_: u8 = 0;
    let mut v_v_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringId_x3f_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intModuleInst_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leInst_x3f_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltInst_x3f_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lawfulOrderLTInst_x3f_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isPreorderInst_x3f_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_orderedAddInst_x3f_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isLinearInst_x3f_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noNatDivInst_x3f_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_x3f_4360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_x3f_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_orderedRingInst_x3f_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ofNatZero_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leFn_x3f_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltFn_x3f_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zsmulFn_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nsmulFn_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zsmulFn_x3f_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nsmulFn_x3f_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_homomulFn_x3f_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lowers_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uppers_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignment_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_caseSplits_4384_: u8 = 0;
    let mut v_conflict_x3f_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqSplits_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_elimEqs_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_elimStack_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_occurs_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ignored_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4393_: u8 = 0;
    let mut v___x_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4404_: u8 = 0;
    let mut v_isSharedCheck_4405_: u8 = 0;
    let mut v_unused_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_4334_ = leanh::lean_ctor_get(v_s_4333_, 0);
                v_typeIdOf_4335_ = leanh::lean_ctor_get(v_s_4333_, 1);
                v_exprToStructId_4336_ = leanh::lean_ctor_get(v_s_4333_, 2);
                v_exprToStructIdEntries_4337_ = leanh::lean_ctor_get(v_s_4333_, 3);
                v_forbiddenNatModules_4338_ = leanh::lean_ctor_get(v_s_4333_, 4);
                v_natStructs_4339_ = leanh::lean_ctor_get(v_s_4333_, 5);
                v_natTypeIdOf_4340_ = leanh::lean_ctor_get(v_s_4333_, 6);
                v_exprToNatStructId_4341_ = leanh::lean_ctor_get(v_s_4333_, 7);
                v___x_4342_ = lean_array_get_size(v_structs_4334_);
                v___x_4343_ = lean_nat_dec_lt(v_a_4331_, v___x_4342_);
                if v___x_4343_ == 0 {
                    return v_s_4333_;
                } else {
                    leanh::lean_inc_ref(v_exprToNatStructId_4341_);
                    leanh::lean_inc_ref(v_natTypeIdOf_4340_);
                    leanh::lean_inc_ref(v_natStructs_4339_);
                    leanh::lean_inc_ref(v_forbiddenNatModules_4338_);
                    leanh::lean_inc_ref(v_exprToStructIdEntries_4337_);
                    leanh::lean_inc_ref(v_exprToStructId_4336_);
                    leanh::lean_inc_ref(v_typeIdOf_4335_);
                    leanh::lean_inc_ref(v_structs_4334_);
                    v_isSharedCheck_4405_ = (!leanh::lean_is_exclusive(v_s_4333_)) as u8;
                    if v_isSharedCheck_4405_ == 0 {
                        v_unused_4406_ = leanh::lean_ctor_get(v_s_4333_, 7);
                        leanh::lean_dec(v_unused_4406_);
                        v_unused_4407_ = leanh::lean_ctor_get(v_s_4333_, 6);
                        leanh::lean_dec(v_unused_4407_);
                        v_unused_4408_ = leanh::lean_ctor_get(v_s_4333_, 5);
                        leanh::lean_dec(v_unused_4408_);
                        v_unused_4409_ = leanh::lean_ctor_get(v_s_4333_, 4);
                        leanh::lean_dec(v_unused_4409_);
                        v_unused_4410_ = leanh::lean_ctor_get(v_s_4333_, 3);
                        leanh::lean_dec(v_unused_4410_);
                        v_unused_4411_ = leanh::lean_ctor_get(v_s_4333_, 2);
                        leanh::lean_dec(v_unused_4411_);
                        v_unused_4412_ = leanh::lean_ctor_get(v_s_4333_, 1);
                        leanh::lean_dec(v_unused_4412_);
                        v_unused_4413_ = leanh::lean_ctor_get(v_s_4333_, 0);
                        leanh::lean_dec(v_unused_4413_);
                        v___x_4345_ = v_s_4333_;
                        v_isShared_4346_ = v_isSharedCheck_4405_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_s_4333_);
                        v___x_4345_ = leanh::lean_box(0);
                        v_isShared_4346_ = v_isSharedCheck_4405_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4347_ = lean_array_fget(v_structs_4334_, v_a_4331_);
                v_id_4348_ = leanh::lean_ctor_get(v_v_4347_, 0);
                v_ringId_x3f_4349_ = leanh::lean_ctor_get(v_v_4347_, 1);
                v_type_4350_ = leanh::lean_ctor_get(v_v_4347_, 2);
                v_u_4351_ = leanh::lean_ctor_get(v_v_4347_, 3);
                v_intModuleInst_4352_ = leanh::lean_ctor_get(v_v_4347_, 4);
                v_leInst_x3f_4353_ = leanh::lean_ctor_get(v_v_4347_, 5);
                v_ltInst_x3f_4354_ = leanh::lean_ctor_get(v_v_4347_, 6);
                v_lawfulOrderLTInst_x3f_4355_ = leanh::lean_ctor_get(v_v_4347_, 7);
                v_isPreorderInst_x3f_4356_ = leanh::lean_ctor_get(v_v_4347_, 8);
                v_orderedAddInst_x3f_4357_ = leanh::lean_ctor_get(v_v_4347_, 9);
                v_isLinearInst_x3f_4358_ = leanh::lean_ctor_get(v_v_4347_, 10);
                v_noNatDivInst_x3f_4359_ = leanh::lean_ctor_get(v_v_4347_, 11);
                v_ringInst_x3f_4360_ = leanh::lean_ctor_get(v_v_4347_, 12);
                v_commRingInst_x3f_4361_ = leanh::lean_ctor_get(v_v_4347_, 13);
                v_orderedRingInst_x3f_4362_ = leanh::lean_ctor_get(v_v_4347_, 14);
                v_fieldInst_x3f_4363_ = leanh::lean_ctor_get(v_v_4347_, 15);
                v_charInst_x3f_4364_ = leanh::lean_ctor_get(v_v_4347_, 16);
                v_zero_4365_ = leanh::lean_ctor_get(v_v_4347_, 17);
                v_ofNatZero_4366_ = leanh::lean_ctor_get(v_v_4347_, 18);
                v_one_x3f_4367_ = leanh::lean_ctor_get(v_v_4347_, 19);
                v_leFn_x3f_4368_ = leanh::lean_ctor_get(v_v_4347_, 20);
                v_ltFn_x3f_4369_ = leanh::lean_ctor_get(v_v_4347_, 21);
                v_addFn_4370_ = leanh::lean_ctor_get(v_v_4347_, 22);
                v_zsmulFn_4371_ = leanh::lean_ctor_get(v_v_4347_, 23);
                v_nsmulFn_4372_ = leanh::lean_ctor_get(v_v_4347_, 24);
                v_zsmulFn_x3f_4373_ = leanh::lean_ctor_get(v_v_4347_, 25);
                v_nsmulFn_x3f_4374_ = leanh::lean_ctor_get(v_v_4347_, 26);
                v_homomulFn_x3f_4375_ = leanh::lean_ctor_get(v_v_4347_, 27);
                v_subFn_4376_ = leanh::lean_ctor_get(v_v_4347_, 28);
                v_negFn_4377_ = leanh::lean_ctor_get(v_v_4347_, 29);
                v_vars_4378_ = leanh::lean_ctor_get(v_v_4347_, 30);
                v_varMap_4379_ = leanh::lean_ctor_get(v_v_4347_, 31);
                v_lowers_4380_ = leanh::lean_ctor_get(v_v_4347_, 32);
                v_uppers_4381_ = leanh::lean_ctor_get(v_v_4347_, 33);
                v_diseqs_4382_ = leanh::lean_ctor_get(v_v_4347_, 34);
                v_assignment_4383_ = leanh::lean_ctor_get(v_v_4347_, 35);
                v_caseSplits_4384_ = leanh::lean_ctor_get_uint8(
                    v_v_4347_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 42) as u32,
                );
                v_conflict_x3f_4385_ = leanh::lean_ctor_get(v_v_4347_, 36);
                v_diseqSplits_4386_ = leanh::lean_ctor_get(v_v_4347_, 37);
                v_elimEqs_4387_ = leanh::lean_ctor_get(v_v_4347_, 38);
                v_elimStack_4388_ = leanh::lean_ctor_get(v_v_4347_, 39);
                v_occurs_4389_ = leanh::lean_ctor_get(v_v_4347_, 40);
                v_ignored_4390_ = leanh::lean_ctor_get(v_v_4347_, 41);
                v_isSharedCheck_4404_ = (!leanh::lean_is_exclusive(v_v_4347_)) as u8;
                if v_isSharedCheck_4404_ == 0 {
                    v___x_4392_ = v_v_4347_;
                    v_isShared_4393_ = v_isSharedCheck_4404_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_ignored_4390_);
                    leanh::lean_inc(v_occurs_4389_);
                    leanh::lean_inc(v_elimStack_4388_);
                    leanh::lean_inc(v_elimEqs_4387_);
                    leanh::lean_inc(v_diseqSplits_4386_);
                    leanh::lean_inc(v_conflict_x3f_4385_);
                    leanh::lean_inc(v_assignment_4383_);
                    leanh::lean_inc(v_diseqs_4382_);
                    leanh::lean_inc(v_uppers_4381_);
                    leanh::lean_inc(v_lowers_4380_);
                    leanh::lean_inc(v_varMap_4379_);
                    leanh::lean_inc(v_vars_4378_);
                    leanh::lean_inc(v_negFn_4377_);
                    leanh::lean_inc(v_subFn_4376_);
                    leanh::lean_inc(v_homomulFn_x3f_4375_);
                    leanh::lean_inc(v_nsmulFn_x3f_4374_);
                    leanh::lean_inc(v_zsmulFn_x3f_4373_);
                    leanh::lean_inc(v_nsmulFn_4372_);
                    leanh::lean_inc(v_zsmulFn_4371_);
                    leanh::lean_inc(v_addFn_4370_);
                    leanh::lean_inc(v_ltFn_x3f_4369_);
                    leanh::lean_inc(v_leFn_x3f_4368_);
                    leanh::lean_inc(v_one_x3f_4367_);
                    leanh::lean_inc(v_ofNatZero_4366_);
                    leanh::lean_inc(v_zero_4365_);
                    leanh::lean_inc(v_charInst_x3f_4364_);
                    leanh::lean_inc(v_fieldInst_x3f_4363_);
                    leanh::lean_inc(v_orderedRingInst_x3f_4362_);
                    leanh::lean_inc(v_commRingInst_x3f_4361_);
                    leanh::lean_inc(v_ringInst_x3f_4360_);
                    leanh::lean_inc(v_noNatDivInst_x3f_4359_);
                    leanh::lean_inc(v_isLinearInst_x3f_4358_);
                    leanh::lean_inc(v_orderedAddInst_x3f_4357_);
                    leanh::lean_inc(v_isPreorderInst_x3f_4356_);
                    leanh::lean_inc(v_lawfulOrderLTInst_x3f_4355_);
                    leanh::lean_inc(v_ltInst_x3f_4354_);
                    leanh::lean_inc(v_leInst_x3f_4353_);
                    leanh::lean_inc(v_intModuleInst_4352_);
                    leanh::lean_inc(v_u_4351_);
                    leanh::lean_inc(v_type_4350_);
                    leanh::lean_inc(v_ringId_x3f_4349_);
                    leanh::lean_inc(v_id_4348_);
                    leanh::lean_dec(v_v_4347_);
                    v___x_4392_ = leanh::lean_box(0);
                    v_isShared_4393_ = v_isSharedCheck_4404_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4394_ = leanh::lean_box(0);
                v_xs_x27_4395_ = lean_array_fset(v_structs_4334_, v_a_4331_, v___x_4394_);
                v___x_4396_ = l_Lean_Meta_Grind_Arith_shrink(v_assignment_4383_, v_x_4332_);
                if v_isShared_4393_ == 0 {
                    leanh::lean_ctor_set(v___x_4392_, 35, v___x_4396_);
                    v___x_4398_ = v___x_4392_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4403_ = leanh::lean_alloc_ctor(0, 42, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 0, v_id_4348_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 1, v_ringId_x3f_4349_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 2, v_type_4350_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 3, v_u_4351_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 4, v_intModuleInst_4352_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 5, v_leInst_x3f_4353_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 6, v_ltInst_x3f_4354_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4403_,
                        7,
                        v_lawfulOrderLTInst_x3f_4355_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4403_,
                        8,
                        v_isPreorderInst_x3f_4356_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4403_,
                        9,
                        v_orderedAddInst_x3f_4357_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4403_,
                        10,
                        v_isLinearInst_x3f_4358_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4403_,
                        11,
                        v_noNatDivInst_x3f_4359_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 12, v_ringInst_x3f_4360_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4403_,
                        13,
                        v_commRingInst_x3f_4361_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4403_,
                        14,
                        v_orderedRingInst_x3f_4362_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 15, v_fieldInst_x3f_4363_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 16, v_charInst_x3f_4364_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 17, v_zero_4365_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 18, v_ofNatZero_4366_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 19, v_one_x3f_4367_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 20, v_leFn_x3f_4368_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 21, v_ltFn_x3f_4369_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 22, v_addFn_4370_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 23, v_zsmulFn_4371_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 24, v_nsmulFn_4372_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 25, v_zsmulFn_x3f_4373_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 26, v_nsmulFn_x3f_4374_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 27, v_homomulFn_x3f_4375_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 28, v_subFn_4376_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 29, v_negFn_4377_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 30, v_vars_4378_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 31, v_varMap_4379_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 32, v_lowers_4380_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 33, v_uppers_4381_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 34, v_diseqs_4382_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 35, v___x_4396_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 36, v_conflict_x3f_4385_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 37, v_diseqSplits_4386_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 38, v_elimEqs_4387_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 39, v_elimStack_4388_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 40, v_occurs_4389_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 41, v_ignored_4390_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4403_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 42) as u32,
                        v_caseSplits_4384_,
                    );
                    v___x_4398_ = v_reuseFailAlloc_4403_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4399_ = lean_array_fset(v_xs_x27_4395_, v_a_4331_, v___x_4398_);
                if v_isShared_4346_ == 0 {
                    leanh::lean_ctor_set(v___x_4345_, 0, v___x_4399_);
                    v___x_4401_ = v___x_4345_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4402_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4402_, 0, v___x_4399_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4402_, 1, v_typeIdOf_4335_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4402_, 2, v_exprToStructId_4336_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4402_,
                        3,
                        v_exprToStructIdEntries_4337_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4402_,
                        4,
                        v_forbiddenNatModules_4338_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4402_, 5, v_natStructs_4339_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4402_, 6, v_natTypeIdOf_4340_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4402_,
                        7,
                        v_exprToNatStructId_4341_,
                    );
                    v___x_4401_ = v_reuseFailAlloc_4402_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4401_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0___boxed(
    mut v_a_4414_: *mut leanh::LeanObject,
    mut v_x_4415_: *mut leanh::LeanObject,
    mut v_s_4416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4417_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0(
        v_a_4414_, v_x_4415_, v_s_4416_,
    );
    leanh::lean_dec(v_x_4415_);
    leanh::lean_dec(v_a_4414_);
    return v_res_4417_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(
    mut v_x_4418_: *mut leanh::LeanObject,
    mut v_a_4419_: *mut leanh::LeanObject,
    mut v_a_4420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_4419_);
    v___f_4422_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_4422_, 0, v_a_4419_);
    leanh::lean_closure_set(v___f_4422_, 1, v_x_4418_);
    v___x_4423_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
    v___x_4424_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4423_, v___f_4422_, v_a_4420_);
    return v___x_4424_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___boxed(
    mut v_x_4425_: *mut leanh::LeanObject,
    mut v_a_4426_: *mut leanh::LeanObject,
    mut v_a_4427_: *mut leanh::LeanObject,
    mut v_a_4428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4429_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(
        v_x_4425_, v_a_4426_, v_a_4427_,
    );
    leanh::lean_dec(v_a_4427_);
    leanh::lean_dec(v_a_4426_);
    return v_res_4429_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom(
    mut v_x_4430_: *mut leanh::LeanObject,
    mut v_a_4431_: *mut leanh::LeanObject,
    mut v_a_4432_: *mut leanh::LeanObject,
    mut v_a_4433_: *mut leanh::LeanObject,
    mut v_a_4434_: *mut leanh::LeanObject,
    mut v_a_4435_: *mut leanh::LeanObject,
    mut v_a_4436_: *mut leanh::LeanObject,
    mut v_a_4437_: *mut leanh::LeanObject,
    mut v_a_4438_: *mut leanh::LeanObject,
    mut v_a_4439_: *mut leanh::LeanObject,
    mut v_a_4440_: *mut leanh::LeanObject,
    mut v_a_4441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4443_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(
        v_x_4430_, v_a_4431_, v_a_4432_,
    );
    return v___x_4443_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___boxed(
    mut v_x_4444_: *mut leanh::LeanObject,
    mut v_a_4445_: *mut leanh::LeanObject,
    mut v_a_4446_: *mut leanh::LeanObject,
    mut v_a_4447_: *mut leanh::LeanObject,
    mut v_a_4448_: *mut leanh::LeanObject,
    mut v_a_4449_: *mut leanh::LeanObject,
    mut v_a_4450_: *mut leanh::LeanObject,
    mut v_a_4451_: *mut leanh::LeanObject,
    mut v_a_4452_: *mut leanh::LeanObject,
    mut v_a_4453_: *mut leanh::LeanObject,
    mut v_a_4454_: *mut leanh::LeanObject,
    mut v_a_4455_: *mut leanh::LeanObject,
    mut v_a_4456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4457_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom(
        v_x_4444_, v_a_4445_, v_a_4446_, v_a_4447_, v_a_4448_, v_a_4449_, v_a_4450_, v_a_4451_,
        v_a_4452_, v_a_4453_, v_a_4454_, v_a_4455_,
    );
    leanh::lean_dec(v_a_4455_);
    leanh::lean_dec_ref(v_a_4454_);
    leanh::lean_dec(v_a_4453_);
    leanh::lean_dec_ref(v_a_4452_);
    leanh::lean_dec(v_a_4451_);
    leanh::lean_dec_ref(v_a_4450_);
    leanh::lean_dec(v_a_4449_);
    leanh::lean_dec_ref(v_a_4448_);
    leanh::lean_dec(v_a_4447_);
    leanh::lean_dec(v_a_4446_);
    leanh::lean_dec(v_a_4445_);
    return v_res_4457_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getVar(
    mut v_x_4458_: *mut leanh::LeanObject,
    mut v_a_4459_: *mut leanh::LeanObject,
    mut v_a_4460_: *mut leanh::LeanObject,
    mut v_a_4461_: *mut leanh::LeanObject,
    mut v_a_4462_: *mut leanh::LeanObject,
    mut v_a_4463_: *mut leanh::LeanObject,
    mut v_a_4464_: *mut leanh::LeanObject,
    mut v_a_4465_: *mut leanh::LeanObject,
    mut v_a_4466_: *mut leanh::LeanObject,
    mut v_a_4467_: *mut leanh::LeanObject,
    mut v_a_4468_: *mut leanh::LeanObject,
    mut v_a_4469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4475_: u8 = 0;
    let mut v_vars_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: u8 = 0;
    let mut v___x_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4488_: u8 = 0;
    let mut v_a_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4492_: u8 = 0;
    let mut v___x_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4496_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4471_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_, v_a_4463_, v_a_4464_, v_a_4465_,
                    v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_,
                );
                if leanh::lean_obj_tag(v___x_4471_) == 0 {
                    v_a_4472_ = leanh::lean_ctor_get(v___x_4471_, 0);
                    v_isSharedCheck_4488_ = (!leanh::lean_is_exclusive(v___x_4471_)) as u8;
                    if v_isSharedCheck_4488_ == 0 {
                        v___x_4474_ = v___x_4471_;
                        v_isShared_4475_ = v_isSharedCheck_4488_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4472_);
                        leanh::lean_dec(v___x_4471_);
                        v___x_4474_ = leanh::lean_box(0);
                        v_isShared_4475_ = v_isSharedCheck_4488_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4489_ = leanh::lean_ctor_get(v___x_4471_, 0);
                    v_isSharedCheck_4496_ = (!leanh::lean_is_exclusive(v___x_4471_)) as u8;
                    if v_isSharedCheck_4496_ == 0 {
                        v___x_4491_ = v___x_4471_;
                        v_isShared_4492_ = v_isSharedCheck_4496_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4489_);
                        leanh::lean_dec(v___x_4471_);
                        v___x_4491_ = leanh::lean_box(0);
                        v_isShared_4492_ = v_isSharedCheck_4496_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_vars_4476_ = leanh::lean_ctor_get(v_a_4472_, 30);
                leanh::lean_inc_ref(v_vars_4476_);
                leanh::lean_dec(v_a_4472_);
                v_size_4477_ = leanh::lean_ctor_get(v_vars_4476_, 2);
                v___x_4478_ = l_Lean_instInhabitedExpr;
                v___x_4479_ = lean_nat_dec_lt(v_x_4458_, v_size_4477_);
                if v___x_4479_ == 0 {
                    leanh::lean_dec_ref(v_vars_4476_);
                    v___x_4480_ = l_outOfBounds___redArg(v___x_4478_);
                    if v_isShared_4475_ == 0 {
                        leanh::lean_ctor_set(v___x_4474_, 0, v___x_4480_);
                        v___x_4482_ = v___x_4474_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4483_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4483_, 0, v___x_4480_);
                        v___x_4482_ = v_reuseFailAlloc_4483_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4484_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_4478_,
                        v_vars_4476_,
                        v_x_4458_,
                    );
                    leanh::lean_dec_ref(v_vars_4476_);
                    if v_isShared_4475_ == 0 {
                        leanh::lean_ctor_set(v___x_4474_, 0, v___x_4484_);
                        v___x_4486_ = v___x_4474_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4487_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4487_, 0, v___x_4484_);
                        v___x_4486_ = v_reuseFailAlloc_4487_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4482_;
            }
            3 => {
                return v___x_4486_;
            }
            4 => {
                if v_isShared_4492_ == 0 {
                    v___x_4494_ = v___x_4491_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4495_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4495_, 0, v_a_4489_);
                    v___x_4494_ = v_reuseFailAlloc_4495_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4494_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getVar___boxed(
    mut v_x_4497_: *mut leanh::LeanObject,
    mut v_a_4498_: *mut leanh::LeanObject,
    mut v_a_4499_: *mut leanh::LeanObject,
    mut v_a_4500_: *mut leanh::LeanObject,
    mut v_a_4501_: *mut leanh::LeanObject,
    mut v_a_4502_: *mut leanh::LeanObject,
    mut v_a_4503_: *mut leanh::LeanObject,
    mut v_a_4504_: *mut leanh::LeanObject,
    mut v_a_4505_: *mut leanh::LeanObject,
    mut v_a_4506_: *mut leanh::LeanObject,
    mut v_a_4507_: *mut leanh::LeanObject,
    mut v_a_4508_: *mut leanh::LeanObject,
    mut v_a_4509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4510_ = l_Lean_Meta_Grind_Arith_Linear_getVar(
        v_x_4497_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_,
        v_a_4505_, v_a_4506_, v_a_4507_, v_a_4508_,
    );
    leanh::lean_dec(v_a_4508_);
    leanh::lean_dec_ref(v_a_4507_);
    leanh::lean_dec(v_a_4506_);
    leanh::lean_dec_ref(v_a_4505_);
    leanh::lean_dec(v_a_4504_);
    leanh::lean_dec_ref(v_a_4503_);
    leanh::lean_dec(v_a_4502_);
    leanh::lean_dec_ref(v_a_4501_);
    leanh::lean_dec(v_a_4500_);
    leanh::lean_dec(v_a_4499_);
    leanh::lean_dec(v_a_4498_);
    leanh::lean_dec(v_x_4497_);
    return v_res_4510_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_inconsistent(
    mut v_a_4511_: *mut leanh::LeanObject,
    mut v_a_4512_: *mut leanh::LeanObject,
    mut v_a_4513_: *mut leanh::LeanObject,
    mut v_a_4514_: *mut leanh::LeanObject,
    mut v_a_4515_: *mut leanh::LeanObject,
    mut v_a_4516_: *mut leanh::LeanObject,
    mut v_a_4517_: *mut leanh::LeanObject,
    mut v_a_4518_: *mut leanh::LeanObject,
    mut v_a_4519_: *mut leanh::LeanObject,
    mut v_a_4520_: *mut leanh::LeanObject,
    mut v_a_4521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: u8 = 0;
    let mut v___x_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4530_: u8 = 0;
    let mut v_conflict_x3f_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: u8 = 0;
    let mut v___x_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4540_: u8 = 0;
    let mut v_a_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4544_: u8 = 0;
    let mut v___x_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4548_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4523_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_4512_);
                if leanh::lean_obj_tag(v___x_4523_) == 0 {
                    v_a_4524_ = leanh::lean_ctor_get(v___x_4523_, 0);
                    leanh::lean_inc(v_a_4524_);
                    v___x_4525_ = (leanh::lean_unbox(v_a_4524_) as u8);
                    if v___x_4525_ == 0 {
                        leanh::lean_dec_ref_known(v___x_4523_, 1);
                        v___x_4526_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                            v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_,
                            v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_,
                        );
                        if leanh::lean_obj_tag(v___x_4526_) == 0 {
                            v_a_4527_ = leanh::lean_ctor_get(v___x_4526_, 0);
                            v_isSharedCheck_4540_ =
                                (!leanh::lean_is_exclusive(v___x_4526_)) as u8;
                            if v_isSharedCheck_4540_ == 0 {
                                v___x_4529_ = v___x_4526_;
                                v_isShared_4530_ = v_isSharedCheck_4540_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4527_);
                                leanh::lean_dec(v___x_4526_);
                                v___x_4529_ = leanh::lean_box(0);
                                v_isShared_4530_ = v_isSharedCheck_4540_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_4524_);
                            v_a_4541_ = leanh::lean_ctor_get(v___x_4526_, 0);
                            v_isSharedCheck_4548_ =
                                (!leanh::lean_is_exclusive(v___x_4526_)) as u8;
                            if v_isSharedCheck_4548_ == 0 {
                                v___x_4543_ = v___x_4526_;
                                v_isShared_4544_ = v_isSharedCheck_4548_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4541_);
                                leanh::lean_dec(v___x_4526_);
                                v___x_4543_ = leanh::lean_box(0);
                                v_isShared_4544_ = v_isSharedCheck_4548_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_4524_);
                        return v___x_4523_;
                    }
                } else {
                    return v___x_4523_;
                }
            }
            1 => {
                v_conflict_x3f_4531_ = leanh::lean_ctor_get(v_a_4527_, 36);
                leanh::lean_inc(v_conflict_x3f_4531_);
                leanh::lean_dec(v_a_4527_);
                if leanh::lean_obj_tag(v_conflict_x3f_4531_) == 0 {
                    if v_isShared_4530_ == 0 {
                        leanh::lean_ctor_set(v___x_4529_, 0, v_a_4524_);
                        v___x_4533_ = v___x_4529_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4534_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4534_, 0, v_a_4524_);
                        v___x_4533_ = v_reuseFailAlloc_4534_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_conflict_x3f_4531_, 1);
                    leanh::lean_dec(v_a_4524_);
                    v___x_4535_ = 1;
                    v___x_4536_ = leanh::lean_box((v___x_4535_) as usize);
                    if v_isShared_4530_ == 0 {
                        leanh::lean_ctor_set(v___x_4529_, 0, v___x_4536_);
                        v___x_4538_ = v___x_4529_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4539_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4539_, 0, v___x_4536_);
                        v___x_4538_ = v_reuseFailAlloc_4539_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4533_;
            }
            3 => {
                return v___x_4538_;
            }
            4 => {
                if v_isShared_4544_ == 0 {
                    v___x_4546_ = v___x_4543_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4547_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4547_, 0, v_a_4541_);
                    v___x_4546_ = v_reuseFailAlloc_4547_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4546_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_inconsistent___boxed(
    mut v_a_4549_: *mut leanh::LeanObject,
    mut v_a_4550_: *mut leanh::LeanObject,
    mut v_a_4551_: *mut leanh::LeanObject,
    mut v_a_4552_: *mut leanh::LeanObject,
    mut v_a_4553_: *mut leanh::LeanObject,
    mut v_a_4554_: *mut leanh::LeanObject,
    mut v_a_4555_: *mut leanh::LeanObject,
    mut v_a_4556_: *mut leanh::LeanObject,
    mut v_a_4557_: *mut leanh::LeanObject,
    mut v_a_4558_: *mut leanh::LeanObject,
    mut v_a_4559_: *mut leanh::LeanObject,
    mut v_a_4560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4561_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(
        v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_, v_a_4553_, v_a_4554_, v_a_4555_, v_a_4556_,
        v_a_4557_, v_a_4558_, v_a_4559_,
    );
    leanh::lean_dec(v_a_4559_);
    leanh::lean_dec_ref(v_a_4558_);
    leanh::lean_dec(v_a_4557_);
    leanh::lean_dec_ref(v_a_4556_);
    leanh::lean_dec(v_a_4555_);
    leanh::lean_dec_ref(v_a_4554_);
    leanh::lean_dec(v_a_4553_);
    leanh::lean_dec_ref(v_a_4552_);
    leanh::lean_dec(v_a_4551_);
    leanh::lean_dec(v_a_4550_);
    leanh::lean_dec(v_a_4549_);
    return v_res_4561_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_eliminated(
    mut v_x_4562_: *mut leanh::LeanObject,
    mut v_a_4563_: *mut leanh::LeanObject,
    mut v_a_4564_: *mut leanh::LeanObject,
    mut v_a_4565_: *mut leanh::LeanObject,
    mut v_a_4566_: *mut leanh::LeanObject,
    mut v_a_4567_: *mut leanh::LeanObject,
    mut v_a_4568_: *mut leanh::LeanObject,
    mut v_a_4569_: *mut leanh::LeanObject,
    mut v_a_4570_: *mut leanh::LeanObject,
    mut v_a_4571_: *mut leanh::LeanObject,
    mut v_a_4572_: *mut leanh::LeanObject,
    mut v_a_4573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4579_: u8 = 0;
    let mut v___y_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: u8 = 0;
    let mut v___x_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: u8 = 0;
    let mut v___x_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_elimEqs_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: u8 = 0;
    let mut v___x_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4598_: u8 = 0;
    let mut v_a_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4602_: u8 = 0;
    let mut v___x_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4606_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4575_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_,
                    v_a_4570_, v_a_4571_, v_a_4572_, v_a_4573_,
                );
                if leanh::lean_obj_tag(v___x_4575_) == 0 {
                    v_a_4576_ = leanh::lean_ctor_get(v___x_4575_, 0);
                    v_isSharedCheck_4598_ = (!leanh::lean_is_exclusive(v___x_4575_)) as u8;
                    if v_isSharedCheck_4598_ == 0 {
                        v___x_4578_ = v___x_4575_;
                        v_isShared_4579_ = v_isSharedCheck_4598_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4576_);
                        leanh::lean_dec(v___x_4575_);
                        v___x_4578_ = leanh::lean_box(0);
                        v_isShared_4579_ = v_isSharedCheck_4598_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4599_ = leanh::lean_ctor_get(v___x_4575_, 0);
                    v_isSharedCheck_4606_ = (!leanh::lean_is_exclusive(v___x_4575_)) as u8;
                    if v_isSharedCheck_4606_ == 0 {
                        v___x_4601_ = v___x_4575_;
                        v_isShared_4602_ = v_isSharedCheck_4606_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4599_);
                        leanh::lean_dec(v___x_4575_);
                        v___x_4601_ = leanh::lean_box(0);
                        v_isShared_4602_ = v_isSharedCheck_4606_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_elimEqs_4592_ = leanh::lean_ctor_get(v_a_4576_, 38);
                leanh::lean_inc_ref(v_elimEqs_4592_);
                leanh::lean_dec(v_a_4576_);
                v_size_4593_ = leanh::lean_ctor_get(v_elimEqs_4592_, 2);
                v___x_4594_ = leanh::lean_box(0);
                v___x_4595_ = lean_nat_dec_lt(v_x_4562_, v_size_4593_);
                if v___x_4595_ == 0 {
                    leanh::lean_dec_ref(v_elimEqs_4592_);
                    v___x_4596_ = l_outOfBounds___redArg(v___x_4594_);
                    v___y_4581_ = v___x_4596_;
                    state = 2;
                    continue;
                } else {
                    v___x_4597_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_4594_,
                        v_elimEqs_4592_,
                        v_x_4562_,
                    );
                    leanh::lean_dec_ref(v_elimEqs_4592_);
                    v___y_4581_ = v___x_4597_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if leanh::lean_obj_tag(v___y_4581_) == 0 {
                    v___x_4582_ = 0;
                    v___x_4583_ = leanh::lean_box((v___x_4582_) as usize);
                    if v_isShared_4579_ == 0 {
                        leanh::lean_ctor_set(v___x_4578_, 0, v___x_4583_);
                        v___x_4585_ = v___x_4578_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4586_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4586_, 0, v___x_4583_);
                        v___x_4585_ = v_reuseFailAlloc_4586_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___y_4581_, 1);
                    v___x_4587_ = 1;
                    v___x_4588_ = leanh::lean_box((v___x_4587_) as usize);
                    if v_isShared_4579_ == 0 {
                        leanh::lean_ctor_set(v___x_4578_, 0, v___x_4588_);
                        v___x_4590_ = v___x_4578_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4591_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4591_, 0, v___x_4588_);
                        v___x_4590_ = v_reuseFailAlloc_4591_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4585_;
            }
            4 => {
                return v___x_4590_;
            }
            5 => {
                if v_isShared_4602_ == 0 {
                    v___x_4604_ = v___x_4601_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4605_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4605_, 0, v_a_4599_);
                    v___x_4604_ = v_reuseFailAlloc_4605_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4604_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_eliminated___boxed(
    mut v_x_4607_: *mut leanh::LeanObject,
    mut v_a_4608_: *mut leanh::LeanObject,
    mut v_a_4609_: *mut leanh::LeanObject,
    mut v_a_4610_: *mut leanh::LeanObject,
    mut v_a_4611_: *mut leanh::LeanObject,
    mut v_a_4612_: *mut leanh::LeanObject,
    mut v_a_4613_: *mut leanh::LeanObject,
    mut v_a_4614_: *mut leanh::LeanObject,
    mut v_a_4615_: *mut leanh::LeanObject,
    mut v_a_4616_: *mut leanh::LeanObject,
    mut v_a_4617_: *mut leanh::LeanObject,
    mut v_a_4618_: *mut leanh::LeanObject,
    mut v_a_4619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4620_ = l_Lean_Meta_Grind_Arith_Linear_eliminated(
        v_x_4607_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_, v_a_4614_,
        v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_,
    );
    leanh::lean_dec(v_a_4618_);
    leanh::lean_dec_ref(v_a_4617_);
    leanh::lean_dec(v_a_4616_);
    leanh::lean_dec_ref(v_a_4615_);
    leanh::lean_dec(v_a_4614_);
    leanh::lean_dec_ref(v_a_4613_);
    leanh::lean_dec(v_a_4612_);
    leanh::lean_dec_ref(v_a_4611_);
    leanh::lean_dec(v_a_4610_);
    leanh::lean_dec(v_a_4609_);
    leanh::lean_dec(v_a_4608_);
    leanh::lean_dec(v_x_4607_);
    return v_res_4620_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getOccursOf(
    mut v_x_4621_: *mut leanh::LeanObject,
    mut v_a_4622_: *mut leanh::LeanObject,
    mut v_a_4623_: *mut leanh::LeanObject,
    mut v_a_4624_: *mut leanh::LeanObject,
    mut v_a_4625_: *mut leanh::LeanObject,
    mut v_a_4626_: *mut leanh::LeanObject,
    mut v_a_4627_: *mut leanh::LeanObject,
    mut v_a_4628_: *mut leanh::LeanObject,
    mut v_a_4629_: *mut leanh::LeanObject,
    mut v_a_4630_: *mut leanh::LeanObject,
    mut v_a_4631_: *mut leanh::LeanObject,
    mut v_a_4632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4638_: u8 = 0;
    let mut v_occurs_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: u8 = 0;
    let mut v___x_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4651_: u8 = 0;
    let mut v_a_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4655_: u8 = 0;
    let mut v___x_4657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4659_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4634_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_4622_, v_a_4623_, v_a_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_,
                    v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_,
                );
                if leanh::lean_obj_tag(v___x_4634_) == 0 {
                    v_a_4635_ = leanh::lean_ctor_get(v___x_4634_, 0);
                    v_isSharedCheck_4651_ = (!leanh::lean_is_exclusive(v___x_4634_)) as u8;
                    if v_isSharedCheck_4651_ == 0 {
                        v___x_4637_ = v___x_4634_;
                        v_isShared_4638_ = v_isSharedCheck_4651_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4635_);
                        leanh::lean_dec(v___x_4634_);
                        v___x_4637_ = leanh::lean_box(0);
                        v_isShared_4638_ = v_isSharedCheck_4651_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4652_ = leanh::lean_ctor_get(v___x_4634_, 0);
                    v_isSharedCheck_4659_ = (!leanh::lean_is_exclusive(v___x_4634_)) as u8;
                    if v_isSharedCheck_4659_ == 0 {
                        v___x_4654_ = v___x_4634_;
                        v_isShared_4655_ = v_isSharedCheck_4659_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4652_);
                        leanh::lean_dec(v___x_4634_);
                        v___x_4654_ = leanh::lean_box(0);
                        v_isShared_4655_ = v_isSharedCheck_4659_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_occurs_4639_ = leanh::lean_ctor_get(v_a_4635_, 40);
                leanh::lean_inc_ref(v_occurs_4639_);
                leanh::lean_dec(v_a_4635_);
                v_size_4640_ = leanh::lean_ctor_get(v_occurs_4639_, 2);
                v___x_4641_ = leanh::lean_box(1);
                v___x_4642_ = lean_nat_dec_lt(v_x_4621_, v_size_4640_);
                if v___x_4642_ == 0 {
                    leanh::lean_dec_ref(v_occurs_4639_);
                    v___x_4643_ = l_outOfBounds___redArg(v___x_4641_);
                    if v_isShared_4638_ == 0 {
                        leanh::lean_ctor_set(v___x_4637_, 0, v___x_4643_);
                        v___x_4645_ = v___x_4637_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4646_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4646_, 0, v___x_4643_);
                        v___x_4645_ = v_reuseFailAlloc_4646_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4647_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_4641_,
                        v_occurs_4639_,
                        v_x_4621_,
                    );
                    leanh::lean_dec_ref(v_occurs_4639_);
                    if v_isShared_4638_ == 0 {
                        leanh::lean_ctor_set(v___x_4637_, 0, v___x_4647_);
                        v___x_4649_ = v___x_4637_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4650_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4650_, 0, v___x_4647_);
                        v___x_4649_ = v_reuseFailAlloc_4650_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4645_;
            }
            3 => {
                return v___x_4649_;
            }
            4 => {
                if v_isShared_4655_ == 0 {
                    v___x_4657_ = v___x_4654_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4658_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4658_, 0, v_a_4652_);
                    v___x_4657_ = v_reuseFailAlloc_4658_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4657_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getOccursOf___boxed(
    mut v_x_4660_: *mut leanh::LeanObject,
    mut v_a_4661_: *mut leanh::LeanObject,
    mut v_a_4662_: *mut leanh::LeanObject,
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
) -> *mut leanh::LeanObject {
    let mut v_res_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4673_ = l_Lean_Meta_Grind_Arith_Linear_getOccursOf(
        v_x_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_,
        v_a_4668_, v_a_4669_, v_a_4670_, v_a_4671_,
    );
    leanh::lean_dec(v_a_4671_);
    leanh::lean_dec_ref(v_a_4670_);
    leanh::lean_dec(v_a_4669_);
    leanh::lean_dec_ref(v_a_4668_);
    leanh::lean_dec(v_a_4667_);
    leanh::lean_dec_ref(v_a_4666_);
    leanh::lean_dec(v_a_4665_);
    leanh::lean_dec_ref(v_a_4664_);
    leanh::lean_dec(v_a_4663_);
    leanh::lean_dec(v_a_4662_);
    leanh::lean_dec(v_a_4661_);
    leanh::lean_dec(v_x_4660_);
    return v_res_4673_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(
    mut v_k_4674_: *mut leanh::LeanObject,
    mut v_t_4675_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_k_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: u8 = 0;
    let mut v___x_4680_: u8 = 0;
    let mut v___x_4683_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_4675_) == 0 {
                    v_k_4676_ = leanh::lean_ctor_get(v_t_4675_, 1);
                    v_l_4677_ = leanh::lean_ctor_get(v_t_4675_, 3);
                    v_r_4678_ = leanh::lean_ctor_get(v_t_4675_, 4);
                    v___x_4679_ = lean_nat_dec_lt(v_k_4674_, v_k_4676_);
                    if v___x_4679_ == 0 {
                        v___x_4680_ = lean_nat_dec_eq(v_k_4674_, v_k_4676_);
                        if v___x_4680_ == 0 {
                            v_t_4675_ = v_r_4678_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_4680_;
                        }
                    } else {
                        v_t_4675_ = v_l_4677_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_4683_ = 0;
                    return v___x_4683_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg___boxed(
    mut v_k_4684_: *mut leanh::LeanObject,
    mut v_t_4685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4686_: u8 = 0;
    let mut v_r_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4686_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_k_4684_, v_t_4685_);
    leanh::lean_dec(v_t_4685_);
    leanh::lean_dec(v_k_4684_);
    v_r_4687_ = leanh::lean_box((v_res_4686_) as usize);
    return v_r_4687_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(
    mut v_k_4688_: *mut leanh::LeanObject,
    mut v_v_4689_: *mut leanh::LeanObject,
    mut v_t_4690_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4698_: u8 = 0;
    let mut v___x_4699_: u8 = 0;
    let mut v___x_4700_: u8 = 0;
    let mut v_impl_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: u8 = 0;
    let mut v___x_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4719_: u8 = 0;
    let mut v_size_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: u8 = 0;
    let mut v___x_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4731_: u8 = 0;
    let mut v___x_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4756_: u8 = 0;
    let mut v_unused_4757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4769_: u8 = 0;
    let mut v___x_4771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4773_: u8 = 0;
    let mut v_unused_4774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4780_: u8 = 0;
    let mut v_unused_4781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4792_: u8 = 0;
    let mut v_k_4793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4797_: u8 = 0;
    let mut v___x_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4808_: u8 = 0;
    let mut v_unused_4809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4812_: u8 = 0;
    let mut v_unused_4813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4820_: u8 = 0;
    let mut v___x_4821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4828_: u8 = 0;
    let mut v_unused_4829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_4839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: u8 = 0;
    let mut v___x_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4857_: u8 = 0;
    let mut v_size_4858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: u8 = 0;
    let mut v___x_4868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4869_: u8 = 0;
    let mut v___x_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4895_: u8 = 0;
    let mut v_unused_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4909_: u8 = 0;
    let mut v___x_4911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4913_: u8 = 0;
    let mut v_unused_4914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4920_: u8 = 0;
    let mut v_unused_4921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4932_: u8 = 0;
    let mut v___x_4933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4940_: u8 = 0;
    let mut v_unused_4941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4948_: u8 = 0;
    let mut v_k_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4953_: u8 = 0;
    let mut v___x_4954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4964_: u8 = 0;
    let mut v_unused_4965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4968_: u8 = 0;
    let mut v_unused_4969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4976_: u8 = 0;
    let mut v___x_4977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_4690_) == 0 {
                    v_size_4691_ = leanh::lean_ctor_get(v_t_4690_, 0);
                    v_k_4692_ = leanh::lean_ctor_get(v_t_4690_, 1);
                    v_v_4693_ = leanh::lean_ctor_get(v_t_4690_, 2);
                    v_l_4694_ = leanh::lean_ctor_get(v_t_4690_, 3);
                    v_r_4695_ = leanh::lean_ctor_get(v_t_4690_, 4);
                    v_isSharedCheck_4976_ = (!leanh::lean_is_exclusive(v_t_4690_)) as u8;
                    if v_isSharedCheck_4976_ == 0 {
                        v___x_4697_ = v_t_4690_;
                        v_isShared_4698_ = v_isSharedCheck_4976_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_4695_);
                        leanh::lean_inc(v_l_4694_);
                        leanh::lean_inc(v_v_4693_);
                        leanh::lean_inc(v_k_4692_);
                        leanh::lean_inc(v_size_4691_);
                        leanh::lean_dec(v_t_4690_);
                        v___x_4697_ = leanh::lean_box(0);
                        v_isShared_4698_ = v_isSharedCheck_4976_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_4977_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4978_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_4978_, 0, v___x_4977_);
                    leanh::lean_ctor_set(v___x_4978_, 1, v_k_4688_);
                    leanh::lean_ctor_set(v___x_4978_, 2, v_v_4689_);
                    leanh::lean_ctor_set(v___x_4978_, 3, v_t_4690_);
                    leanh::lean_ctor_set(v___x_4978_, 4, v_t_4690_);
                    return v___x_4978_;
                }
            }
            1 => {
                v___x_4699_ = lean_nat_dec_lt(v_k_4688_, v_k_4692_);
                if v___x_4699_ == 0 {
                    v___x_4700_ = lean_nat_dec_eq(v_k_4688_, v_k_4692_);
                    if v___x_4700_ == 0 {
                        leanh::lean_dec(v_size_4691_);
                        v_impl_4701_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_4688_, v_v_4689_, v_r_4695_);
                        v___x_4702_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_l_4694_) == 0 {
                            v_size_4703_ = leanh::lean_ctor_get(v_l_4694_, 0);
                            v_size_4704_ = leanh::lean_ctor_get(v_impl_4701_, 0);
                            leanh::lean_inc(v_size_4704_);
                            v_k_4705_ = leanh::lean_ctor_get(v_impl_4701_, 1);
                            leanh::lean_inc(v_k_4705_);
                            v_v_4706_ = leanh::lean_ctor_get(v_impl_4701_, 2);
                            leanh::lean_inc(v_v_4706_);
                            v_l_4707_ = leanh::lean_ctor_get(v_impl_4701_, 3);
                            leanh::lean_inc(v_l_4707_);
                            v_r_4708_ = leanh::lean_ctor_get(v_impl_4701_, 4);
                            leanh::lean_inc(v_r_4708_);
                            v___x_4709_ = leanh::lean_unsigned_to_nat(3);
                            v___x_4710_ = lean_nat_mul(v___x_4709_, v_size_4703_);
                            v___x_4711_ = lean_nat_dec_lt(v___x_4710_, v_size_4704_);
                            leanh::lean_dec(v___x_4710_);
                            if v___x_4711_ == 0 {
                                leanh::lean_dec(v_r_4708_);
                                leanh::lean_dec(v_l_4707_);
                                leanh::lean_dec(v_v_4706_);
                                leanh::lean_dec(v_k_4705_);
                                v___x_4712_ = lean_nat_add(v___x_4702_, v_size_4703_);
                                v___x_4713_ = lean_nat_add(v___x_4712_, v_size_4704_);
                                leanh::lean_dec(v_size_4704_);
                                leanh::lean_dec(v___x_4712_);
                                if v_isShared_4698_ == 0 {
                                    leanh::lean_ctor_set(v___x_4697_, 4, v_impl_4701_);
                                    leanh::lean_ctor_set(v___x_4697_, 0, v___x_4713_);
                                    v___x_4715_ = v___x_4697_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4716_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4716_,
                                        0,
                                        v___x_4713_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4716_,
                                        1,
                                        v_k_4692_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4716_,
                                        2,
                                        v_v_4693_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4716_,
                                        3,
                                        v_l_4694_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4716_,
                                        4,
                                        v_impl_4701_,
                                    );
                                    v___x_4715_ = v_reuseFailAlloc_4716_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_4780_ =
                                    (!leanh::lean_is_exclusive(v_impl_4701_)) as u8;
                                if v_isSharedCheck_4780_ == 0 {
                                    v_unused_4781_ = leanh::lean_ctor_get(v_impl_4701_, 4);
                                    leanh::lean_dec(v_unused_4781_);
                                    v_unused_4782_ = leanh::lean_ctor_get(v_impl_4701_, 3);
                                    leanh::lean_dec(v_unused_4782_);
                                    v_unused_4783_ = leanh::lean_ctor_get(v_impl_4701_, 2);
                                    leanh::lean_dec(v_unused_4783_);
                                    v_unused_4784_ = leanh::lean_ctor_get(v_impl_4701_, 1);
                                    leanh::lean_dec(v_unused_4784_);
                                    v_unused_4785_ = leanh::lean_ctor_get(v_impl_4701_, 0);
                                    leanh::lean_dec(v_unused_4785_);
                                    v___x_4718_ = v_impl_4701_;
                                    v_isShared_4719_ = v_isSharedCheck_4780_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_impl_4701_);
                                    v___x_4718_ = leanh::lean_box(0);
                                    v_isShared_4719_ = v_isSharedCheck_4780_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_4786_ = leanh::lean_ctor_get(v_impl_4701_, 3);
                            leanh::lean_inc(v_l_4786_);
                            if leanh::lean_obj_tag(v_l_4786_) == 0 {
                                v_r_4787_ = leanh::lean_ctor_get(v_impl_4701_, 4);
                                v_k_4788_ = leanh::lean_ctor_get(v_impl_4701_, 1);
                                v_v_4789_ = leanh::lean_ctor_get(v_impl_4701_, 2);
                                v_isSharedCheck_4812_ =
                                    (!leanh::lean_is_exclusive(v_impl_4701_)) as u8;
                                if v_isSharedCheck_4812_ == 0 {
                                    v_unused_4813_ = leanh::lean_ctor_get(v_impl_4701_, 3);
                                    leanh::lean_dec(v_unused_4813_);
                                    v_unused_4814_ = leanh::lean_ctor_get(v_impl_4701_, 0);
                                    leanh::lean_dec(v_unused_4814_);
                                    v___x_4791_ = v_impl_4701_;
                                    v_isShared_4792_ = v_isSharedCheck_4812_;
                                    state = 13;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_r_4787_);
                                    leanh::lean_inc(v_v_4789_);
                                    leanh::lean_inc(v_k_4788_);
                                    leanh::lean_dec(v_impl_4701_);
                                    v___x_4791_ = leanh::lean_box(0);
                                    v_isShared_4792_ = v_isSharedCheck_4812_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_4815_ = leanh::lean_ctor_get(v_impl_4701_, 4);
                                leanh::lean_inc(v_r_4815_);
                                if leanh::lean_obj_tag(v_r_4815_) == 0 {
                                    v_k_4816_ = leanh::lean_ctor_get(v_impl_4701_, 1);
                                    v_v_4817_ = leanh::lean_ctor_get(v_impl_4701_, 2);
                                    v_isSharedCheck_4828_ =
                                        (!leanh::lean_is_exclusive(v_impl_4701_)) as u8;
                                    if v_isSharedCheck_4828_ == 0 {
                                        v_unused_4829_ =
                                            leanh::lean_ctor_get(v_impl_4701_, 4);
                                        leanh::lean_dec(v_unused_4829_);
                                        v_unused_4830_ =
                                            leanh::lean_ctor_get(v_impl_4701_, 3);
                                        leanh::lean_dec(v_unused_4830_);
                                        v_unused_4831_ =
                                            leanh::lean_ctor_get(v_impl_4701_, 0);
                                        leanh::lean_dec(v_unused_4831_);
                                        v___x_4819_ = v_impl_4701_;
                                        v_isShared_4820_ = v_isSharedCheck_4828_;
                                        state = 18;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_v_4817_);
                                        leanh::lean_inc(v_k_4816_);
                                        leanh::lean_dec(v_impl_4701_);
                                        v___x_4819_ = leanh::lean_box(0);
                                        v_isShared_4820_ = v_isSharedCheck_4828_;
                                        state = 18;
                                        continue;
                                    }
                                } else {
                                    v___x_4832_ = leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_4698_ == 0 {
                                        leanh::lean_ctor_set(v___x_4697_, 4, v_impl_4701_);
                                        leanh::lean_ctor_set(v___x_4697_, 3, v_r_4815_);
                                        leanh::lean_ctor_set(v___x_4697_, 0, v___x_4832_);
                                        v___x_4834_ = v___x_4697_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_4835_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4835_,
                                            0,
                                            v___x_4832_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4835_,
                                            1,
                                            v_k_4692_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4835_,
                                            2,
                                            v_v_4693_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4835_,
                                            3,
                                            v_r_4815_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4835_,
                                            4,
                                            v_impl_4701_,
                                        );
                                        v___x_4834_ = v_reuseFailAlloc_4835_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_v_4693_);
                        leanh::lean_dec(v_k_4692_);
                        if v_isShared_4698_ == 0 {
                            leanh::lean_ctor_set(v___x_4697_, 2, v_v_4689_);
                            leanh::lean_ctor_set(v___x_4697_, 1, v_k_4688_);
                            v___x_4837_ = v___x_4697_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_4838_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4838_, 0, v_size_4691_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4838_, 1, v_k_4688_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4838_, 2, v_v_4689_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4838_, 3, v_l_4694_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4838_, 4, v_r_4695_);
                            v___x_4837_ = v_reuseFailAlloc_4838_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_size_4691_);
                    v_impl_4839_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_4688_, v_v_4689_, v_l_4694_);
                    v___x_4840_ = leanh::lean_unsigned_to_nat(1);
                    if leanh::lean_obj_tag(v_r_4695_) == 0 {
                        v_size_4841_ = leanh::lean_ctor_get(v_r_4695_, 0);
                        v_size_4842_ = leanh::lean_ctor_get(v_impl_4839_, 0);
                        leanh::lean_inc(v_size_4842_);
                        v_k_4843_ = leanh::lean_ctor_get(v_impl_4839_, 1);
                        leanh::lean_inc(v_k_4843_);
                        v_v_4844_ = leanh::lean_ctor_get(v_impl_4839_, 2);
                        leanh::lean_inc(v_v_4844_);
                        v_l_4845_ = leanh::lean_ctor_get(v_impl_4839_, 3);
                        leanh::lean_inc(v_l_4845_);
                        v_r_4846_ = leanh::lean_ctor_get(v_impl_4839_, 4);
                        leanh::lean_inc(v_r_4846_);
                        v___x_4847_ = leanh::lean_unsigned_to_nat(3);
                        v___x_4848_ = lean_nat_mul(v___x_4847_, v_size_4841_);
                        v___x_4849_ = lean_nat_dec_lt(v___x_4848_, v_size_4842_);
                        leanh::lean_dec(v___x_4848_);
                        if v___x_4849_ == 0 {
                            leanh::lean_dec(v_r_4846_);
                            leanh::lean_dec(v_l_4845_);
                            leanh::lean_dec(v_v_4844_);
                            leanh::lean_dec(v_k_4843_);
                            v___x_4850_ = lean_nat_add(v___x_4840_, v_size_4842_);
                            leanh::lean_dec(v_size_4842_);
                            v___x_4851_ = lean_nat_add(v___x_4850_, v_size_4841_);
                            leanh::lean_dec(v___x_4850_);
                            if v_isShared_4698_ == 0 {
                                leanh::lean_ctor_set(v___x_4697_, 3, v_impl_4839_);
                                leanh::lean_ctor_set(v___x_4697_, 0, v___x_4851_);
                                v___x_4853_ = v___x_4697_;
                                state = 23;
                                continue;
                            } else {
                                v_reuseFailAlloc_4854_ =
                                    leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_4854_, 0, v___x_4851_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_4854_, 1, v_k_4692_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_4854_, 2, v_v_4693_);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4854_,
                                    3,
                                    v_impl_4839_,
                                );
                                leanh::lean_ctor_set(v_reuseFailAlloc_4854_, 4, v_r_4695_);
                                v___x_4853_ = v_reuseFailAlloc_4854_;
                                state = 23;
                                continue;
                            }
                        } else {
                            v_isSharedCheck_4920_ =
                                (!leanh::lean_is_exclusive(v_impl_4839_)) as u8;
                            if v_isSharedCheck_4920_ == 0 {
                                v_unused_4921_ = leanh::lean_ctor_get(v_impl_4839_, 4);
                                leanh::lean_dec(v_unused_4921_);
                                v_unused_4922_ = leanh::lean_ctor_get(v_impl_4839_, 3);
                                leanh::lean_dec(v_unused_4922_);
                                v_unused_4923_ = leanh::lean_ctor_get(v_impl_4839_, 2);
                                leanh::lean_dec(v_unused_4923_);
                                v_unused_4924_ = leanh::lean_ctor_get(v_impl_4839_, 1);
                                leanh::lean_dec(v_unused_4924_);
                                v_unused_4925_ = leanh::lean_ctor_get(v_impl_4839_, 0);
                                leanh::lean_dec(v_unused_4925_);
                                v___x_4856_ = v_impl_4839_;
                                v_isShared_4857_ = v_isSharedCheck_4920_;
                                state = 24;
                                continue;
                            } else {
                                leanh::lean_dec(v_impl_4839_);
                                v___x_4856_ = leanh::lean_box(0);
                                v_isShared_4857_ = v_isSharedCheck_4920_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        v_l_4926_ = leanh::lean_ctor_get(v_impl_4839_, 3);
                        leanh::lean_inc(v_l_4926_);
                        if leanh::lean_obj_tag(v_l_4926_) == 0 {
                            v_r_4927_ = leanh::lean_ctor_get(v_impl_4839_, 4);
                            v_k_4928_ = leanh::lean_ctor_get(v_impl_4839_, 1);
                            v_v_4929_ = leanh::lean_ctor_get(v_impl_4839_, 2);
                            v_isSharedCheck_4940_ =
                                (!leanh::lean_is_exclusive(v_impl_4839_)) as u8;
                            if v_isSharedCheck_4940_ == 0 {
                                v_unused_4941_ = leanh::lean_ctor_get(v_impl_4839_, 3);
                                leanh::lean_dec(v_unused_4941_);
                                v_unused_4942_ = leanh::lean_ctor_get(v_impl_4839_, 0);
                                leanh::lean_dec(v_unused_4942_);
                                v___x_4931_ = v_impl_4839_;
                                v_isShared_4932_ = v_isSharedCheck_4940_;
                                state = 34;
                                continue;
                            } else {
                                leanh::lean_inc(v_r_4927_);
                                leanh::lean_inc(v_v_4929_);
                                leanh::lean_inc(v_k_4928_);
                                leanh::lean_dec(v_impl_4839_);
                                v___x_4931_ = leanh::lean_box(0);
                                v_isShared_4932_ = v_isSharedCheck_4940_;
                                state = 34;
                                continue;
                            }
                        } else {
                            v_r_4943_ = leanh::lean_ctor_get(v_impl_4839_, 4);
                            leanh::lean_inc(v_r_4943_);
                            if leanh::lean_obj_tag(v_r_4943_) == 0 {
                                v_k_4944_ = leanh::lean_ctor_get(v_impl_4839_, 1);
                                v_v_4945_ = leanh::lean_ctor_get(v_impl_4839_, 2);
                                v_isSharedCheck_4968_ =
                                    (!leanh::lean_is_exclusive(v_impl_4839_)) as u8;
                                if v_isSharedCheck_4968_ == 0 {
                                    v_unused_4969_ = leanh::lean_ctor_get(v_impl_4839_, 4);
                                    leanh::lean_dec(v_unused_4969_);
                                    v_unused_4970_ = leanh::lean_ctor_get(v_impl_4839_, 3);
                                    leanh::lean_dec(v_unused_4970_);
                                    v_unused_4971_ = leanh::lean_ctor_get(v_impl_4839_, 0);
                                    leanh::lean_dec(v_unused_4971_);
                                    v___x_4947_ = v_impl_4839_;
                                    v_isShared_4948_ = v_isSharedCheck_4968_;
                                    state = 37;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_v_4945_);
                                    leanh::lean_inc(v_k_4944_);
                                    leanh::lean_dec(v_impl_4839_);
                                    v___x_4947_ = leanh::lean_box(0);
                                    v_isShared_4948_ = v_isSharedCheck_4968_;
                                    state = 37;
                                    continue;
                                }
                            } else {
                                v___x_4972_ = leanh::lean_unsigned_to_nat(2);
                                if v_isShared_4698_ == 0 {
                                    leanh::lean_ctor_set(v___x_4697_, 4, v_r_4943_);
                                    leanh::lean_ctor_set(v___x_4697_, 3, v_impl_4839_);
                                    leanh::lean_ctor_set(v___x_4697_, 0, v___x_4972_);
                                    v___x_4974_ = v___x_4697_;
                                    state = 42;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4975_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4975_,
                                        0,
                                        v___x_4972_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4975_,
                                        1,
                                        v_k_4692_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4975_,
                                        2,
                                        v_v_4693_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4975_,
                                        3,
                                        v_impl_4839_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4975_,
                                        4,
                                        v_r_4943_,
                                    );
                                    v___x_4974_ = v_reuseFailAlloc_4975_;
                                    state = 42;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_4715_;
            }
            3 => {
                v_size_4720_ = leanh::lean_ctor_get(v_l_4707_, 0);
                v_k_4721_ = leanh::lean_ctor_get(v_l_4707_, 1);
                v_v_4722_ = leanh::lean_ctor_get(v_l_4707_, 2);
                v_l_4723_ = leanh::lean_ctor_get(v_l_4707_, 3);
                v_r_4724_ = leanh::lean_ctor_get(v_l_4707_, 4);
                v_size_4725_ = leanh::lean_ctor_get(v_r_4708_, 0);
                v___x_4726_ = leanh::lean_unsigned_to_nat(2);
                v___x_4727_ = lean_nat_mul(v___x_4726_, v_size_4725_);
                v___x_4728_ = lean_nat_dec_lt(v_size_4720_, v___x_4727_);
                leanh::lean_dec(v___x_4727_);
                if v___x_4728_ == 0 {
                    leanh::lean_inc(v_r_4724_);
                    leanh::lean_inc(v_l_4723_);
                    leanh::lean_inc(v_v_4722_);
                    leanh::lean_inc(v_k_4721_);
                    v_isSharedCheck_4756_ = (!leanh::lean_is_exclusive(v_l_4707_)) as u8;
                    if v_isSharedCheck_4756_ == 0 {
                        v_unused_4757_ = leanh::lean_ctor_get(v_l_4707_, 4);
                        leanh::lean_dec(v_unused_4757_);
                        v_unused_4758_ = leanh::lean_ctor_get(v_l_4707_, 3);
                        leanh::lean_dec(v_unused_4758_);
                        v_unused_4759_ = leanh::lean_ctor_get(v_l_4707_, 2);
                        leanh::lean_dec(v_unused_4759_);
                        v_unused_4760_ = leanh::lean_ctor_get(v_l_4707_, 1);
                        leanh::lean_dec(v_unused_4760_);
                        v_unused_4761_ = leanh::lean_ctor_get(v_l_4707_, 0);
                        leanh::lean_dec(v_unused_4761_);
                        v___x_4730_ = v_l_4707_;
                        v_isShared_4731_ = v_isSharedCheck_4756_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_l_4707_);
                        v___x_4730_ = leanh::lean_box(0);
                        v_isShared_4731_ = v_isSharedCheck_4756_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4697_);
                    v___x_4762_ = lean_nat_add(v___x_4702_, v_size_4703_);
                    v___x_4763_ = lean_nat_add(v___x_4762_, v_size_4704_);
                    leanh::lean_dec(v_size_4704_);
                    v___x_4764_ = lean_nat_add(v___x_4762_, v_size_4720_);
                    leanh::lean_dec(v___x_4762_);
                    leanh::lean_inc_ref(v_l_4694_);
                    if v_isShared_4719_ == 0 {
                        leanh::lean_ctor_set(v___x_4718_, 4, v_l_4707_);
                        leanh::lean_ctor_set(v___x_4718_, 3, v_l_4694_);
                        leanh::lean_ctor_set(v___x_4718_, 2, v_v_4693_);
                        leanh::lean_ctor_set(v___x_4718_, 1, v_k_4692_);
                        leanh::lean_ctor_set(v___x_4718_, 0, v___x_4764_);
                        v___x_4766_ = v___x_4718_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4779_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4779_, 0, v___x_4764_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4779_, 1, v_k_4692_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4779_, 2, v_v_4693_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4779_, 3, v_l_4694_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4779_, 4, v_l_4707_);
                        v___x_4766_ = v_reuseFailAlloc_4779_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_4732_ = lean_nat_add(v___x_4702_, v_size_4703_);
                v___x_4733_ = lean_nat_add(v___x_4732_, v_size_4704_);
                leanh::lean_dec(v_size_4704_);
                if leanh::lean_obj_tag(v_l_4723_) == 0 {
                    v_size_4754_ = leanh::lean_ctor_get(v_l_4723_, 0);
                    leanh::lean_inc(v_size_4754_);
                    v___y_4746_ = v_size_4754_;
                    state = 8;
                    continue;
                } else {
                    v___x_4755_ = leanh::lean_unsigned_to_nat(0);
                    v___y_4746_ = v___x_4755_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_4738_ = lean_nat_add(v___y_4736_, v___y_4737_);
                leanh::lean_dec(v___y_4737_);
                leanh::lean_dec(v___y_4736_);
                if v_isShared_4731_ == 0 {
                    leanh::lean_ctor_set(v___x_4730_, 4, v_r_4708_);
                    leanh::lean_ctor_set(v___x_4730_, 3, v_r_4724_);
                    leanh::lean_ctor_set(v___x_4730_, 2, v_v_4706_);
                    leanh::lean_ctor_set(v___x_4730_, 1, v_k_4705_);
                    leanh::lean_ctor_set(v___x_4730_, 0, v___x_4738_);
                    v___x_4740_ = v___x_4730_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4744_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4744_, 0, v___x_4738_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4744_, 1, v_k_4705_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4744_, 2, v_v_4706_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4744_, 3, v_r_4724_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4744_, 4, v_r_4708_);
                    v___x_4740_ = v_reuseFailAlloc_4744_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4719_ == 0 {
                    leanh::lean_ctor_set(v___x_4718_, 4, v___x_4740_);
                    leanh::lean_ctor_set(v___x_4718_, 3, v___y_4735_);
                    leanh::lean_ctor_set(v___x_4718_, 2, v_v_4722_);
                    leanh::lean_ctor_set(v___x_4718_, 1, v_k_4721_);
                    leanh::lean_ctor_set(v___x_4718_, 0, v___x_4733_);
                    v___x_4742_ = v___x_4718_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4743_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4743_, 0, v___x_4733_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4743_, 1, v_k_4721_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4743_, 2, v_v_4722_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4743_, 3, v___y_4735_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4743_, 4, v___x_4740_);
                    v___x_4742_ = v_reuseFailAlloc_4743_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4742_;
            }
            8 => {
                v___x_4747_ = lean_nat_add(v___x_4732_, v___y_4746_);
                leanh::lean_dec(v___y_4746_);
                leanh::lean_dec(v___x_4732_);
                if v_isShared_4698_ == 0 {
                    leanh::lean_ctor_set(v___x_4697_, 4, v_l_4723_);
                    leanh::lean_ctor_set(v___x_4697_, 0, v___x_4747_);
                    v___x_4749_ = v___x_4697_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4753_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4753_, 0, v___x_4747_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4753_, 1, v_k_4692_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4753_, 2, v_v_4693_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4753_, 3, v_l_4694_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4753_, 4, v_l_4723_);
                    v___x_4749_ = v_reuseFailAlloc_4753_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_4750_ = lean_nat_add(v___x_4702_, v_size_4725_);
                if leanh::lean_obj_tag(v_r_4724_) == 0 {
                    v_size_4751_ = leanh::lean_ctor_get(v_r_4724_, 0);
                    leanh::lean_inc(v_size_4751_);
                    v___y_4735_ = v___x_4749_;
                    v___y_4736_ = v___x_4750_;
                    v___y_4737_ = v_size_4751_;
                    state = 5;
                    continue;
                } else {
                    v___x_4752_ = leanh::lean_unsigned_to_nat(0);
                    v___y_4735_ = v___x_4749_;
                    v___y_4736_ = v___x_4750_;
                    v___y_4737_ = v___x_4752_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_4773_ = (!leanh::lean_is_exclusive(v_l_4694_)) as u8;
                if v_isSharedCheck_4773_ == 0 {
                    v_unused_4774_ = leanh::lean_ctor_get(v_l_4694_, 4);
                    leanh::lean_dec(v_unused_4774_);
                    v_unused_4775_ = leanh::lean_ctor_get(v_l_4694_, 3);
                    leanh::lean_dec(v_unused_4775_);
                    v_unused_4776_ = leanh::lean_ctor_get(v_l_4694_, 2);
                    leanh::lean_dec(v_unused_4776_);
                    v_unused_4777_ = leanh::lean_ctor_get(v_l_4694_, 1);
                    leanh::lean_dec(v_unused_4777_);
                    v_unused_4778_ = leanh::lean_ctor_get(v_l_4694_, 0);
                    leanh::lean_dec(v_unused_4778_);
                    v___x_4768_ = v_l_4694_;
                    v_isShared_4769_ = v_isSharedCheck_4773_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_dec(v_l_4694_);
                    v___x_4768_ = leanh::lean_box(0);
                    v_isShared_4769_ = v_isSharedCheck_4773_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_4769_ == 0 {
                    leanh::lean_ctor_set(v___x_4768_, 4, v_r_4708_);
                    leanh::lean_ctor_set(v___x_4768_, 3, v___x_4766_);
                    leanh::lean_ctor_set(v___x_4768_, 2, v_v_4706_);
                    leanh::lean_ctor_set(v___x_4768_, 1, v_k_4705_);
                    leanh::lean_ctor_set(v___x_4768_, 0, v___x_4763_);
                    v___x_4771_ = v___x_4768_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4772_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4772_, 0, v___x_4763_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4772_, 1, v_k_4705_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4772_, 2, v_v_4706_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4772_, 3, v___x_4766_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4772_, 4, v_r_4708_);
                    v___x_4771_ = v_reuseFailAlloc_4772_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4771_;
            }
            13 => {
                v_k_4793_ = leanh::lean_ctor_get(v_l_4786_, 1);
                v_v_4794_ = leanh::lean_ctor_get(v_l_4786_, 2);
                v_isSharedCheck_4808_ = (!leanh::lean_is_exclusive(v_l_4786_)) as u8;
                if v_isSharedCheck_4808_ == 0 {
                    v_unused_4809_ = leanh::lean_ctor_get(v_l_4786_, 4);
                    leanh::lean_dec(v_unused_4809_);
                    v_unused_4810_ = leanh::lean_ctor_get(v_l_4786_, 3);
                    leanh::lean_dec(v_unused_4810_);
                    v_unused_4811_ = leanh::lean_ctor_get(v_l_4786_, 0);
                    leanh::lean_dec(v_unused_4811_);
                    v___x_4796_ = v_l_4786_;
                    v_isShared_4797_ = v_isSharedCheck_4808_;
                    state = 14;
                    continue;
                } else {
                    leanh::lean_inc(v_v_4794_);
                    leanh::lean_inc(v_k_4793_);
                    leanh::lean_dec(v_l_4786_);
                    v___x_4796_ = leanh::lean_box(0);
                    v_isShared_4797_ = v_isSharedCheck_4808_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_4798_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc_n(v_r_4787_, 2);
                if v_isShared_4797_ == 0 {
                    leanh::lean_ctor_set(v___x_4796_, 4, v_r_4787_);
                    leanh::lean_ctor_set(v___x_4796_, 3, v_r_4787_);
                    leanh::lean_ctor_set(v___x_4796_, 2, v_v_4693_);
                    leanh::lean_ctor_set(v___x_4796_, 1, v_k_4692_);
                    leanh::lean_ctor_set(v___x_4796_, 0, v___x_4702_);
                    v___x_4800_ = v___x_4796_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4807_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4807_, 0, v___x_4702_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4807_, 1, v_k_4692_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4807_, 2, v_v_4693_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4807_, 3, v_r_4787_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4807_, 4, v_r_4787_);
                    v___x_4800_ = v_reuseFailAlloc_4807_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                leanh::lean_inc(v_r_4787_);
                if v_isShared_4792_ == 0 {
                    leanh::lean_ctor_set(v___x_4791_, 3, v_r_4787_);
                    leanh::lean_ctor_set(v___x_4791_, 0, v___x_4702_);
                    v___x_4802_ = v___x_4791_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4806_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4806_, 0, v___x_4702_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4806_, 1, v_k_4788_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4806_, 2, v_v_4789_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4806_, 3, v_r_4787_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4806_, 4, v_r_4787_);
                    v___x_4802_ = v_reuseFailAlloc_4806_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_4698_ == 0 {
                    leanh::lean_ctor_set(v___x_4697_, 4, v___x_4802_);
                    leanh::lean_ctor_set(v___x_4697_, 3, v___x_4800_);
                    leanh::lean_ctor_set(v___x_4697_, 2, v_v_4794_);
                    leanh::lean_ctor_set(v___x_4697_, 1, v_k_4793_);
                    leanh::lean_ctor_set(v___x_4697_, 0, v___x_4798_);
                    v___x_4804_ = v___x_4697_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4805_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4805_, 0, v___x_4798_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4805_, 1, v_k_4793_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4805_, 2, v_v_4794_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4805_, 3, v___x_4800_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4805_, 4, v___x_4802_);
                    v___x_4804_ = v_reuseFailAlloc_4805_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4804_;
            }
            18 => {
                v___x_4821_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_4820_ == 0 {
                    leanh::lean_ctor_set(v___x_4819_, 4, v_l_4786_);
                    leanh::lean_ctor_set(v___x_4819_, 2, v_v_4693_);
                    leanh::lean_ctor_set(v___x_4819_, 1, v_k_4692_);
                    leanh::lean_ctor_set(v___x_4819_, 0, v___x_4702_);
                    v___x_4823_ = v___x_4819_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4827_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4827_, 0, v___x_4702_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4827_, 1, v_k_4692_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4827_, 2, v_v_4693_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4827_, 3, v_l_4786_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4827_, 4, v_l_4786_);
                    v___x_4823_ = v_reuseFailAlloc_4827_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_4698_ == 0 {
                    leanh::lean_ctor_set(v___x_4697_, 4, v_r_4815_);
                    leanh::lean_ctor_set(v___x_4697_, 3, v___x_4823_);
                    leanh::lean_ctor_set(v___x_4697_, 2, v_v_4817_);
                    leanh::lean_ctor_set(v___x_4697_, 1, v_k_4816_);
                    leanh::lean_ctor_set(v___x_4697_, 0, v___x_4821_);
                    v___x_4825_ = v___x_4697_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4826_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4826_, 0, v___x_4821_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4826_, 1, v_k_4816_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4826_, 2, v_v_4817_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4826_, 3, v___x_4823_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4826_, 4, v_r_4815_);
                    v___x_4825_ = v_reuseFailAlloc_4826_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4825_;
            }
            21 => {
                return v___x_4834_;
            }
            22 => {
                return v___x_4837_;
            }
            23 => {
                return v___x_4853_;
            }
            24 => {
                v_size_4858_ = leanh::lean_ctor_get(v_l_4845_, 0);
                v_size_4859_ = leanh::lean_ctor_get(v_r_4846_, 0);
                v_k_4860_ = leanh::lean_ctor_get(v_r_4846_, 1);
                v_v_4861_ = leanh::lean_ctor_get(v_r_4846_, 2);
                v_l_4862_ = leanh::lean_ctor_get(v_r_4846_, 3);
                v_r_4863_ = leanh::lean_ctor_get(v_r_4846_, 4);
                v___x_4864_ = leanh::lean_unsigned_to_nat(2);
                v___x_4865_ = lean_nat_mul(v___x_4864_, v_size_4858_);
                v___x_4866_ = lean_nat_dec_lt(v_size_4859_, v___x_4865_);
                leanh::lean_dec(v___x_4865_);
                if v___x_4866_ == 0 {
                    leanh::lean_inc(v_r_4863_);
                    leanh::lean_inc(v_l_4862_);
                    leanh::lean_inc(v_v_4861_);
                    leanh::lean_inc(v_k_4860_);
                    v_isSharedCheck_4895_ = (!leanh::lean_is_exclusive(v_r_4846_)) as u8;
                    if v_isSharedCheck_4895_ == 0 {
                        v_unused_4896_ = leanh::lean_ctor_get(v_r_4846_, 4);
                        leanh::lean_dec(v_unused_4896_);
                        v_unused_4897_ = leanh::lean_ctor_get(v_r_4846_, 3);
                        leanh::lean_dec(v_unused_4897_);
                        v_unused_4898_ = leanh::lean_ctor_get(v_r_4846_, 2);
                        leanh::lean_dec(v_unused_4898_);
                        v_unused_4899_ = leanh::lean_ctor_get(v_r_4846_, 1);
                        leanh::lean_dec(v_unused_4899_);
                        v_unused_4900_ = leanh::lean_ctor_get(v_r_4846_, 0);
                        leanh::lean_dec(v_unused_4900_);
                        v___x_4868_ = v_r_4846_;
                        v_isShared_4869_ = v_isSharedCheck_4895_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_4846_);
                        v___x_4868_ = leanh::lean_box(0);
                        v_isShared_4869_ = v_isSharedCheck_4895_;
                        state = 25;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4697_);
                    v___x_4901_ = lean_nat_add(v___x_4840_, v_size_4842_);
                    leanh::lean_dec(v_size_4842_);
                    v___x_4902_ = lean_nat_add(v___x_4901_, v_size_4841_);
                    leanh::lean_dec(v___x_4901_);
                    v___x_4903_ = lean_nat_add(v___x_4840_, v_size_4841_);
                    v___x_4904_ = lean_nat_add(v___x_4903_, v_size_4859_);
                    leanh::lean_dec(v___x_4903_);
                    leanh::lean_inc_ref(v_r_4695_);
                    if v_isShared_4857_ == 0 {
                        leanh::lean_ctor_set(v___x_4856_, 4, v_r_4695_);
                        leanh::lean_ctor_set(v___x_4856_, 3, v_r_4846_);
                        leanh::lean_ctor_set(v___x_4856_, 2, v_v_4693_);
                        leanh::lean_ctor_set(v___x_4856_, 1, v_k_4692_);
                        leanh::lean_ctor_set(v___x_4856_, 0, v___x_4904_);
                        v___x_4906_ = v___x_4856_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_4919_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4919_, 0, v___x_4904_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4919_, 1, v_k_4692_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4919_, 2, v_v_4693_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4919_, 3, v_r_4846_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4919_, 4, v_r_4695_);
                        v___x_4906_ = v_reuseFailAlloc_4919_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_4870_ = lean_nat_add(v___x_4840_, v_size_4842_);
                leanh::lean_dec(v_size_4842_);
                v___x_4871_ = lean_nat_add(v___x_4870_, v_size_4841_);
                leanh::lean_dec(v___x_4870_);
                v___x_4883_ = lean_nat_add(v___x_4840_, v_size_4858_);
                if leanh::lean_obj_tag(v_l_4862_) == 0 {
                    v_size_4893_ = leanh::lean_ctor_get(v_l_4862_, 0);
                    leanh::lean_inc(v_size_4893_);
                    v___y_4885_ = v_size_4893_;
                    state = 29;
                    continue;
                } else {
                    v___x_4894_ = leanh::lean_unsigned_to_nat(0);
                    v___y_4885_ = v___x_4894_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_4876_ = lean_nat_add(v___y_4874_, v___y_4875_);
                leanh::lean_dec(v___y_4875_);
                leanh::lean_dec(v___y_4874_);
                if v_isShared_4869_ == 0 {
                    leanh::lean_ctor_set(v___x_4868_, 4, v_r_4695_);
                    leanh::lean_ctor_set(v___x_4868_, 3, v_r_4863_);
                    leanh::lean_ctor_set(v___x_4868_, 2, v_v_4693_);
                    leanh::lean_ctor_set(v___x_4868_, 1, v_k_4692_);
                    leanh::lean_ctor_set(v___x_4868_, 0, v___x_4876_);
                    v___x_4878_ = v___x_4868_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_4882_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4882_, 0, v___x_4876_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4882_, 1, v_k_4692_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4882_, 2, v_v_4693_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4882_, 3, v_r_4863_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4882_, 4, v_r_4695_);
                    v___x_4878_ = v_reuseFailAlloc_4882_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_4857_ == 0 {
                    leanh::lean_ctor_set(v___x_4856_, 4, v___x_4878_);
                    leanh::lean_ctor_set(v___x_4856_, 3, v___y_4873_);
                    leanh::lean_ctor_set(v___x_4856_, 2, v_v_4861_);
                    leanh::lean_ctor_set(v___x_4856_, 1, v_k_4860_);
                    leanh::lean_ctor_set(v___x_4856_, 0, v___x_4871_);
                    v___x_4880_ = v___x_4856_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4881_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4881_, 0, v___x_4871_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4881_, 1, v_k_4860_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4881_, 2, v_v_4861_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4881_, 3, v___y_4873_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4881_, 4, v___x_4878_);
                    v___x_4880_ = v_reuseFailAlloc_4881_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_4880_;
            }
            29 => {
                v___x_4886_ = lean_nat_add(v___x_4883_, v___y_4885_);
                leanh::lean_dec(v___y_4885_);
                leanh::lean_dec(v___x_4883_);
                if v_isShared_4698_ == 0 {
                    leanh::lean_ctor_set(v___x_4697_, 4, v_l_4862_);
                    leanh::lean_ctor_set(v___x_4697_, 3, v_l_4845_);
                    leanh::lean_ctor_set(v___x_4697_, 2, v_v_4844_);
                    leanh::lean_ctor_set(v___x_4697_, 1, v_k_4843_);
                    leanh::lean_ctor_set(v___x_4697_, 0, v___x_4886_);
                    v___x_4888_ = v___x_4697_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_4892_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4892_, 0, v___x_4886_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4892_, 1, v_k_4843_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4892_, 2, v_v_4844_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4892_, 3, v_l_4845_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4892_, 4, v_l_4862_);
                    v___x_4888_ = v_reuseFailAlloc_4892_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_4889_ = lean_nat_add(v___x_4840_, v_size_4841_);
                if leanh::lean_obj_tag(v_r_4863_) == 0 {
                    v_size_4890_ = leanh::lean_ctor_get(v_r_4863_, 0);
                    leanh::lean_inc(v_size_4890_);
                    v___y_4873_ = v___x_4888_;
                    v___y_4874_ = v___x_4889_;
                    v___y_4875_ = v_size_4890_;
                    state = 26;
                    continue;
                } else {
                    v___x_4891_ = leanh::lean_unsigned_to_nat(0);
                    v___y_4873_ = v___x_4888_;
                    v___y_4874_ = v___x_4889_;
                    v___y_4875_ = v___x_4891_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_4913_ = (!leanh::lean_is_exclusive(v_r_4695_)) as u8;
                if v_isSharedCheck_4913_ == 0 {
                    v_unused_4914_ = leanh::lean_ctor_get(v_r_4695_, 4);
                    leanh::lean_dec(v_unused_4914_);
                    v_unused_4915_ = leanh::lean_ctor_get(v_r_4695_, 3);
                    leanh::lean_dec(v_unused_4915_);
                    v_unused_4916_ = leanh::lean_ctor_get(v_r_4695_, 2);
                    leanh::lean_dec(v_unused_4916_);
                    v_unused_4917_ = leanh::lean_ctor_get(v_r_4695_, 1);
                    leanh::lean_dec(v_unused_4917_);
                    v_unused_4918_ = leanh::lean_ctor_get(v_r_4695_, 0);
                    leanh::lean_dec(v_unused_4918_);
                    v___x_4908_ = v_r_4695_;
                    v_isShared_4909_ = v_isSharedCheck_4913_;
                    state = 32;
                    continue;
                } else {
                    leanh::lean_dec(v_r_4695_);
                    v___x_4908_ = leanh::lean_box(0);
                    v_isShared_4909_ = v_isSharedCheck_4913_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_4909_ == 0 {
                    leanh::lean_ctor_set(v___x_4908_, 4, v___x_4906_);
                    leanh::lean_ctor_set(v___x_4908_, 3, v_l_4845_);
                    leanh::lean_ctor_set(v___x_4908_, 2, v_v_4844_);
                    leanh::lean_ctor_set(v___x_4908_, 1, v_k_4843_);
                    leanh::lean_ctor_set(v___x_4908_, 0, v___x_4902_);
                    v___x_4911_ = v___x_4908_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_4912_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4912_, 0, v___x_4902_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4912_, 1, v_k_4843_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4912_, 2, v_v_4844_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4912_, 3, v_l_4845_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4912_, 4, v___x_4906_);
                    v___x_4911_ = v_reuseFailAlloc_4912_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_4911_;
            }
            34 => {
                v___x_4933_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc(v_r_4927_);
                if v_isShared_4932_ == 0 {
                    leanh::lean_ctor_set(v___x_4931_, 3, v_r_4927_);
                    leanh::lean_ctor_set(v___x_4931_, 2, v_v_4693_);
                    leanh::lean_ctor_set(v___x_4931_, 1, v_k_4692_);
                    leanh::lean_ctor_set(v___x_4931_, 0, v___x_4840_);
                    v___x_4935_ = v___x_4931_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_4939_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4939_, 0, v___x_4840_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4939_, 1, v_k_4692_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4939_, 2, v_v_4693_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4939_, 3, v_r_4927_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4939_, 4, v_r_4927_);
                    v___x_4935_ = v_reuseFailAlloc_4939_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_4698_ == 0 {
                    leanh::lean_ctor_set(v___x_4697_, 4, v___x_4935_);
                    leanh::lean_ctor_set(v___x_4697_, 3, v_l_4926_);
                    leanh::lean_ctor_set(v___x_4697_, 2, v_v_4929_);
                    leanh::lean_ctor_set(v___x_4697_, 1, v_k_4928_);
                    leanh::lean_ctor_set(v___x_4697_, 0, v___x_4933_);
                    v___x_4937_ = v___x_4697_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_4938_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4938_, 0, v___x_4933_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4938_, 1, v_k_4928_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4938_, 2, v_v_4929_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4938_, 3, v_l_4926_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4938_, 4, v___x_4935_);
                    v___x_4937_ = v_reuseFailAlloc_4938_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_4937_;
            }
            37 => {
                v_k_4949_ = leanh::lean_ctor_get(v_r_4943_, 1);
                v_v_4950_ = leanh::lean_ctor_get(v_r_4943_, 2);
                v_isSharedCheck_4964_ = (!leanh::lean_is_exclusive(v_r_4943_)) as u8;
                if v_isSharedCheck_4964_ == 0 {
                    v_unused_4965_ = leanh::lean_ctor_get(v_r_4943_, 4);
                    leanh::lean_dec(v_unused_4965_);
                    v_unused_4966_ = leanh::lean_ctor_get(v_r_4943_, 3);
                    leanh::lean_dec(v_unused_4966_);
                    v_unused_4967_ = leanh::lean_ctor_get(v_r_4943_, 0);
                    leanh::lean_dec(v_unused_4967_);
                    v___x_4952_ = v_r_4943_;
                    v_isShared_4953_ = v_isSharedCheck_4964_;
                    state = 38;
                    continue;
                } else {
                    leanh::lean_inc(v_v_4950_);
                    leanh::lean_inc(v_k_4949_);
                    leanh::lean_dec(v_r_4943_);
                    v___x_4952_ = leanh::lean_box(0);
                    v_isShared_4953_ = v_isSharedCheck_4964_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_4954_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_4953_ == 0 {
                    leanh::lean_ctor_set(v___x_4952_, 4, v_l_4926_);
                    leanh::lean_ctor_set(v___x_4952_, 3, v_l_4926_);
                    leanh::lean_ctor_set(v___x_4952_, 2, v_v_4945_);
                    leanh::lean_ctor_set(v___x_4952_, 1, v_k_4944_);
                    leanh::lean_ctor_set(v___x_4952_, 0, v___x_4840_);
                    v___x_4956_ = v___x_4952_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_4963_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4963_, 0, v___x_4840_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4963_, 1, v_k_4944_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4963_, 2, v_v_4945_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4963_, 3, v_l_4926_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4963_, 4, v_l_4926_);
                    v___x_4956_ = v_reuseFailAlloc_4963_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                if v_isShared_4948_ == 0 {
                    leanh::lean_ctor_set(v___x_4947_, 4, v_l_4926_);
                    leanh::lean_ctor_set(v___x_4947_, 2, v_v_4693_);
                    leanh::lean_ctor_set(v___x_4947_, 1, v_k_4692_);
                    leanh::lean_ctor_set(v___x_4947_, 0, v___x_4840_);
                    v___x_4958_ = v___x_4947_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_4962_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4962_, 0, v___x_4840_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4962_, 1, v_k_4692_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4962_, 2, v_v_4693_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4962_, 3, v_l_4926_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4962_, 4, v_l_4926_);
                    v___x_4958_ = v_reuseFailAlloc_4962_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_4698_ == 0 {
                    leanh::lean_ctor_set(v___x_4697_, 4, v___x_4958_);
                    leanh::lean_ctor_set(v___x_4697_, 3, v___x_4956_);
                    leanh::lean_ctor_set(v___x_4697_, 2, v_v_4950_);
                    leanh::lean_ctor_set(v___x_4697_, 1, v_k_4949_);
                    leanh::lean_ctor_set(v___x_4697_, 0, v___x_4954_);
                    v___x_4960_ = v___x_4697_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_4961_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4961_, 0, v___x_4954_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4961_, 1, v_k_4949_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4961_, 2, v_v_4950_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4961_, 3, v___x_4956_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4961_, 4, v___x_4958_);
                    v___x_4960_ = v_reuseFailAlloc_4961_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_4960_;
            }
            42 => {
                return v___x_4974_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(
    mut v_y_4979_: *mut leanh::LeanObject,
    mut v_x_4980_: *mut leanh::LeanObject,
    mut v_x_4981_: usize,
    mut v_x_4982_: usize,
) -> *mut leanh::LeanObject {
    let mut v_cs_4983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_4984_: usize = 0;
    let mut v___x_4985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: u8 = 0;
    let mut v___x_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4990_: u8 = 0;
    let mut v___x_4991_: usize = 0;
    let mut v___x_4992_: usize = 0;
    let mut v___x_4993_: usize = 0;
    let mut v_i_4994_: usize = 0;
    let mut v___x_4995_: usize = 0;
    let mut v_shift_4996_: usize = 0;
    let mut v_v_4997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5005_: u8 = 0;
    let mut v_unused_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: u8 = 0;
    let mut v___x_5012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5013_: u8 = 0;
    let mut v_v_5014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: u8 = 0;
    let mut v___x_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5025_: u8 = 0;
    let mut v_unused_5026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4980_) == 0 {
                    v_cs_4983_ = leanh::lean_ctor_get(v_x_4980_, 0);
                    v_j_4984_ = lean_usize_shift_right(v_x_4981_, v_x_4982_);
                    v___x_4985_ = lean_usize_to_nat(v_j_4984_);
                    v___x_4986_ = lean_array_get_size(v_cs_4983_);
                    v___x_4987_ = lean_nat_dec_lt(v___x_4985_, v___x_4986_);
                    if v___x_4987_ == 0 {
                        leanh::lean_dec(v___x_4985_);
                        leanh::lean_dec(v_y_4979_);
                        return v_x_4980_;
                    } else {
                        leanh::lean_inc_ref(v_cs_4983_);
                        v_isSharedCheck_5005_ = (!leanh::lean_is_exclusive(v_x_4980_)) as u8;
                        if v_isSharedCheck_5005_ == 0 {
                            v_unused_5006_ = leanh::lean_ctor_get(v_x_4980_, 0);
                            leanh::lean_dec(v_unused_5006_);
                            v___x_4989_ = v_x_4980_;
                            v_isShared_4990_ = v_isSharedCheck_5005_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_4980_);
                            v___x_4989_ = leanh::lean_box(0);
                            v_isShared_4990_ = v_isSharedCheck_5005_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_vs_5007_ = leanh::lean_ctor_get(v_x_4980_, 0);
                    v___x_5008_ = lean_usize_to_nat(v_x_4981_);
                    v___x_5009_ = lean_array_get_size(v_vs_5007_);
                    v___x_5010_ = lean_nat_dec_lt(v___x_5008_, v___x_5009_);
                    if v___x_5010_ == 0 {
                        leanh::lean_dec(v___x_5008_);
                        leanh::lean_dec(v_y_4979_);
                        return v_x_4980_;
                    } else {
                        leanh::lean_inc_ref(v_vs_5007_);
                        v_isSharedCheck_5025_ = (!leanh::lean_is_exclusive(v_x_4980_)) as u8;
                        if v_isSharedCheck_5025_ == 0 {
                            v_unused_5026_ = leanh::lean_ctor_get(v_x_4980_, 0);
                            leanh::lean_dec(v_unused_5026_);
                            v___x_5012_ = v_x_4980_;
                            v_isShared_5013_ = v_isSharedCheck_5025_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_4980_);
                            v___x_5012_ = leanh::lean_box(0);
                            v_isShared_5013_ = v_isSharedCheck_5025_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4991_ = 1usize;
                v___x_4992_ = lean_usize_shift_left(v___x_4991_, v_x_4982_);
                v___x_4993_ = lean_usize_sub(v___x_4992_, v___x_4991_);
                v_i_4994_ = lean_usize_land(v_x_4981_, v___x_4993_);
                v___x_4995_ = 5usize;
                v_shift_4996_ = lean_usize_sub(v_x_4982_, v___x_4995_);
                v_v_4997_ = lean_array_fget(v_cs_4983_, v___x_4985_);
                v___x_4998_ = leanh::lean_box(0);
                v_xs_x27_4999_ = lean_array_fset(v_cs_4983_, v___x_4985_, v___x_4998_);
                v___x_5000_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(v_y_4979_, v_v_4997_, v_i_4994_, v_shift_4996_);
                v___x_5001_ = lean_array_fset(v_xs_x27_4999_, v___x_4985_, v___x_5000_);
                leanh::lean_dec(v___x_4985_);
                if v_isShared_4990_ == 0 {
                    leanh::lean_ctor_set(v___x_4989_, 0, v___x_5001_);
                    v___x_5003_ = v___x_4989_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5004_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5004_, 0, v___x_5001_);
                    v___x_5003_ = v_reuseFailAlloc_5004_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5003_;
            }
            3 => {
                v_v_5014_ = lean_array_fget(v_vs_5007_, v___x_5008_);
                v___x_5015_ = leanh::lean_box(0);
                v_xs_x27_5016_ = lean_array_fset(v_vs_5007_, v___x_5008_, v___x_5015_);
                v___x_5023_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_4979_, v_v_5014_);
                if v___x_5023_ == 0 {
                    v___x_5024_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_y_4979_, v___x_5015_, v_v_5014_);
                    v___y_5018_ = v___x_5024_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_dec(v_y_4979_);
                    v___y_5018_ = v_v_5014_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5019_ = lean_array_fset(v_xs_x27_5016_, v___x_5008_, v___y_5018_);
                leanh::lean_dec(v___x_5008_);
                if v_isShared_5013_ == 0 {
                    leanh::lean_ctor_set(v___x_5012_, 0, v___x_5019_);
                    v___x_5021_ = v___x_5012_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5022_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5022_, 0, v___x_5019_);
                    v___x_5021_ = v_reuseFailAlloc_5022_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5021_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___boxed(
    mut v_y_5027_: *mut leanh::LeanObject,
    mut v_x_5028_: *mut leanh::LeanObject,
    mut v_x_5029_: *mut leanh::LeanObject,
    mut v_x_5030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_6038__boxed_5031_: usize = 0;
    let mut v_x_6039__boxed_5032_: usize = 0;
    let mut v_res_5033_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_6038__boxed_5031_ = leanh::lean_unbox_usize(v_x_5029_);
    leanh::lean_dec(v_x_5029_);
    v_x_6039__boxed_5032_ = leanh::lean_unbox_usize(v_x_5030_);
    leanh::lean_dec(v_x_5030_);
    v_res_5033_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(v_y_5027_, v_x_5028_, v_x_6038__boxed_5031_, v_x_6039__boxed_5032_);
    return v_res_5033_;
}
pub unsafe fn l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(
    mut v_y_5034_: *mut leanh::LeanObject,
    mut v_t_5035_: *mut leanh::LeanObject,
    mut v_i_5036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_5037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shift_5040_: usize = 0;
    let mut v_tailOff_5041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5044_: u8 = 0;
    let mut v___x_5045_: u8 = 0;
    let mut v___x_5046_: usize = 0;
    let mut v___x_5047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: u8 = 0;
    let mut v___x_5055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: u8 = 0;
    let mut v___x_5067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_5037_ = leanh::lean_ctor_get(v_t_5035_, 0);
                v_tail_5038_ = leanh::lean_ctor_get(v_t_5035_, 1);
                v_size_5039_ = leanh::lean_ctor_get(v_t_5035_, 2);
                v_shift_5040_ = leanh::lean_ctor_get_usize(v_t_5035_, 4);
                v_tailOff_5041_ = leanh::lean_ctor_get(v_t_5035_, 3);
                v_isSharedCheck_5068_ = (!leanh::lean_is_exclusive(v_t_5035_)) as u8;
                if v_isSharedCheck_5068_ == 0 {
                    v___x_5043_ = v_t_5035_;
                    v_isShared_5044_ = v_isSharedCheck_5068_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_tailOff_5041_);
                    leanh::lean_inc(v_size_5039_);
                    leanh::lean_inc(v_tail_5038_);
                    leanh::lean_inc(v_root_5037_);
                    leanh::lean_dec(v_t_5035_);
                    v___x_5043_ = leanh::lean_box(0);
                    v_isShared_5044_ = v_isSharedCheck_5068_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5045_ = lean_nat_dec_le(v_tailOff_5041_, v_i_5036_);
                if v___x_5045_ == 0 {
                    v___x_5046_ = lean_usize_of_nat(v_i_5036_);
                    v___x_5047_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(v_y_5034_, v_root_5037_, v___x_5046_, v_shift_5040_);
                    if v_isShared_5044_ == 0 {
                        leanh::lean_ctor_set(v___x_5043_, 0, v___x_5047_);
                        v___x_5049_ = v___x_5043_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5050_ = leanh::lean_alloc_ctor(
                            0,
                            4,
                            (core::mem::size_of::<usize>() * 1) as u32,
                        );
                        leanh::lean_ctor_set(v_reuseFailAlloc_5050_, 0, v___x_5047_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5050_, 1, v_tail_5038_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5050_, 2, v_size_5039_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5050_, 3, v_tailOff_5041_);
                        leanh::lean_ctor_set_usize(v_reuseFailAlloc_5050_, 4, v_shift_5040_);
                        v___x_5049_ = v_reuseFailAlloc_5050_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5051_ = lean_nat_sub(v_i_5036_, v_tailOff_5041_);
                    v___x_5052_ = lean_array_get_size(v_tail_5038_);
                    v___x_5053_ = lean_nat_dec_lt(v___x_5051_, v___x_5052_);
                    if v___x_5053_ == 0 {
                        leanh::lean_dec(v___x_5051_);
                        leanh::lean_dec(v_y_5034_);
                        if v_isShared_5044_ == 0 {
                            v___x_5055_ = v___x_5043_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5056_ = leanh::lean_alloc_ctor(
                                0,
                                4,
                                (core::mem::size_of::<usize>() * 1) as u32,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_5056_, 0, v_root_5037_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5056_, 1, v_tail_5038_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5056_, 2, v_size_5039_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5056_, 3, v_tailOff_5041_);
                            leanh::lean_ctor_set_usize(
                                v_reuseFailAlloc_5056_,
                                4,
                                v_shift_5040_,
                            );
                            v___x_5055_ = v_reuseFailAlloc_5056_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_v_5057_ = lean_array_fget(v_tail_5038_, v___x_5051_);
                        v___x_5058_ = leanh::lean_box(0);
                        v_xs_x27_5059_ = lean_array_fset(v_tail_5038_, v___x_5051_, v___x_5058_);
                        v___x_5066_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_5034_, v_v_5057_);
                        if v___x_5066_ == 0 {
                            v___x_5067_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_y_5034_, v___x_5058_, v_v_5057_);
                            v___y_5061_ = v___x_5067_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_dec(v_y_5034_);
                            v___y_5061_ = v_v_5057_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5049_;
            }
            3 => {
                return v___x_5055_;
            }
            4 => {
                v___x_5062_ = lean_array_fset(v_xs_x27_5059_, v___x_5051_, v___y_5061_);
                leanh::lean_dec(v___x_5051_);
                if v_isShared_5044_ == 0 {
                    leanh::lean_ctor_set(v___x_5043_, 1, v___x_5062_);
                    v___x_5064_ = v___x_5043_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5065_ = leanh::lean_alloc_ctor(
                        0,
                        4,
                        (core::mem::size_of::<usize>() * 1) as u32,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5065_, 0, v_root_5037_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5065_, 1, v___x_5062_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5065_, 2, v_size_5039_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5065_, 3, v_tailOff_5041_);
                    leanh::lean_ctor_set_usize(v_reuseFailAlloc_5065_, 4, v_shift_5040_);
                    v___x_5064_ = v_reuseFailAlloc_5065_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5064_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2___boxed(
    mut v_y_5069_: *mut leanh::LeanObject,
    mut v_t_5070_: *mut leanh::LeanObject,
    mut v_i_5071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5072_ =
        l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(
            v_y_5069_, v_t_5070_, v_i_5071_,
        );
    leanh::lean_dec(v_i_5071_);
    return v_res_5072_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0(
    mut v_a_5073_: *mut leanh::LeanObject,
    mut v_y_5074_: *mut leanh::LeanObject,
    mut v_x_5075_: *mut leanh::LeanObject,
    mut v_s_5076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_structs_5077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_5078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToStructId_5079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToStructIdEntries_5080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_forbiddenNatModules_5081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natStructs_5082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natTypeIdOf_5083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNatStructId_5084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: u8 = 0;
    let mut v___x_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5089_: u8 = 0;
    let mut v_v_5090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_5091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringId_x3f_5092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intModuleInst_5095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leInst_x3f_5096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltInst_x3f_5097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lawfulOrderLTInst_x3f_5098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isPreorderInst_x3f_5099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_orderedAddInst_x3f_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isLinearInst_x3f_5101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noNatDivInst_x3f_5102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_x3f_5103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_x3f_5104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_orderedRingInst_x3f_5105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_5107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ofNatZero_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leFn_x3f_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltFn_x3f_5112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_5113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zsmulFn_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nsmulFn_5115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zsmulFn_x3f_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nsmulFn_x3f_5117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_homomulFn_x3f_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_5119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_5120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_5122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lowers_5123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uppers_5124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_5125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignment_5126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_caseSplits_5127_: u8 = 0;
    let mut v_conflict_x3f_5128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqSplits_5129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_elimEqs_5130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_elimStack_5131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_occurs_5132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ignored_5133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5136_: u8 = 0;
    let mut v___x_5137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5147_: u8 = 0;
    let mut v_isSharedCheck_5148_: u8 = 0;
    let mut v_unused_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_5077_ = leanh::lean_ctor_get(v_s_5076_, 0);
                v_typeIdOf_5078_ = leanh::lean_ctor_get(v_s_5076_, 1);
                v_exprToStructId_5079_ = leanh::lean_ctor_get(v_s_5076_, 2);
                v_exprToStructIdEntries_5080_ = leanh::lean_ctor_get(v_s_5076_, 3);
                v_forbiddenNatModules_5081_ = leanh::lean_ctor_get(v_s_5076_, 4);
                v_natStructs_5082_ = leanh::lean_ctor_get(v_s_5076_, 5);
                v_natTypeIdOf_5083_ = leanh::lean_ctor_get(v_s_5076_, 6);
                v_exprToNatStructId_5084_ = leanh::lean_ctor_get(v_s_5076_, 7);
                v___x_5085_ = lean_array_get_size(v_structs_5077_);
                v___x_5086_ = lean_nat_dec_lt(v_a_5073_, v___x_5085_);
                if v___x_5086_ == 0 {
                    leanh::lean_dec(v_y_5074_);
                    return v_s_5076_;
                } else {
                    leanh::lean_inc_ref(v_exprToNatStructId_5084_);
                    leanh::lean_inc_ref(v_natTypeIdOf_5083_);
                    leanh::lean_inc_ref(v_natStructs_5082_);
                    leanh::lean_inc_ref(v_forbiddenNatModules_5081_);
                    leanh::lean_inc_ref(v_exprToStructIdEntries_5080_);
                    leanh::lean_inc_ref(v_exprToStructId_5079_);
                    leanh::lean_inc_ref(v_typeIdOf_5078_);
                    leanh::lean_inc_ref(v_structs_5077_);
                    v_isSharedCheck_5148_ = (!leanh::lean_is_exclusive(v_s_5076_)) as u8;
                    if v_isSharedCheck_5148_ == 0 {
                        v_unused_5149_ = leanh::lean_ctor_get(v_s_5076_, 7);
                        leanh::lean_dec(v_unused_5149_);
                        v_unused_5150_ = leanh::lean_ctor_get(v_s_5076_, 6);
                        leanh::lean_dec(v_unused_5150_);
                        v_unused_5151_ = leanh::lean_ctor_get(v_s_5076_, 5);
                        leanh::lean_dec(v_unused_5151_);
                        v_unused_5152_ = leanh::lean_ctor_get(v_s_5076_, 4);
                        leanh::lean_dec(v_unused_5152_);
                        v_unused_5153_ = leanh::lean_ctor_get(v_s_5076_, 3);
                        leanh::lean_dec(v_unused_5153_);
                        v_unused_5154_ = leanh::lean_ctor_get(v_s_5076_, 2);
                        leanh::lean_dec(v_unused_5154_);
                        v_unused_5155_ = leanh::lean_ctor_get(v_s_5076_, 1);
                        leanh::lean_dec(v_unused_5155_);
                        v_unused_5156_ = leanh::lean_ctor_get(v_s_5076_, 0);
                        leanh::lean_dec(v_unused_5156_);
                        v___x_5088_ = v_s_5076_;
                        v_isShared_5089_ = v_isSharedCheck_5148_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_s_5076_);
                        v___x_5088_ = leanh::lean_box(0);
                        v_isShared_5089_ = v_isSharedCheck_5148_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_5090_ = lean_array_fget(v_structs_5077_, v_a_5073_);
                v_id_5091_ = leanh::lean_ctor_get(v_v_5090_, 0);
                v_ringId_x3f_5092_ = leanh::lean_ctor_get(v_v_5090_, 1);
                v_type_5093_ = leanh::lean_ctor_get(v_v_5090_, 2);
                v_u_5094_ = leanh::lean_ctor_get(v_v_5090_, 3);
                v_intModuleInst_5095_ = leanh::lean_ctor_get(v_v_5090_, 4);
                v_leInst_x3f_5096_ = leanh::lean_ctor_get(v_v_5090_, 5);
                v_ltInst_x3f_5097_ = leanh::lean_ctor_get(v_v_5090_, 6);
                v_lawfulOrderLTInst_x3f_5098_ = leanh::lean_ctor_get(v_v_5090_, 7);
                v_isPreorderInst_x3f_5099_ = leanh::lean_ctor_get(v_v_5090_, 8);
                v_orderedAddInst_x3f_5100_ = leanh::lean_ctor_get(v_v_5090_, 9);
                v_isLinearInst_x3f_5101_ = leanh::lean_ctor_get(v_v_5090_, 10);
                v_noNatDivInst_x3f_5102_ = leanh::lean_ctor_get(v_v_5090_, 11);
                v_ringInst_x3f_5103_ = leanh::lean_ctor_get(v_v_5090_, 12);
                v_commRingInst_x3f_5104_ = leanh::lean_ctor_get(v_v_5090_, 13);
                v_orderedRingInst_x3f_5105_ = leanh::lean_ctor_get(v_v_5090_, 14);
                v_fieldInst_x3f_5106_ = leanh::lean_ctor_get(v_v_5090_, 15);
                v_charInst_x3f_5107_ = leanh::lean_ctor_get(v_v_5090_, 16);
                v_zero_5108_ = leanh::lean_ctor_get(v_v_5090_, 17);
                v_ofNatZero_5109_ = leanh::lean_ctor_get(v_v_5090_, 18);
                v_one_x3f_5110_ = leanh::lean_ctor_get(v_v_5090_, 19);
                v_leFn_x3f_5111_ = leanh::lean_ctor_get(v_v_5090_, 20);
                v_ltFn_x3f_5112_ = leanh::lean_ctor_get(v_v_5090_, 21);
                v_addFn_5113_ = leanh::lean_ctor_get(v_v_5090_, 22);
                v_zsmulFn_5114_ = leanh::lean_ctor_get(v_v_5090_, 23);
                v_nsmulFn_5115_ = leanh::lean_ctor_get(v_v_5090_, 24);
                v_zsmulFn_x3f_5116_ = leanh::lean_ctor_get(v_v_5090_, 25);
                v_nsmulFn_x3f_5117_ = leanh::lean_ctor_get(v_v_5090_, 26);
                v_homomulFn_x3f_5118_ = leanh::lean_ctor_get(v_v_5090_, 27);
                v_subFn_5119_ = leanh::lean_ctor_get(v_v_5090_, 28);
                v_negFn_5120_ = leanh::lean_ctor_get(v_v_5090_, 29);
                v_vars_5121_ = leanh::lean_ctor_get(v_v_5090_, 30);
                v_varMap_5122_ = leanh::lean_ctor_get(v_v_5090_, 31);
                v_lowers_5123_ = leanh::lean_ctor_get(v_v_5090_, 32);
                v_uppers_5124_ = leanh::lean_ctor_get(v_v_5090_, 33);
                v_diseqs_5125_ = leanh::lean_ctor_get(v_v_5090_, 34);
                v_assignment_5126_ = leanh::lean_ctor_get(v_v_5090_, 35);
                v_caseSplits_5127_ = leanh::lean_ctor_get_uint8(
                    v_v_5090_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 42) as u32,
                );
                v_conflict_x3f_5128_ = leanh::lean_ctor_get(v_v_5090_, 36);
                v_diseqSplits_5129_ = leanh::lean_ctor_get(v_v_5090_, 37);
                v_elimEqs_5130_ = leanh::lean_ctor_get(v_v_5090_, 38);
                v_elimStack_5131_ = leanh::lean_ctor_get(v_v_5090_, 39);
                v_occurs_5132_ = leanh::lean_ctor_get(v_v_5090_, 40);
                v_ignored_5133_ = leanh::lean_ctor_get(v_v_5090_, 41);
                v_isSharedCheck_5147_ = (!leanh::lean_is_exclusive(v_v_5090_)) as u8;
                if v_isSharedCheck_5147_ == 0 {
                    v___x_5135_ = v_v_5090_;
                    v_isShared_5136_ = v_isSharedCheck_5147_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_ignored_5133_);
                    leanh::lean_inc(v_occurs_5132_);
                    leanh::lean_inc(v_elimStack_5131_);
                    leanh::lean_inc(v_elimEqs_5130_);
                    leanh::lean_inc(v_diseqSplits_5129_);
                    leanh::lean_inc(v_conflict_x3f_5128_);
                    leanh::lean_inc(v_assignment_5126_);
                    leanh::lean_inc(v_diseqs_5125_);
                    leanh::lean_inc(v_uppers_5124_);
                    leanh::lean_inc(v_lowers_5123_);
                    leanh::lean_inc(v_varMap_5122_);
                    leanh::lean_inc(v_vars_5121_);
                    leanh::lean_inc(v_negFn_5120_);
                    leanh::lean_inc(v_subFn_5119_);
                    leanh::lean_inc(v_homomulFn_x3f_5118_);
                    leanh::lean_inc(v_nsmulFn_x3f_5117_);
                    leanh::lean_inc(v_zsmulFn_x3f_5116_);
                    leanh::lean_inc(v_nsmulFn_5115_);
                    leanh::lean_inc(v_zsmulFn_5114_);
                    leanh::lean_inc(v_addFn_5113_);
                    leanh::lean_inc(v_ltFn_x3f_5112_);
                    leanh::lean_inc(v_leFn_x3f_5111_);
                    leanh::lean_inc(v_one_x3f_5110_);
                    leanh::lean_inc(v_ofNatZero_5109_);
                    leanh::lean_inc(v_zero_5108_);
                    leanh::lean_inc(v_charInst_x3f_5107_);
                    leanh::lean_inc(v_fieldInst_x3f_5106_);
                    leanh::lean_inc(v_orderedRingInst_x3f_5105_);
                    leanh::lean_inc(v_commRingInst_x3f_5104_);
                    leanh::lean_inc(v_ringInst_x3f_5103_);
                    leanh::lean_inc(v_noNatDivInst_x3f_5102_);
                    leanh::lean_inc(v_isLinearInst_x3f_5101_);
                    leanh::lean_inc(v_orderedAddInst_x3f_5100_);
                    leanh::lean_inc(v_isPreorderInst_x3f_5099_);
                    leanh::lean_inc(v_lawfulOrderLTInst_x3f_5098_);
                    leanh::lean_inc(v_ltInst_x3f_5097_);
                    leanh::lean_inc(v_leInst_x3f_5096_);
                    leanh::lean_inc(v_intModuleInst_5095_);
                    leanh::lean_inc(v_u_5094_);
                    leanh::lean_inc(v_type_5093_);
                    leanh::lean_inc(v_ringId_x3f_5092_);
                    leanh::lean_inc(v_id_5091_);
                    leanh::lean_dec(v_v_5090_);
                    v___x_5135_ = leanh::lean_box(0);
                    v_isShared_5136_ = v_isSharedCheck_5147_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5137_ = leanh::lean_box(0);
                v_xs_x27_5138_ = lean_array_fset(v_structs_5077_, v_a_5073_, v___x_5137_);
                v___x_5139_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(v_y_5074_, v_occurs_5132_, v_x_5075_);
                if v_isShared_5136_ == 0 {
                    leanh::lean_ctor_set(v___x_5135_, 40, v___x_5139_);
                    v___x_5141_ = v___x_5135_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5146_ = leanh::lean_alloc_ctor(0, 42, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 0, v_id_5091_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 1, v_ringId_x3f_5092_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 2, v_type_5093_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 3, v_u_5094_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 4, v_intModuleInst_5095_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 5, v_leInst_x3f_5096_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 6, v_ltInst_x3f_5097_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5146_,
                        7,
                        v_lawfulOrderLTInst_x3f_5098_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5146_,
                        8,
                        v_isPreorderInst_x3f_5099_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5146_,
                        9,
                        v_orderedAddInst_x3f_5100_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5146_,
                        10,
                        v_isLinearInst_x3f_5101_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5146_,
                        11,
                        v_noNatDivInst_x3f_5102_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 12, v_ringInst_x3f_5103_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5146_,
                        13,
                        v_commRingInst_x3f_5104_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5146_,
                        14,
                        v_orderedRingInst_x3f_5105_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 15, v_fieldInst_x3f_5106_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 16, v_charInst_x3f_5107_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 17, v_zero_5108_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 18, v_ofNatZero_5109_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 19, v_one_x3f_5110_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 20, v_leFn_x3f_5111_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 21, v_ltFn_x3f_5112_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 22, v_addFn_5113_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 23, v_zsmulFn_5114_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 24, v_nsmulFn_5115_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 25, v_zsmulFn_x3f_5116_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 26, v_nsmulFn_x3f_5117_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 27, v_homomulFn_x3f_5118_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 28, v_subFn_5119_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 29, v_negFn_5120_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 30, v_vars_5121_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 31, v_varMap_5122_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 32, v_lowers_5123_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 33, v_uppers_5124_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 34, v_diseqs_5125_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 35, v_assignment_5126_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 36, v_conflict_x3f_5128_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 37, v_diseqSplits_5129_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 38, v_elimEqs_5130_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 39, v_elimStack_5131_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 40, v___x_5139_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 41, v_ignored_5133_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5146_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 42) as u32,
                        v_caseSplits_5127_,
                    );
                    v___x_5141_ = v_reuseFailAlloc_5146_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5142_ = lean_array_fset(v_xs_x27_5138_, v_a_5073_, v___x_5141_);
                if v_isShared_5089_ == 0 {
                    leanh::lean_ctor_set(v___x_5088_, 0, v___x_5142_);
                    v___x_5144_ = v___x_5088_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5145_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5145_, 0, v___x_5142_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5145_, 1, v_typeIdOf_5078_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5145_, 2, v_exprToStructId_5079_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5145_,
                        3,
                        v_exprToStructIdEntries_5080_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5145_,
                        4,
                        v_forbiddenNatModules_5081_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5145_, 5, v_natStructs_5082_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5145_, 6, v_natTypeIdOf_5083_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5145_,
                        7,
                        v_exprToNatStructId_5084_,
                    );
                    v___x_5144_ = v_reuseFailAlloc_5145_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5144_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0___boxed(
    mut v_a_5157_: *mut leanh::LeanObject,
    mut v_y_5158_: *mut leanh::LeanObject,
    mut v_x_5159_: *mut leanh::LeanObject,
    mut v_s_5160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5161_ =
        l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0(v_a_5157_, v_y_5158_, v_x_5159_, v_s_5160_);
    leanh::lean_dec(v_x_5159_);
    leanh::lean_dec(v_a_5157_);
    return v_res_5161_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_addOcc(
    mut v_x_5162_: *mut leanh::LeanObject,
    mut v_y_5163_: *mut leanh::LeanObject,
    mut v_a_5164_: *mut leanh::LeanObject,
    mut v_a_5165_: *mut leanh::LeanObject,
    mut v_a_5166_: *mut leanh::LeanObject,
    mut v_a_5167_: *mut leanh::LeanObject,
    mut v_a_5168_: *mut leanh::LeanObject,
    mut v_a_5169_: *mut leanh::LeanObject,
    mut v_a_5170_: *mut leanh::LeanObject,
    mut v_a_5171_: *mut leanh::LeanObject,
    mut v_a_5172_: *mut leanh::LeanObject,
    mut v_a_5173_: *mut leanh::LeanObject,
    mut v_a_5174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5180_: u8 = 0;
    let mut v___x_5181_: u8 = 0;
    let mut v___f_5182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5189_: u8 = 0;
    let mut v_a_5190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5193_: u8 = 0;
    let mut v___x_5195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5197_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5176_ = l_Lean_Meta_Grind_Arith_Linear_getOccursOf(
                    v_x_5162_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_, v_a_5169_,
                    v_a_5170_, v_a_5171_, v_a_5172_, v_a_5173_, v_a_5174_,
                );
                if leanh::lean_obj_tag(v___x_5176_) == 0 {
                    v_a_5177_ = leanh::lean_ctor_get(v___x_5176_, 0);
                    v_isSharedCheck_5189_ = (!leanh::lean_is_exclusive(v___x_5176_)) as u8;
                    if v_isSharedCheck_5189_ == 0 {
                        v___x_5179_ = v___x_5176_;
                        v_isShared_5180_ = v_isSharedCheck_5189_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5177_);
                        leanh::lean_dec(v___x_5176_);
                        v___x_5179_ = leanh::lean_box(0);
                        v_isShared_5180_ = v_isSharedCheck_5189_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_y_5163_);
                    leanh::lean_dec(v_x_5162_);
                    v_a_5190_ = leanh::lean_ctor_get(v___x_5176_, 0);
                    v_isSharedCheck_5197_ = (!leanh::lean_is_exclusive(v___x_5176_)) as u8;
                    if v_isSharedCheck_5197_ == 0 {
                        v___x_5192_ = v___x_5176_;
                        v_isShared_5193_ = v_isSharedCheck_5197_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5190_);
                        leanh::lean_dec(v___x_5176_);
                        v___x_5192_ = leanh::lean_box(0);
                        v_isShared_5193_ = v_isSharedCheck_5197_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5181_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_5163_, v_a_5177_);
                leanh::lean_dec(v_a_5177_);
                if v___x_5181_ == 0 {
                    leanh::lean_del_object(v___x_5179_);
                    leanh::lean_inc(v_a_5164_);
                    v___f_5182_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0___boxed
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    leanh::lean_closure_set(v___f_5182_, 0, v_a_5164_);
                    leanh::lean_closure_set(v___f_5182_, 1, v_y_5163_);
                    leanh::lean_closure_set(v___f_5182_, 2, v_x_5162_);
                    v___x_5183_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
                    v___x_5184_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_5183_, v___f_5182_, v_a_5165_);
                    return v___x_5184_;
                } else {
                    leanh::lean_dec(v_y_5163_);
                    leanh::lean_dec(v_x_5162_);
                    v___x_5185_ = leanh::lean_box(0);
                    if v_isShared_5180_ == 0 {
                        leanh::lean_ctor_set(v___x_5179_, 0, v___x_5185_);
                        v___x_5187_ = v___x_5179_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5188_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5188_, 0, v___x_5185_);
                        v___x_5187_ = v_reuseFailAlloc_5188_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5187_;
            }
            3 => {
                if v_isShared_5193_ == 0 {
                    v___x_5195_ = v___x_5192_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5196_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5196_, 0, v_a_5190_);
                    v___x_5195_ = v_reuseFailAlloc_5196_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5195_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_addOcc___boxed(
    mut v_x_5198_: *mut leanh::LeanObject,
    mut v_y_5199_: *mut leanh::LeanObject,
    mut v_a_5200_: *mut leanh::LeanObject,
    mut v_a_5201_: *mut leanh::LeanObject,
    mut v_a_5202_: *mut leanh::LeanObject,
    mut v_a_5203_: *mut leanh::LeanObject,
    mut v_a_5204_: *mut leanh::LeanObject,
    mut v_a_5205_: *mut leanh::LeanObject,
    mut v_a_5206_: *mut leanh::LeanObject,
    mut v_a_5207_: *mut leanh::LeanObject,
    mut v_a_5208_: *mut leanh::LeanObject,
    mut v_a_5209_: *mut leanh::LeanObject,
    mut v_a_5210_: *mut leanh::LeanObject,
    mut v_a_5211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5212_ = l_Lean_Meta_Grind_Arith_Linear_addOcc(
        v_x_5198_, v_y_5199_, v_a_5200_, v_a_5201_, v_a_5202_, v_a_5203_, v_a_5204_, v_a_5205_,
        v_a_5206_, v_a_5207_, v_a_5208_, v_a_5209_, v_a_5210_,
    );
    leanh::lean_dec(v_a_5210_);
    leanh::lean_dec_ref(v_a_5209_);
    leanh::lean_dec(v_a_5208_);
    leanh::lean_dec_ref(v_a_5207_);
    leanh::lean_dec(v_a_5206_);
    leanh::lean_dec_ref(v_a_5205_);
    leanh::lean_dec(v_a_5204_);
    leanh::lean_dec_ref(v_a_5203_);
    leanh::lean_dec(v_a_5202_);
    leanh::lean_dec(v_a_5201_);
    leanh::lean_dec(v_a_5200_);
    return v_res_5212_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0(
    mut v_00_u03b2_5213_: *mut leanh::LeanObject,
    mut v_k_5214_: *mut leanh::LeanObject,
    mut v_t_5215_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5216_: u8 = 0;
    v___x_5216_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_k_5214_, v_t_5215_);
    return v___x_5216_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___boxed(
    mut v_00_u03b2_5217_: *mut leanh::LeanObject,
    mut v_k_5218_: *mut leanh::LeanObject,
    mut v_t_5219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5220_: u8 = 0;
    let mut v_r_5221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5220_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0(
            v_00_u03b2_5217_,
            v_k_5218_,
            v_t_5219_,
        );
    leanh::lean_dec(v_t_5219_);
    leanh::lean_dec(v_k_5218_);
    v_r_5221_ = leanh::lean_box((v_res_5220_) as usize);
    return v_r_5221_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1(
    mut v_00_u03b2_5222_: *mut leanh::LeanObject,
    mut v_k_5223_: *mut leanh::LeanObject,
    mut v_v_5224_: *mut leanh::LeanObject,
    mut v_t_5225_: *mut leanh::LeanObject,
    mut v_hl_5226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5227_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_5223_, v_v_5224_, v_t_5225_);
    return v___x_5227_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(
    mut v_y_5228_: *mut leanh::LeanObject,
    mut v_p_5229_: *mut leanh::LeanObject,
    mut v_a_5230_: *mut leanh::LeanObject,
    mut v_a_5231_: *mut leanh::LeanObject,
    mut v_a_5232_: *mut leanh::LeanObject,
    mut v_a_5233_: *mut leanh::LeanObject,
    mut v_a_5234_: *mut leanh::LeanObject,
    mut v_a_5235_: *mut leanh::LeanObject,
    mut v_a_5236_: *mut leanh::LeanObject,
    mut v_a_5237_: *mut leanh::LeanObject,
    mut v_a_5238_: *mut leanh::LeanObject,
    mut v_a_5239_: *mut leanh::LeanObject,
    mut v_a_5240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_5242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_p_5229_) == 1 {
                    v_v_5242_ = leanh::lean_ctor_get(v_p_5229_, 1);
                    leanh::lean_inc(v_v_5242_);
                    v_p_5243_ = leanh::lean_ctor_get(v_p_5229_, 2);
                    leanh::lean_inc(v_p_5243_);
                    leanh::lean_dec_ref_known(v_p_5229_, 3);
                    leanh::lean_inc(v_y_5228_);
                    v___x_5244_ = l_Lean_Meta_Grind_Arith_Linear_addOcc(
                        v_v_5242_, v_y_5228_, v_a_5230_, v_a_5231_, v_a_5232_, v_a_5233_,
                        v_a_5234_, v_a_5235_, v_a_5236_, v_a_5237_, v_a_5238_, v_a_5239_,
                        v_a_5240_,
                    );
                    if leanh::lean_obj_tag(v___x_5244_) == 0 {
                        leanh::lean_dec_ref_known(v___x_5244_, 1);
                        v_p_5229_ = v_p_5243_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_p_5243_);
                        leanh::lean_dec(v_y_5228_);
                        return v___x_5244_;
                    }
                } else {
                    leanh::lean_dec(v_p_5229_);
                    leanh::lean_dec(v_y_5228_);
                    v___x_5246_ = leanh::lean_box(0);
                    v___x_5247_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5247_, 0, v___x_5246_);
                    return v___x_5247_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go___boxed(
    mut v_y_5248_: *mut leanh::LeanObject,
    mut v_p_5249_: *mut leanh::LeanObject,
    mut v_a_5250_: *mut leanh::LeanObject,
    mut v_a_5251_: *mut leanh::LeanObject,
    mut v_a_5252_: *mut leanh::LeanObject,
    mut v_a_5253_: *mut leanh::LeanObject,
    mut v_a_5254_: *mut leanh::LeanObject,
    mut v_a_5255_: *mut leanh::LeanObject,
    mut v_a_5256_: *mut leanh::LeanObject,
    mut v_a_5257_: *mut leanh::LeanObject,
    mut v_a_5258_: *mut leanh::LeanObject,
    mut v_a_5259_: *mut leanh::LeanObject,
    mut v_a_5260_: *mut leanh::LeanObject,
    mut v_a_5261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5262_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(v_y_5248_, v_p_5249_, v_a_5250_, v_a_5251_, v_a_5252_, v_a_5253_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5257_, v_a_5258_, v_a_5259_, v_a_5260_);
    leanh::lean_dec(v_a_5260_);
    leanh::lean_dec_ref(v_a_5259_);
    leanh::lean_dec(v_a_5258_);
    leanh::lean_dec_ref(v_a_5257_);
    leanh::lean_dec(v_a_5256_);
    leanh::lean_dec_ref(v_a_5255_);
    leanh::lean_dec(v_a_5254_);
    leanh::lean_dec_ref(v_a_5253_);
    leanh::lean_dec(v_a_5252_);
    leanh::lean_dec(v_a_5251_);
    leanh::lean_dec(v_a_5250_);
    return v_res_5262_;
}
pub unsafe fn _init_l_Lean_Grind_Linarith_Poly_updateOccs___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5264_ = l_Lean_Grind_Linarith_Poly_updateOccs___closed__0;
    v___x_5265_ = l_Lean_stringToMessageData(v___x_5264_);
    return v___x_5265_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_updateOccs(
    mut v_p_5266_: *mut leanh::LeanObject,
    mut v_a_5267_: *mut leanh::LeanObject,
    mut v_a_5268_: *mut leanh::LeanObject,
    mut v_a_5269_: *mut leanh::LeanObject,
    mut v_a_5270_: *mut leanh::LeanObject,
    mut v_a_5271_: *mut leanh::LeanObject,
    mut v_a_5272_: *mut leanh::LeanObject,
    mut v_a_5273_: *mut leanh::LeanObject,
    mut v_a_5274_: *mut leanh::LeanObject,
    mut v_a_5275_: *mut leanh::LeanObject,
    mut v_a_5276_: *mut leanh::LeanObject,
    mut v_a_5277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_p_5266_) == 1 {
        let mut v_v_5279_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_5280_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5281_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_v_5279_ = leanh::lean_ctor_get(v_p_5266_, 1);
        leanh::lean_inc(v_v_5279_);
        v_p_5280_ = leanh::lean_ctor_get(v_p_5266_, 2);
        leanh::lean_inc(v_p_5280_);
        leanh::lean_dec_ref_known(v_p_5266_, 3);
        v___x_5281_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(v_v_5279_, v_p_5280_, v_a_5267_, v_a_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_, v_a_5276_, v_a_5277_);
        return v___x_5281_;
    } else {
        let mut v___x_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_p_5266_);
        v___x_5282_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_Poly_updateOccs___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_Poly_updateOccs___closed__1_once),
            _init_l_Lean_Grind_Linarith_Poly_updateOccs___closed__1,
        );
        v___x_5283_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_5282_, v_a_5274_, v_a_5275_, v_a_5276_, v_a_5277_);
        return v___x_5283_;
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_updateOccs___boxed(
    mut v_p_5284_: *mut leanh::LeanObject,
    mut v_a_5285_: *mut leanh::LeanObject,
    mut v_a_5286_: *mut leanh::LeanObject,
    mut v_a_5287_: *mut leanh::LeanObject,
    mut v_a_5288_: *mut leanh::LeanObject,
    mut v_a_5289_: *mut leanh::LeanObject,
    mut v_a_5290_: *mut leanh::LeanObject,
    mut v_a_5291_: *mut leanh::LeanObject,
    mut v_a_5292_: *mut leanh::LeanObject,
    mut v_a_5293_: *mut leanh::LeanObject,
    mut v_a_5294_: *mut leanh::LeanObject,
    mut v_a_5295_: *mut leanh::LeanObject,
    mut v_a_5296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5297_ = l_Lean_Grind_Linarith_Poly_updateOccs(
        v_p_5284_, v_a_5285_, v_a_5286_, v_a_5287_, v_a_5288_, v_a_5289_, v_a_5290_, v_a_5291_,
        v_a_5292_, v_a_5293_, v_a_5294_, v_a_5295_,
    );
    leanh::lean_dec(v_a_5295_);
    leanh::lean_dec_ref(v_a_5294_);
    leanh::lean_dec(v_a_5293_);
    leanh::lean_dec_ref(v_a_5292_);
    leanh::lean_dec(v_a_5291_);
    leanh::lean_dec_ref(v_a_5290_);
    leanh::lean_dec(v_a_5289_);
    leanh::lean_dec_ref(v_a_5288_);
    leanh::lean_dec(v_a_5287_);
    leanh::lean_dec(v_a_5286_);
    leanh::lean_dec(v_a_5285_);
    return v_res_5297_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_findVarToSubst(
    mut v_p_5298_: *mut leanh::LeanObject,
    mut v_a_5299_: *mut leanh::LeanObject,
    mut v_a_5300_: *mut leanh::LeanObject,
    mut v_a_5301_: *mut leanh::LeanObject,
    mut v_a_5302_: *mut leanh::LeanObject,
    mut v_a_5303_: *mut leanh::LeanObject,
    mut v_a_5304_: *mut leanh::LeanObject,
    mut v_a_5305_: *mut leanh::LeanObject,
    mut v_a_5306_: *mut leanh::LeanObject,
    mut v_a_5307_: *mut leanh::LeanObject,
    mut v_a_5308_: *mut leanh::LeanObject,
    mut v_a_5309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5320_: u8 = 0;
    let mut v___y_5322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5326_: u8 = 0;
    let mut v___x_5327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5335_: u8 = 0;
    let mut v_elimEqs_5337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: u8 = 0;
    let mut v___x_5341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5343_: u8 = 0;
    let mut v_a_5344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5347_: u8 = 0;
    let mut v___x_5349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5351_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_p_5298_) == 0 {
                    v___x_5311_ = leanh::lean_box(0);
                    v___x_5312_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5312_, 0, v___x_5311_);
                    return v___x_5312_;
                } else {
                    v_k_5313_ = leanh::lean_ctor_get(v_p_5298_, 0);
                    v_v_5314_ = leanh::lean_ctor_get(v_p_5298_, 1);
                    v_p_5315_ = leanh::lean_ctor_get(v_p_5298_, 2);
                    v___x_5316_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                        v_a_5299_, v_a_5300_, v_a_5301_, v_a_5302_, v_a_5303_, v_a_5304_,
                        v_a_5305_, v_a_5306_, v_a_5307_, v_a_5308_, v_a_5309_,
                    );
                    if leanh::lean_obj_tag(v___x_5316_) == 0 {
                        v_a_5317_ = leanh::lean_ctor_get(v___x_5316_, 0);
                        v_isSharedCheck_5343_ =
                            (!leanh::lean_is_exclusive(v___x_5316_)) as u8;
                        if v_isSharedCheck_5343_ == 0 {
                            v___x_5319_ = v___x_5316_;
                            v_isShared_5320_ = v_isSharedCheck_5343_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5317_);
                            leanh::lean_dec(v___x_5316_);
                            v___x_5319_ = leanh::lean_box(0);
                            v_isShared_5320_ = v_isSharedCheck_5343_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5344_ = leanh::lean_ctor_get(v___x_5316_, 0);
                        v_isSharedCheck_5351_ =
                            (!leanh::lean_is_exclusive(v___x_5316_)) as u8;
                        if v_isSharedCheck_5351_ == 0 {
                            v___x_5346_ = v___x_5316_;
                            v_isShared_5347_ = v_isSharedCheck_5351_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5344_);
                            leanh::lean_dec(v___x_5316_);
                            v___x_5346_ = leanh::lean_box(0);
                            v_isShared_5347_ = v_isSharedCheck_5351_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_elimEqs_5337_ = leanh::lean_ctor_get(v_a_5317_, 38);
                leanh::lean_inc_ref(v_elimEqs_5337_);
                leanh::lean_dec(v_a_5317_);
                v_size_5338_ = leanh::lean_ctor_get(v_elimEqs_5337_, 2);
                v___x_5339_ = leanh::lean_box(0);
                v___x_5340_ = lean_nat_dec_lt(v_v_5314_, v_size_5338_);
                if v___x_5340_ == 0 {
                    leanh::lean_dec_ref(v_elimEqs_5337_);
                    v___x_5341_ = l_outOfBounds___redArg(v___x_5339_);
                    v___y_5322_ = v___x_5341_;
                    state = 2;
                    continue;
                } else {
                    v___x_5342_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_5339_,
                        v_elimEqs_5337_,
                        v_v_5314_,
                    );
                    leanh::lean_dec_ref(v_elimEqs_5337_);
                    v___y_5322_ = v___x_5342_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if leanh::lean_obj_tag(v___y_5322_) == 1 {
                    v_val_5323_ = leanh::lean_ctor_get(v___y_5322_, 0);
                    v_isSharedCheck_5335_ = (!leanh::lean_is_exclusive(v___y_5322_)) as u8;
                    if v_isSharedCheck_5335_ == 0 {
                        v___x_5325_ = v___y_5322_;
                        v_isShared_5326_ = v_isSharedCheck_5335_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5323_);
                        leanh::lean_dec(v___y_5322_);
                        v___x_5325_ = leanh::lean_box(0);
                        v_isShared_5326_ = v_isSharedCheck_5335_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_5322_);
                    leanh::lean_del_object(v___x_5319_);
                    v_p_5298_ = v_p_5315_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc(v_v_5314_);
                v___x_5327_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5327_, 0, v_v_5314_);
                leanh::lean_ctor_set(v___x_5327_, 1, v_val_5323_);
                leanh::lean_inc(v_k_5313_);
                v___x_5328_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5328_, 0, v_k_5313_);
                leanh::lean_ctor_set(v___x_5328_, 1, v___x_5327_);
                if v_isShared_5326_ == 0 {
                    leanh::lean_ctor_set(v___x_5325_, 0, v___x_5328_);
                    v___x_5330_ = v___x_5325_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5334_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5334_, 0, v___x_5328_);
                    v___x_5330_ = v_reuseFailAlloc_5334_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5320_ == 0 {
                    leanh::lean_ctor_set(v___x_5319_, 0, v___x_5330_);
                    v___x_5332_ = v___x_5319_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5333_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5333_, 0, v___x_5330_);
                    v___x_5332_ = v_reuseFailAlloc_5333_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5332_;
            }
            6 => {
                if v_isShared_5347_ == 0 {
                    v___x_5349_ = v___x_5346_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5350_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5350_, 0, v_a_5344_);
                    v___x_5349_ = v_reuseFailAlloc_5350_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5349_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_findVarToSubst___boxed(
    mut v_p_5352_: *mut leanh::LeanObject,
    mut v_a_5353_: *mut leanh::LeanObject,
    mut v_a_5354_: *mut leanh::LeanObject,
    mut v_a_5355_: *mut leanh::LeanObject,
    mut v_a_5356_: *mut leanh::LeanObject,
    mut v_a_5357_: *mut leanh::LeanObject,
    mut v_a_5358_: *mut leanh::LeanObject,
    mut v_a_5359_: *mut leanh::LeanObject,
    mut v_a_5360_: *mut leanh::LeanObject,
    mut v_a_5361_: *mut leanh::LeanObject,
    mut v_a_5362_: *mut leanh::LeanObject,
    mut v_a_5363_: *mut leanh::LeanObject,
    mut v_a_5364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5365_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(
        v_p_5352_, v_a_5353_, v_a_5354_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_, v_a_5359_,
        v_a_5360_, v_a_5361_, v_a_5362_, v_a_5363_,
    );
    leanh::lean_dec(v_a_5363_);
    leanh::lean_dec_ref(v_a_5362_);
    leanh::lean_dec(v_a_5361_);
    leanh::lean_dec_ref(v_a_5360_);
    leanh::lean_dec(v_a_5359_);
    leanh::lean_dec_ref(v_a_5358_);
    leanh::lean_dec(v_a_5357_);
    leanh::lean_dec_ref(v_a_5356_);
    leanh::lean_dec(v_a_5355_);
    leanh::lean_dec(v_a_5354_);
    leanh::lean_dec(v_a_5353_);
    leanh::lean_dec(v_p_5352_);
    return v_res_5365_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_gcdCoeffsAux(
    mut v_x_5366_: *mut leanh::LeanObject,
    mut v_x_5367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_5368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5366_) == 0 {
                    return v_x_5367_;
                } else {
                    v_k_5368_ = leanh::lean_ctor_get(v_x_5366_, 0);
                    v_p_5369_ = leanh::lean_ctor_get(v_x_5366_, 2);
                    v___x_5370_ = lean_nat_to_int(v_x_5367_);
                    v___x_5371_ = l_Int_gcd(v_k_5368_, v___x_5370_);
                    leanh::lean_dec(v___x_5370_);
                    v_x_5366_ = v_p_5369_;
                    v_x_5367_ = v___x_5371_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_gcdCoeffsAux___boxed(
    mut v_x_5373_: *mut leanh::LeanObject,
    mut v_x_5374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5375_ = l_Lean_Grind_Linarith_Poly_gcdCoeffsAux(v_x_5373_, v_x_5374_);
    leanh::lean_dec(v_x_5373_);
    return v_res_5375_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_gcdCoeffs(
    mut v_p_5376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_p_5376_) == 0 {
        let mut v___x_5377_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5377_ = leanh::lean_unsigned_to_nat(1);
        return v___x_5377_;
    } else {
        let mut v_k_5378_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_5379_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5380_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5381_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_k_5378_ = leanh::lean_ctor_get(v_p_5376_, 0);
        v_p_5379_ = leanh::lean_ctor_get(v_p_5376_, 2);
        v___x_5380_ = lean_nat_abs(v_k_5378_);
        v___x_5381_ = l_Lean_Grind_Linarith_Poly_gcdCoeffsAux(v_p_5379_, v___x_5380_);
        return v___x_5381_;
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_gcdCoeffs___boxed(
    mut v_p_5382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5383_ = l_Lean_Grind_Linarith_Poly_gcdCoeffs(v_p_5382_);
    leanh::lean_dec(v_p_5382_);
    return v_res_5383_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_div(
    mut v_p_5384_: *mut leanh::LeanObject,
    mut v_k_5385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_5386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5391_: u8 = 0;
    let mut v___x_5392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5397_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_p_5384_) == 0 {
                    return v_p_5384_;
                } else {
                    v_k_5386_ = leanh::lean_ctor_get(v_p_5384_, 0);
                    v_v_5387_ = leanh::lean_ctor_get(v_p_5384_, 1);
                    v_p_5388_ = leanh::lean_ctor_get(v_p_5384_, 2);
                    v_isSharedCheck_5397_ = (!leanh::lean_is_exclusive(v_p_5384_)) as u8;
                    if v_isSharedCheck_5397_ == 0 {
                        v___x_5390_ = v_p_5384_;
                        v_isShared_5391_ = v_isSharedCheck_5397_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_p_5388_);
                        leanh::lean_inc(v_v_5387_);
                        leanh::lean_inc(v_k_5386_);
                        leanh::lean_dec(v_p_5384_);
                        v___x_5390_ = leanh::lean_box(0);
                        v_isShared_5391_ = v_isSharedCheck_5397_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5392_ = lean_int_ediv(v_k_5386_, v_k_5385_);
                leanh::lean_dec(v_k_5386_);
                v___x_5393_ = l_Lean_Grind_Linarith_Poly_div(v_p_5388_, v_k_5385_);
                if v_isShared_5391_ == 0 {
                    leanh::lean_ctor_set(v___x_5390_, 2, v___x_5393_);
                    leanh::lean_ctor_set(v___x_5390_, 0, v___x_5392_);
                    v___x_5395_ = v___x_5390_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5396_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5396_, 0, v___x_5392_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5396_, 1, v_v_5387_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5396_, 2, v___x_5393_);
                    v___x_5395_ = v_reuseFailAlloc_5396_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5395_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_div___boxed(
    mut v_p_5398_: *mut leanh::LeanObject,
    mut v_k_5399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5400_ = l_Lean_Grind_Linarith_Poly_div(v_p_5398_, v_k_5399_);
    leanh::lean_dec(v_k_5399_);
    return v_res_5400_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5401_ = leanh::lean_unsigned_to_nat(1);
    v___x_5402_ = lean_nat_to_int(v___x_5401_);
    return v___x_5402_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5403_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0);
    v___x_5404_ = lean_int_neg(v___x_5403_);
    return v___x_5404_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go(
    mut v_k_5405_: *mut leanh::LeanObject,
    mut v_x_5406_: *mut leanh::LeanObject,
    mut v_p_5407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5409_: u8 = 0;
    let mut v___x_5410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: u8 = 0;
    let mut v___x_5419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: u8 = 0;
    let mut v___x_5422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5420_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0);
                v___x_5421_ = lean_int_dec_eq(v_k_5405_, v___x_5420_);
                if v___x_5421_ == 0 {
                    v___x_5422_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1);
                    v___x_5423_ = lean_int_dec_eq(v_k_5405_, v___x_5422_);
                    v___y_5409_ = v___x_5423_;
                    state = 1;
                    continue;
                } else {
                    v___y_5409_ = v___x_5421_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_5409_ == 0 {
                    if leanh::lean_obj_tag(v_p_5407_) == 0 {
                        v___x_5410_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5410_, 0, v_k_5405_);
                        leanh::lean_ctor_set(v___x_5410_, 1, v_x_5406_);
                        return v___x_5410_;
                    } else {
                        v_k_5411_ = leanh::lean_ctor_get(v_p_5407_, 0);
                        leanh::lean_inc(v_k_5411_);
                        v_v_5412_ = leanh::lean_ctor_get(v_p_5407_, 1);
                        leanh::lean_inc(v_v_5412_);
                        v_p_5413_ = leanh::lean_ctor_get(v_p_5407_, 2);
                        leanh::lean_inc(v_p_5413_);
                        leanh::lean_dec_ref_known(v_p_5407_, 3);
                        v___x_5414_ = lean_nat_abs(v_k_5411_);
                        v___x_5415_ = lean_nat_abs(v_k_5405_);
                        v___x_5416_ = lean_nat_dec_lt(v___x_5414_, v___x_5415_);
                        leanh::lean_dec(v___x_5415_);
                        leanh::lean_dec(v___x_5414_);
                        if v___x_5416_ == 0 {
                            leanh::lean_dec(v_v_5412_);
                            leanh::lean_dec(v_k_5411_);
                            v_p_5407_ = v_p_5413_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_5406_);
                            leanh::lean_dec(v_k_5405_);
                            v_k_5405_ = v_k_5411_;
                            v_x_5406_ = v_v_5412_;
                            v_p_5407_ = v_p_5413_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_p_5407_);
                    v___x_5419_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5419_, 0, v_k_5405_);
                    leanh::lean_ctor_set(v___x_5419_, 1, v_x_5406_);
                    return v___x_5419_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_pickVarToElim_x3f(
    mut v_p_5424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_p_5424_) == 0 {
        let mut v___x_5425_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5425_ = leanh::lean_box(0);
        return v___x_5425_;
    } else {
        let mut v_k_5426_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5427_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_5428_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5429_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5430_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_k_5426_ = leanh::lean_ctor_get(v_p_5424_, 0);
        leanh::lean_inc(v_k_5426_);
        v_v_5427_ = leanh::lean_ctor_get(v_p_5424_, 1);
        leanh::lean_inc(v_v_5427_);
        v_p_5428_ = leanh::lean_ctor_get(v_p_5424_, 2);
        leanh::lean_inc(v_p_5428_);
        leanh::lean_dec_ref_known(v_p_5424_, 3);
        v___x_5429_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go(v_k_5426_, v_v_5427_, v_p_5428_);
        v___x_5430_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5430_, 0, v___x_5429_);
        return v___x_5430_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Gcd(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_Gcd(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
}