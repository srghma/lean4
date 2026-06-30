// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
// Imports: Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Lean.Meta.Tactic.Simp.Arith.Int.Simp
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_grind_cutsat_assert_eq, lean_grind_cutsat_assert_le,
    lean_grind_cutsat_mk_var, lean_int_dec_eq, lean_int_dec_le, lean_int_ediv, lean_int_emod,
    lean_int_mul, lean_int_neg, lean_nat_abs, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_mul, lean_nat_sub, lean_nat_to_int, lean_st_ref_get,
    lean_uint64_to_usize, lean_usize_land, lean_usize_of_nat, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Int::Basic::l_Int_toNat;
use crate::r#gen::Init::Data::Int::DivMod::Lemmas::l_Int_decidableDvd;
use crate::r#gen::Init::Data::Int::Gcd::{l_Int_gcd, l_Int_lcm};
use crate::r#gen::Init::Data::Int::Linear::{
    l_Int_Linear_Poly_getConst, l_Int_Linear_Poly_isUnsatDvd, l_Int_Linear_Poly_isUnsatLe,
    l_Int_Linear_Poly_leadCoeff,
};
use crate::r#gen::Init::Data::Int::Repr::l_Int_repr;
use crate::r#gen::Init::Data::Rat::Basic::{
    l_Rat_add, l_Rat_instDecidableLe, l_Rat_mul, l_Rat_ofInt, l_instDecidableEqRat_decEq,
    l_instInhabitedRat,
};
use crate::r#gen::Init::GetElem::l_outOfBounds___redArg;
use crate::r#gen::Lean::Data::LBool::l_Bool_toLBool;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_get_x21___redArg;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_const___override, l_Lean_instInhabitedExpr, l_Lean_mkApp3, l_Lean_mkIntDvd,
    l_Lean_mkIntEq, l_Lean_mkIntLE, l_Lean_mkIntLit, l_Lean_mkNot,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_indentD, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Types::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types, l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Util::{
    l_Lean_Meta_Grind_Arith_quoteIfArithTerm, l_Lean_Meta_Grind_Arith_shrink,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg,
    l_Lean_Meta_Grind_SolverExtension_getState___redArg, l_Lean_Meta_Grind_isInconsistent___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Arith::Int::Basic::l_Int_Linear_Poly_denoteExpr___redArg;
use crate::r#gen::Lean::Meta::Tactic::Simp::Arith::Int::Simp::{
    initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp, l_Int_Linear_Poly_gcdCoeffs_x27,
    runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp,
};
use crate::r#gen::Lean::ToExpr::l_Lean_instToExprInt_mkNat;
static mut l_Int_Linear_Poly_isZero___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int_Linear_Poly_isZero___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__1: usize = 0;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__0_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 43, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__3_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [42, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__0_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 3,
    m_data: [32, 226, 136, 163, 32, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__0_value:
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
    m_data: [78, 101, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__1_value:
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
    m_data: [110, 101, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__1_value
) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__2_value_aux_0:
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
            l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__0_value
        ) as *mut leanh::LeanObject,
        9626815015619986526 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__2_value:
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
            l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__2_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__1_value
        ) as *mut leanh::LeanObject,
        17185717442815859305 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__2_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__6_value:
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
    m_data: [73, 110, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__6_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__7_value:
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
            l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__6_value
        ) as *mut leanh::LeanObject,
        7009148538150066493 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__7_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__9_value:
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
    m_data: [105, 110, 115, 116, 78, 101, 103, 73, 110, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__9_value
) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__10_value_aux_0:
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
            l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__6_value
        ) as *mut leanh::LeanObject,
        7009148538150066493 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__10_value:
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
            l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__10_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__9_value
        ) as *mut leanh::LeanObject,
        6362876895233142233 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__10_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__0_value:
    leanh::LeanStringObject<35> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        96, 103, 114, 105, 110, 100, 96, 32, 105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114,
        114, 111, 114, 44, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__2_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [32, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__2_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__0_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 4,
    m_data: [32, 226, 137, 160, 32, 48, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__0_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 4,
    m_data: [32, 226, 137, 164, 32, 48, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__0_value:
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
    m_data: [32, 61, 32, 48, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Int_Linear_Poly_updateOccs___redArg___closed__0_value: leanh::LeanStringObject<
    55,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 55,
    m_capacity: 55,
    m_length: 54,
    m_data: [
        96, 103, 114, 105, 110, 100, 96, 32, 105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114,
        114, 111, 114, 44, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 99, 111, 110,
        115, 116, 97, 110, 116, 32, 112, 111, 108, 121, 110, 111, 109, 105, 97, 108, 0,
    ],
};
static mut l_Int_Linear_Poly_updateOccs___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_updateOccs___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Int_Linear_Poly_updateOccs___redArg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int_Linear_Poly_updateOccs___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Int_Linear_Poly_eval_x3f___redArg___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int_Linear_Poly_eval_x3f___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__0_value:
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
    m_data: [44, 32, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__2_value:
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
    m_data: [110, 111, 110, 101, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__3_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__2_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__3_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Int_Linear_Poly_isZero___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3063_ = leanh::lean_unsigned_to_nat(0);
    v___x_3064_ = lean_nat_to_int(v___x_3063_);
    return v___x_3064_;
}
pub unsafe fn l_Int_Linear_Poly_isZero(mut v_x_3065_: *mut leanh::LeanObject) -> u8 {
    if leanh::lean_obj_tag(v_x_3065_) == 0 {
        let mut v_k_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3068_: u8 = 0;
        v_k_3066_ = leanh::lean_ctor_get(v_x_3065_, 0);
        v___x_3067_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_Linear_Poly_isZero___closed__0),
            core::ptr::addr_of_mut!(l_Int_Linear_Poly_isZero___closed__0_once),
            _init_l_Int_Linear_Poly_isZero___closed__0,
        );
        v___x_3068_ = lean_int_dec_eq(v_k_3066_, v___x_3067_);
        return v___x_3068_;
    } else {
        let mut v___x_3069_: u8 = 0;
        v___x_3069_ = 0;
        return v___x_3069_;
    }
}
pub unsafe fn l_Int_Linear_Poly_isZero___boxed(
    mut v_x_3070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3071_: u8 = 0;
    let mut v_r_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3071_ = l_Int_Linear_Poly_isZero(v_x_3070_);
    leanh::lean_dec_ref(v_x_3070_);
    v_r_3072_ = leanh::lean_box((v_res_3071_) as usize);
    return v_r_3072_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_isSorted_go(
    mut v_a_3073_: *mut leanh::LeanObject,
    mut v_a_3074_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3075_: u8 = 0;
    let mut v_v_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3085_: u8 = 0;
    let mut v___x_3086_: u8 = 0;
    let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3091_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_3074_) == 0 {
                    leanh::lean_dec(v_a_3073_);
                    v___x_3075_ = 1;
                    return v___x_3075_;
                } else {
                    if leanh::lean_obj_tag(v_a_3073_) == 0 {
                        v_v_3076_ = leanh::lean_ctor_get(v_a_3074_, 1);
                        v_p_3077_ = leanh::lean_ctor_get(v_a_3074_, 2);
                        leanh::lean_inc(v_v_3076_);
                        v___x_3078_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3078_, 0, v_v_3076_);
                        v_a_3073_ = v___x_3078_;
                        v_a_3074_ = v_p_3077_;
                        state = 0;
                        continue;
                    } else {
                        v_v_3080_ = leanh::lean_ctor_get(v_a_3074_, 1);
                        v_p_3081_ = leanh::lean_ctor_get(v_a_3074_, 2);
                        v_val_3082_ = leanh::lean_ctor_get(v_a_3073_, 0);
                        v_isSharedCheck_3091_ = (!leanh::lean_is_exclusive(v_a_3073_)) as u8;
                        if v_isSharedCheck_3091_ == 0 {
                            v___x_3084_ = v_a_3073_;
                            v_isShared_3085_ = v_isSharedCheck_3091_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3082_);
                            leanh::lean_dec(v_a_3073_);
                            v___x_3084_ = leanh::lean_box(0);
                            v_isShared_3085_ = v_isSharedCheck_3091_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3086_ = lean_nat_dec_lt(v_v_3080_, v_val_3082_);
                leanh::lean_dec(v_val_3082_);
                if v___x_3086_ == 0 {
                    leanh::lean_del_object(v___x_3084_);
                    return v___x_3086_;
                } else {
                    leanh::lean_inc(v_v_3080_);
                    if v_isShared_3085_ == 0 {
                        leanh::lean_ctor_set(v___x_3084_, 0, v_v_3080_);
                        v___x_3088_ = v___x_3084_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3090_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_v_3080_);
                        v___x_3088_ = v_reuseFailAlloc_3090_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_a_3073_ = v___x_3088_;
                v_a_3074_ = v_p_3081_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_isSorted_go___boxed(
    mut v_a_3092_: *mut leanh::LeanObject,
    mut v_a_3093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3094_: u8 = 0;
    let mut v_r_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3094_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_isSorted_go(
            v_a_3092_, v_a_3093_,
        );
    leanh::lean_dec_ref(v_a_3093_);
    v_r_3095_ = leanh::lean_box((v_res_3094_) as usize);
    return v_r_3095_;
}
pub unsafe fn l_Int_Linear_Poly_isSorted(mut v_p_3096_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: u8 = 0;
    v___x_3097_ = leanh::lean_box(0);
    v___x_3098_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_isSorted_go(
            v___x_3097_,
            v_p_3096_,
        );
    return v___x_3098_;
}
pub unsafe fn l_Int_Linear_Poly_isSorted___boxed(
    mut v_p_3099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3100_: u8 = 0;
    let mut v_r_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3100_ = l_Int_Linear_Poly_isSorted(v_p_3099_);
    leanh::lean_dec_ref(v_p_3099_);
    v_r_3101_ = leanh::lean_box((v_res_3100_) as usize);
    return v_r_3101_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(
    mut v_a_3102_: *mut leanh::LeanObject,
    mut v_a_3103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3105_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
    v___x_3106_ =
        l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_3105_, v_a_3102_, v_a_3103_);
    return v___x_3106_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg___boxed(
    mut v_a_3107_: *mut leanh::LeanObject,
    mut v_a_3108_: *mut leanh::LeanObject,
    mut v_a_3109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3110_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3107_, v_a_3108_);
    leanh::lean_dec_ref(v_a_3108_);
    leanh::lean_dec(v_a_3107_);
    return v_res_3110_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_get_x27(
    mut v_a_3111_: *mut leanh::LeanObject,
    mut v_a_3112_: *mut leanh::LeanObject,
    mut v_a_3113_: *mut leanh::LeanObject,
    mut v_a_3114_: *mut leanh::LeanObject,
    mut v_a_3115_: *mut leanh::LeanObject,
    mut v_a_3116_: *mut leanh::LeanObject,
    mut v_a_3117_: *mut leanh::LeanObject,
    mut v_a_3118_: *mut leanh::LeanObject,
    mut v_a_3119_: *mut leanh::LeanObject,
    mut v_a_3120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3122_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3111_, v_a_3119_);
    return v___x_3122_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_get_x27___boxed(
    mut v_a_3123_: *mut leanh::LeanObject,
    mut v_a_3124_: *mut leanh::LeanObject,
    mut v_a_3125_: *mut leanh::LeanObject,
    mut v_a_3126_: *mut leanh::LeanObject,
    mut v_a_3127_: *mut leanh::LeanObject,
    mut v_a_3128_: *mut leanh::LeanObject,
    mut v_a_3129_: *mut leanh::LeanObject,
    mut v_a_3130_: *mut leanh::LeanObject,
    mut v_a_3131_: *mut leanh::LeanObject,
    mut v_a_3132_: *mut leanh::LeanObject,
    mut v_a_3133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3134_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(
        v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_,
        v_a_3131_, v_a_3132_,
    );
    leanh::lean_dec(v_a_3132_);
    leanh::lean_dec_ref(v_a_3131_);
    leanh::lean_dec(v_a_3130_);
    leanh::lean_dec_ref(v_a_3129_);
    leanh::lean_dec(v_a_3128_);
    leanh::lean_dec_ref(v_a_3127_);
    leanh::lean_dec(v_a_3126_);
    leanh::lean_dec_ref(v_a_3125_);
    leanh::lean_dec(v_a_3124_);
    leanh::lean_dec(v_a_3123_);
    return v_res_3134_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_modify_x27___redArg(
    mut v_f_3135_: *mut leanh::LeanObject,
    mut v_a_3136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3138_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
    v___x_3139_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3138_, v_f_3135_, v_a_3136_);
    return v___x_3139_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_modify_x27___redArg___boxed(
    mut v_f_3140_: *mut leanh::LeanObject,
    mut v_a_3141_: *mut leanh::LeanObject,
    mut v_a_3142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3143_ = l_Lean_Meta_Grind_Arith_Cutsat_modify_x27___redArg(v_f_3140_, v_a_3141_);
    leanh::lean_dec(v_a_3141_);
    return v_res_3143_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_modify_x27(
    mut v_f_3144_: *mut leanh::LeanObject,
    mut v_a_3145_: *mut leanh::LeanObject,
    mut v_a_3146_: *mut leanh::LeanObject,
    mut v_a_3147_: *mut leanh::LeanObject,
    mut v_a_3148_: *mut leanh::LeanObject,
    mut v_a_3149_: *mut leanh::LeanObject,
    mut v_a_3150_: *mut leanh::LeanObject,
    mut v_a_3151_: *mut leanh::LeanObject,
    mut v_a_3152_: *mut leanh::LeanObject,
    mut v_a_3153_: *mut leanh::LeanObject,
    mut v_a_3154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3156_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
    v___x_3157_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3156_, v_f_3144_, v_a_3145_);
    return v___x_3157_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_modify_x27___boxed(
    mut v_f_3158_: *mut leanh::LeanObject,
    mut v_a_3159_: *mut leanh::LeanObject,
    mut v_a_3160_: *mut leanh::LeanObject,
    mut v_a_3161_: *mut leanh::LeanObject,
    mut v_a_3162_: *mut leanh::LeanObject,
    mut v_a_3163_: *mut leanh::LeanObject,
    mut v_a_3164_: *mut leanh::LeanObject,
    mut v_a_3165_: *mut leanh::LeanObject,
    mut v_a_3166_: *mut leanh::LeanObject,
    mut v_a_3167_: *mut leanh::LeanObject,
    mut v_a_3168_: *mut leanh::LeanObject,
    mut v_a_3169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3170_ = l_Lean_Meta_Grind_Arith_Cutsat_modify_x27(
        v_f_3158_, v_a_3159_, v_a_3160_, v_a_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_,
        v_a_3166_, v_a_3167_, v_a_3168_,
    );
    leanh::lean_dec(v_a_3168_);
    leanh::lean_dec_ref(v_a_3167_);
    leanh::lean_dec(v_a_3166_);
    leanh::lean_dec_ref(v_a_3165_);
    leanh::lean_dec(v_a_3164_);
    leanh::lean_dec_ref(v_a_3163_);
    leanh::lean_dec(v_a_3162_);
    leanh::lean_dec_ref(v_a_3161_);
    leanh::lean_dec(v_a_3160_);
    leanh::lean_dec(v_a_3159_);
    return v_res_3170_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(
    mut v_a_3171_: *mut leanh::LeanObject,
    mut v_a_3172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: u8 = 0;
    let mut v___x_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3181_: u8 = 0;
    let mut v_conflict_x3f_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: u8 = 0;
    let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3191_: u8 = 0;
    let mut v_a_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3195_: u8 = 0;
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3199_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3174_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_3171_);
                if leanh::lean_obj_tag(v___x_3174_) == 0 {
                    v_a_3175_ = leanh::lean_ctor_get(v___x_3174_, 0);
                    leanh::lean_inc(v_a_3175_);
                    v___x_3176_ = (leanh::lean_unbox(v_a_3175_) as u8);
                    if v___x_3176_ == 0 {
                        leanh::lean_dec_ref_known(v___x_3174_, 1);
                        v___x_3177_ =
                            l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3171_, v_a_3172_);
                        if leanh::lean_obj_tag(v___x_3177_) == 0 {
                            v_a_3178_ = leanh::lean_ctor_get(v___x_3177_, 0);
                            v_isSharedCheck_3191_ =
                                (!leanh::lean_is_exclusive(v___x_3177_)) as u8;
                            if v_isSharedCheck_3191_ == 0 {
                                v___x_3180_ = v___x_3177_;
                                v_isShared_3181_ = v_isSharedCheck_3191_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3178_);
                                leanh::lean_dec(v___x_3177_);
                                v___x_3180_ = leanh::lean_box(0);
                                v_isShared_3181_ = v_isSharedCheck_3191_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_3175_);
                            v_a_3192_ = leanh::lean_ctor_get(v___x_3177_, 0);
                            v_isSharedCheck_3199_ =
                                (!leanh::lean_is_exclusive(v___x_3177_)) as u8;
                            if v_isSharedCheck_3199_ == 0 {
                                v___x_3194_ = v___x_3177_;
                                v_isShared_3195_ = v_isSharedCheck_3199_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3192_);
                                leanh::lean_dec(v___x_3177_);
                                v___x_3194_ = leanh::lean_box(0);
                                v_isShared_3195_ = v_isSharedCheck_3199_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_3175_);
                        return v___x_3174_;
                    }
                } else {
                    return v___x_3174_;
                }
            }
            1 => {
                v_conflict_x3f_3182_ = leanh::lean_ctor_get(v_a_3178_, 15);
                leanh::lean_inc(v_conflict_x3f_3182_);
                leanh::lean_dec(v_a_3178_);
                if leanh::lean_obj_tag(v_conflict_x3f_3182_) == 0 {
                    if v_isShared_3181_ == 0 {
                        leanh::lean_ctor_set(v___x_3180_, 0, v_a_3175_);
                        v___x_3184_ = v___x_3180_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3185_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3175_);
                        v___x_3184_ = v_reuseFailAlloc_3185_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_conflict_x3f_3182_, 1);
                    leanh::lean_dec(v_a_3175_);
                    v___x_3186_ = 1;
                    v___x_3187_ = leanh::lean_box((v___x_3186_) as usize);
                    if v_isShared_3181_ == 0 {
                        leanh::lean_ctor_set(v___x_3180_, 0, v___x_3187_);
                        v___x_3189_ = v___x_3180_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3190_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3187_);
                        v___x_3189_ = v_reuseFailAlloc_3190_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3184_;
            }
            3 => {
                return v___x_3189_;
            }
            4 => {
                if v_isShared_3195_ == 0 {
                    v___x_3197_ = v___x_3194_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3198_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3192_);
                    v___x_3197_ = v_reuseFailAlloc_3198_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3197_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg___boxed(
    mut v_a_3200_: *mut leanh::LeanObject,
    mut v_a_3201_: *mut leanh::LeanObject,
    mut v_a_3202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3203_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_3200_, v_a_3201_);
    leanh::lean_dec_ref(v_a_3201_);
    leanh::lean_dec(v_a_3200_);
    return v_res_3203_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_inconsistent(
    mut v_a_3204_: *mut leanh::LeanObject,
    mut v_a_3205_: *mut leanh::LeanObject,
    mut v_a_3206_: *mut leanh::LeanObject,
    mut v_a_3207_: *mut leanh::LeanObject,
    mut v_a_3208_: *mut leanh::LeanObject,
    mut v_a_3209_: *mut leanh::LeanObject,
    mut v_a_3210_: *mut leanh::LeanObject,
    mut v_a_3211_: *mut leanh::LeanObject,
    mut v_a_3212_: *mut leanh::LeanObject,
    mut v_a_3213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3215_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_3204_, v_a_3212_);
    return v___x_3215_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___boxed(
    mut v_a_3216_: *mut leanh::LeanObject,
    mut v_a_3217_: *mut leanh::LeanObject,
    mut v_a_3218_: *mut leanh::LeanObject,
    mut v_a_3219_: *mut leanh::LeanObject,
    mut v_a_3220_: *mut leanh::LeanObject,
    mut v_a_3221_: *mut leanh::LeanObject,
    mut v_a_3222_: *mut leanh::LeanObject,
    mut v_a_3223_: *mut leanh::LeanObject,
    mut v_a_3224_: *mut leanh::LeanObject,
    mut v_a_3225_: *mut leanh::LeanObject,
    mut v_a_3226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3227_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent(
        v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_,
        v_a_3224_, v_a_3225_,
    );
    leanh::lean_dec(v_a_3225_);
    leanh::lean_dec_ref(v_a_3224_);
    leanh::lean_dec(v_a_3223_);
    leanh::lean_dec_ref(v_a_3222_);
    leanh::lean_dec(v_a_3221_);
    leanh::lean_dec_ref(v_a_3220_);
    leanh::lean_dec(v_a_3219_);
    leanh::lean_dec_ref(v_a_3218_);
    leanh::lean_dec(v_a_3217_);
    leanh::lean_dec(v_a_3216_);
    return v_res_3227_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_mkVar___boxed(
    mut v_e_3240_: *mut leanh::LeanObject,
    mut v_a_3241_: *mut leanh::LeanObject,
    mut v_a_3242_: *mut leanh::LeanObject,
    mut v_a_3243_: *mut leanh::LeanObject,
    mut v_a_3244_: *mut leanh::LeanObject,
    mut v_a_3245_: *mut leanh::LeanObject,
    mut v_a_3246_: *mut leanh::LeanObject,
    mut v_a_3247_: *mut leanh::LeanObject,
    mut v_a_3248_: *mut leanh::LeanObject,
    mut v_a_3249_: *mut leanh::LeanObject,
    mut v_a_3250_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_3251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3252_ = lean_grind_cutsat_mk_var(
        v_e_3240_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_,
        v_a_3248_, v_a_3249_, v_a_3250_,
    );
    return v_res_3252_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(
    mut v_a_3253_: *mut leanh::LeanObject,
    mut v_a_3254_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3260_: u8 = 0;
    let mut v_vars_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3265_: u8 = 0;
    let mut v_a_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3269_: u8 = 0;
    let mut v___x_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3273_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3256_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3253_, v_a_3254_);
                if leanh::lean_obj_tag(v___x_3256_) == 0 {
                    v_a_3257_ = leanh::lean_ctor_get(v___x_3256_, 0);
                    v_isSharedCheck_3265_ = (!leanh::lean_is_exclusive(v___x_3256_)) as u8;
                    if v_isSharedCheck_3265_ == 0 {
                        v___x_3259_ = v___x_3256_;
                        v_isShared_3260_ = v_isSharedCheck_3265_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3257_);
                        leanh::lean_dec(v___x_3256_);
                        v___x_3259_ = leanh::lean_box(0);
                        v_isShared_3260_ = v_isSharedCheck_3265_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3266_ = leanh::lean_ctor_get(v___x_3256_, 0);
                    v_isSharedCheck_3273_ = (!leanh::lean_is_exclusive(v___x_3256_)) as u8;
                    if v_isSharedCheck_3273_ == 0 {
                        v___x_3268_ = v___x_3256_;
                        v_isShared_3269_ = v_isSharedCheck_3273_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3266_);
                        leanh::lean_dec(v___x_3256_);
                        v___x_3268_ = leanh::lean_box(0);
                        v_isShared_3269_ = v_isSharedCheck_3273_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_vars_3261_ = leanh::lean_ctor_get(v_a_3257_, 0);
                leanh::lean_inc_ref(v_vars_3261_);
                leanh::lean_dec(v_a_3257_);
                if v_isShared_3260_ == 0 {
                    leanh::lean_ctor_set(v___x_3259_, 0, v_vars_3261_);
                    v___x_3263_ = v___x_3259_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3264_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_vars_3261_);
                    v___x_3263_ = v_reuseFailAlloc_3264_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3263_;
            }
            3 => {
                if v_isShared_3269_ == 0 {
                    v___x_3271_ = v___x_3268_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3272_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3266_);
                    v___x_3271_ = v_reuseFailAlloc_3272_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3271_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg___boxed(
    mut v_a_3274_: *mut leanh::LeanObject,
    mut v_a_3275_: *mut leanh::LeanObject,
    mut v_a_3276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3277_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(v_a_3274_, v_a_3275_);
    leanh::lean_dec_ref(v_a_3275_);
    leanh::lean_dec(v_a_3274_);
    return v_res_3277_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_getVars(
    mut v_a_3278_: *mut leanh::LeanObject,
    mut v_a_3279_: *mut leanh::LeanObject,
    mut v_a_3280_: *mut leanh::LeanObject,
    mut v_a_3281_: *mut leanh::LeanObject,
    mut v_a_3282_: *mut leanh::LeanObject,
    mut v_a_3283_: *mut leanh::LeanObject,
    mut v_a_3284_: *mut leanh::LeanObject,
    mut v_a_3285_: *mut leanh::LeanObject,
    mut v_a_3286_: *mut leanh::LeanObject,
    mut v_a_3287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3289_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(v_a_3278_, v_a_3286_);
    return v___x_3289_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_getVars___boxed(
    mut v_a_3290_: *mut leanh::LeanObject,
    mut v_a_3291_: *mut leanh::LeanObject,
    mut v_a_3292_: *mut leanh::LeanObject,
    mut v_a_3293_: *mut leanh::LeanObject,
    mut v_a_3294_: *mut leanh::LeanObject,
    mut v_a_3295_: *mut leanh::LeanObject,
    mut v_a_3296_: *mut leanh::LeanObject,
    mut v_a_3297_: *mut leanh::LeanObject,
    mut v_a_3298_: *mut leanh::LeanObject,
    mut v_a_3299_: *mut leanh::LeanObject,
    mut v_a_3300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3301_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars(
        v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_,
        v_a_3298_, v_a_3299_,
    );
    leanh::lean_dec(v_a_3299_);
    leanh::lean_dec_ref(v_a_3298_);
    leanh::lean_dec(v_a_3297_);
    leanh::lean_dec_ref(v_a_3296_);
    leanh::lean_dec(v_a_3295_);
    leanh::lean_dec_ref(v_a_3294_);
    leanh::lean_dec(v_a_3293_);
    leanh::lean_dec_ref(v_a_3292_);
    leanh::lean_dec(v_a_3291_);
    leanh::lean_dec(v_a_3290_);
    return v_res_3301_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(
    mut v_x_3302_: *mut leanh::LeanObject,
    mut v_a_3303_: *mut leanh::LeanObject,
    mut v_a_3304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3310_: u8 = 0;
    let mut v_vars_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: u8 = 0;
    let mut v___x_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3323_: u8 = 0;
    let mut v_a_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3327_: u8 = 0;
    let mut v___x_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3331_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3306_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3303_, v_a_3304_);
                if leanh::lean_obj_tag(v___x_3306_) == 0 {
                    v_a_3307_ = leanh::lean_ctor_get(v___x_3306_, 0);
                    v_isSharedCheck_3323_ = (!leanh::lean_is_exclusive(v___x_3306_)) as u8;
                    if v_isSharedCheck_3323_ == 0 {
                        v___x_3309_ = v___x_3306_;
                        v_isShared_3310_ = v_isSharedCheck_3323_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3307_);
                        leanh::lean_dec(v___x_3306_);
                        v___x_3309_ = leanh::lean_box(0);
                        v_isShared_3310_ = v_isSharedCheck_3323_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3324_ = leanh::lean_ctor_get(v___x_3306_, 0);
                    v_isSharedCheck_3331_ = (!leanh::lean_is_exclusive(v___x_3306_)) as u8;
                    if v_isSharedCheck_3331_ == 0 {
                        v___x_3326_ = v___x_3306_;
                        v_isShared_3327_ = v_isSharedCheck_3331_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3324_);
                        leanh::lean_dec(v___x_3306_);
                        v___x_3326_ = leanh::lean_box(0);
                        v_isShared_3327_ = v_isSharedCheck_3331_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_vars_3311_ = leanh::lean_ctor_get(v_a_3307_, 0);
                leanh::lean_inc_ref(v_vars_3311_);
                leanh::lean_dec(v_a_3307_);
                v_size_3312_ = leanh::lean_ctor_get(v_vars_3311_, 2);
                v___x_3313_ = l_Lean_instInhabitedExpr;
                v___x_3314_ = lean_nat_dec_lt(v_x_3302_, v_size_3312_);
                if v___x_3314_ == 0 {
                    leanh::lean_dec_ref(v_vars_3311_);
                    v___x_3315_ = l_outOfBounds___redArg(v___x_3313_);
                    if v_isShared_3310_ == 0 {
                        leanh::lean_ctor_set(v___x_3309_, 0, v___x_3315_);
                        v___x_3317_ = v___x_3309_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3318_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3318_, 0, v___x_3315_);
                        v___x_3317_ = v_reuseFailAlloc_3318_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3319_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_3313_,
                        v_vars_3311_,
                        v_x_3302_,
                    );
                    leanh::lean_dec_ref(v_vars_3311_);
                    if v_isShared_3310_ == 0 {
                        leanh::lean_ctor_set(v___x_3309_, 0, v___x_3319_);
                        v___x_3321_ = v___x_3309_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3322_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3322_, 0, v___x_3319_);
                        v___x_3321_ = v_reuseFailAlloc_3322_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3317_;
            }
            3 => {
                return v___x_3321_;
            }
            4 => {
                if v_isShared_3327_ == 0 {
                    v___x_3329_ = v___x_3326_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3330_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3324_);
                    v___x_3329_ = v_reuseFailAlloc_3330_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3329_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg___boxed(
    mut v_x_3332_: *mut leanh::LeanObject,
    mut v_a_3333_: *mut leanh::LeanObject,
    mut v_a_3334_: *mut leanh::LeanObject,
    mut v_a_3335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3336_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_3332_, v_a_3333_, v_a_3334_);
    leanh::lean_dec_ref(v_a_3334_);
    leanh::lean_dec(v_a_3333_);
    leanh::lean_dec(v_x_3332_);
    return v_res_3336_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_getVar(
    mut v_x_3337_: *mut leanh::LeanObject,
    mut v_a_3338_: *mut leanh::LeanObject,
    mut v_a_3339_: *mut leanh::LeanObject,
    mut v_a_3340_: *mut leanh::LeanObject,
    mut v_a_3341_: *mut leanh::LeanObject,
    mut v_a_3342_: *mut leanh::LeanObject,
    mut v_a_3343_: *mut leanh::LeanObject,
    mut v_a_3344_: *mut leanh::LeanObject,
    mut v_a_3345_: *mut leanh::LeanObject,
    mut v_a_3346_: *mut leanh::LeanObject,
    mut v_a_3347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3349_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_3337_, v_a_3338_, v_a_3346_);
    return v___x_3349_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_getVar___boxed(
    mut v_x_3350_: *mut leanh::LeanObject,
    mut v_a_3351_: *mut leanh::LeanObject,
    mut v_a_3352_: *mut leanh::LeanObject,
    mut v_a_3353_: *mut leanh::LeanObject,
    mut v_a_3354_: *mut leanh::LeanObject,
    mut v_a_3355_: *mut leanh::LeanObject,
    mut v_a_3356_: *mut leanh::LeanObject,
    mut v_a_3357_: *mut leanh::LeanObject,
    mut v_a_3358_: *mut leanh::LeanObject,
    mut v_a_3359_: *mut leanh::LeanObject,
    mut v_a_3360_: *mut leanh::LeanObject,
    mut v_a_3361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3362_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar(
        v_x_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_,
        v_a_3358_, v_a_3359_, v_a_3360_,
    );
    leanh::lean_dec(v_a_3360_);
    leanh::lean_dec_ref(v_a_3359_);
    leanh::lean_dec(v_a_3358_);
    leanh::lean_dec_ref(v_a_3357_);
    leanh::lean_dec(v_a_3356_);
    leanh::lean_dec_ref(v_a_3355_);
    leanh::lean_dec(v_a_3354_);
    leanh::lean_dec_ref(v_a_3353_);
    leanh::lean_dec(v_a_3352_);
    leanh::lean_dec(v_a_3351_);
    leanh::lean_dec(v_x_3350_);
    return v_res_3362_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(
    mut v_keys_3363_: *mut leanh::LeanObject,
    mut v_i_3364_: *mut leanh::LeanObject,
    mut v_k_3365_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: u8 = 0;
    let mut v_k_x27_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: u8 = 0;
    let mut v___x_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3366_ = lean_array_get_size(v_keys_3363_);
                v___x_3367_ = lean_nat_dec_lt(v_i_3364_, v___x_3366_);
                if v___x_3367_ == 0 {
                    leanh::lean_dec(v_i_3364_);
                    return v___x_3367_;
                } else {
                    v_k_x27_3368_ = lean_array_fget_borrowed(v_keys_3363_, v_i_3364_);
                    v___x_3369_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_3365_,
                            v_k_x27_3368_,
                        );
                    if v___x_3369_ == 0 {
                        v___x_3370_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3371_ = lean_nat_add(v_i_3364_, v___x_3370_);
                        leanh::lean_dec(v_i_3364_);
                        v_i_3364_ = v___x_3371_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_3364_);
                        return v___x_3369_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_3373_: *mut leanh::LeanObject,
    mut v_i_3374_: *mut leanh::LeanObject,
    mut v_k_3375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3376_: u8 = 0;
    let mut v_r_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3376_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(v_keys_3373_, v_i_3374_, v_k_3375_);
    leanh::lean_dec_ref(v_k_3375_);
    leanh::lean_dec_ref(v_keys_3373_);
    v_r_3377_ = leanh::lean_box((v_res_3376_) as usize);
    return v_r_3377_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_3378_: usize = 0;
    let mut v___x_3379_: usize = 0;
    let mut v___x_3380_: usize = 0;
    v___x_3378_ = 5usize;
    v___x_3379_ = 1usize;
    v___x_3380_ = lean_usize_shift_left(v___x_3379_, v___x_3378_);
    return v___x_3380_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_3381_: usize = 0;
    let mut v___x_3382_: usize = 0;
    let mut v___x_3383_: usize = 0;
    v___x_3381_ = 1usize;
    v___x_3382_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__0);
    v___x_3383_ = lean_usize_sub(v___x_3382_, v___x_3381_);
    return v___x_3383_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(
    mut v_x_3384_: *mut leanh::LeanObject,
    mut v_x_3385_: usize,
    mut v_x_3386_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_es_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: usize = 0;
    let mut v___x_3390_: usize = 0;
    let mut v___x_3391_: usize = 0;
    let mut v_j_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: u8 = 0;
    let mut v_node_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: usize = 0;
    let mut v___x_3399_: u8 = 0;
    let mut v_ks_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3384_) == 0 {
                    v_es_3387_ = leanh::lean_ctor_get(v_x_3384_, 0);
                    v___x_3388_ = leanh::lean_box(2);
                    v___x_3389_ = 5usize;
                    v___x_3390_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__1);
                    v___x_3391_ = lean_usize_land(v_x_3385_, v___x_3390_);
                    v_j_3392_ = lean_usize_to_nat(v___x_3391_);
                    v___x_3393_ = lean_array_get_borrowed(v___x_3388_, v_es_3387_, v_j_3392_);
                    leanh::lean_dec(v_j_3392_);
                    match leanh::lean_obj_tag(v___x_3393_) {
                        0 => {
                            v_key_3394_ = leanh::lean_ctor_get(v___x_3393_, 0);
                            v___x_3395_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_3386_, v_key_3394_);
                            return v___x_3395_;
                        }
                        1 => {
                            v_node_3396_ = leanh::lean_ctor_get(v___x_3393_, 0);
                            v___x_3397_ = lean_usize_shift_right(v_x_3385_, v___x_3389_);
                            v_x_3384_ = v_node_3396_;
                            v_x_3385_ = v___x_3397_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3399_ = 0;
                            return v___x_3399_;
                        }
                    }
                } else {
                    v_ks_3400_ = leanh::lean_ctor_get(v_x_3384_, 0);
                    v___x_3401_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3402_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(v_ks_3400_, v___x_3401_, v_x_3386_);
                    return v___x_3402_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___boxed(
    mut v_x_3403_: *mut leanh::LeanObject,
    mut v_x_3404_: *mut leanh::LeanObject,
    mut v_x_3405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_853__boxed_3406_: usize = 0;
    let mut v_res_3407_: u8 = 0;
    let mut v_r_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_853__boxed_3406_ = leanh::lean_unbox_usize(v_x_3404_);
    leanh::lean_dec(v_x_3404_);
    v_res_3407_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(v_x_3403_, v_x_853__boxed_3406_, v_x_3405_);
    leanh::lean_dec_ref(v_x_3405_);
    leanh::lean_dec_ref(v_x_3403_);
    v_r_3408_ = leanh::lean_box((v_res_3407_) as usize);
    return v_r_3408_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(
    mut v_x_3409_: *mut leanh::LeanObject,
    mut v_x_3410_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3411_: u64 = 0;
    let mut v___x_3412_: usize = 0;
    let mut v___x_3413_: u8 = 0;
    v___x_3411_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_3410_);
    v___x_3412_ = lean_uint64_to_usize(v___x_3411_);
    v___x_3413_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(v_x_3409_, v___x_3412_, v_x_3410_);
    return v___x_3413_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg___boxed(
    mut v_x_3414_: *mut leanh::LeanObject,
    mut v_x_3415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3416_: u8 = 0;
    let mut v_r_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3416_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(v_x_3414_, v_x_3415_);
    leanh::lean_dec_ref(v_x_3415_);
    leanh::lean_dec_ref(v_x_3414_);
    v_r_3417_ = leanh::lean_box((v_res_3416_) as usize);
    return v_r_3417_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(
    mut v_e_3418_: *mut leanh::LeanObject,
    mut v_a_3419_: *mut leanh::LeanObject,
    mut v_a_3420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3426_: u8 = 0;
    let mut v_varMap_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: u8 = 0;
    let mut v___x_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3433_: u8 = 0;
    let mut v_a_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3437_: u8 = 0;
    let mut v___x_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3441_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3422_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3419_, v_a_3420_);
                if leanh::lean_obj_tag(v___x_3422_) == 0 {
                    v_a_3423_ = leanh::lean_ctor_get(v___x_3422_, 0);
                    v_isSharedCheck_3433_ = (!leanh::lean_is_exclusive(v___x_3422_)) as u8;
                    if v_isSharedCheck_3433_ == 0 {
                        v___x_3425_ = v___x_3422_;
                        v_isShared_3426_ = v_isSharedCheck_3433_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3423_);
                        leanh::lean_dec(v___x_3422_);
                        v___x_3425_ = leanh::lean_box(0);
                        v_isShared_3426_ = v_isSharedCheck_3433_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3434_ = leanh::lean_ctor_get(v___x_3422_, 0);
                    v_isSharedCheck_3441_ = (!leanh::lean_is_exclusive(v___x_3422_)) as u8;
                    if v_isSharedCheck_3441_ == 0 {
                        v___x_3436_ = v___x_3422_;
                        v_isShared_3437_ = v_isSharedCheck_3441_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3434_);
                        leanh::lean_dec(v___x_3422_);
                        v___x_3436_ = leanh::lean_box(0);
                        v_isShared_3437_ = v_isSharedCheck_3441_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_varMap_3427_ = leanh::lean_ctor_get(v_a_3423_, 1);
                leanh::lean_inc_ref(v_varMap_3427_);
                leanh::lean_dec(v_a_3423_);
                v___x_3428_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(v_varMap_3427_, v_e_3418_);
                leanh::lean_dec_ref(v_varMap_3427_);
                v___x_3429_ = leanh::lean_box((v___x_3428_) as usize);
                if v_isShared_3426_ == 0 {
                    leanh::lean_ctor_set(v___x_3425_, 0, v___x_3429_);
                    v___x_3431_ = v___x_3425_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3432_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3432_, 0, v___x_3429_);
                    v___x_3431_ = v_reuseFailAlloc_3432_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3431_;
            }
            3 => {
                if v_isShared_3437_ == 0 {
                    v___x_3439_ = v___x_3436_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3440_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
                    v___x_3439_ = v_reuseFailAlloc_3440_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3439_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg___boxed(
    mut v_e_3442_: *mut leanh::LeanObject,
    mut v_a_3443_: *mut leanh::LeanObject,
    mut v_a_3444_: *mut leanh::LeanObject,
    mut v_a_3445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3446_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_3442_, v_a_3443_, v_a_3444_);
    leanh::lean_dec_ref(v_a_3444_);
    leanh::lean_dec(v_a_3443_);
    leanh::lean_dec_ref(v_e_3442_);
    return v_res_3446_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_hasVar(
    mut v_e_3447_: *mut leanh::LeanObject,
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
    let mut v___x_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3459_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_3447_, v_a_3448_, v_a_3456_);
    return v___x_3459_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_hasVar___boxed(
    mut v_e_3460_: *mut leanh::LeanObject,
    mut v_a_3461_: *mut leanh::LeanObject,
    mut v_a_3462_: *mut leanh::LeanObject,
    mut v_a_3463_: *mut leanh::LeanObject,
    mut v_a_3464_: *mut leanh::LeanObject,
    mut v_a_3465_: *mut leanh::LeanObject,
    mut v_a_3466_: *mut leanh::LeanObject,
    mut v_a_3467_: *mut leanh::LeanObject,
    mut v_a_3468_: *mut leanh::LeanObject,
    mut v_a_3469_: *mut leanh::LeanObject,
    mut v_a_3470_: *mut leanh::LeanObject,
    mut v_a_3471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3472_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar(
        v_e_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_,
        v_a_3468_, v_a_3469_, v_a_3470_,
    );
    leanh::lean_dec(v_a_3470_);
    leanh::lean_dec_ref(v_a_3469_);
    leanh::lean_dec(v_a_3468_);
    leanh::lean_dec_ref(v_a_3467_);
    leanh::lean_dec(v_a_3466_);
    leanh::lean_dec_ref(v_a_3465_);
    leanh::lean_dec(v_a_3464_);
    leanh::lean_dec_ref(v_a_3463_);
    leanh::lean_dec(v_a_3462_);
    leanh::lean_dec(v_a_3461_);
    leanh::lean_dec_ref(v_e_3460_);
    return v_res_3472_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0(
    mut v_00_u03b2_3473_: *mut leanh::LeanObject,
    mut v_x_3474_: *mut leanh::LeanObject,
    mut v_x_3475_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3476_: u8 = 0;
    v___x_3476_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(v_x_3474_, v_x_3475_);
    return v___x_3476_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___boxed(
    mut v_00_u03b2_3477_: *mut leanh::LeanObject,
    mut v_x_3478_: *mut leanh::LeanObject,
    mut v_x_3479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3480_: u8 = 0;
    let mut v_r_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3480_ =
        l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0(
            v_00_u03b2_3477_,
            v_x_3478_,
            v_x_3479_,
        );
    leanh::lean_dec_ref(v_x_3479_);
    leanh::lean_dec_ref(v_x_3478_);
    v_r_3481_ = leanh::lean_box((v_res_3480_) as usize);
    return v_r_3481_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0(
    mut v_00_u03b2_3482_: *mut leanh::LeanObject,
    mut v_x_3483_: *mut leanh::LeanObject,
    mut v_x_3484_: usize,
    mut v_x_3485_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3486_: u8 = 0;
    v___x_3486_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(v_x_3483_, v_x_3484_, v_x_3485_);
    return v___x_3486_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___boxed(
    mut v_00_u03b2_3487_: *mut leanh::LeanObject,
    mut v_x_3488_: *mut leanh::LeanObject,
    mut v_x_3489_: *mut leanh::LeanObject,
    mut v_x_3490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_966__boxed_3491_: usize = 0;
    let mut v_res_3492_: u8 = 0;
    let mut v_r_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_966__boxed_3491_ = leanh::lean_unbox_usize(v_x_3489_);
    leanh::lean_dec(v_x_3489_);
    v_res_3492_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0(v_00_u03b2_3487_, v_x_3488_, v_x_966__boxed_3491_, v_x_3490_);
    leanh::lean_dec_ref(v_x_3490_);
    leanh::lean_dec_ref(v_x_3488_);
    v_r_3493_ = leanh::lean_box((v_res_3492_) as usize);
    return v_r_3493_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3494_: *mut leanh::LeanObject,
    mut v_keys_3495_: *mut leanh::LeanObject,
    mut v_vals_3496_: *mut leanh::LeanObject,
    mut v_heq_3497_: *mut leanh::LeanObject,
    mut v_i_3498_: *mut leanh::LeanObject,
    mut v_k_3499_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3500_: u8 = 0;
    v___x_3500_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(v_keys_3495_, v_i_3498_, v_k_3499_);
    return v___x_3500_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_3501_: *mut leanh::LeanObject,
    mut v_keys_3502_: *mut leanh::LeanObject,
    mut v_vals_3503_: *mut leanh::LeanObject,
    mut v_heq_3504_: *mut leanh::LeanObject,
    mut v_i_3505_: *mut leanh::LeanObject,
    mut v_k_3506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3507_: u8 = 0;
    let mut v_r_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3507_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1(v_00_u03b2_3501_, v_keys_3502_, v_vals_3503_, v_heq_3504_, v_i_3505_, v_k_3506_);
    leanh::lean_dec_ref(v_k_3506_);
    leanh::lean_dec_ref(v_vals_3503_);
    leanh::lean_dec_ref(v_keys_3502_);
    v_r_3508_ = leanh::lean_box((v_res_3507_) as usize);
    return v_r_3508_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg(
    mut v_e_3509_: *mut leanh::LeanObject,
    mut v_a_3510_: *mut leanh::LeanObject,
    mut v_a_3511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3513_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_3509_, v_a_3510_, v_a_3511_);
    return v___x_3513_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg___boxed(
    mut v_e_3514_: *mut leanh::LeanObject,
    mut v_a_3515_: *mut leanh::LeanObject,
    mut v_a_3516_: *mut leanh::LeanObject,
    mut v_a_3517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3518_ =
        l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg(v_e_3514_, v_a_3515_, v_a_3516_);
    leanh::lean_dec_ref(v_a_3516_);
    leanh::lean_dec(v_a_3515_);
    leanh::lean_dec_ref(v_e_3514_);
    return v_res_3518_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm(
    mut v_e_3519_: *mut leanh::LeanObject,
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
) -> *mut leanh::LeanObject {
    let mut v___x_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3531_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_3519_, v_a_3520_, v_a_3528_);
    return v___x_3531_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___boxed(
    mut v_e_3532_: *mut leanh::LeanObject,
    mut v_a_3533_: *mut leanh::LeanObject,
    mut v_a_3534_: *mut leanh::LeanObject,
    mut v_a_3535_: *mut leanh::LeanObject,
    mut v_a_3536_: *mut leanh::LeanObject,
    mut v_a_3537_: *mut leanh::LeanObject,
    mut v_a_3538_: *mut leanh::LeanObject,
    mut v_a_3539_: *mut leanh::LeanObject,
    mut v_a_3540_: *mut leanh::LeanObject,
    mut v_a_3541_: *mut leanh::LeanObject,
    mut v_a_3542_: *mut leanh::LeanObject,
    mut v_a_3543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3544_ = l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm(
        v_e_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_,
        v_a_3540_, v_a_3541_, v_a_3542_,
    );
    leanh::lean_dec(v_a_3542_);
    leanh::lean_dec_ref(v_a_3541_);
    leanh::lean_dec(v_a_3540_);
    leanh::lean_dec_ref(v_a_3539_);
    leanh::lean_dec(v_a_3538_);
    leanh::lean_dec_ref(v_a_3537_);
    leanh::lean_dec(v_a_3536_);
    leanh::lean_dec_ref(v_a_3535_);
    leanh::lean_dec(v_a_3534_);
    leanh::lean_dec(v_a_3533_);
    leanh::lean_dec_ref(v_e_3532_);
    return v_res_3544_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(
    mut v_x_3545_: *mut leanh::LeanObject,
    mut v_a_3546_: *mut leanh::LeanObject,
    mut v_a_3547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3553_: u8 = 0;
    let mut v___y_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: u8 = 0;
    let mut v___x_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: u8 = 0;
    let mut v___x_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_elimEqs_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: u8 = 0;
    let mut v___x_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3572_: u8 = 0;
    let mut v_a_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3576_: u8 = 0;
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3580_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3549_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3546_, v_a_3547_);
                if leanh::lean_obj_tag(v___x_3549_) == 0 {
                    v_a_3550_ = leanh::lean_ctor_get(v___x_3549_, 0);
                    v_isSharedCheck_3572_ = (!leanh::lean_is_exclusive(v___x_3549_)) as u8;
                    if v_isSharedCheck_3572_ == 0 {
                        v___x_3552_ = v___x_3549_;
                        v_isShared_3553_ = v_isSharedCheck_3572_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3550_);
                        leanh::lean_dec(v___x_3549_);
                        v___x_3552_ = leanh::lean_box(0);
                        v_isShared_3553_ = v_isSharedCheck_3572_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3573_ = leanh::lean_ctor_get(v___x_3549_, 0);
                    v_isSharedCheck_3580_ = (!leanh::lean_is_exclusive(v___x_3549_)) as u8;
                    if v_isSharedCheck_3580_ == 0 {
                        v___x_3575_ = v___x_3549_;
                        v_isShared_3576_ = v_isSharedCheck_3580_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3573_);
                        leanh::lean_dec(v___x_3549_);
                        v___x_3575_ = leanh::lean_box(0);
                        v_isShared_3576_ = v_isSharedCheck_3580_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_elimEqs_3566_ = leanh::lean_ctor_get(v_a_3550_, 10);
                leanh::lean_inc_ref(v_elimEqs_3566_);
                leanh::lean_dec(v_a_3550_);
                v_size_3567_ = leanh::lean_ctor_get(v_elimEqs_3566_, 2);
                v___x_3568_ = leanh::lean_box(0);
                v___x_3569_ = lean_nat_dec_lt(v_x_3545_, v_size_3567_);
                if v___x_3569_ == 0 {
                    leanh::lean_dec_ref(v_elimEqs_3566_);
                    v___x_3570_ = l_outOfBounds___redArg(v___x_3568_);
                    v___y_3555_ = v___x_3570_;
                    state = 2;
                    continue;
                } else {
                    v___x_3571_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_3568_,
                        v_elimEqs_3566_,
                        v_x_3545_,
                    );
                    leanh::lean_dec_ref(v_elimEqs_3566_);
                    v___y_3555_ = v___x_3571_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if leanh::lean_obj_tag(v___y_3555_) == 0 {
                    v___x_3556_ = 0;
                    v___x_3557_ = leanh::lean_box((v___x_3556_) as usize);
                    if v_isShared_3553_ == 0 {
                        leanh::lean_ctor_set(v___x_3552_, 0, v___x_3557_);
                        v___x_3559_ = v___x_3552_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3560_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3557_);
                        v___x_3559_ = v_reuseFailAlloc_3560_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___y_3555_, 1);
                    v___x_3561_ = 1;
                    v___x_3562_ = leanh::lean_box((v___x_3561_) as usize);
                    if v_isShared_3553_ == 0 {
                        leanh::lean_ctor_set(v___x_3552_, 0, v___x_3562_);
                        v___x_3564_ = v___x_3552_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3565_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___x_3562_);
                        v___x_3564_ = v_reuseFailAlloc_3565_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3559_;
            }
            4 => {
                return v___x_3564_;
            }
            5 => {
                if v_isShared_3576_ == 0 {
                    v___x_3578_ = v___x_3575_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3579_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_a_3573_);
                    v___x_3578_ = v_reuseFailAlloc_3579_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3578_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg___boxed(
    mut v_x_3581_: *mut leanh::LeanObject,
    mut v_a_3582_: *mut leanh::LeanObject,
    mut v_a_3583_: *mut leanh::LeanObject,
    mut v_a_3584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3585_ =
        l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_x_3581_, v_a_3582_, v_a_3583_);
    leanh::lean_dec_ref(v_a_3583_);
    leanh::lean_dec(v_a_3582_);
    leanh::lean_dec(v_x_3581_);
    return v_res_3585_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_eliminated(
    mut v_x_3586_: *mut leanh::LeanObject,
    mut v_a_3587_: *mut leanh::LeanObject,
    mut v_a_3588_: *mut leanh::LeanObject,
    mut v_a_3589_: *mut leanh::LeanObject,
    mut v_a_3590_: *mut leanh::LeanObject,
    mut v_a_3591_: *mut leanh::LeanObject,
    mut v_a_3592_: *mut leanh::LeanObject,
    mut v_a_3593_: *mut leanh::LeanObject,
    mut v_a_3594_: *mut leanh::LeanObject,
    mut v_a_3595_: *mut leanh::LeanObject,
    mut v_a_3596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3598_ =
        l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_x_3586_, v_a_3587_, v_a_3595_);
    return v___x_3598_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_eliminated___boxed(
    mut v_x_3599_: *mut leanh::LeanObject,
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
    mut v_a_3610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3611_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated(
        v_x_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_,
        v_a_3607_, v_a_3608_, v_a_3609_,
    );
    leanh::lean_dec(v_a_3609_);
    leanh::lean_dec_ref(v_a_3608_);
    leanh::lean_dec(v_a_3607_);
    leanh::lean_dec_ref(v_a_3606_);
    leanh::lean_dec(v_a_3605_);
    leanh::lean_dec_ref(v_a_3604_);
    leanh::lean_dec(v_a_3603_);
    leanh::lean_dec_ref(v_a_3602_);
    leanh::lean_dec(v_a_3601_);
    leanh::lean_dec(v_a_3600_);
    leanh::lean_dec(v_x_3599_);
    return v_res_3611_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_assert___boxed(
    mut v_c_3624_: *mut leanh::LeanObject,
    mut v_a_3625_: *mut leanh::LeanObject,
    mut v_a_3626_: *mut leanh::LeanObject,
    mut v_a_3627_: *mut leanh::LeanObject,
    mut v_a_3628_: *mut leanh::LeanObject,
    mut v_a_3629_: *mut leanh::LeanObject,
    mut v_a_3630_: *mut leanh::LeanObject,
    mut v_a_3631_: *mut leanh::LeanObject,
    mut v_a_3632_: *mut leanh::LeanObject,
    mut v_a_3633_: *mut leanh::LeanObject,
    mut v_a_3634_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_3635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3636_ = lean_grind_cutsat_assert_eq(
        v_c_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_,
        v_a_3632_, v_a_3633_, v_a_3634_,
    );
    return v_res_3636_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0(
    mut v_x_3637_: *mut leanh::LeanObject,
    mut v_s_3638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_vars_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_x27_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_x27_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natToIntMap_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natDef_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dvds_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lowers_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uppers_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_elimEqs_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_elimStack_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_occurs_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignment_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextCnstrId_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_caseSplits_3654_: u8 = 0;
    let mut v_conflict_x3f_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqSplits_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_divMod_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntIds_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntInfos_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntTermMap_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntVarMap_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedCommRing_3662_: u8 = 0;
    let mut v_nonlinearOccs_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3666_: u8 = 0;
    let mut v___x_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3671_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vars_3639_ = leanh::lean_ctor_get(v_s_3638_, 0);
                v_varMap_3640_ = leanh::lean_ctor_get(v_s_3638_, 1);
                v_vars_x27_3641_ = leanh::lean_ctor_get(v_s_3638_, 2);
                v_varMap_x27_3642_ = leanh::lean_ctor_get(v_s_3638_, 3);
                v_natToIntMap_3643_ = leanh::lean_ctor_get(v_s_3638_, 4);
                v_natDef_3644_ = leanh::lean_ctor_get(v_s_3638_, 5);
                v_dvds_3645_ = leanh::lean_ctor_get(v_s_3638_, 6);
                v_lowers_3646_ = leanh::lean_ctor_get(v_s_3638_, 7);
                v_uppers_3647_ = leanh::lean_ctor_get(v_s_3638_, 8);
                v_diseqs_3648_ = leanh::lean_ctor_get(v_s_3638_, 9);
                v_elimEqs_3649_ = leanh::lean_ctor_get(v_s_3638_, 10);
                v_elimStack_3650_ = leanh::lean_ctor_get(v_s_3638_, 11);
                v_occurs_3651_ = leanh::lean_ctor_get(v_s_3638_, 12);
                v_assignment_3652_ = leanh::lean_ctor_get(v_s_3638_, 13);
                v_nextCnstrId_3653_ = leanh::lean_ctor_get(v_s_3638_, 14);
                v_caseSplits_3654_ = leanh::lean_ctor_get_uint8(
                    v_s_3638_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 23) as u32,
                );
                v_conflict_x3f_3655_ = leanh::lean_ctor_get(v_s_3638_, 15);
                v_diseqSplits_3656_ = leanh::lean_ctor_get(v_s_3638_, 16);
                v_divMod_3657_ = leanh::lean_ctor_get(v_s_3638_, 17);
                v_toIntIds_3658_ = leanh::lean_ctor_get(v_s_3638_, 18);
                v_toIntInfos_3659_ = leanh::lean_ctor_get(v_s_3638_, 19);
                v_toIntTermMap_3660_ = leanh::lean_ctor_get(v_s_3638_, 20);
                v_toIntVarMap_3661_ = leanh::lean_ctor_get(v_s_3638_, 21);
                v_usedCommRing_3662_ = leanh::lean_ctor_get_uint8(
                    v_s_3638_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 23 + 1) as u32,
                );
                v_nonlinearOccs_3663_ = leanh::lean_ctor_get(v_s_3638_, 22);
                v_isSharedCheck_3671_ = (!leanh::lean_is_exclusive(v_s_3638_)) as u8;
                if v_isSharedCheck_3671_ == 0 {
                    v___x_3665_ = v_s_3638_;
                    v_isShared_3666_ = v_isSharedCheck_3671_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_nonlinearOccs_3663_);
                    leanh::lean_inc(v_toIntVarMap_3661_);
                    leanh::lean_inc(v_toIntTermMap_3660_);
                    leanh::lean_inc(v_toIntInfos_3659_);
                    leanh::lean_inc(v_toIntIds_3658_);
                    leanh::lean_inc(v_divMod_3657_);
                    leanh::lean_inc(v_diseqSplits_3656_);
                    leanh::lean_inc(v_conflict_x3f_3655_);
                    leanh::lean_inc(v_nextCnstrId_3653_);
                    leanh::lean_inc(v_assignment_3652_);
                    leanh::lean_inc(v_occurs_3651_);
                    leanh::lean_inc(v_elimStack_3650_);
                    leanh::lean_inc(v_elimEqs_3649_);
                    leanh::lean_inc(v_diseqs_3648_);
                    leanh::lean_inc(v_uppers_3647_);
                    leanh::lean_inc(v_lowers_3646_);
                    leanh::lean_inc(v_dvds_3645_);
                    leanh::lean_inc(v_natDef_3644_);
                    leanh::lean_inc(v_natToIntMap_3643_);
                    leanh::lean_inc(v_varMap_x27_3642_);
                    leanh::lean_inc(v_vars_x27_3641_);
                    leanh::lean_inc(v_varMap_3640_);
                    leanh::lean_inc(v_vars_3639_);
                    leanh::lean_dec(v_s_3638_);
                    v___x_3665_ = leanh::lean_box(0);
                    v_isShared_3666_ = v_isSharedCheck_3671_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3667_ = l_Lean_Meta_Grind_Arith_shrink(v_assignment_3652_, v_x_3637_);
                if v_isShared_3666_ == 0 {
                    leanh::lean_ctor_set(v___x_3665_, 13, v___x_3667_);
                    v___x_3669_ = v___x_3665_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3670_ = leanh::lean_alloc_ctor(0, 23, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_vars_3639_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 1, v_varMap_3640_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 2, v_vars_x27_3641_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 3, v_varMap_x27_3642_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 4, v_natToIntMap_3643_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 5, v_natDef_3644_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 6, v_dvds_3645_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 7, v_lowers_3646_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 8, v_uppers_3647_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 9, v_diseqs_3648_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 10, v_elimEqs_3649_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 11, v_elimStack_3650_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 12, v_occurs_3651_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 13, v___x_3667_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 14, v_nextCnstrId_3653_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 15, v_conflict_x3f_3655_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 16, v_diseqSplits_3656_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 17, v_divMod_3657_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 18, v_toIntIds_3658_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 19, v_toIntInfos_3659_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 20, v_toIntTermMap_3660_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 21, v_toIntVarMap_3661_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 22, v_nonlinearOccs_3663_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3670_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 23) as u32,
                        v_caseSplits_3654_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3670_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 23 + 1) as u32,
                        v_usedCommRing_3662_,
                    );
                    v___x_3669_ = v_reuseFailAlloc_3670_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3669_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0___boxed(
    mut v_x_3672_: *mut leanh::LeanObject,
    mut v_s_3673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3674_ =
        l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0(v_x_3672_, v_s_3673_);
    leanh::lean_dec(v_x_3672_);
    return v_res_3674_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(
    mut v_x_3675_: *mut leanh::LeanObject,
    mut v_a_3676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3678_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3678_, 0, v_x_3675_);
    v___x_3679_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
    v___x_3680_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3679_, v___f_3678_, v_a_3676_);
    return v___x_3680_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___boxed(
    mut v_x_3681_: *mut leanh::LeanObject,
    mut v_a_3682_: *mut leanh::LeanObject,
    mut v_a_3683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3684_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_x_3681_, v_a_3682_);
    leanh::lean_dec(v_a_3682_);
    return v_res_3684_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom(
    mut v_x_3685_: *mut leanh::LeanObject,
    mut v_a_3686_: *mut leanh::LeanObject,
    mut v_a_3687_: *mut leanh::LeanObject,
    mut v_a_3688_: *mut leanh::LeanObject,
    mut v_a_3689_: *mut leanh::LeanObject,
    mut v_a_3690_: *mut leanh::LeanObject,
    mut v_a_3691_: *mut leanh::LeanObject,
    mut v_a_3692_: *mut leanh::LeanObject,
    mut v_a_3693_: *mut leanh::LeanObject,
    mut v_a_3694_: *mut leanh::LeanObject,
    mut v_a_3695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3697_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_x_3685_, v_a_3686_);
    return v___x_3697_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___boxed(
    mut v_x_3698_: *mut leanh::LeanObject,
    mut v_a_3699_: *mut leanh::LeanObject,
    mut v_a_3700_: *mut leanh::LeanObject,
    mut v_a_3701_: *mut leanh::LeanObject,
    mut v_a_3702_: *mut leanh::LeanObject,
    mut v_a_3703_: *mut leanh::LeanObject,
    mut v_a_3704_: *mut leanh::LeanObject,
    mut v_a_3705_: *mut leanh::LeanObject,
    mut v_a_3706_: *mut leanh::LeanObject,
    mut v_a_3707_: *mut leanh::LeanObject,
    mut v_a_3708_: *mut leanh::LeanObject,
    mut v_a_3709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3710_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom(
        v_x_3698_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_,
        v_a_3706_, v_a_3707_, v_a_3708_,
    );
    leanh::lean_dec(v_a_3708_);
    leanh::lean_dec_ref(v_a_3707_);
    leanh::lean_dec(v_a_3706_);
    leanh::lean_dec_ref(v_a_3705_);
    leanh::lean_dec(v_a_3704_);
    leanh::lean_dec_ref(v_a_3703_);
    leanh::lean_dec(v_a_3702_);
    leanh::lean_dec_ref(v_a_3701_);
    leanh::lean_dec(v_a_3700_);
    leanh::lean_dec(v_a_3699_);
    return v_res_3710_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3712_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__0;
    v___x_3713_ = l_Lean_stringToMessageData(v___x_3712_);
    return v___x_3713_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3714_ = leanh::lean_unsigned_to_nat(1);
    v___x_3715_ = lean_nat_to_int(v___x_3714_);
    return v___x_3715_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3717_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__3;
    v___x_3718_ = l_Lean_stringToMessageData(v___x_3717_);
    return v___x_3718_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg(
    mut v_r_3719_: *mut leanh::LeanObject,
    mut v_p_3720_: *mut leanh::LeanObject,
    mut v_a_3721_: *mut leanh::LeanObject,
    mut v_a_3722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3727_: u8 = 0;
    let mut v___x_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: u8 = 0;
    let mut v___x_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3742_: u8 = 0;
    let mut v_k_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: u8 = 0;
    let mut v___x_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3764_: u8 = 0;
    let mut v___x_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3768_: u8 = 0;
    let mut v___x_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3779_: u8 = 0;
    let mut v___x_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3783_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_p_3720_) == 0 {
                    v_k_3724_ = leanh::lean_ctor_get(v_p_3720_, 0);
                    v_isSharedCheck_3742_ = (!leanh::lean_is_exclusive(v_p_3720_)) as u8;
                    if v_isSharedCheck_3742_ == 0 {
                        v___x_3726_ = v_p_3720_;
                        v_isShared_3727_ = v_isSharedCheck_3742_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_3724_);
                        leanh::lean_dec(v_p_3720_);
                        v___x_3726_ = leanh::lean_box(0);
                        v_isShared_3727_ = v_isSharedCheck_3742_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_3743_ = leanh::lean_ctor_get(v_p_3720_, 0);
                    leanh::lean_inc(v_k_3743_);
                    v_v_3744_ = leanh::lean_ctor_get(v_p_3720_, 1);
                    leanh::lean_inc(v_v_3744_);
                    v_p_3745_ = leanh::lean_ctor_get(v_p_3720_, 2);
                    leanh::lean_inc_ref(v_p_3745_);
                    leanh::lean_dec_ref_known(v_p_3720_, 3);
                    v___x_3746_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2);
                    v___x_3747_ = lean_int_dec_eq(v_k_3743_, v___x_3746_);
                    if v___x_3747_ == 0 {
                        v___x_3748_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(
                            v_v_3744_, v_a_3721_, v_a_3722_,
                        );
                        leanh::lean_dec(v_v_3744_);
                        if leanh::lean_obj_tag(v___x_3748_) == 0 {
                            v_a_3749_ = leanh::lean_ctor_get(v___x_3748_, 0);
                            leanh::lean_inc(v_a_3749_);
                            leanh::lean_dec_ref_known(v___x_3748_, 1);
                            v___x_3750_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1);
                            v___x_3751_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3751_, 0, v_r_3719_);
                            leanh::lean_ctor_set(v___x_3751_, 1, v___x_3750_);
                            v___x_3752_ = l_Int_repr(v_k_3743_);
                            leanh::lean_dec(v_k_3743_);
                            v___x_3753_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3753_, 0, v___x_3752_);
                            v___x_3754_ = l_Lean_MessageData_ofFormat(v___x_3753_);
                            v___x_3755_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3755_, 0, v___x_3751_);
                            leanh::lean_ctor_set(v___x_3755_, 1, v___x_3754_);
                            v___x_3756_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4);
                            v___x_3757_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3757_, 0, v___x_3755_);
                            leanh::lean_ctor_set(v___x_3757_, 1, v___x_3756_);
                            v___x_3758_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_3749_);
                            v___x_3759_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3759_, 0, v___x_3757_);
                            leanh::lean_ctor_set(v___x_3759_, 1, v___x_3758_);
                            v_r_3719_ = v___x_3759_;
                            v_p_3720_ = v_p_3745_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_p_3745_);
                            leanh::lean_dec(v_k_3743_);
                            leanh::lean_dec_ref(v_r_3719_);
                            v_a_3761_ = leanh::lean_ctor_get(v___x_3748_, 0);
                            v_isSharedCheck_3768_ =
                                (!leanh::lean_is_exclusive(v___x_3748_)) as u8;
                            if v_isSharedCheck_3768_ == 0 {
                                v___x_3763_ = v___x_3748_;
                                v_isShared_3764_ = v_isSharedCheck_3768_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3761_);
                                leanh::lean_dec(v___x_3748_);
                                v___x_3763_ = leanh::lean_box(0);
                                v_isShared_3764_ = v_isSharedCheck_3768_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_k_3743_);
                        v___x_3769_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(
                            v_v_3744_, v_a_3721_, v_a_3722_,
                        );
                        leanh::lean_dec(v_v_3744_);
                        if leanh::lean_obj_tag(v___x_3769_) == 0 {
                            v_a_3770_ = leanh::lean_ctor_get(v___x_3769_, 0);
                            leanh::lean_inc(v_a_3770_);
                            leanh::lean_dec_ref_known(v___x_3769_, 1);
                            v___x_3771_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1);
                            v___x_3772_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3772_, 0, v_r_3719_);
                            leanh::lean_ctor_set(v___x_3772_, 1, v___x_3771_);
                            v___x_3773_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_3770_);
                            v___x_3774_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3774_, 0, v___x_3772_);
                            leanh::lean_ctor_set(v___x_3774_, 1, v___x_3773_);
                            v_r_3719_ = v___x_3774_;
                            v_p_3720_ = v_p_3745_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_p_3745_);
                            leanh::lean_dec_ref(v_r_3719_);
                            v_a_3776_ = leanh::lean_ctor_get(v___x_3769_, 0);
                            v_isSharedCheck_3783_ =
                                (!leanh::lean_is_exclusive(v___x_3769_)) as u8;
                            if v_isSharedCheck_3783_ == 0 {
                                v___x_3778_ = v___x_3769_;
                                v_isShared_3779_ = v_isSharedCheck_3783_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3776_);
                                leanh::lean_dec(v___x_3769_);
                                v___x_3778_ = leanh::lean_box(0);
                                v_isShared_3779_ = v_isSharedCheck_3783_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3728_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Int_Linear_Poly_isZero___closed__0),
                    core::ptr::addr_of_mut!(l_Int_Linear_Poly_isZero___closed__0_once),
                    _init_l_Int_Linear_Poly_isZero___closed__0,
                );
                v___x_3729_ = lean_int_dec_eq(v_k_3724_, v___x_3728_);
                if v___x_3729_ == 0 {
                    v___x_3730_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1);
                    v___x_3731_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3731_, 0, v_r_3719_);
                    leanh::lean_ctor_set(v___x_3731_, 1, v___x_3730_);
                    v___x_3732_ = l_Int_repr(v_k_3724_);
                    leanh::lean_dec(v_k_3724_);
                    if v_isShared_3727_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3726_, 3);
                        leanh::lean_ctor_set(v___x_3726_, 0, v___x_3732_);
                        v___x_3734_ = v___x_3726_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3738_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 0, v___x_3732_);
                        v___x_3734_ = v_reuseFailAlloc_3738_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_k_3724_);
                    if v_isShared_3727_ == 0 {
                        leanh::lean_ctor_set(v___x_3726_, 0, v_r_3719_);
                        v___x_3740_ = v___x_3726_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3741_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_r_3719_);
                        v___x_3740_ = v_reuseFailAlloc_3741_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3735_ = l_Lean_MessageData_ofFormat(v___x_3734_);
                v___x_3736_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3736_, 0, v___x_3731_);
                leanh::lean_ctor_set(v___x_3736_, 1, v___x_3735_);
                v___x_3737_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3737_, 0, v___x_3736_);
                return v___x_3737_;
            }
            3 => {
                return v___x_3740_;
            }
            4 => {
                if v_isShared_3764_ == 0 {
                    v___x_3766_ = v___x_3763_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3767_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_a_3761_);
                    v___x_3766_ = v_reuseFailAlloc_3767_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3766_;
            }
            6 => {
                if v_isShared_3779_ == 0 {
                    v___x_3781_ = v___x_3778_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3782_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_a_3776_);
                    v___x_3781_ = v_reuseFailAlloc_3782_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3781_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___boxed(
    mut v_r_3784_: *mut leanh::LeanObject,
    mut v_p_3785_: *mut leanh::LeanObject,
    mut v_a_3786_: *mut leanh::LeanObject,
    mut v_a_3787_: *mut leanh::LeanObject,
    mut v_a_3788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3789_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg(
            v_r_3784_, v_p_3785_, v_a_3786_, v_a_3787_,
        );
    leanh::lean_dec_ref(v_a_3787_);
    leanh::lean_dec(v_a_3786_);
    return v_res_3789_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go(
    mut v_r_3790_: *mut leanh::LeanObject,
    mut v_p_3791_: *mut leanh::LeanObject,
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
) -> *mut leanh::LeanObject {
    let mut v___x_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3803_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg(
            v_r_3790_, v_p_3791_, v_a_3792_, v_a_3800_,
        );
    return v___x_3803_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___boxed(
    mut v_r_3804_: *mut leanh::LeanObject,
    mut v_p_3805_: *mut leanh::LeanObject,
    mut v_a_3806_: *mut leanh::LeanObject,
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
) -> *mut leanh::LeanObject {
    let mut v_res_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3817_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go(
        v_r_3804_, v_p_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_,
        v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_,
    );
    leanh::lean_dec(v_a_3815_);
    leanh::lean_dec_ref(v_a_3814_);
    leanh::lean_dec(v_a_3813_);
    leanh::lean_dec_ref(v_a_3812_);
    leanh::lean_dec(v_a_3811_);
    leanh::lean_dec_ref(v_a_3810_);
    leanh::lean_dec(v_a_3809_);
    leanh::lean_dec_ref(v_a_3808_);
    leanh::lean_dec(v_a_3807_);
    leanh::lean_dec(v_a_3806_);
    return v_res_3817_;
}
pub unsafe fn l_Int_Linear_Poly_pp___redArg(
    mut v_p_3818_: *mut leanh::LeanObject,
    mut v_a_3819_: *mut leanh::LeanObject,
    mut v_a_3820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3825_: u8 = 0;
    let mut v___x_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3832_: u8 = 0;
    let mut v_k_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: u8 = 0;
    let mut v___x_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3851_: u8 = 0;
    let mut v___x_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3855_: u8 = 0;
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3863_: u8 = 0;
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3867_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_p_3818_) == 0 {
                    v_k_3822_ = leanh::lean_ctor_get(v_p_3818_, 0);
                    v_isSharedCheck_3832_ = (!leanh::lean_is_exclusive(v_p_3818_)) as u8;
                    if v_isSharedCheck_3832_ == 0 {
                        v___x_3824_ = v_p_3818_;
                        v_isShared_3825_ = v_isSharedCheck_3832_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_3822_);
                        leanh::lean_dec(v_p_3818_);
                        v___x_3824_ = leanh::lean_box(0);
                        v_isShared_3825_ = v_isSharedCheck_3832_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_3833_ = leanh::lean_ctor_get(v_p_3818_, 0);
                    leanh::lean_inc(v_k_3833_);
                    v_v_3834_ = leanh::lean_ctor_get(v_p_3818_, 1);
                    leanh::lean_inc(v_v_3834_);
                    v_p_3835_ = leanh::lean_ctor_get(v_p_3818_, 2);
                    leanh::lean_inc_ref(v_p_3835_);
                    leanh::lean_dec_ref_known(v_p_3818_, 3);
                    v___x_3836_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2);
                    v___x_3837_ = lean_int_dec_eq(v_k_3833_, v___x_3836_);
                    if v___x_3837_ == 0 {
                        v___x_3838_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(
                            v_v_3834_, v_a_3819_, v_a_3820_,
                        );
                        leanh::lean_dec(v_v_3834_);
                        if leanh::lean_obj_tag(v___x_3838_) == 0 {
                            v_a_3839_ = leanh::lean_ctor_get(v___x_3838_, 0);
                            leanh::lean_inc(v_a_3839_);
                            leanh::lean_dec_ref_known(v___x_3838_, 1);
                            v___x_3840_ = l_Int_repr(v_k_3833_);
                            leanh::lean_dec(v_k_3833_);
                            v___x_3841_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3841_, 0, v___x_3840_);
                            v___x_3842_ = l_Lean_MessageData_ofFormat(v___x_3841_);
                            v___x_3843_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4);
                            v___x_3844_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3844_, 0, v___x_3842_);
                            leanh::lean_ctor_set(v___x_3844_, 1, v___x_3843_);
                            v___x_3845_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_3839_);
                            v___x_3846_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3846_, 0, v___x_3844_);
                            leanh::lean_ctor_set(v___x_3846_, 1, v___x_3845_);
                            v___x_3847_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg(v___x_3846_, v_p_3835_, v_a_3819_, v_a_3820_);
                            return v___x_3847_;
                        } else {
                            leanh::lean_dec_ref(v_p_3835_);
                            leanh::lean_dec(v_k_3833_);
                            v_a_3848_ = leanh::lean_ctor_get(v___x_3838_, 0);
                            v_isSharedCheck_3855_ =
                                (!leanh::lean_is_exclusive(v___x_3838_)) as u8;
                            if v_isSharedCheck_3855_ == 0 {
                                v___x_3850_ = v___x_3838_;
                                v_isShared_3851_ = v_isSharedCheck_3855_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3848_);
                                leanh::lean_dec(v___x_3838_);
                                v___x_3850_ = leanh::lean_box(0);
                                v_isShared_3851_ = v_isSharedCheck_3855_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_k_3833_);
                        v___x_3856_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(
                            v_v_3834_, v_a_3819_, v_a_3820_,
                        );
                        leanh::lean_dec(v_v_3834_);
                        if leanh::lean_obj_tag(v___x_3856_) == 0 {
                            v_a_3857_ = leanh::lean_ctor_get(v___x_3856_, 0);
                            leanh::lean_inc(v_a_3857_);
                            leanh::lean_dec_ref_known(v___x_3856_, 1);
                            v___x_3858_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_3857_);
                            v___x_3859_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg(v___x_3858_, v_p_3835_, v_a_3819_, v_a_3820_);
                            return v___x_3859_;
                        } else {
                            leanh::lean_dec_ref(v_p_3835_);
                            v_a_3860_ = leanh::lean_ctor_get(v___x_3856_, 0);
                            v_isSharedCheck_3867_ =
                                (!leanh::lean_is_exclusive(v___x_3856_)) as u8;
                            if v_isSharedCheck_3867_ == 0 {
                                v___x_3862_ = v___x_3856_;
                                v_isShared_3863_ = v_isSharedCheck_3867_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3860_);
                                leanh::lean_dec(v___x_3856_);
                                v___x_3862_ = leanh::lean_box(0);
                                v_isShared_3863_ = v_isSharedCheck_3867_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3826_ = l_Int_repr(v_k_3822_);
                leanh::lean_dec(v_k_3822_);
                if v_isShared_3825_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3824_, 3);
                    leanh::lean_ctor_set(v___x_3824_, 0, v___x_3826_);
                    v___x_3828_ = v___x_3824_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3831_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3826_);
                    v___x_3828_ = v_reuseFailAlloc_3831_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3829_ = l_Lean_MessageData_ofFormat(v___x_3828_);
                v___x_3830_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3830_, 0, v___x_3829_);
                return v___x_3830_;
            }
            3 => {
                if v_isShared_3851_ == 0 {
                    v___x_3853_ = v___x_3850_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3854_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_a_3848_);
                    v___x_3853_ = v_reuseFailAlloc_3854_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3853_;
            }
            5 => {
                if v_isShared_3863_ == 0 {
                    v___x_3865_ = v___x_3862_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3866_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
                    v___x_3865_ = v_reuseFailAlloc_3866_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3865_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Poly_pp___redArg___boxed(
    mut v_p_3868_: *mut leanh::LeanObject,
    mut v_a_3869_: *mut leanh::LeanObject,
    mut v_a_3870_: *mut leanh::LeanObject,
    mut v_a_3871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3872_ = l_Int_Linear_Poly_pp___redArg(v_p_3868_, v_a_3869_, v_a_3870_);
    leanh::lean_dec_ref(v_a_3870_);
    leanh::lean_dec(v_a_3869_);
    return v_res_3872_;
}
pub unsafe fn l_Int_Linear_Poly_pp(
    mut v_p_3873_: *mut leanh::LeanObject,
    mut v_a_3874_: *mut leanh::LeanObject,
    mut v_a_3875_: *mut leanh::LeanObject,
    mut v_a_3876_: *mut leanh::LeanObject,
    mut v_a_3877_: *mut leanh::LeanObject,
    mut v_a_3878_: *mut leanh::LeanObject,
    mut v_a_3879_: *mut leanh::LeanObject,
    mut v_a_3880_: *mut leanh::LeanObject,
    mut v_a_3881_: *mut leanh::LeanObject,
    mut v_a_3882_: *mut leanh::LeanObject,
    mut v_a_3883_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3885_ = l_Int_Linear_Poly_pp___redArg(v_p_3873_, v_a_3874_, v_a_3882_);
    return v___x_3885_;
}
pub unsafe fn l_Int_Linear_Poly_pp___boxed(
    mut v_p_3886_: *mut leanh::LeanObject,
    mut v_a_3887_: *mut leanh::LeanObject,
    mut v_a_3888_: *mut leanh::LeanObject,
    mut v_a_3889_: *mut leanh::LeanObject,
    mut v_a_3890_: *mut leanh::LeanObject,
    mut v_a_3891_: *mut leanh::LeanObject,
    mut v_a_3892_: *mut leanh::LeanObject,
    mut v_a_3893_: *mut leanh::LeanObject,
    mut v_a_3894_: *mut leanh::LeanObject,
    mut v_a_3895_: *mut leanh::LeanObject,
    mut v_a_3896_: *mut leanh::LeanObject,
    mut v_a_3897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3898_ = l_Int_Linear_Poly_pp(
        v_p_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_,
        v_a_3894_, v_a_3895_, v_a_3896_,
    );
    leanh::lean_dec(v_a_3896_);
    leanh::lean_dec_ref(v_a_3895_);
    leanh::lean_dec(v_a_3894_);
    leanh::lean_dec_ref(v_a_3893_);
    leanh::lean_dec(v_a_3892_);
    leanh::lean_dec_ref(v_a_3891_);
    leanh::lean_dec(v_a_3890_);
    leanh::lean_dec_ref(v_a_3889_);
    leanh::lean_dec(v_a_3888_);
    leanh::lean_dec(v_a_3887_);
    return v_res_3898_;
}
pub unsafe fn l_Int_Linear_Poly_denoteExpr_x27___redArg___lam__0(
    mut v_a_3899_: *mut leanh::LeanObject,
    mut v___x_3900_: *mut leanh::LeanObject,
    mut v_x_3901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: u8 = 0;
    v_size_3902_ = leanh::lean_ctor_get(v_a_3899_, 2);
    v___x_3903_ = lean_nat_dec_lt(v_x_3901_, v_size_3902_);
    if v___x_3903_ == 0 {
        let mut v___x_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3904_ = l_outOfBounds___redArg(v___x_3900_);
        return v___x_3904_;
    } else {
        let mut v___x_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3905_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3900_, v_a_3899_, v_x_3901_);
        return v___x_3905_;
    }
}
pub unsafe fn l_Int_Linear_Poly_denoteExpr_x27___redArg___lam__0___boxed(
    mut v_a_3906_: *mut leanh::LeanObject,
    mut v___x_3907_: *mut leanh::LeanObject,
    mut v_x_3908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3909_ =
        l_Int_Linear_Poly_denoteExpr_x27___redArg___lam__0(v_a_3906_, v___x_3907_, v_x_3908_);
    leanh::lean_dec(v_x_3908_);
    leanh::lean_dec_ref(v___x_3907_);
    leanh::lean_dec_ref(v_a_3906_);
    return v_res_3909_;
}
pub unsafe fn l_Int_Linear_Poly_denoteExpr_x27___redArg(
    mut v_p_3910_: *mut leanh::LeanObject,
    mut v_a_3911_: *mut leanh::LeanObject,
    mut v_a_3912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3922_: u8 = 0;
    let mut v___x_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3926_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3914_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(v_a_3911_, v_a_3912_);
                if leanh::lean_obj_tag(v___x_3914_) == 0 {
                    v_a_3915_ = leanh::lean_ctor_get(v___x_3914_, 0);
                    leanh::lean_inc(v_a_3915_);
                    leanh::lean_dec_ref_known(v___x_3914_, 1);
                    v___x_3916_ = l_Lean_instInhabitedExpr;
                    v___f_3917_ = leanh::lean_alloc_closure(
                        l_Int_Linear_Poly_denoteExpr_x27___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    leanh::lean_closure_set(v___f_3917_, 0, v_a_3915_);
                    leanh::lean_closure_set(v___f_3917_, 1, v___x_3916_);
                    v___x_3918_ = l_Int_Linear_Poly_denoteExpr___redArg(v___f_3917_, v_p_3910_);
                    return v___x_3918_;
                } else {
                    leanh::lean_dec_ref(v_p_3910_);
                    v_a_3919_ = leanh::lean_ctor_get(v___x_3914_, 0);
                    v_isSharedCheck_3926_ = (!leanh::lean_is_exclusive(v___x_3914_)) as u8;
                    if v_isSharedCheck_3926_ == 0 {
                        v___x_3921_ = v___x_3914_;
                        v_isShared_3922_ = v_isSharedCheck_3926_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3919_);
                        leanh::lean_dec(v___x_3914_);
                        v___x_3921_ = leanh::lean_box(0);
                        v_isShared_3922_ = v_isSharedCheck_3926_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3922_ == 0 {
                    v___x_3924_ = v___x_3921_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3925_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_a_3919_);
                    v___x_3924_ = v_reuseFailAlloc_3925_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3924_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Poly_denoteExpr_x27___redArg___boxed(
    mut v_p_3927_: *mut leanh::LeanObject,
    mut v_a_3928_: *mut leanh::LeanObject,
    mut v_a_3929_: *mut leanh::LeanObject,
    mut v_a_3930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3931_ = l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_3927_, v_a_3928_, v_a_3929_);
    leanh::lean_dec_ref(v_a_3929_);
    leanh::lean_dec(v_a_3928_);
    return v_res_3931_;
}
pub unsafe fn l_Int_Linear_Poly_denoteExpr_x27(
    mut v_p_3932_: *mut leanh::LeanObject,
    mut v_a_3933_: *mut leanh::LeanObject,
    mut v_a_3934_: *mut leanh::LeanObject,
    mut v_a_3935_: *mut leanh::LeanObject,
    mut v_a_3936_: *mut leanh::LeanObject,
    mut v_a_3937_: *mut leanh::LeanObject,
    mut v_a_3938_: *mut leanh::LeanObject,
    mut v_a_3939_: *mut leanh::LeanObject,
    mut v_a_3940_: *mut leanh::LeanObject,
    mut v_a_3941_: *mut leanh::LeanObject,
    mut v_a_3942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3944_ = l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_3932_, v_a_3933_, v_a_3941_);
    return v___x_3944_;
}
pub unsafe fn l_Int_Linear_Poly_denoteExpr_x27___boxed(
    mut v_p_3945_: *mut leanh::LeanObject,
    mut v_a_3946_: *mut leanh::LeanObject,
    mut v_a_3947_: *mut leanh::LeanObject,
    mut v_a_3948_: *mut leanh::LeanObject,
    mut v_a_3949_: *mut leanh::LeanObject,
    mut v_a_3950_: *mut leanh::LeanObject,
    mut v_a_3951_: *mut leanh::LeanObject,
    mut v_a_3952_: *mut leanh::LeanObject,
    mut v_a_3953_: *mut leanh::LeanObject,
    mut v_a_3954_: *mut leanh::LeanObject,
    mut v_a_3955_: *mut leanh::LeanObject,
    mut v_a_3956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3957_ = l_Int_Linear_Poly_denoteExpr_x27(
        v_p_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_,
        v_a_3953_, v_a_3954_, v_a_3955_,
    );
    leanh::lean_dec(v_a_3955_);
    leanh::lean_dec_ref(v_a_3954_);
    leanh::lean_dec(v_a_3953_);
    leanh::lean_dec_ref(v_a_3952_);
    leanh::lean_dec(v_a_3951_);
    leanh::lean_dec_ref(v_a_3950_);
    leanh::lean_dec(v_a_3949_);
    leanh::lean_dec_ref(v_a_3948_);
    leanh::lean_dec(v_a_3947_);
    leanh::lean_dec(v_a_3946_);
    return v_res_3957_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(
    mut v_c_3958_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_p_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_p_3959_ = leanh::lean_ctor_get(v_c_3958_, 1);
    if leanh::lean_obj_tag(v_p_3959_) == 0 {
        let mut v_d_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3964_: u8 = 0;
        v_d_3960_ = leanh::lean_ctor_get(v_c_3958_, 0);
        v_k_3961_ = leanh::lean_ctor_get(v_p_3959_, 0);
        v___x_3962_ = lean_int_emod(v_k_3961_, v_d_3960_);
        v___x_3963_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_Linear_Poly_isZero___closed__0),
            core::ptr::addr_of_mut!(l_Int_Linear_Poly_isZero___closed__0_once),
            _init_l_Int_Linear_Poly_isZero___closed__0,
        );
        v___x_3964_ = lean_int_dec_eq(v___x_3962_, v___x_3963_);
        leanh::lean_dec(v___x_3962_);
        return v___x_3964_;
    } else {
        let mut v_d_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3967_: u8 = 0;
        v_d_3965_ = leanh::lean_ctor_get(v_c_3958_, 0);
        v___x_3966_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2);
        v___x_3967_ = lean_int_dec_eq(v_d_3965_, v___x_3966_);
        return v___x_3967_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial___boxed(
    mut v_c_3968_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3969_: u8 = 0;
    let mut v_r_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3969_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v_c_3968_);
    leanh::lean_dec_ref(v_c_3968_);
    v_r_3970_ = leanh::lean_box((v_res_3969_) as usize);
    return v_r_3970_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3972_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__0;
    v___x_3973_ = l_Lean_stringToMessageData(v___x_3972_);
    return v___x_3973_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(
    mut v_c_3974_: *mut leanh::LeanObject,
    mut v_a_3975_: *mut leanh::LeanObject,
    mut v_a_3976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_d_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3984_: u8 = 0;
    let mut v___x_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3994_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_d_3978_ = leanh::lean_ctor_get(v_c_3974_, 0);
                leanh::lean_inc(v_d_3978_);
                v_p_3979_ = leanh::lean_ctor_get(v_c_3974_, 1);
                leanh::lean_inc_ref(v_p_3979_);
                leanh::lean_dec_ref(v_c_3974_);
                v___x_3980_ = l_Int_Linear_Poly_pp___redArg(v_p_3979_, v_a_3975_, v_a_3976_);
                if leanh::lean_obj_tag(v___x_3980_) == 0 {
                    v_a_3981_ = leanh::lean_ctor_get(v___x_3980_, 0);
                    v_isSharedCheck_3994_ = (!leanh::lean_is_exclusive(v___x_3980_)) as u8;
                    if v_isSharedCheck_3994_ == 0 {
                        v___x_3983_ = v___x_3980_;
                        v_isShared_3984_ = v_isSharedCheck_3994_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3981_);
                        leanh::lean_dec(v___x_3980_);
                        v___x_3983_ = leanh::lean_box(0);
                        v_isShared_3984_ = v_isSharedCheck_3994_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_d_3978_);
                    return v___x_3980_;
                }
            }
            1 => {
                v___x_3985_ = l_Int_repr(v_d_3978_);
                leanh::lean_dec(v_d_3978_);
                v___x_3986_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3986_, 0, v___x_3985_);
                v___x_3987_ = l_Lean_MessageData_ofFormat(v___x_3986_);
                v___x_3988_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1,
                );
                v___x_3989_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3989_, 0, v___x_3987_);
                leanh::lean_ctor_set(v___x_3989_, 1, v___x_3988_);
                v___x_3990_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3990_, 0, v___x_3989_);
                leanh::lean_ctor_set(v___x_3990_, 1, v_a_3981_);
                if v_isShared_3984_ == 0 {
                    leanh::lean_ctor_set(v___x_3983_, 0, v___x_3990_);
                    v___x_3992_ = v___x_3983_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3993_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3993_, 0, v___x_3990_);
                    v___x_3992_ = v_reuseFailAlloc_3993_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3992_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___boxed(
    mut v_c_3995_: *mut leanh::LeanObject,
    mut v_a_3996_: *mut leanh::LeanObject,
    mut v_a_3997_: *mut leanh::LeanObject,
    mut v_a_3998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3999_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_3995_, v_a_3996_, v_a_3997_);
    leanh::lean_dec_ref(v_a_3997_);
    leanh::lean_dec(v_a_3996_);
    return v_res_3999_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(
    mut v_c_4000_: *mut leanh::LeanObject,
    mut v_a_4001_: *mut leanh::LeanObject,
    mut v_a_4002_: *mut leanh::LeanObject,
    mut v_a_4003_: *mut leanh::LeanObject,
    mut v_a_4004_: *mut leanh::LeanObject,
    mut v_a_4005_: *mut leanh::LeanObject,
    mut v_a_4006_: *mut leanh::LeanObject,
    mut v_a_4007_: *mut leanh::LeanObject,
    mut v_a_4008_: *mut leanh::LeanObject,
    mut v_a_4009_: *mut leanh::LeanObject,
    mut v_a_4010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4012_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_4000_, v_a_4001_, v_a_4009_);
    return v___x_4012_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___boxed(
    mut v_c_4013_: *mut leanh::LeanObject,
    mut v_a_4014_: *mut leanh::LeanObject,
    mut v_a_4015_: *mut leanh::LeanObject,
    mut v_a_4016_: *mut leanh::LeanObject,
    mut v_a_4017_: *mut leanh::LeanObject,
    mut v_a_4018_: *mut leanh::LeanObject,
    mut v_a_4019_: *mut leanh::LeanObject,
    mut v_a_4020_: *mut leanh::LeanObject,
    mut v_a_4021_: *mut leanh::LeanObject,
    mut v_a_4022_: *mut leanh::LeanObject,
    mut v_a_4023_: *mut leanh::LeanObject,
    mut v_a_4024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4025_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(
        v_c_4013_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_,
        v_a_4021_, v_a_4022_, v_a_4023_,
    );
    leanh::lean_dec(v_a_4023_);
    leanh::lean_dec_ref(v_a_4022_);
    leanh::lean_dec(v_a_4021_);
    leanh::lean_dec_ref(v_a_4020_);
    leanh::lean_dec(v_a_4019_);
    leanh::lean_dec_ref(v_a_4018_);
    leanh::lean_dec(v_a_4017_);
    leanh::lean_dec_ref(v_a_4016_);
    leanh::lean_dec(v_a_4015_);
    leanh::lean_dec(v_a_4014_);
    return v_res_4025_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4031_ = leanh::lean_unsigned_to_nat(0);
    v___x_4032_ = l_Lean_Level_ofNat(v___x_4031_);
    return v___x_4032_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4033_ = leanh::lean_box(0);
    v___x_4034_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3,
    );
    v___x_4035_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4035_, 0, v___x_4034_);
    leanh::lean_ctor_set(v___x_4035_, 1, v___x_4033_);
    return v___x_4035_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4036_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4,
    );
    v___x_4037_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__2;
    v___x_4038_ = l_Lean_Expr_const___override(v___x_4037_, v___x_4036_);
    return v___x_4038_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4042_ = leanh::lean_box(0);
    v___x_4043_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__7;
    v___x_4044_ = l_Lean_Expr_const___override(v___x_4043_, v___x_4042_);
    return v___x_4044_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4049_ = leanh::lean_box(0);
    v___x_4050_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__10;
    v___x_4051_ = l_Lean_Expr_const___override(v___x_4050_, v___x_4049_);
    return v___x_4051_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(
    mut v_c_4052_: *mut leanh::LeanObject,
    mut v_a_4053_: *mut leanh::LeanObject,
    mut v_a_4054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_d_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4062_: u8 = 0;
    let mut v___y_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: u8 = 0;
    let mut v___x_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4080_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_d_4056_ = leanh::lean_ctor_get(v_c_4052_, 0);
                leanh::lean_inc(v_d_4056_);
                v_p_4057_ = leanh::lean_ctor_get(v_c_4052_, 1);
                leanh::lean_inc_ref(v_p_4057_);
                leanh::lean_dec_ref(v_c_4052_);
                v___x_4058_ =
                    l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_4057_, v_a_4053_, v_a_4054_);
                if leanh::lean_obj_tag(v___x_4058_) == 0 {
                    v_a_4059_ = leanh::lean_ctor_get(v___x_4058_, 0);
                    v_isSharedCheck_4080_ = (!leanh::lean_is_exclusive(v___x_4058_)) as u8;
                    if v_isSharedCheck_4080_ == 0 {
                        v___x_4061_ = v___x_4058_;
                        v_isShared_4062_ = v_isSharedCheck_4080_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4059_);
                        leanh::lean_dec(v___x_4058_);
                        v___x_4061_ = leanh::lean_box(0);
                        v_isShared_4062_ = v_isSharedCheck_4080_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_d_4056_);
                    return v___x_4058_;
                }
            }
            1 => {
                v___x_4069_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Int_Linear_Poly_isZero___closed__0),
                    core::ptr::addr_of_mut!(l_Int_Linear_Poly_isZero___closed__0_once),
                    _init_l_Int_Linear_Poly_isZero___closed__0,
                );
                v___x_4070_ = lean_int_dec_le(v___x_4069_, v_d_4056_);
                if v___x_4070_ == 0 {
                    v___x_4071_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5);
                    v___x_4072_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8);
                    v___x_4073_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11);
                    v___x_4074_ = lean_int_neg(v_d_4056_);
                    leanh::lean_dec(v_d_4056_);
                    v___x_4075_ = l_Int_toNat(v___x_4074_);
                    leanh::lean_dec(v___x_4074_);
                    v___x_4076_ = l_Lean_instToExprInt_mkNat(v___x_4075_);
                    v___x_4077_ = l_Lean_mkApp3(v___x_4071_, v___x_4072_, v___x_4073_, v___x_4076_);
                    v___y_4064_ = v___x_4077_;
                    state = 2;
                    continue;
                } else {
                    v___x_4078_ = l_Int_toNat(v_d_4056_);
                    leanh::lean_dec(v_d_4056_);
                    v___x_4079_ = l_Lean_instToExprInt_mkNat(v___x_4078_);
                    v___y_4064_ = v___x_4079_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4065_ = l_Lean_mkIntDvd(v___y_4064_, v_a_4059_);
                if v_isShared_4062_ == 0 {
                    leanh::lean_ctor_set(v___x_4061_, 0, v___x_4065_);
                    v___x_4067_ = v___x_4061_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4068_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4068_, 0, v___x_4065_);
                    v___x_4067_ = v_reuseFailAlloc_4068_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4067_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___boxed(
    mut v_c_4081_: *mut leanh::LeanObject,
    mut v_a_4082_: *mut leanh::LeanObject,
    mut v_a_4083_: *mut leanh::LeanObject,
    mut v_a_4084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4085_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(
        v_c_4081_, v_a_4082_, v_a_4083_,
    );
    leanh::lean_dec_ref(v_a_4083_);
    leanh::lean_dec(v_a_4082_);
    return v_res_4085_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr(
    mut v_c_4086_: *mut leanh::LeanObject,
    mut v_a_4087_: *mut leanh::LeanObject,
    mut v_a_4088_: *mut leanh::LeanObject,
    mut v_a_4089_: *mut leanh::LeanObject,
    mut v_a_4090_: *mut leanh::LeanObject,
    mut v_a_4091_: *mut leanh::LeanObject,
    mut v_a_4092_: *mut leanh::LeanObject,
    mut v_a_4093_: *mut leanh::LeanObject,
    mut v_a_4094_: *mut leanh::LeanObject,
    mut v_a_4095_: *mut leanh::LeanObject,
    mut v_a_4096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4098_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(
        v_c_4086_, v_a_4087_, v_a_4095_,
    );
    return v___x_4098_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___boxed(
    mut v_c_4099_: *mut leanh::LeanObject,
    mut v_a_4100_: *mut leanh::LeanObject,
    mut v_a_4101_: *mut leanh::LeanObject,
    mut v_a_4102_: *mut leanh::LeanObject,
    mut v_a_4103_: *mut leanh::LeanObject,
    mut v_a_4104_: *mut leanh::LeanObject,
    mut v_a_4105_: *mut leanh::LeanObject,
    mut v_a_4106_: *mut leanh::LeanObject,
    mut v_a_4107_: *mut leanh::LeanObject,
    mut v_a_4108_: *mut leanh::LeanObject,
    mut v_a_4109_: *mut leanh::LeanObject,
    mut v_a_4110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4111_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr(
        v_c_4099_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_,
        v_a_4107_, v_a_4108_, v_a_4109_,
    );
    leanh::lean_dec(v_a_4109_);
    leanh::lean_dec_ref(v_a_4108_);
    leanh::lean_dec(v_a_4107_);
    leanh::lean_dec_ref(v_a_4106_);
    leanh::lean_dec(v_a_4105_);
    leanh::lean_dec_ref(v_a_4104_);
    leanh::lean_dec(v_a_4103_);
    leanh::lean_dec_ref(v_a_4102_);
    leanh::lean_dec(v_a_4101_);
    leanh::lean_dec(v_a_4100_);
    return v_res_4111_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(
    mut v_msgData_4112_: *mut leanh::LeanObject,
    mut v___y_4113_: *mut leanh::LeanObject,
    mut v___y_4114_: *mut leanh::LeanObject,
    mut v___y_4115_: *mut leanh::LeanObject,
    mut v___y_4116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4118_ = lean_st_ref_get(v___y_4116_);
    v_env_4119_ = leanh::lean_ctor_get(v___x_4118_, 0);
    leanh::lean_inc_ref(v_env_4119_);
    leanh::lean_dec(v___x_4118_);
    v___x_4120_ = lean_st_ref_get(v___y_4114_);
    v_mctx_4121_ = leanh::lean_ctor_get(v___x_4120_, 0);
    leanh::lean_inc_ref(v_mctx_4121_);
    leanh::lean_dec(v___x_4120_);
    v_lctx_4122_ = leanh::lean_ctor_get(v___y_4113_, 2);
    v_options_4123_ = leanh::lean_ctor_get(v___y_4115_, 2);
    leanh::lean_inc_ref(v_options_4123_);
    leanh::lean_inc_ref(v_lctx_4122_);
    v___x_4124_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_4124_, 0, v_env_4119_);
    leanh::lean_ctor_set(v___x_4124_, 1, v_mctx_4121_);
    leanh::lean_ctor_set(v___x_4124_, 2, v_lctx_4122_);
    leanh::lean_ctor_set(v___x_4124_, 3, v_options_4123_);
    v___x_4125_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4125_, 0, v___x_4124_);
    leanh::lean_ctor_set(v___x_4125_, 1, v_msgData_4112_);
    v___x_4126_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4126_, 0, v___x_4125_);
    return v___x_4126_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0___boxed(
    mut v_msgData_4127_: *mut leanh::LeanObject,
    mut v___y_4128_: *mut leanh::LeanObject,
    mut v___y_4129_: *mut leanh::LeanObject,
    mut v___y_4130_: *mut leanh::LeanObject,
    mut v___y_4131_: *mut leanh::LeanObject,
    mut v___y_4132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4133_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(v_msgData_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
    leanh::lean_dec(v___y_4131_);
    leanh::lean_dec_ref(v___y_4130_);
    leanh::lean_dec(v___y_4129_);
    leanh::lean_dec_ref(v___y_4128_);
    return v_res_4133_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(
    mut v_msg_4134_: *mut leanh::LeanObject,
    mut v___y_4135_: *mut leanh::LeanObject,
    mut v___y_4136_: *mut leanh::LeanObject,
    mut v___y_4137_: *mut leanh::LeanObject,
    mut v___y_4138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4145_: u8 = 0;
    let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4150_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4140_ = leanh::lean_ctor_get(v___y_4137_, 5);
                v___x_4141_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(v_msg_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
                v_a_4142_ = leanh::lean_ctor_get(v___x_4141_, 0);
                v_isSharedCheck_4150_ = (!leanh::lean_is_exclusive(v___x_4141_)) as u8;
                if v_isSharedCheck_4150_ == 0 {
                    v___x_4144_ = v___x_4141_;
                    v_isShared_4145_ = v_isSharedCheck_4150_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4142_);
                    leanh::lean_dec(v___x_4141_);
                    v___x_4144_ = leanh::lean_box(0);
                    v_isShared_4145_ = v_isSharedCheck_4150_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_4140_);
                v___x_4146_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4146_, 0, v_ref_4140_);
                leanh::lean_ctor_set(v___x_4146_, 1, v_a_4142_);
                if v_isShared_4145_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4144_, 1);
                    leanh::lean_ctor_set(v___x_4144_, 0, v___x_4146_);
                    v___x_4148_ = v___x_4144_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4149_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4149_, 0, v___x_4146_);
                    v___x_4148_ = v_reuseFailAlloc_4149_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4148_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg___boxed(
    mut v_msg_4151_: *mut leanh::LeanObject,
    mut v___y_4152_: *mut leanh::LeanObject,
    mut v___y_4153_: *mut leanh::LeanObject,
    mut v___y_4154_: *mut leanh::LeanObject,
    mut v___y_4155_: *mut leanh::LeanObject,
    mut v___y_4156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4157_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v_msg_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_);
    leanh::lean_dec(v___y_4155_);
    leanh::lean_dec_ref(v___y_4154_);
    leanh::lean_dec(v___y_4153_);
    leanh::lean_dec_ref(v___y_4152_);
    return v_res_4157_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4159_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__0;
    v___x_4160_ = l_Lean_stringToMessageData(v___x_4159_);
    return v___x_4160_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4162_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__2;
    v___x_4163_ = l_Lean_stringToMessageData(v___x_4162_);
    return v___x_4163_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(
    mut v_c_4164_: *mut leanh::LeanObject,
    mut v_a_4165_: *mut leanh::LeanObject,
    mut v_a_4166_: *mut leanh::LeanObject,
    mut v_a_4167_: *mut leanh::LeanObject,
    mut v_a_4168_: *mut leanh::LeanObject,
    mut v_a_4169_: *mut leanh::LeanObject,
    mut v_a_4170_: *mut leanh::LeanObject,
    mut v_a_4171_: *mut leanh::LeanObject,
    mut v_a_4172_: *mut leanh::LeanObject,
    mut v_a_4173_: *mut leanh::LeanObject,
    mut v_a_4174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4187_: u8 = 0;
    let mut v___x_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4191_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4176_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(
                    v_c_4164_, v_a_4165_, v_a_4173_,
                );
                if leanh::lean_obj_tag(v___x_4176_) == 0 {
                    v_a_4177_ = leanh::lean_ctor_get(v___x_4176_, 0);
                    leanh::lean_inc(v_a_4177_);
                    leanh::lean_dec_ref_known(v___x_4176_, 1);
                    v___x_4178_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
                    v___x_4179_ = l_Lean_indentD(v_a_4177_);
                    v___x_4180_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4180_, 0, v___x_4178_);
                    leanh::lean_ctor_set(v___x_4180_, 1, v___x_4179_);
                    v___x_4181_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3);
                    v___x_4182_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4182_, 0, v___x_4180_);
                    leanh::lean_ctor_set(v___x_4182_, 1, v___x_4181_);
                    v___x_4183_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_4182_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_);
                    return v___x_4183_;
                } else {
                    v_a_4184_ = leanh::lean_ctor_get(v___x_4176_, 0);
                    v_isSharedCheck_4191_ = (!leanh::lean_is_exclusive(v___x_4176_)) as u8;
                    if v_isSharedCheck_4191_ == 0 {
                        v___x_4186_ = v___x_4176_;
                        v_isShared_4187_ = v_isSharedCheck_4191_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4184_);
                        leanh::lean_dec(v___x_4176_);
                        v___x_4186_ = leanh::lean_box(0);
                        v_isShared_4187_ = v_isSharedCheck_4191_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4187_ == 0 {
                    v___x_4189_ = v___x_4186_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4190_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4190_, 0, v_a_4184_);
                    v___x_4189_ = v_reuseFailAlloc_4190_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4189_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___boxed(
    mut v_c_4192_: *mut leanh::LeanObject,
    mut v_a_4193_: *mut leanh::LeanObject,
    mut v_a_4194_: *mut leanh::LeanObject,
    mut v_a_4195_: *mut leanh::LeanObject,
    mut v_a_4196_: *mut leanh::LeanObject,
    mut v_a_4197_: *mut leanh::LeanObject,
    mut v_a_4198_: *mut leanh::LeanObject,
    mut v_a_4199_: *mut leanh::LeanObject,
    mut v_a_4200_: *mut leanh::LeanObject,
    mut v_a_4201_: *mut leanh::LeanObject,
    mut v_a_4202_: *mut leanh::LeanObject,
    mut v_a_4203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4204_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(
        v_c_4192_, v_a_4193_, v_a_4194_, v_a_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_,
        v_a_4200_, v_a_4201_, v_a_4202_,
    );
    leanh::lean_dec(v_a_4202_);
    leanh::lean_dec_ref(v_a_4201_);
    leanh::lean_dec(v_a_4200_);
    leanh::lean_dec_ref(v_a_4199_);
    leanh::lean_dec(v_a_4198_);
    leanh::lean_dec_ref(v_a_4197_);
    leanh::lean_dec(v_a_4196_);
    leanh::lean_dec_ref(v_a_4195_);
    leanh::lean_dec(v_a_4194_);
    leanh::lean_dec(v_a_4193_);
    return v_res_4204_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(
    mut v_00_u03b1_4205_: *mut leanh::LeanObject,
    mut v_c_4206_: *mut leanh::LeanObject,
    mut v_a_4207_: *mut leanh::LeanObject,
    mut v_a_4208_: *mut leanh::LeanObject,
    mut v_a_4209_: *mut leanh::LeanObject,
    mut v_a_4210_: *mut leanh::LeanObject,
    mut v_a_4211_: *mut leanh::LeanObject,
    mut v_a_4212_: *mut leanh::LeanObject,
    mut v_a_4213_: *mut leanh::LeanObject,
    mut v_a_4214_: *mut leanh::LeanObject,
    mut v_a_4215_: *mut leanh::LeanObject,
    mut v_a_4216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4218_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(
        v_c_4206_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_,
        v_a_4214_, v_a_4215_, v_a_4216_,
    );
    return v___x_4218_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___boxed(
    mut v_00_u03b1_4219_: *mut leanh::LeanObject,
    mut v_c_4220_: *mut leanh::LeanObject,
    mut v_a_4221_: *mut leanh::LeanObject,
    mut v_a_4222_: *mut leanh::LeanObject,
    mut v_a_4223_: *mut leanh::LeanObject,
    mut v_a_4224_: *mut leanh::LeanObject,
    mut v_a_4225_: *mut leanh::LeanObject,
    mut v_a_4226_: *mut leanh::LeanObject,
    mut v_a_4227_: *mut leanh::LeanObject,
    mut v_a_4228_: *mut leanh::LeanObject,
    mut v_a_4229_: *mut leanh::LeanObject,
    mut v_a_4230_: *mut leanh::LeanObject,
    mut v_a_4231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4232_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(
        v_00_u03b1_4219_,
        v_c_4220_,
        v_a_4221_,
        v_a_4222_,
        v_a_4223_,
        v_a_4224_,
        v_a_4225_,
        v_a_4226_,
        v_a_4227_,
        v_a_4228_,
        v_a_4229_,
        v_a_4230_,
    );
    leanh::lean_dec(v_a_4230_);
    leanh::lean_dec_ref(v_a_4229_);
    leanh::lean_dec(v_a_4228_);
    leanh::lean_dec_ref(v_a_4227_);
    leanh::lean_dec(v_a_4226_);
    leanh::lean_dec_ref(v_a_4225_);
    leanh::lean_dec(v_a_4224_);
    leanh::lean_dec_ref(v_a_4223_);
    leanh::lean_dec(v_a_4222_);
    leanh::lean_dec(v_a_4221_);
    return v_res_4232_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0(
    mut v_00_u03b1_4233_: *mut leanh::LeanObject,
    mut v_msg_4234_: *mut leanh::LeanObject,
    mut v___y_4235_: *mut leanh::LeanObject,
    mut v___y_4236_: *mut leanh::LeanObject,
    mut v___y_4237_: *mut leanh::LeanObject,
    mut v___y_4238_: *mut leanh::LeanObject,
    mut v___y_4239_: *mut leanh::LeanObject,
    mut v___y_4240_: *mut leanh::LeanObject,
    mut v___y_4241_: *mut leanh::LeanObject,
    mut v___y_4242_: *mut leanh::LeanObject,
    mut v___y_4243_: *mut leanh::LeanObject,
    mut v___y_4244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4246_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v_msg_4234_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_);
    return v___x_4246_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___boxed(
    mut v_00_u03b1_4247_: *mut leanh::LeanObject,
    mut v_msg_4248_: *mut leanh::LeanObject,
    mut v___y_4249_: *mut leanh::LeanObject,
    mut v___y_4250_: *mut leanh::LeanObject,
    mut v___y_4251_: *mut leanh::LeanObject,
    mut v___y_4252_: *mut leanh::LeanObject,
    mut v___y_4253_: *mut leanh::LeanObject,
    mut v___y_4254_: *mut leanh::LeanObject,
    mut v___y_4255_: *mut leanh::LeanObject,
    mut v___y_4256_: *mut leanh::LeanObject,
    mut v___y_4257_: *mut leanh::LeanObject,
    mut v___y_4258_: *mut leanh::LeanObject,
    mut v___y_4259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4260_ =
        l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0(
            v_00_u03b1_4247_,
            v_msg_4248_,
            v___y_4249_,
            v___y_4250_,
            v___y_4251_,
            v___y_4252_,
            v___y_4253_,
            v___y_4254_,
            v___y_4255_,
            v___y_4256_,
            v___y_4257_,
            v___y_4258_,
        );
    leanh::lean_dec(v___y_4258_);
    leanh::lean_dec_ref(v___y_4257_);
    leanh::lean_dec(v___y_4256_);
    leanh::lean_dec_ref(v___y_4255_);
    leanh::lean_dec(v___y_4254_);
    leanh::lean_dec_ref(v___y_4253_);
    leanh::lean_dec(v___y_4252_);
    leanh::lean_dec_ref(v___y_4251_);
    leanh::lean_dec(v___y_4250_);
    leanh::lean_dec(v___y_4249_);
    return v_res_4260_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial_spec__0(
    mut v_a_4261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4262_ = lean_nat_to_int(v_a_4261_);
    return v___x_4262_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial(
    mut v_c_4263_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_p_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_p_4264_ = leanh::lean_ctor_get(v_c_4263_, 0);
    if leanh::lean_obj_tag(v_p_4264_) == 0 {
        let mut v_k_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4267_: u8 = 0;
        v_k_4265_ = leanh::lean_ctor_get(v_p_4264_, 0);
        v___x_4266_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_Linear_Poly_isZero___closed__0),
            core::ptr::addr_of_mut!(l_Int_Linear_Poly_isZero___closed__0_once),
            _init_l_Int_Linear_Poly_isZero___closed__0,
        );
        v___x_4267_ = lean_int_dec_eq(v_k_4265_, v___x_4266_);
        if v___x_4267_ == 0 {
            let mut v___x_4268_: u8 = 0;
            v___x_4268_ = 1;
            return v___x_4268_;
        } else {
            let mut v___x_4269_: u8 = 0;
            v___x_4269_ = 0;
            return v___x_4269_;
        }
    } else {
        let mut v___x_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4275_: u8 = 0;
        v___x_4270_ = l_Int_Linear_Poly_getConst(v_p_4264_);
        v___x_4271_ = l_Int_Linear_Poly_gcdCoeffs_x27(v_p_4264_);
        v___x_4272_ = lean_nat_to_int(v___x_4271_);
        v___x_4273_ = lean_int_emod(v___x_4270_, v___x_4272_);
        leanh::lean_dec(v___x_4272_);
        leanh::lean_dec(v___x_4270_);
        v___x_4274_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_Linear_Poly_isZero___closed__0),
            core::ptr::addr_of_mut!(l_Int_Linear_Poly_isZero___closed__0_once),
            _init_l_Int_Linear_Poly_isZero___closed__0,
        );
        v___x_4275_ = lean_int_dec_eq(v___x_4273_, v___x_4274_);
        leanh::lean_dec(v___x_4273_);
        if v___x_4275_ == 0 {
            let mut v___x_4276_: u8 = 0;
            v___x_4276_ = 1;
            return v___x_4276_;
        } else {
            let mut v___x_4277_: u8 = 0;
            v___x_4277_ = 0;
            return v___x_4277_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial___boxed(
    mut v_c_4278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4279_: u8 = 0;
    let mut v_r_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4279_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial(v_c_4278_);
    leanh::lean_dec_ref(v_c_4278_);
    v_r_4280_ = leanh::lean_box((v_res_4279_) as usize);
    return v_r_4280_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4282_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__0;
    v___x_4283_ = l_Lean_stringToMessageData(v___x_4282_);
    return v___x_4283_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(
    mut v_c_4284_: *mut leanh::LeanObject,
    mut v_a_4285_: *mut leanh::LeanObject,
    mut v_a_4286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_p_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4291_: u8 = 0;
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4296_: u8 = 0;
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4304_: u8 = 0;
    let mut v_isSharedCheck_4305_: u8 = 0;
    let mut v_unused_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_p_4288_ = leanh::lean_ctor_get(v_c_4284_, 0);
                v_isSharedCheck_4305_ = (!leanh::lean_is_exclusive(v_c_4284_)) as u8;
                if v_isSharedCheck_4305_ == 0 {
                    v_unused_4306_ = leanh::lean_ctor_get(v_c_4284_, 1);
                    leanh::lean_dec(v_unused_4306_);
                    v___x_4290_ = v_c_4284_;
                    v_isShared_4291_ = v_isSharedCheck_4305_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_p_4288_);
                    leanh::lean_dec(v_c_4284_);
                    v___x_4290_ = leanh::lean_box(0);
                    v_isShared_4291_ = v_isSharedCheck_4305_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4292_ = l_Int_Linear_Poly_pp___redArg(v_p_4288_, v_a_4285_, v_a_4286_);
                if leanh::lean_obj_tag(v___x_4292_) == 0 {
                    v_a_4293_ = leanh::lean_ctor_get(v___x_4292_, 0);
                    v_isSharedCheck_4304_ = (!leanh::lean_is_exclusive(v___x_4292_)) as u8;
                    if v_isSharedCheck_4304_ == 0 {
                        v___x_4295_ = v___x_4292_;
                        v_isShared_4296_ = v_isSharedCheck_4304_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4293_);
                        leanh::lean_dec(v___x_4292_);
                        v___x_4295_ = leanh::lean_box(0);
                        v_isShared_4296_ = v_isSharedCheck_4304_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4290_);
                    return v___x_4292_;
                }
            }
            2 => {
                v___x_4297_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1,
                );
                if v_isShared_4291_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4290_, 7);
                    leanh::lean_ctor_set(v___x_4290_, 1, v___x_4297_);
                    leanh::lean_ctor_set(v___x_4290_, 0, v_a_4293_);
                    v___x_4299_ = v___x_4290_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4303_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4303_, 0, v_a_4293_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4303_, 1, v___x_4297_);
                    v___x_4299_ = v_reuseFailAlloc_4303_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4296_ == 0 {
                    leanh::lean_ctor_set(v___x_4295_, 0, v___x_4299_);
                    v___x_4301_ = v___x_4295_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4302_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4302_, 0, v___x_4299_);
                    v___x_4301_ = v_reuseFailAlloc_4302_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4301_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___boxed(
    mut v_c_4307_: *mut leanh::LeanObject,
    mut v_a_4308_: *mut leanh::LeanObject,
    mut v_a_4309_: *mut leanh::LeanObject,
    mut v_a_4310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4311_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_4307_, v_a_4308_, v_a_4309_);
    leanh::lean_dec_ref(v_a_4309_);
    leanh::lean_dec(v_a_4308_);
    return v_res_4311_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(
    mut v_c_4312_: *mut leanh::LeanObject,
    mut v_a_4313_: *mut leanh::LeanObject,
    mut v_a_4314_: *mut leanh::LeanObject,
    mut v_a_4315_: *mut leanh::LeanObject,
    mut v_a_4316_: *mut leanh::LeanObject,
    mut v_a_4317_: *mut leanh::LeanObject,
    mut v_a_4318_: *mut leanh::LeanObject,
    mut v_a_4319_: *mut leanh::LeanObject,
    mut v_a_4320_: *mut leanh::LeanObject,
    mut v_a_4321_: *mut leanh::LeanObject,
    mut v_a_4322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4324_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_4312_, v_a_4313_, v_a_4321_);
    return v___x_4324_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___boxed(
    mut v_c_4325_: *mut leanh::LeanObject,
    mut v_a_4326_: *mut leanh::LeanObject,
    mut v_a_4327_: *mut leanh::LeanObject,
    mut v_a_4328_: *mut leanh::LeanObject,
    mut v_a_4329_: *mut leanh::LeanObject,
    mut v_a_4330_: *mut leanh::LeanObject,
    mut v_a_4331_: *mut leanh::LeanObject,
    mut v_a_4332_: *mut leanh::LeanObject,
    mut v_a_4333_: *mut leanh::LeanObject,
    mut v_a_4334_: *mut leanh::LeanObject,
    mut v_a_4335_: *mut leanh::LeanObject,
    mut v_a_4336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4337_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(
        v_c_4325_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_, v_a_4331_, v_a_4332_,
        v_a_4333_, v_a_4334_, v_a_4335_,
    );
    leanh::lean_dec(v_a_4335_);
    leanh::lean_dec_ref(v_a_4334_);
    leanh::lean_dec(v_a_4333_);
    leanh::lean_dec_ref(v_a_4332_);
    leanh::lean_dec(v_a_4331_);
    leanh::lean_dec_ref(v_a_4330_);
    leanh::lean_dec(v_a_4329_);
    leanh::lean_dec_ref(v_a_4328_);
    leanh::lean_dec(v_a_4327_);
    leanh::lean_dec(v_a_4326_);
    return v_res_4337_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(
    mut v_c_4338_: *mut leanh::LeanObject,
    mut v_a_4339_: *mut leanh::LeanObject,
    mut v_a_4340_: *mut leanh::LeanObject,
    mut v_a_4341_: *mut leanh::LeanObject,
    mut v_a_4342_: *mut leanh::LeanObject,
    mut v_a_4343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4354_: u8 = 0;
    let mut v___x_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4358_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4345_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(
                    v_c_4338_, v_a_4339_, v_a_4342_,
                );
                if leanh::lean_obj_tag(v___x_4345_) == 0 {
                    v_a_4346_ = leanh::lean_ctor_get(v___x_4345_, 0);
                    leanh::lean_inc(v_a_4346_);
                    leanh::lean_dec_ref_known(v___x_4345_, 1);
                    v___x_4347_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
                    v___x_4348_ = l_Lean_indentD(v_a_4346_);
                    v___x_4349_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4349_, 0, v___x_4347_);
                    leanh::lean_ctor_set(v___x_4349_, 1, v___x_4348_);
                    v___x_4350_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_4349_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_);
                    return v___x_4350_;
                } else {
                    v_a_4351_ = leanh::lean_ctor_get(v___x_4345_, 0);
                    v_isSharedCheck_4358_ = (!leanh::lean_is_exclusive(v___x_4345_)) as u8;
                    if v_isSharedCheck_4358_ == 0 {
                        v___x_4353_ = v___x_4345_;
                        v_isShared_4354_ = v_isSharedCheck_4358_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4351_);
                        leanh::lean_dec(v___x_4345_);
                        v___x_4353_ = leanh::lean_box(0);
                        v_isShared_4354_ = v_isSharedCheck_4358_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4354_ == 0 {
                    v___x_4356_ = v___x_4353_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4357_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4357_, 0, v_a_4351_);
                    v___x_4356_ = v_reuseFailAlloc_4357_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4356_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg___boxed(
    mut v_c_4359_: *mut leanh::LeanObject,
    mut v_a_4360_: *mut leanh::LeanObject,
    mut v_a_4361_: *mut leanh::LeanObject,
    mut v_a_4362_: *mut leanh::LeanObject,
    mut v_a_4363_: *mut leanh::LeanObject,
    mut v_a_4364_: *mut leanh::LeanObject,
    mut v_a_4365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4366_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(
        v_c_4359_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_,
    );
    leanh::lean_dec(v_a_4364_);
    leanh::lean_dec_ref(v_a_4363_);
    leanh::lean_dec(v_a_4362_);
    leanh::lean_dec_ref(v_a_4361_);
    leanh::lean_dec(v_a_4360_);
    return v_res_4366_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected(
    mut v_00_u03b1_4367_: *mut leanh::LeanObject,
    mut v_c_4368_: *mut leanh::LeanObject,
    mut v_a_4369_: *mut leanh::LeanObject,
    mut v_a_4370_: *mut leanh::LeanObject,
    mut v_a_4371_: *mut leanh::LeanObject,
    mut v_a_4372_: *mut leanh::LeanObject,
    mut v_a_4373_: *mut leanh::LeanObject,
    mut v_a_4374_: *mut leanh::LeanObject,
    mut v_a_4375_: *mut leanh::LeanObject,
    mut v_a_4376_: *mut leanh::LeanObject,
    mut v_a_4377_: *mut leanh::LeanObject,
    mut v_a_4378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4380_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(
        v_c_4368_, v_a_4369_, v_a_4375_, v_a_4376_, v_a_4377_, v_a_4378_,
    );
    return v___x_4380_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___boxed(
    mut v_00_u03b1_4381_: *mut leanh::LeanObject,
    mut v_c_4382_: *mut leanh::LeanObject,
    mut v_a_4383_: *mut leanh::LeanObject,
    mut v_a_4384_: *mut leanh::LeanObject,
    mut v_a_4385_: *mut leanh::LeanObject,
    mut v_a_4386_: *mut leanh::LeanObject,
    mut v_a_4387_: *mut leanh::LeanObject,
    mut v_a_4388_: *mut leanh::LeanObject,
    mut v_a_4389_: *mut leanh::LeanObject,
    mut v_a_4390_: *mut leanh::LeanObject,
    mut v_a_4391_: *mut leanh::LeanObject,
    mut v_a_4392_: *mut leanh::LeanObject,
    mut v_a_4393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4394_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected(
        v_00_u03b1_4381_,
        v_c_4382_,
        v_a_4383_,
        v_a_4384_,
        v_a_4385_,
        v_a_4386_,
        v_a_4387_,
        v_a_4388_,
        v_a_4389_,
        v_a_4390_,
        v_a_4391_,
        v_a_4392_,
    );
    leanh::lean_dec(v_a_4392_);
    leanh::lean_dec_ref(v_a_4391_);
    leanh::lean_dec(v_a_4390_);
    leanh::lean_dec_ref(v_a_4389_);
    leanh::lean_dec(v_a_4388_);
    leanh::lean_dec_ref(v_a_4387_);
    leanh::lean_dec(v_a_4386_);
    leanh::lean_dec_ref(v_a_4385_);
    leanh::lean_dec(v_a_4384_);
    leanh::lean_dec(v_a_4383_);
    return v_res_4394_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4395_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_Linear_Poly_isZero___closed__0),
        core::ptr::addr_of_mut!(l_Int_Linear_Poly_isZero___closed__0_once),
        _init_l_Int_Linear_Poly_isZero___closed__0,
    );
    v___x_4396_ = l_Lean_mkIntLit(v___x_4395_);
    return v___x_4396_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(
    mut v_c_4397_: *mut leanh::LeanObject,
    mut v_a_4398_: *mut leanh::LeanObject,
    mut v_a_4399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_p_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4406_: u8 = 0;
    let mut v___x_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4413_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_p_4401_ = leanh::lean_ctor_get(v_c_4397_, 0);
                leanh::lean_inc_ref(v_p_4401_);
                leanh::lean_dec_ref(v_c_4397_);
                v___x_4402_ =
                    l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_4401_, v_a_4398_, v_a_4399_);
                if leanh::lean_obj_tag(v___x_4402_) == 0 {
                    v_a_4403_ = leanh::lean_ctor_get(v___x_4402_, 0);
                    v_isSharedCheck_4413_ = (!leanh::lean_is_exclusive(v___x_4402_)) as u8;
                    if v_isSharedCheck_4413_ == 0 {
                        v___x_4405_ = v___x_4402_;
                        v_isShared_4406_ = v_isSharedCheck_4413_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4403_);
                        leanh::lean_dec(v___x_4402_);
                        v___x_4405_ = leanh::lean_box(0);
                        v_isShared_4406_ = v_isSharedCheck_4413_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_4402_;
                }
            }
            1 => {
                v___x_4407_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
                v___x_4408_ = l_Lean_mkIntEq(v_a_4403_, v___x_4407_);
                v___x_4409_ = l_Lean_mkNot(v___x_4408_);
                if v_isShared_4406_ == 0 {
                    leanh::lean_ctor_set(v___x_4405_, 0, v___x_4409_);
                    v___x_4411_ = v___x_4405_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4412_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4412_, 0, v___x_4409_);
                    v___x_4411_ = v_reuseFailAlloc_4412_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4411_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___boxed(
    mut v_c_4414_: *mut leanh::LeanObject,
    mut v_a_4415_: *mut leanh::LeanObject,
    mut v_a_4416_: *mut leanh::LeanObject,
    mut v_a_4417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4418_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(
        v_c_4414_, v_a_4415_, v_a_4416_,
    );
    leanh::lean_dec_ref(v_a_4416_);
    leanh::lean_dec(v_a_4415_);
    return v_res_4418_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(
    mut v_c_4419_: *mut leanh::LeanObject,
    mut v_a_4420_: *mut leanh::LeanObject,
    mut v_a_4421_: *mut leanh::LeanObject,
    mut v_a_4422_: *mut leanh::LeanObject,
    mut v_a_4423_: *mut leanh::LeanObject,
    mut v_a_4424_: *mut leanh::LeanObject,
    mut v_a_4425_: *mut leanh::LeanObject,
    mut v_a_4426_: *mut leanh::LeanObject,
    mut v_a_4427_: *mut leanh::LeanObject,
    mut v_a_4428_: *mut leanh::LeanObject,
    mut v_a_4429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4431_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(
        v_c_4419_, v_a_4420_, v_a_4428_,
    );
    return v___x_4431_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___boxed(
    mut v_c_4432_: *mut leanh::LeanObject,
    mut v_a_4433_: *mut leanh::LeanObject,
    mut v_a_4434_: *mut leanh::LeanObject,
    mut v_a_4435_: *mut leanh::LeanObject,
    mut v_a_4436_: *mut leanh::LeanObject,
    mut v_a_4437_: *mut leanh::LeanObject,
    mut v_a_4438_: *mut leanh::LeanObject,
    mut v_a_4439_: *mut leanh::LeanObject,
    mut v_a_4440_: *mut leanh::LeanObject,
    mut v_a_4441_: *mut leanh::LeanObject,
    mut v_a_4442_: *mut leanh::LeanObject,
    mut v_a_4443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4444_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(
        v_c_4432_, v_a_4433_, v_a_4434_, v_a_4435_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_,
        v_a_4440_, v_a_4441_, v_a_4442_,
    );
    leanh::lean_dec(v_a_4442_);
    leanh::lean_dec_ref(v_a_4441_);
    leanh::lean_dec(v_a_4440_);
    leanh::lean_dec_ref(v_a_4439_);
    leanh::lean_dec(v_a_4438_);
    leanh::lean_dec_ref(v_a_4437_);
    leanh::lean_dec(v_a_4436_);
    leanh::lean_dec_ref(v_a_4435_);
    leanh::lean_dec(v_a_4434_);
    leanh::lean_dec(v_a_4433_);
    return v_res_4444_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assert___boxed(
    mut v_c_4457_: *mut leanh::LeanObject,
    mut v_a_4458_: *mut leanh::LeanObject,
    mut v_a_4459_: *mut leanh::LeanObject,
    mut v_a_4460_: *mut leanh::LeanObject,
    mut v_a_4461_: *mut leanh::LeanObject,
    mut v_a_4462_: *mut leanh::LeanObject,
    mut v_a_4463_: *mut leanh::LeanObject,
    mut v_a_4464_: *mut leanh::LeanObject,
    mut v_a_4465_: *mut leanh::LeanObject,
    mut v_a_4466_: *mut leanh::LeanObject,
    mut v_a_4467_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_4468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4469_ = lean_grind_cutsat_assert_le(
        v_c_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_, v_a_4463_, v_a_4464_,
        v_a_4465_, v_a_4466_, v_a_4467_,
    );
    return v_res_4469_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(
    mut v_c_4470_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_p_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_p_4471_ = leanh::lean_ctor_get(v_c_4470_, 0);
    if leanh::lean_obj_tag(v_p_4471_) == 0 {
        let mut v_k_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4474_: u8 = 0;
        v_k_4472_ = leanh::lean_ctor_get(v_p_4471_, 0);
        v___x_4473_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_Linear_Poly_isZero___closed__0),
            core::ptr::addr_of_mut!(l_Int_Linear_Poly_isZero___closed__0_once),
            _init_l_Int_Linear_Poly_isZero___closed__0,
        );
        v___x_4474_ = lean_int_dec_le(v_k_4472_, v___x_4473_);
        return v___x_4474_;
    } else {
        let mut v___x_4475_: u8 = 0;
        v___x_4475_ = 0;
        return v___x_4475_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial___boxed(
    mut v_c_4476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4477_: u8 = 0;
    let mut v_r_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4477_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(v_c_4476_);
    leanh::lean_dec_ref(v_c_4476_);
    v_r_4478_ = leanh::lean_box((v_res_4477_) as usize);
    return v_r_4478_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4480_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__0;
    v___x_4481_ = l_Lean_stringToMessageData(v___x_4480_);
    return v___x_4481_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(
    mut v_c_4482_: *mut leanh::LeanObject,
    mut v_a_4483_: *mut leanh::LeanObject,
    mut v_a_4484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_p_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4489_: u8 = 0;
    let mut v___x_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4494_: u8 = 0;
    let mut v___x_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4502_: u8 = 0;
    let mut v_isSharedCheck_4503_: u8 = 0;
    let mut v_unused_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_p_4486_ = leanh::lean_ctor_get(v_c_4482_, 0);
                v_isSharedCheck_4503_ = (!leanh::lean_is_exclusive(v_c_4482_)) as u8;
                if v_isSharedCheck_4503_ == 0 {
                    v_unused_4504_ = leanh::lean_ctor_get(v_c_4482_, 1);
                    leanh::lean_dec(v_unused_4504_);
                    v___x_4488_ = v_c_4482_;
                    v_isShared_4489_ = v_isSharedCheck_4503_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_p_4486_);
                    leanh::lean_dec(v_c_4482_);
                    v___x_4488_ = leanh::lean_box(0);
                    v_isShared_4489_ = v_isSharedCheck_4503_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4490_ = l_Int_Linear_Poly_pp___redArg(v_p_4486_, v_a_4483_, v_a_4484_);
                if leanh::lean_obj_tag(v___x_4490_) == 0 {
                    v_a_4491_ = leanh::lean_ctor_get(v___x_4490_, 0);
                    v_isSharedCheck_4502_ = (!leanh::lean_is_exclusive(v___x_4490_)) as u8;
                    if v_isSharedCheck_4502_ == 0 {
                        v___x_4493_ = v___x_4490_;
                        v_isShared_4494_ = v_isSharedCheck_4502_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4491_);
                        leanh::lean_dec(v___x_4490_);
                        v___x_4493_ = leanh::lean_box(0);
                        v_isShared_4494_ = v_isSharedCheck_4502_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4488_);
                    return v___x_4490_;
                }
            }
            2 => {
                v___x_4495_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1,
                );
                if v_isShared_4489_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4488_, 7);
                    leanh::lean_ctor_set(v___x_4488_, 1, v___x_4495_);
                    leanh::lean_ctor_set(v___x_4488_, 0, v_a_4491_);
                    v___x_4497_ = v___x_4488_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4501_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4501_, 0, v_a_4491_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4501_, 1, v___x_4495_);
                    v___x_4497_ = v_reuseFailAlloc_4501_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4494_ == 0 {
                    leanh::lean_ctor_set(v___x_4493_, 0, v___x_4497_);
                    v___x_4499_ = v___x_4493_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4500_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4500_, 0, v___x_4497_);
                    v___x_4499_ = v_reuseFailAlloc_4500_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4499_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___boxed(
    mut v_c_4505_: *mut leanh::LeanObject,
    mut v_a_4506_: *mut leanh::LeanObject,
    mut v_a_4507_: *mut leanh::LeanObject,
    mut v_a_4508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4509_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_4505_, v_a_4506_, v_a_4507_);
    leanh::lean_dec_ref(v_a_4507_);
    leanh::lean_dec(v_a_4506_);
    return v_res_4509_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(
    mut v_c_4510_: *mut leanh::LeanObject,
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
) -> *mut leanh::LeanObject {
    let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4522_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_4510_, v_a_4511_, v_a_4519_);
    return v___x_4522_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___boxed(
    mut v_c_4523_: *mut leanh::LeanObject,
    mut v_a_4524_: *mut leanh::LeanObject,
    mut v_a_4525_: *mut leanh::LeanObject,
    mut v_a_4526_: *mut leanh::LeanObject,
    mut v_a_4527_: *mut leanh::LeanObject,
    mut v_a_4528_: *mut leanh::LeanObject,
    mut v_a_4529_: *mut leanh::LeanObject,
    mut v_a_4530_: *mut leanh::LeanObject,
    mut v_a_4531_: *mut leanh::LeanObject,
    mut v_a_4532_: *mut leanh::LeanObject,
    mut v_a_4533_: *mut leanh::LeanObject,
    mut v_a_4534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4535_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(
        v_c_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_,
        v_a_4531_, v_a_4532_, v_a_4533_,
    );
    leanh::lean_dec(v_a_4533_);
    leanh::lean_dec_ref(v_a_4532_);
    leanh::lean_dec(v_a_4531_);
    leanh::lean_dec_ref(v_a_4530_);
    leanh::lean_dec(v_a_4529_);
    leanh::lean_dec_ref(v_a_4528_);
    leanh::lean_dec(v_a_4527_);
    leanh::lean_dec_ref(v_a_4526_);
    leanh::lean_dec(v_a_4525_);
    leanh::lean_dec(v_a_4524_);
    return v_res_4535_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(
    mut v_c_4536_: *mut leanh::LeanObject,
    mut v_a_4537_: *mut leanh::LeanObject,
    mut v_a_4538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_p_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4545_: u8 = 0;
    let mut v___x_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4551_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_p_4540_ = leanh::lean_ctor_get(v_c_4536_, 0);
                leanh::lean_inc_ref(v_p_4540_);
                leanh::lean_dec_ref(v_c_4536_);
                v___x_4541_ =
                    l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_4540_, v_a_4537_, v_a_4538_);
                if leanh::lean_obj_tag(v___x_4541_) == 0 {
                    v_a_4542_ = leanh::lean_ctor_get(v___x_4541_, 0);
                    v_isSharedCheck_4551_ = (!leanh::lean_is_exclusive(v___x_4541_)) as u8;
                    if v_isSharedCheck_4551_ == 0 {
                        v___x_4544_ = v___x_4541_;
                        v_isShared_4545_ = v_isSharedCheck_4551_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4542_);
                        leanh::lean_dec(v___x_4541_);
                        v___x_4544_ = leanh::lean_box(0);
                        v_isShared_4545_ = v_isSharedCheck_4551_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_4541_;
                }
            }
            1 => {
                v___x_4546_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
                v___x_4547_ = l_Lean_mkIntLE(v_a_4542_, v___x_4546_);
                if v_isShared_4545_ == 0 {
                    leanh::lean_ctor_set(v___x_4544_, 0, v___x_4547_);
                    v___x_4549_ = v___x_4544_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4550_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4550_, 0, v___x_4547_);
                    v___x_4549_ = v_reuseFailAlloc_4550_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4549_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg___boxed(
    mut v_c_4552_: *mut leanh::LeanObject,
    mut v_a_4553_: *mut leanh::LeanObject,
    mut v_a_4554_: *mut leanh::LeanObject,
    mut v_a_4555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4556_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(v_c_4552_, v_a_4553_, v_a_4554_);
    leanh::lean_dec_ref(v_a_4554_);
    leanh::lean_dec(v_a_4553_);
    return v_res_4556_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(
    mut v_c_4557_: *mut leanh::LeanObject,
    mut v_a_4558_: *mut leanh::LeanObject,
    mut v_a_4559_: *mut leanh::LeanObject,
    mut v_a_4560_: *mut leanh::LeanObject,
    mut v_a_4561_: *mut leanh::LeanObject,
    mut v_a_4562_: *mut leanh::LeanObject,
    mut v_a_4563_: *mut leanh::LeanObject,
    mut v_a_4564_: *mut leanh::LeanObject,
    mut v_a_4565_: *mut leanh::LeanObject,
    mut v_a_4566_: *mut leanh::LeanObject,
    mut v_a_4567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4569_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(v_c_4557_, v_a_4558_, v_a_4566_);
    return v___x_4569_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___boxed(
    mut v_c_4570_: *mut leanh::LeanObject,
    mut v_a_4571_: *mut leanh::LeanObject,
    mut v_a_4572_: *mut leanh::LeanObject,
    mut v_a_4573_: *mut leanh::LeanObject,
    mut v_a_4574_: *mut leanh::LeanObject,
    mut v_a_4575_: *mut leanh::LeanObject,
    mut v_a_4576_: *mut leanh::LeanObject,
    mut v_a_4577_: *mut leanh::LeanObject,
    mut v_a_4578_: *mut leanh::LeanObject,
    mut v_a_4579_: *mut leanh::LeanObject,
    mut v_a_4580_: *mut leanh::LeanObject,
    mut v_a_4581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4582_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(
        v_c_4570_, v_a_4571_, v_a_4572_, v_a_4573_, v_a_4574_, v_a_4575_, v_a_4576_, v_a_4577_,
        v_a_4578_, v_a_4579_, v_a_4580_,
    );
    leanh::lean_dec(v_a_4580_);
    leanh::lean_dec_ref(v_a_4579_);
    leanh::lean_dec(v_a_4578_);
    leanh::lean_dec_ref(v_a_4577_);
    leanh::lean_dec(v_a_4576_);
    leanh::lean_dec_ref(v_a_4575_);
    leanh::lean_dec(v_a_4574_);
    leanh::lean_dec_ref(v_a_4573_);
    leanh::lean_dec(v_a_4572_);
    leanh::lean_dec(v_a_4571_);
    return v_res_4582_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(
    mut v_c_4583_: *mut leanh::LeanObject,
    mut v_a_4584_: *mut leanh::LeanObject,
    mut v_a_4585_: *mut leanh::LeanObject,
    mut v_a_4586_: *mut leanh::LeanObject,
    mut v_a_4587_: *mut leanh::LeanObject,
    mut v_a_4588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4599_: u8 = 0;
    let mut v___x_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4603_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4590_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(
                    v_c_4583_, v_a_4584_, v_a_4587_,
                );
                if leanh::lean_obj_tag(v___x_4590_) == 0 {
                    v_a_4591_ = leanh::lean_ctor_get(v___x_4590_, 0);
                    leanh::lean_inc(v_a_4591_);
                    leanh::lean_dec_ref_known(v___x_4590_, 1);
                    v___x_4592_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
                    v___x_4593_ = l_Lean_indentD(v_a_4591_);
                    v___x_4594_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4594_, 0, v___x_4592_);
                    leanh::lean_ctor_set(v___x_4594_, 1, v___x_4593_);
                    v___x_4595_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_4594_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_);
                    return v___x_4595_;
                } else {
                    v_a_4596_ = leanh::lean_ctor_get(v___x_4590_, 0);
                    v_isSharedCheck_4603_ = (!leanh::lean_is_exclusive(v___x_4590_)) as u8;
                    if v_isSharedCheck_4603_ == 0 {
                        v___x_4598_ = v___x_4590_;
                        v_isShared_4599_ = v_isSharedCheck_4603_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4596_);
                        leanh::lean_dec(v___x_4590_);
                        v___x_4598_ = leanh::lean_box(0);
                        v_isShared_4599_ = v_isSharedCheck_4603_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4599_ == 0 {
                    v___x_4601_ = v___x_4598_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4602_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4602_, 0, v_a_4596_);
                    v___x_4601_ = v_reuseFailAlloc_4602_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4601_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg___boxed(
    mut v_c_4604_: *mut leanh::LeanObject,
    mut v_a_4605_: *mut leanh::LeanObject,
    mut v_a_4606_: *mut leanh::LeanObject,
    mut v_a_4607_: *mut leanh::LeanObject,
    mut v_a_4608_: *mut leanh::LeanObject,
    mut v_a_4609_: *mut leanh::LeanObject,
    mut v_a_4610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4611_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(
        v_c_4604_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_,
    );
    leanh::lean_dec(v_a_4609_);
    leanh::lean_dec_ref(v_a_4608_);
    leanh::lean_dec(v_a_4607_);
    leanh::lean_dec_ref(v_a_4606_);
    leanh::lean_dec(v_a_4605_);
    return v_res_4611_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected(
    mut v_00_u03b1_4612_: *mut leanh::LeanObject,
    mut v_c_4613_: *mut leanh::LeanObject,
    mut v_a_4614_: *mut leanh::LeanObject,
    mut v_a_4615_: *mut leanh::LeanObject,
    mut v_a_4616_: *mut leanh::LeanObject,
    mut v_a_4617_: *mut leanh::LeanObject,
    mut v_a_4618_: *mut leanh::LeanObject,
    mut v_a_4619_: *mut leanh::LeanObject,
    mut v_a_4620_: *mut leanh::LeanObject,
    mut v_a_4621_: *mut leanh::LeanObject,
    mut v_a_4622_: *mut leanh::LeanObject,
    mut v_a_4623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4625_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(
        v_c_4613_, v_a_4614_, v_a_4620_, v_a_4621_, v_a_4622_, v_a_4623_,
    );
    return v___x_4625_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___boxed(
    mut v_00_u03b1_4626_: *mut leanh::LeanObject,
    mut v_c_4627_: *mut leanh::LeanObject,
    mut v_a_4628_: *mut leanh::LeanObject,
    mut v_a_4629_: *mut leanh::LeanObject,
    mut v_a_4630_: *mut leanh::LeanObject,
    mut v_a_4631_: *mut leanh::LeanObject,
    mut v_a_4632_: *mut leanh::LeanObject,
    mut v_a_4633_: *mut leanh::LeanObject,
    mut v_a_4634_: *mut leanh::LeanObject,
    mut v_a_4635_: *mut leanh::LeanObject,
    mut v_a_4636_: *mut leanh::LeanObject,
    mut v_a_4637_: *mut leanh::LeanObject,
    mut v_a_4638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4639_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected(
        v_00_u03b1_4626_,
        v_c_4627_,
        v_a_4628_,
        v_a_4629_,
        v_a_4630_,
        v_a_4631_,
        v_a_4632_,
        v_a_4633_,
        v_a_4634_,
        v_a_4635_,
        v_a_4636_,
        v_a_4637_,
    );
    leanh::lean_dec(v_a_4637_);
    leanh::lean_dec_ref(v_a_4636_);
    leanh::lean_dec(v_a_4635_);
    leanh::lean_dec_ref(v_a_4634_);
    leanh::lean_dec(v_a_4633_);
    leanh::lean_dec_ref(v_a_4632_);
    leanh::lean_dec(v_a_4631_);
    leanh::lean_dec_ref(v_a_4630_);
    leanh::lean_dec(v_a_4629_);
    leanh::lean_dec(v_a_4628_);
    return v_res_4639_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(
    mut v_c_4640_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_p_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_p_4641_ = leanh::lean_ctor_get(v_c_4640_, 0);
    if leanh::lean_obj_tag(v_p_4641_) == 0 {
        let mut v_k_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4644_: u8 = 0;
        v_k_4642_ = leanh::lean_ctor_get(v_p_4641_, 0);
        v___x_4643_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_Linear_Poly_isZero___closed__0),
            core::ptr::addr_of_mut!(l_Int_Linear_Poly_isZero___closed__0_once),
            _init_l_Int_Linear_Poly_isZero___closed__0,
        );
        v___x_4644_ = lean_int_dec_eq(v_k_4642_, v___x_4643_);
        return v___x_4644_;
    } else {
        let mut v___x_4645_: u8 = 0;
        v___x_4645_ = 0;
        return v___x_4645_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial___boxed(
    mut v_c_4646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4647_: u8 = 0;
    let mut v_r_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4647_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(v_c_4646_);
    leanh::lean_dec_ref(v_c_4646_);
    v_r_4648_ = leanh::lean_box((v_res_4647_) as usize);
    return v_r_4648_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4650_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__0;
    v___x_4651_ = l_Lean_stringToMessageData(v___x_4650_);
    return v___x_4651_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(
    mut v_c_4652_: *mut leanh::LeanObject,
    mut v_a_4653_: *mut leanh::LeanObject,
    mut v_a_4654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_p_4656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4659_: u8 = 0;
    let mut v___x_4660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4664_: u8 = 0;
    let mut v___x_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4672_: u8 = 0;
    let mut v_isSharedCheck_4673_: u8 = 0;
    let mut v_unused_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_p_4656_ = leanh::lean_ctor_get(v_c_4652_, 0);
                v_isSharedCheck_4673_ = (!leanh::lean_is_exclusive(v_c_4652_)) as u8;
                if v_isSharedCheck_4673_ == 0 {
                    v_unused_4674_ = leanh::lean_ctor_get(v_c_4652_, 1);
                    leanh::lean_dec(v_unused_4674_);
                    v___x_4658_ = v_c_4652_;
                    v_isShared_4659_ = v_isSharedCheck_4673_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_p_4656_);
                    leanh::lean_dec(v_c_4652_);
                    v___x_4658_ = leanh::lean_box(0);
                    v_isShared_4659_ = v_isSharedCheck_4673_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4660_ = l_Int_Linear_Poly_pp___redArg(v_p_4656_, v_a_4653_, v_a_4654_);
                if leanh::lean_obj_tag(v___x_4660_) == 0 {
                    v_a_4661_ = leanh::lean_ctor_get(v___x_4660_, 0);
                    v_isSharedCheck_4672_ = (!leanh::lean_is_exclusive(v___x_4660_)) as u8;
                    if v_isSharedCheck_4672_ == 0 {
                        v___x_4663_ = v___x_4660_;
                        v_isShared_4664_ = v_isSharedCheck_4672_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4661_);
                        leanh::lean_dec(v___x_4660_);
                        v___x_4663_ = leanh::lean_box(0);
                        v_isShared_4664_ = v_isSharedCheck_4672_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4658_);
                    return v___x_4660_;
                }
            }
            2 => {
                v___x_4665_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1,
                );
                if v_isShared_4659_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4658_, 7);
                    leanh::lean_ctor_set(v___x_4658_, 1, v___x_4665_);
                    leanh::lean_ctor_set(v___x_4658_, 0, v_a_4661_);
                    v___x_4667_ = v___x_4658_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4671_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4671_, 0, v_a_4661_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4671_, 1, v___x_4665_);
                    v___x_4667_ = v_reuseFailAlloc_4671_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4664_ == 0 {
                    leanh::lean_ctor_set(v___x_4663_, 0, v___x_4667_);
                    v___x_4669_ = v___x_4663_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4670_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4670_, 0, v___x_4667_);
                    v___x_4669_ = v_reuseFailAlloc_4670_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4669_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___boxed(
    mut v_c_4675_: *mut leanh::LeanObject,
    mut v_a_4676_: *mut leanh::LeanObject,
    mut v_a_4677_: *mut leanh::LeanObject,
    mut v_a_4678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4679_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_4675_, v_a_4676_, v_a_4677_);
    leanh::lean_dec_ref(v_a_4677_);
    leanh::lean_dec(v_a_4676_);
    return v_res_4679_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(
    mut v_c_4680_: *mut leanh::LeanObject,
    mut v_a_4681_: *mut leanh::LeanObject,
    mut v_a_4682_: *mut leanh::LeanObject,
    mut v_a_4683_: *mut leanh::LeanObject,
    mut v_a_4684_: *mut leanh::LeanObject,
    mut v_a_4685_: *mut leanh::LeanObject,
    mut v_a_4686_: *mut leanh::LeanObject,
    mut v_a_4687_: *mut leanh::LeanObject,
    mut v_a_4688_: *mut leanh::LeanObject,
    mut v_a_4689_: *mut leanh::LeanObject,
    mut v_a_4690_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4692_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_4680_, v_a_4681_, v_a_4689_);
    return v___x_4692_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___boxed(
    mut v_c_4693_: *mut leanh::LeanObject,
    mut v_a_4694_: *mut leanh::LeanObject,
    mut v_a_4695_: *mut leanh::LeanObject,
    mut v_a_4696_: *mut leanh::LeanObject,
    mut v_a_4697_: *mut leanh::LeanObject,
    mut v_a_4698_: *mut leanh::LeanObject,
    mut v_a_4699_: *mut leanh::LeanObject,
    mut v_a_4700_: *mut leanh::LeanObject,
    mut v_a_4701_: *mut leanh::LeanObject,
    mut v_a_4702_: *mut leanh::LeanObject,
    mut v_a_4703_: *mut leanh::LeanObject,
    mut v_a_4704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4705_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(
        v_c_4693_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_, v_a_4700_,
        v_a_4701_, v_a_4702_, v_a_4703_,
    );
    leanh::lean_dec(v_a_4703_);
    leanh::lean_dec_ref(v_a_4702_);
    leanh::lean_dec(v_a_4701_);
    leanh::lean_dec_ref(v_a_4700_);
    leanh::lean_dec(v_a_4699_);
    leanh::lean_dec_ref(v_a_4698_);
    leanh::lean_dec(v_a_4697_);
    leanh::lean_dec_ref(v_a_4696_);
    leanh::lean_dec(v_a_4695_);
    leanh::lean_dec(v_a_4694_);
    return v_res_4705_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(
    mut v_c_4706_: *mut leanh::LeanObject,
    mut v_a_4707_: *mut leanh::LeanObject,
    mut v_a_4708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_p_4710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4715_: u8 = 0;
    let mut v___x_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4721_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_p_4710_ = leanh::lean_ctor_get(v_c_4706_, 0);
                leanh::lean_inc_ref(v_p_4710_);
                leanh::lean_dec_ref(v_c_4706_);
                v___x_4711_ =
                    l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_4710_, v_a_4707_, v_a_4708_);
                if leanh::lean_obj_tag(v___x_4711_) == 0 {
                    v_a_4712_ = leanh::lean_ctor_get(v___x_4711_, 0);
                    v_isSharedCheck_4721_ = (!leanh::lean_is_exclusive(v___x_4711_)) as u8;
                    if v_isSharedCheck_4721_ == 0 {
                        v___x_4714_ = v___x_4711_;
                        v_isShared_4715_ = v_isSharedCheck_4721_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4712_);
                        leanh::lean_dec(v___x_4711_);
                        v___x_4714_ = leanh::lean_box(0);
                        v_isShared_4715_ = v_isSharedCheck_4721_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_4711_;
                }
            }
            1 => {
                v___x_4716_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
                v___x_4717_ = l_Lean_mkIntEq(v_a_4712_, v___x_4716_);
                if v_isShared_4715_ == 0 {
                    leanh::lean_ctor_set(v___x_4714_, 0, v___x_4717_);
                    v___x_4719_ = v___x_4714_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4720_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4720_, 0, v___x_4717_);
                    v___x_4719_ = v_reuseFailAlloc_4720_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4719_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg___boxed(
    mut v_c_4722_: *mut leanh::LeanObject,
    mut v_a_4723_: *mut leanh::LeanObject,
    mut v_a_4724_: *mut leanh::LeanObject,
    mut v_a_4725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4726_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(v_c_4722_, v_a_4723_, v_a_4724_);
    leanh::lean_dec_ref(v_a_4724_);
    leanh::lean_dec(v_a_4723_);
    return v_res_4726_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(
    mut v_c_4727_: *mut leanh::LeanObject,
    mut v_a_4728_: *mut leanh::LeanObject,
    mut v_a_4729_: *mut leanh::LeanObject,
    mut v_a_4730_: *mut leanh::LeanObject,
    mut v_a_4731_: *mut leanh::LeanObject,
    mut v_a_4732_: *mut leanh::LeanObject,
    mut v_a_4733_: *mut leanh::LeanObject,
    mut v_a_4734_: *mut leanh::LeanObject,
    mut v_a_4735_: *mut leanh::LeanObject,
    mut v_a_4736_: *mut leanh::LeanObject,
    mut v_a_4737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4739_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(v_c_4727_, v_a_4728_, v_a_4736_);
    return v___x_4739_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___boxed(
    mut v_c_4740_: *mut leanh::LeanObject,
    mut v_a_4741_: *mut leanh::LeanObject,
    mut v_a_4742_: *mut leanh::LeanObject,
    mut v_a_4743_: *mut leanh::LeanObject,
    mut v_a_4744_: *mut leanh::LeanObject,
    mut v_a_4745_: *mut leanh::LeanObject,
    mut v_a_4746_: *mut leanh::LeanObject,
    mut v_a_4747_: *mut leanh::LeanObject,
    mut v_a_4748_: *mut leanh::LeanObject,
    mut v_a_4749_: *mut leanh::LeanObject,
    mut v_a_4750_: *mut leanh::LeanObject,
    mut v_a_4751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4752_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4752_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(
        v_c_4740_, v_a_4741_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_,
        v_a_4748_, v_a_4749_, v_a_4750_,
    );
    leanh::lean_dec(v_a_4750_);
    leanh::lean_dec_ref(v_a_4749_);
    leanh::lean_dec(v_a_4748_);
    leanh::lean_dec_ref(v_a_4747_);
    leanh::lean_dec(v_a_4746_);
    leanh::lean_dec_ref(v_a_4745_);
    leanh::lean_dec(v_a_4744_);
    leanh::lean_dec_ref(v_a_4743_);
    leanh::lean_dec(v_a_4742_);
    leanh::lean_dec(v_a_4741_);
    return v_res_4752_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(
    mut v_c_4753_: *mut leanh::LeanObject,
    mut v_a_4754_: *mut leanh::LeanObject,
    mut v_a_4755_: *mut leanh::LeanObject,
    mut v_a_4756_: *mut leanh::LeanObject,
    mut v_a_4757_: *mut leanh::LeanObject,
    mut v_a_4758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4769_: u8 = 0;
    let mut v___x_4771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4773_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4760_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(
                    v_c_4753_, v_a_4754_, v_a_4757_,
                );
                if leanh::lean_obj_tag(v___x_4760_) == 0 {
                    v_a_4761_ = leanh::lean_ctor_get(v___x_4760_, 0);
                    leanh::lean_inc(v_a_4761_);
                    leanh::lean_dec_ref_known(v___x_4760_, 1);
                    v___x_4762_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
                    v___x_4763_ = l_Lean_indentD(v_a_4761_);
                    v___x_4764_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4764_, 0, v___x_4762_);
                    leanh::lean_ctor_set(v___x_4764_, 1, v___x_4763_);
                    v___x_4765_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_4764_, v_a_4755_, v_a_4756_, v_a_4757_, v_a_4758_);
                    return v___x_4765_;
                } else {
                    v_a_4766_ = leanh::lean_ctor_get(v___x_4760_, 0);
                    v_isSharedCheck_4773_ = (!leanh::lean_is_exclusive(v___x_4760_)) as u8;
                    if v_isSharedCheck_4773_ == 0 {
                        v___x_4768_ = v___x_4760_;
                        v_isShared_4769_ = v_isSharedCheck_4773_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4766_);
                        leanh::lean_dec(v___x_4760_);
                        v___x_4768_ = leanh::lean_box(0);
                        v_isShared_4769_ = v_isSharedCheck_4773_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4769_ == 0 {
                    v___x_4771_ = v___x_4768_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4772_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4772_, 0, v_a_4766_);
                    v___x_4771_ = v_reuseFailAlloc_4772_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4771_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg___boxed(
    mut v_c_4774_: *mut leanh::LeanObject,
    mut v_a_4775_: *mut leanh::LeanObject,
    mut v_a_4776_: *mut leanh::LeanObject,
    mut v_a_4777_: *mut leanh::LeanObject,
    mut v_a_4778_: *mut leanh::LeanObject,
    mut v_a_4779_: *mut leanh::LeanObject,
    mut v_a_4780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4781_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4781_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(
        v_c_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_,
    );
    leanh::lean_dec(v_a_4779_);
    leanh::lean_dec_ref(v_a_4778_);
    leanh::lean_dec(v_a_4777_);
    leanh::lean_dec_ref(v_a_4776_);
    leanh::lean_dec(v_a_4775_);
    return v_res_4781_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected(
    mut v_00_u03b1_4782_: *mut leanh::LeanObject,
    mut v_c_4783_: *mut leanh::LeanObject,
    mut v_a_4784_: *mut leanh::LeanObject,
    mut v_a_4785_: *mut leanh::LeanObject,
    mut v_a_4786_: *mut leanh::LeanObject,
    mut v_a_4787_: *mut leanh::LeanObject,
    mut v_a_4788_: *mut leanh::LeanObject,
    mut v_a_4789_: *mut leanh::LeanObject,
    mut v_a_4790_: *mut leanh::LeanObject,
    mut v_a_4791_: *mut leanh::LeanObject,
    mut v_a_4792_: *mut leanh::LeanObject,
    mut v_a_4793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4795_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(
        v_c_4783_, v_a_4784_, v_a_4790_, v_a_4791_, v_a_4792_, v_a_4793_,
    );
    return v___x_4795_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___boxed(
    mut v_00_u03b1_4796_: *mut leanh::LeanObject,
    mut v_c_4797_: *mut leanh::LeanObject,
    mut v_a_4798_: *mut leanh::LeanObject,
    mut v_a_4799_: *mut leanh::LeanObject,
    mut v_a_4800_: *mut leanh::LeanObject,
    mut v_a_4801_: *mut leanh::LeanObject,
    mut v_a_4802_: *mut leanh::LeanObject,
    mut v_a_4803_: *mut leanh::LeanObject,
    mut v_a_4804_: *mut leanh::LeanObject,
    mut v_a_4805_: *mut leanh::LeanObject,
    mut v_a_4806_: *mut leanh::LeanObject,
    mut v_a_4807_: *mut leanh::LeanObject,
    mut v_a_4808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4809_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4809_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected(
        v_00_u03b1_4796_,
        v_c_4797_,
        v_a_4798_,
        v_a_4799_,
        v_a_4800_,
        v_a_4801_,
        v_a_4802_,
        v_a_4803_,
        v_a_4804_,
        v_a_4805_,
        v_a_4806_,
        v_a_4807_,
    );
    leanh::lean_dec(v_a_4807_);
    leanh::lean_dec_ref(v_a_4806_);
    leanh::lean_dec(v_a_4805_);
    leanh::lean_dec_ref(v_a_4804_);
    leanh::lean_dec(v_a_4803_);
    leanh::lean_dec_ref(v_a_4802_);
    leanh::lean_dec(v_a_4801_);
    leanh::lean_dec_ref(v_a_4800_);
    leanh::lean_dec(v_a_4799_);
    leanh::lean_dec(v_a_4798_);
    return v_res_4809_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(
    mut v_x_4810_: *mut leanh::LeanObject,
    mut v_a_4811_: *mut leanh::LeanObject,
    mut v_a_4812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4818_: u8 = 0;
    let mut v_occurs_4819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: u8 = 0;
    let mut v___x_4823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4831_: u8 = 0;
    let mut v_a_4832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4835_: u8 = 0;
    let mut v___x_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4839_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4814_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_4811_, v_a_4812_);
                if leanh::lean_obj_tag(v___x_4814_) == 0 {
                    v_a_4815_ = leanh::lean_ctor_get(v___x_4814_, 0);
                    v_isSharedCheck_4831_ = (!leanh::lean_is_exclusive(v___x_4814_)) as u8;
                    if v_isSharedCheck_4831_ == 0 {
                        v___x_4817_ = v___x_4814_;
                        v_isShared_4818_ = v_isSharedCheck_4831_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4815_);
                        leanh::lean_dec(v___x_4814_);
                        v___x_4817_ = leanh::lean_box(0);
                        v_isShared_4818_ = v_isSharedCheck_4831_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4832_ = leanh::lean_ctor_get(v___x_4814_, 0);
                    v_isSharedCheck_4839_ = (!leanh::lean_is_exclusive(v___x_4814_)) as u8;
                    if v_isSharedCheck_4839_ == 0 {
                        v___x_4834_ = v___x_4814_;
                        v_isShared_4835_ = v_isSharedCheck_4839_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4832_);
                        leanh::lean_dec(v___x_4814_);
                        v___x_4834_ = leanh::lean_box(0);
                        v_isShared_4835_ = v_isSharedCheck_4839_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_occurs_4819_ = leanh::lean_ctor_get(v_a_4815_, 12);
                leanh::lean_inc_ref(v_occurs_4819_);
                leanh::lean_dec(v_a_4815_);
                v_size_4820_ = leanh::lean_ctor_get(v_occurs_4819_, 2);
                v___x_4821_ = leanh::lean_box(1);
                v___x_4822_ = lean_nat_dec_lt(v_x_4810_, v_size_4820_);
                if v___x_4822_ == 0 {
                    leanh::lean_dec_ref(v_occurs_4819_);
                    v___x_4823_ = l_outOfBounds___redArg(v___x_4821_);
                    if v_isShared_4818_ == 0 {
                        leanh::lean_ctor_set(v___x_4817_, 0, v___x_4823_);
                        v___x_4825_ = v___x_4817_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4826_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4826_, 0, v___x_4823_);
                        v___x_4825_ = v_reuseFailAlloc_4826_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4827_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_4821_,
                        v_occurs_4819_,
                        v_x_4810_,
                    );
                    leanh::lean_dec_ref(v_occurs_4819_);
                    if v_isShared_4818_ == 0 {
                        leanh::lean_ctor_set(v___x_4817_, 0, v___x_4827_);
                        v___x_4829_ = v___x_4817_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4830_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4830_, 0, v___x_4827_);
                        v___x_4829_ = v_reuseFailAlloc_4830_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4825_;
            }
            3 => {
                return v___x_4829_;
            }
            4 => {
                if v_isShared_4835_ == 0 {
                    v___x_4837_ = v___x_4834_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4838_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4838_, 0, v_a_4832_);
                    v___x_4837_ = v_reuseFailAlloc_4838_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4837_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg___boxed(
    mut v_x_4840_: *mut leanh::LeanObject,
    mut v_a_4841_: *mut leanh::LeanObject,
    mut v_a_4842_: *mut leanh::LeanObject,
    mut v_a_4843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4844_ =
        l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_4840_, v_a_4841_, v_a_4842_);
    leanh::lean_dec_ref(v_a_4842_);
    leanh::lean_dec(v_a_4841_);
    leanh::lean_dec(v_x_4840_);
    return v_res_4844_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(
    mut v_x_4845_: *mut leanh::LeanObject,
    mut v_a_4846_: *mut leanh::LeanObject,
    mut v_a_4847_: *mut leanh::LeanObject,
    mut v_a_4848_: *mut leanh::LeanObject,
    mut v_a_4849_: *mut leanh::LeanObject,
    mut v_a_4850_: *mut leanh::LeanObject,
    mut v_a_4851_: *mut leanh::LeanObject,
    mut v_a_4852_: *mut leanh::LeanObject,
    mut v_a_4853_: *mut leanh::LeanObject,
    mut v_a_4854_: *mut leanh::LeanObject,
    mut v_a_4855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4857_ =
        l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_4845_, v_a_4846_, v_a_4854_);
    return v___x_4857_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___boxed(
    mut v_x_4858_: *mut leanh::LeanObject,
    mut v_a_4859_: *mut leanh::LeanObject,
    mut v_a_4860_: *mut leanh::LeanObject,
    mut v_a_4861_: *mut leanh::LeanObject,
    mut v_a_4862_: *mut leanh::LeanObject,
    mut v_a_4863_: *mut leanh::LeanObject,
    mut v_a_4864_: *mut leanh::LeanObject,
    mut v_a_4865_: *mut leanh::LeanObject,
    mut v_a_4866_: *mut leanh::LeanObject,
    mut v_a_4867_: *mut leanh::LeanObject,
    mut v_a_4868_: *mut leanh::LeanObject,
    mut v_a_4869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4870_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(
        v_x_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_,
        v_a_4866_, v_a_4867_, v_a_4868_,
    );
    leanh::lean_dec(v_a_4868_);
    leanh::lean_dec_ref(v_a_4867_);
    leanh::lean_dec(v_a_4866_);
    leanh::lean_dec_ref(v_a_4865_);
    leanh::lean_dec(v_a_4864_);
    leanh::lean_dec_ref(v_a_4863_);
    leanh::lean_dec(v_a_4862_);
    leanh::lean_dec_ref(v_a_4861_);
    leanh::lean_dec(v_a_4860_);
    leanh::lean_dec(v_a_4859_);
    leanh::lean_dec(v_x_4858_);
    return v_res_4870_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(
    mut v_k_4871_: *mut leanh::LeanObject,
    mut v_v_4872_: *mut leanh::LeanObject,
    mut v_t_4873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4881_: u8 = 0;
    let mut v___x_4882_: u8 = 0;
    let mut v___x_4883_: u8 = 0;
    let mut v_impl_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: u8 = 0;
    let mut v___x_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4902_: u8 = 0;
    let mut v_size_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: u8 = 0;
    let mut v___x_4913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4914_: u8 = 0;
    let mut v___x_4915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4939_: u8 = 0;
    let mut v_unused_4940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4952_: u8 = 0;
    let mut v___x_4954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4956_: u8 = 0;
    let mut v_unused_4957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4963_: u8 = 0;
    let mut v_unused_4964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4975_: u8 = 0;
    let mut v_k_4976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4980_: u8 = 0;
    let mut v___x_4981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4991_: u8 = 0;
    let mut v_unused_4992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4995_: u8 = 0;
    let mut v_unused_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5003_: u8 = 0;
    let mut v___x_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5011_: u8 = 0;
    let mut v_unused_5012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: u8 = 0;
    let mut v___x_5033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5040_: u8 = 0;
    let mut v_size_5041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: u8 = 0;
    let mut v___x_5051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5052_: u8 = 0;
    let mut v___x_5053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5078_: u8 = 0;
    let mut v_unused_5079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5092_: u8 = 0;
    let mut v___x_5094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5096_: u8 = 0;
    let mut v_unused_5097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5103_: u8 = 0;
    let mut v_unused_5104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5115_: u8 = 0;
    let mut v___x_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5123_: u8 = 0;
    let mut v_unused_5124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5131_: u8 = 0;
    let mut v_k_5132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5136_: u8 = 0;
    let mut v___x_5137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5147_: u8 = 0;
    let mut v_unused_5148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5151_: u8 = 0;
    let mut v_unused_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5159_: u8 = 0;
    let mut v___x_5160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_4873_) == 0 {
                    v_size_4874_ = leanh::lean_ctor_get(v_t_4873_, 0);
                    v_k_4875_ = leanh::lean_ctor_get(v_t_4873_, 1);
                    v_v_4876_ = leanh::lean_ctor_get(v_t_4873_, 2);
                    v_l_4877_ = leanh::lean_ctor_get(v_t_4873_, 3);
                    v_r_4878_ = leanh::lean_ctor_get(v_t_4873_, 4);
                    v_isSharedCheck_5159_ = (!leanh::lean_is_exclusive(v_t_4873_)) as u8;
                    if v_isSharedCheck_5159_ == 0 {
                        v___x_4880_ = v_t_4873_;
                        v_isShared_4881_ = v_isSharedCheck_5159_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_4878_);
                        leanh::lean_inc(v_l_4877_);
                        leanh::lean_inc(v_v_4876_);
                        leanh::lean_inc(v_k_4875_);
                        leanh::lean_inc(v_size_4874_);
                        leanh::lean_dec(v_t_4873_);
                        v___x_4880_ = leanh::lean_box(0);
                        v_isShared_4881_ = v_isSharedCheck_5159_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_5160_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5161_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_5161_, 0, v___x_5160_);
                    leanh::lean_ctor_set(v___x_5161_, 1, v_k_4871_);
                    leanh::lean_ctor_set(v___x_5161_, 2, v_v_4872_);
                    leanh::lean_ctor_set(v___x_5161_, 3, v_t_4873_);
                    leanh::lean_ctor_set(v___x_5161_, 4, v_t_4873_);
                    return v___x_5161_;
                }
            }
            1 => {
                v___x_4882_ = lean_nat_dec_lt(v_k_4871_, v_k_4875_);
                if v___x_4882_ == 0 {
                    v___x_4883_ = lean_nat_dec_eq(v_k_4871_, v_k_4875_);
                    if v___x_4883_ == 0 {
                        leanh::lean_dec(v_size_4874_);
                        v_impl_4884_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_4871_, v_v_4872_, v_r_4878_);
                        v___x_4885_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_l_4877_) == 0 {
                            v_size_4886_ = leanh::lean_ctor_get(v_l_4877_, 0);
                            v_size_4887_ = leanh::lean_ctor_get(v_impl_4884_, 0);
                            leanh::lean_inc(v_size_4887_);
                            v_k_4888_ = leanh::lean_ctor_get(v_impl_4884_, 1);
                            leanh::lean_inc(v_k_4888_);
                            v_v_4889_ = leanh::lean_ctor_get(v_impl_4884_, 2);
                            leanh::lean_inc(v_v_4889_);
                            v_l_4890_ = leanh::lean_ctor_get(v_impl_4884_, 3);
                            leanh::lean_inc(v_l_4890_);
                            v_r_4891_ = leanh::lean_ctor_get(v_impl_4884_, 4);
                            leanh::lean_inc(v_r_4891_);
                            v___x_4892_ = leanh::lean_unsigned_to_nat(3);
                            v___x_4893_ = lean_nat_mul(v___x_4892_, v_size_4886_);
                            v___x_4894_ = lean_nat_dec_lt(v___x_4893_, v_size_4887_);
                            leanh::lean_dec(v___x_4893_);
                            if v___x_4894_ == 0 {
                                leanh::lean_dec(v_r_4891_);
                                leanh::lean_dec(v_l_4890_);
                                leanh::lean_dec(v_v_4889_);
                                leanh::lean_dec(v_k_4888_);
                                v___x_4895_ = lean_nat_add(v___x_4885_, v_size_4886_);
                                v___x_4896_ = lean_nat_add(v___x_4895_, v_size_4887_);
                                leanh::lean_dec(v_size_4887_);
                                leanh::lean_dec(v___x_4895_);
                                if v_isShared_4881_ == 0 {
                                    leanh::lean_ctor_set(v___x_4880_, 4, v_impl_4884_);
                                    leanh::lean_ctor_set(v___x_4880_, 0, v___x_4896_);
                                    v___x_4898_ = v___x_4880_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4899_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4899_,
                                        0,
                                        v___x_4896_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4899_,
                                        1,
                                        v_k_4875_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4899_,
                                        2,
                                        v_v_4876_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4899_,
                                        3,
                                        v_l_4877_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4899_,
                                        4,
                                        v_impl_4884_,
                                    );
                                    v___x_4898_ = v_reuseFailAlloc_4899_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_4963_ =
                                    (!leanh::lean_is_exclusive(v_impl_4884_)) as u8;
                                if v_isSharedCheck_4963_ == 0 {
                                    v_unused_4964_ = leanh::lean_ctor_get(v_impl_4884_, 4);
                                    leanh::lean_dec(v_unused_4964_);
                                    v_unused_4965_ = leanh::lean_ctor_get(v_impl_4884_, 3);
                                    leanh::lean_dec(v_unused_4965_);
                                    v_unused_4966_ = leanh::lean_ctor_get(v_impl_4884_, 2);
                                    leanh::lean_dec(v_unused_4966_);
                                    v_unused_4967_ = leanh::lean_ctor_get(v_impl_4884_, 1);
                                    leanh::lean_dec(v_unused_4967_);
                                    v_unused_4968_ = leanh::lean_ctor_get(v_impl_4884_, 0);
                                    leanh::lean_dec(v_unused_4968_);
                                    v___x_4901_ = v_impl_4884_;
                                    v_isShared_4902_ = v_isSharedCheck_4963_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_impl_4884_);
                                    v___x_4901_ = leanh::lean_box(0);
                                    v_isShared_4902_ = v_isSharedCheck_4963_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_4969_ = leanh::lean_ctor_get(v_impl_4884_, 3);
                            leanh::lean_inc(v_l_4969_);
                            if leanh::lean_obj_tag(v_l_4969_) == 0 {
                                v_r_4970_ = leanh::lean_ctor_get(v_impl_4884_, 4);
                                v_k_4971_ = leanh::lean_ctor_get(v_impl_4884_, 1);
                                v_v_4972_ = leanh::lean_ctor_get(v_impl_4884_, 2);
                                v_isSharedCheck_4995_ =
                                    (!leanh::lean_is_exclusive(v_impl_4884_)) as u8;
                                if v_isSharedCheck_4995_ == 0 {
                                    v_unused_4996_ = leanh::lean_ctor_get(v_impl_4884_, 3);
                                    leanh::lean_dec(v_unused_4996_);
                                    v_unused_4997_ = leanh::lean_ctor_get(v_impl_4884_, 0);
                                    leanh::lean_dec(v_unused_4997_);
                                    v___x_4974_ = v_impl_4884_;
                                    v_isShared_4975_ = v_isSharedCheck_4995_;
                                    state = 13;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_r_4970_);
                                    leanh::lean_inc(v_v_4972_);
                                    leanh::lean_inc(v_k_4971_);
                                    leanh::lean_dec(v_impl_4884_);
                                    v___x_4974_ = leanh::lean_box(0);
                                    v_isShared_4975_ = v_isSharedCheck_4995_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_4998_ = leanh::lean_ctor_get(v_impl_4884_, 4);
                                leanh::lean_inc(v_r_4998_);
                                if leanh::lean_obj_tag(v_r_4998_) == 0 {
                                    v_k_4999_ = leanh::lean_ctor_get(v_impl_4884_, 1);
                                    v_v_5000_ = leanh::lean_ctor_get(v_impl_4884_, 2);
                                    v_isSharedCheck_5011_ =
                                        (!leanh::lean_is_exclusive(v_impl_4884_)) as u8;
                                    if v_isSharedCheck_5011_ == 0 {
                                        v_unused_5012_ =
                                            leanh::lean_ctor_get(v_impl_4884_, 4);
                                        leanh::lean_dec(v_unused_5012_);
                                        v_unused_5013_ =
                                            leanh::lean_ctor_get(v_impl_4884_, 3);
                                        leanh::lean_dec(v_unused_5013_);
                                        v_unused_5014_ =
                                            leanh::lean_ctor_get(v_impl_4884_, 0);
                                        leanh::lean_dec(v_unused_5014_);
                                        v___x_5002_ = v_impl_4884_;
                                        v_isShared_5003_ = v_isSharedCheck_5011_;
                                        state = 18;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_v_5000_);
                                        leanh::lean_inc(v_k_4999_);
                                        leanh::lean_dec(v_impl_4884_);
                                        v___x_5002_ = leanh::lean_box(0);
                                        v_isShared_5003_ = v_isSharedCheck_5011_;
                                        state = 18;
                                        continue;
                                    }
                                } else {
                                    v___x_5015_ = leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_4881_ == 0 {
                                        leanh::lean_ctor_set(v___x_4880_, 4, v_impl_4884_);
                                        leanh::lean_ctor_set(v___x_4880_, 3, v_r_4998_);
                                        leanh::lean_ctor_set(v___x_4880_, 0, v___x_5015_);
                                        v___x_5017_ = v___x_4880_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_5018_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5018_,
                                            0,
                                            v___x_5015_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5018_,
                                            1,
                                            v_k_4875_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5018_,
                                            2,
                                            v_v_4876_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5018_,
                                            3,
                                            v_r_4998_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5018_,
                                            4,
                                            v_impl_4884_,
                                        );
                                        v___x_5017_ = v_reuseFailAlloc_5018_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_v_4876_);
                        leanh::lean_dec(v_k_4875_);
                        if v_isShared_4881_ == 0 {
                            leanh::lean_ctor_set(v___x_4880_, 2, v_v_4872_);
                            leanh::lean_ctor_set(v___x_4880_, 1, v_k_4871_);
                            v___x_5020_ = v___x_4880_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_5021_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5021_, 0, v_size_4874_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5021_, 1, v_k_4871_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5021_, 2, v_v_4872_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5021_, 3, v_l_4877_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5021_, 4, v_r_4878_);
                            v___x_5020_ = v_reuseFailAlloc_5021_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_size_4874_);
                    v_impl_5022_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_4871_, v_v_4872_, v_l_4877_);
                    v___x_5023_ = leanh::lean_unsigned_to_nat(1);
                    if leanh::lean_obj_tag(v_r_4878_) == 0 {
                        v_size_5024_ = leanh::lean_ctor_get(v_r_4878_, 0);
                        v_size_5025_ = leanh::lean_ctor_get(v_impl_5022_, 0);
                        leanh::lean_inc(v_size_5025_);
                        v_k_5026_ = leanh::lean_ctor_get(v_impl_5022_, 1);
                        leanh::lean_inc(v_k_5026_);
                        v_v_5027_ = leanh::lean_ctor_get(v_impl_5022_, 2);
                        leanh::lean_inc(v_v_5027_);
                        v_l_5028_ = leanh::lean_ctor_get(v_impl_5022_, 3);
                        leanh::lean_inc(v_l_5028_);
                        v_r_5029_ = leanh::lean_ctor_get(v_impl_5022_, 4);
                        leanh::lean_inc(v_r_5029_);
                        v___x_5030_ = leanh::lean_unsigned_to_nat(3);
                        v___x_5031_ = lean_nat_mul(v___x_5030_, v_size_5024_);
                        v___x_5032_ = lean_nat_dec_lt(v___x_5031_, v_size_5025_);
                        leanh::lean_dec(v___x_5031_);
                        if v___x_5032_ == 0 {
                            leanh::lean_dec(v_r_5029_);
                            leanh::lean_dec(v_l_5028_);
                            leanh::lean_dec(v_v_5027_);
                            leanh::lean_dec(v_k_5026_);
                            v___x_5033_ = lean_nat_add(v___x_5023_, v_size_5025_);
                            leanh::lean_dec(v_size_5025_);
                            v___x_5034_ = lean_nat_add(v___x_5033_, v_size_5024_);
                            leanh::lean_dec(v___x_5033_);
                            if v_isShared_4881_ == 0 {
                                leanh::lean_ctor_set(v___x_4880_, 3, v_impl_5022_);
                                leanh::lean_ctor_set(v___x_4880_, 0, v___x_5034_);
                                v___x_5036_ = v___x_4880_;
                                state = 23;
                                continue;
                            } else {
                                v_reuseFailAlloc_5037_ =
                                    leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_5037_, 0, v___x_5034_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_5037_, 1, v_k_4875_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_5037_, 2, v_v_4876_);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_5037_,
                                    3,
                                    v_impl_5022_,
                                );
                                leanh::lean_ctor_set(v_reuseFailAlloc_5037_, 4, v_r_4878_);
                                v___x_5036_ = v_reuseFailAlloc_5037_;
                                state = 23;
                                continue;
                            }
                        } else {
                            v_isSharedCheck_5103_ =
                                (!leanh::lean_is_exclusive(v_impl_5022_)) as u8;
                            if v_isSharedCheck_5103_ == 0 {
                                v_unused_5104_ = leanh::lean_ctor_get(v_impl_5022_, 4);
                                leanh::lean_dec(v_unused_5104_);
                                v_unused_5105_ = leanh::lean_ctor_get(v_impl_5022_, 3);
                                leanh::lean_dec(v_unused_5105_);
                                v_unused_5106_ = leanh::lean_ctor_get(v_impl_5022_, 2);
                                leanh::lean_dec(v_unused_5106_);
                                v_unused_5107_ = leanh::lean_ctor_get(v_impl_5022_, 1);
                                leanh::lean_dec(v_unused_5107_);
                                v_unused_5108_ = leanh::lean_ctor_get(v_impl_5022_, 0);
                                leanh::lean_dec(v_unused_5108_);
                                v___x_5039_ = v_impl_5022_;
                                v_isShared_5040_ = v_isSharedCheck_5103_;
                                state = 24;
                                continue;
                            } else {
                                leanh::lean_dec(v_impl_5022_);
                                v___x_5039_ = leanh::lean_box(0);
                                v_isShared_5040_ = v_isSharedCheck_5103_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        v_l_5109_ = leanh::lean_ctor_get(v_impl_5022_, 3);
                        leanh::lean_inc(v_l_5109_);
                        if leanh::lean_obj_tag(v_l_5109_) == 0 {
                            v_r_5110_ = leanh::lean_ctor_get(v_impl_5022_, 4);
                            v_k_5111_ = leanh::lean_ctor_get(v_impl_5022_, 1);
                            v_v_5112_ = leanh::lean_ctor_get(v_impl_5022_, 2);
                            v_isSharedCheck_5123_ =
                                (!leanh::lean_is_exclusive(v_impl_5022_)) as u8;
                            if v_isSharedCheck_5123_ == 0 {
                                v_unused_5124_ = leanh::lean_ctor_get(v_impl_5022_, 3);
                                leanh::lean_dec(v_unused_5124_);
                                v_unused_5125_ = leanh::lean_ctor_get(v_impl_5022_, 0);
                                leanh::lean_dec(v_unused_5125_);
                                v___x_5114_ = v_impl_5022_;
                                v_isShared_5115_ = v_isSharedCheck_5123_;
                                state = 34;
                                continue;
                            } else {
                                leanh::lean_inc(v_r_5110_);
                                leanh::lean_inc(v_v_5112_);
                                leanh::lean_inc(v_k_5111_);
                                leanh::lean_dec(v_impl_5022_);
                                v___x_5114_ = leanh::lean_box(0);
                                v_isShared_5115_ = v_isSharedCheck_5123_;
                                state = 34;
                                continue;
                            }
                        } else {
                            v_r_5126_ = leanh::lean_ctor_get(v_impl_5022_, 4);
                            leanh::lean_inc(v_r_5126_);
                            if leanh::lean_obj_tag(v_r_5126_) == 0 {
                                v_k_5127_ = leanh::lean_ctor_get(v_impl_5022_, 1);
                                v_v_5128_ = leanh::lean_ctor_get(v_impl_5022_, 2);
                                v_isSharedCheck_5151_ =
                                    (!leanh::lean_is_exclusive(v_impl_5022_)) as u8;
                                if v_isSharedCheck_5151_ == 0 {
                                    v_unused_5152_ = leanh::lean_ctor_get(v_impl_5022_, 4);
                                    leanh::lean_dec(v_unused_5152_);
                                    v_unused_5153_ = leanh::lean_ctor_get(v_impl_5022_, 3);
                                    leanh::lean_dec(v_unused_5153_);
                                    v_unused_5154_ = leanh::lean_ctor_get(v_impl_5022_, 0);
                                    leanh::lean_dec(v_unused_5154_);
                                    v___x_5130_ = v_impl_5022_;
                                    v_isShared_5131_ = v_isSharedCheck_5151_;
                                    state = 37;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_v_5128_);
                                    leanh::lean_inc(v_k_5127_);
                                    leanh::lean_dec(v_impl_5022_);
                                    v___x_5130_ = leanh::lean_box(0);
                                    v_isShared_5131_ = v_isSharedCheck_5151_;
                                    state = 37;
                                    continue;
                                }
                            } else {
                                v___x_5155_ = leanh::lean_unsigned_to_nat(2);
                                if v_isShared_4881_ == 0 {
                                    leanh::lean_ctor_set(v___x_4880_, 4, v_r_5126_);
                                    leanh::lean_ctor_set(v___x_4880_, 3, v_impl_5022_);
                                    leanh::lean_ctor_set(v___x_4880_, 0, v___x_5155_);
                                    v___x_5157_ = v___x_4880_;
                                    state = 42;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_5158_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5158_,
                                        0,
                                        v___x_5155_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5158_,
                                        1,
                                        v_k_4875_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5158_,
                                        2,
                                        v_v_4876_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5158_,
                                        3,
                                        v_impl_5022_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5158_,
                                        4,
                                        v_r_5126_,
                                    );
                                    v___x_5157_ = v_reuseFailAlloc_5158_;
                                    state = 42;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_4898_;
            }
            3 => {
                v_size_4903_ = leanh::lean_ctor_get(v_l_4890_, 0);
                v_k_4904_ = leanh::lean_ctor_get(v_l_4890_, 1);
                v_v_4905_ = leanh::lean_ctor_get(v_l_4890_, 2);
                v_l_4906_ = leanh::lean_ctor_get(v_l_4890_, 3);
                v_r_4907_ = leanh::lean_ctor_get(v_l_4890_, 4);
                v_size_4908_ = leanh::lean_ctor_get(v_r_4891_, 0);
                v___x_4909_ = leanh::lean_unsigned_to_nat(2);
                v___x_4910_ = lean_nat_mul(v___x_4909_, v_size_4908_);
                v___x_4911_ = lean_nat_dec_lt(v_size_4903_, v___x_4910_);
                leanh::lean_dec(v___x_4910_);
                if v___x_4911_ == 0 {
                    leanh::lean_inc(v_r_4907_);
                    leanh::lean_inc(v_l_4906_);
                    leanh::lean_inc(v_v_4905_);
                    leanh::lean_inc(v_k_4904_);
                    v_isSharedCheck_4939_ = (!leanh::lean_is_exclusive(v_l_4890_)) as u8;
                    if v_isSharedCheck_4939_ == 0 {
                        v_unused_4940_ = leanh::lean_ctor_get(v_l_4890_, 4);
                        leanh::lean_dec(v_unused_4940_);
                        v_unused_4941_ = leanh::lean_ctor_get(v_l_4890_, 3);
                        leanh::lean_dec(v_unused_4941_);
                        v_unused_4942_ = leanh::lean_ctor_get(v_l_4890_, 2);
                        leanh::lean_dec(v_unused_4942_);
                        v_unused_4943_ = leanh::lean_ctor_get(v_l_4890_, 1);
                        leanh::lean_dec(v_unused_4943_);
                        v_unused_4944_ = leanh::lean_ctor_get(v_l_4890_, 0);
                        leanh::lean_dec(v_unused_4944_);
                        v___x_4913_ = v_l_4890_;
                        v_isShared_4914_ = v_isSharedCheck_4939_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_l_4890_);
                        v___x_4913_ = leanh::lean_box(0);
                        v_isShared_4914_ = v_isSharedCheck_4939_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4880_);
                    v___x_4945_ = lean_nat_add(v___x_4885_, v_size_4886_);
                    v___x_4946_ = lean_nat_add(v___x_4945_, v_size_4887_);
                    leanh::lean_dec(v_size_4887_);
                    v___x_4947_ = lean_nat_add(v___x_4945_, v_size_4903_);
                    leanh::lean_dec(v___x_4945_);
                    leanh::lean_inc_ref(v_l_4877_);
                    if v_isShared_4902_ == 0 {
                        leanh::lean_ctor_set(v___x_4901_, 4, v_l_4890_);
                        leanh::lean_ctor_set(v___x_4901_, 3, v_l_4877_);
                        leanh::lean_ctor_set(v___x_4901_, 2, v_v_4876_);
                        leanh::lean_ctor_set(v___x_4901_, 1, v_k_4875_);
                        leanh::lean_ctor_set(v___x_4901_, 0, v___x_4947_);
                        v___x_4949_ = v___x_4901_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4962_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4962_, 0, v___x_4947_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4962_, 1, v_k_4875_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4962_, 2, v_v_4876_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4962_, 3, v_l_4877_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4962_, 4, v_l_4890_);
                        v___x_4949_ = v_reuseFailAlloc_4962_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_4915_ = lean_nat_add(v___x_4885_, v_size_4886_);
                v___x_4916_ = lean_nat_add(v___x_4915_, v_size_4887_);
                leanh::lean_dec(v_size_4887_);
                if leanh::lean_obj_tag(v_l_4906_) == 0 {
                    v_size_4937_ = leanh::lean_ctor_get(v_l_4906_, 0);
                    leanh::lean_inc(v_size_4937_);
                    v___y_4929_ = v_size_4937_;
                    state = 8;
                    continue;
                } else {
                    v___x_4938_ = leanh::lean_unsigned_to_nat(0);
                    v___y_4929_ = v___x_4938_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_4921_ = lean_nat_add(v___y_4918_, v___y_4920_);
                leanh::lean_dec(v___y_4920_);
                leanh::lean_dec(v___y_4918_);
                if v_isShared_4914_ == 0 {
                    leanh::lean_ctor_set(v___x_4913_, 4, v_r_4891_);
                    leanh::lean_ctor_set(v___x_4913_, 3, v_r_4907_);
                    leanh::lean_ctor_set(v___x_4913_, 2, v_v_4889_);
                    leanh::lean_ctor_set(v___x_4913_, 1, v_k_4888_);
                    leanh::lean_ctor_set(v___x_4913_, 0, v___x_4921_);
                    v___x_4923_ = v___x_4913_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4927_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4927_, 0, v___x_4921_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4927_, 1, v_k_4888_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4927_, 2, v_v_4889_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4927_, 3, v_r_4907_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4927_, 4, v_r_4891_);
                    v___x_4923_ = v_reuseFailAlloc_4927_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4902_ == 0 {
                    leanh::lean_ctor_set(v___x_4901_, 4, v___x_4923_);
                    leanh::lean_ctor_set(v___x_4901_, 3, v___y_4919_);
                    leanh::lean_ctor_set(v___x_4901_, 2, v_v_4905_);
                    leanh::lean_ctor_set(v___x_4901_, 1, v_k_4904_);
                    leanh::lean_ctor_set(v___x_4901_, 0, v___x_4916_);
                    v___x_4925_ = v___x_4901_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4926_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4926_, 0, v___x_4916_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4926_, 1, v_k_4904_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4926_, 2, v_v_4905_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4926_, 3, v___y_4919_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4926_, 4, v___x_4923_);
                    v___x_4925_ = v_reuseFailAlloc_4926_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4925_;
            }
            8 => {
                v___x_4930_ = lean_nat_add(v___x_4915_, v___y_4929_);
                leanh::lean_dec(v___y_4929_);
                leanh::lean_dec(v___x_4915_);
                if v_isShared_4881_ == 0 {
                    leanh::lean_ctor_set(v___x_4880_, 4, v_l_4906_);
                    leanh::lean_ctor_set(v___x_4880_, 0, v___x_4930_);
                    v___x_4932_ = v___x_4880_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4936_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4936_, 0, v___x_4930_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4936_, 1, v_k_4875_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4936_, 2, v_v_4876_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4936_, 3, v_l_4877_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4936_, 4, v_l_4906_);
                    v___x_4932_ = v_reuseFailAlloc_4936_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_4933_ = lean_nat_add(v___x_4885_, v_size_4908_);
                if leanh::lean_obj_tag(v_r_4907_) == 0 {
                    v_size_4934_ = leanh::lean_ctor_get(v_r_4907_, 0);
                    leanh::lean_inc(v_size_4934_);
                    v___y_4918_ = v___x_4933_;
                    v___y_4919_ = v___x_4932_;
                    v___y_4920_ = v_size_4934_;
                    state = 5;
                    continue;
                } else {
                    v___x_4935_ = leanh::lean_unsigned_to_nat(0);
                    v___y_4918_ = v___x_4933_;
                    v___y_4919_ = v___x_4932_;
                    v___y_4920_ = v___x_4935_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_4956_ = (!leanh::lean_is_exclusive(v_l_4877_)) as u8;
                if v_isSharedCheck_4956_ == 0 {
                    v_unused_4957_ = leanh::lean_ctor_get(v_l_4877_, 4);
                    leanh::lean_dec(v_unused_4957_);
                    v_unused_4958_ = leanh::lean_ctor_get(v_l_4877_, 3);
                    leanh::lean_dec(v_unused_4958_);
                    v_unused_4959_ = leanh::lean_ctor_get(v_l_4877_, 2);
                    leanh::lean_dec(v_unused_4959_);
                    v_unused_4960_ = leanh::lean_ctor_get(v_l_4877_, 1);
                    leanh::lean_dec(v_unused_4960_);
                    v_unused_4961_ = leanh::lean_ctor_get(v_l_4877_, 0);
                    leanh::lean_dec(v_unused_4961_);
                    v___x_4951_ = v_l_4877_;
                    v_isShared_4952_ = v_isSharedCheck_4956_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_dec(v_l_4877_);
                    v___x_4951_ = leanh::lean_box(0);
                    v_isShared_4952_ = v_isSharedCheck_4956_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_4952_ == 0 {
                    leanh::lean_ctor_set(v___x_4951_, 4, v_r_4891_);
                    leanh::lean_ctor_set(v___x_4951_, 3, v___x_4949_);
                    leanh::lean_ctor_set(v___x_4951_, 2, v_v_4889_);
                    leanh::lean_ctor_set(v___x_4951_, 1, v_k_4888_);
                    leanh::lean_ctor_set(v___x_4951_, 0, v___x_4946_);
                    v___x_4954_ = v___x_4951_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4955_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4955_, 0, v___x_4946_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4955_, 1, v_k_4888_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4955_, 2, v_v_4889_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4955_, 3, v___x_4949_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4955_, 4, v_r_4891_);
                    v___x_4954_ = v_reuseFailAlloc_4955_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4954_;
            }
            13 => {
                v_k_4976_ = leanh::lean_ctor_get(v_l_4969_, 1);
                v_v_4977_ = leanh::lean_ctor_get(v_l_4969_, 2);
                v_isSharedCheck_4991_ = (!leanh::lean_is_exclusive(v_l_4969_)) as u8;
                if v_isSharedCheck_4991_ == 0 {
                    v_unused_4992_ = leanh::lean_ctor_get(v_l_4969_, 4);
                    leanh::lean_dec(v_unused_4992_);
                    v_unused_4993_ = leanh::lean_ctor_get(v_l_4969_, 3);
                    leanh::lean_dec(v_unused_4993_);
                    v_unused_4994_ = leanh::lean_ctor_get(v_l_4969_, 0);
                    leanh::lean_dec(v_unused_4994_);
                    v___x_4979_ = v_l_4969_;
                    v_isShared_4980_ = v_isSharedCheck_4991_;
                    state = 14;
                    continue;
                } else {
                    leanh::lean_inc(v_v_4977_);
                    leanh::lean_inc(v_k_4976_);
                    leanh::lean_dec(v_l_4969_);
                    v___x_4979_ = leanh::lean_box(0);
                    v_isShared_4980_ = v_isSharedCheck_4991_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_4981_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc_n(v_r_4970_, 2);
                if v_isShared_4980_ == 0 {
                    leanh::lean_ctor_set(v___x_4979_, 4, v_r_4970_);
                    leanh::lean_ctor_set(v___x_4979_, 3, v_r_4970_);
                    leanh::lean_ctor_set(v___x_4979_, 2, v_v_4876_);
                    leanh::lean_ctor_set(v___x_4979_, 1, v_k_4875_);
                    leanh::lean_ctor_set(v___x_4979_, 0, v___x_4885_);
                    v___x_4983_ = v___x_4979_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4990_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4990_, 0, v___x_4885_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4990_, 1, v_k_4875_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4990_, 2, v_v_4876_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4990_, 3, v_r_4970_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4990_, 4, v_r_4970_);
                    v___x_4983_ = v_reuseFailAlloc_4990_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                leanh::lean_inc(v_r_4970_);
                if v_isShared_4975_ == 0 {
                    leanh::lean_ctor_set(v___x_4974_, 3, v_r_4970_);
                    leanh::lean_ctor_set(v___x_4974_, 0, v___x_4885_);
                    v___x_4985_ = v___x_4974_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4989_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4989_, 0, v___x_4885_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4989_, 1, v_k_4971_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4989_, 2, v_v_4972_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4989_, 3, v_r_4970_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4989_, 4, v_r_4970_);
                    v___x_4985_ = v_reuseFailAlloc_4989_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_4881_ == 0 {
                    leanh::lean_ctor_set(v___x_4880_, 4, v___x_4985_);
                    leanh::lean_ctor_set(v___x_4880_, 3, v___x_4983_);
                    leanh::lean_ctor_set(v___x_4880_, 2, v_v_4977_);
                    leanh::lean_ctor_set(v___x_4880_, 1, v_k_4976_);
                    leanh::lean_ctor_set(v___x_4880_, 0, v___x_4981_);
                    v___x_4987_ = v___x_4880_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4988_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4988_, 0, v___x_4981_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4988_, 1, v_k_4976_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4988_, 2, v_v_4977_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4988_, 3, v___x_4983_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4988_, 4, v___x_4985_);
                    v___x_4987_ = v_reuseFailAlloc_4988_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4987_;
            }
            18 => {
                v___x_5004_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_5003_ == 0 {
                    leanh::lean_ctor_set(v___x_5002_, 4, v_l_4969_);
                    leanh::lean_ctor_set(v___x_5002_, 2, v_v_4876_);
                    leanh::lean_ctor_set(v___x_5002_, 1, v_k_4875_);
                    leanh::lean_ctor_set(v___x_5002_, 0, v___x_4885_);
                    v___x_5006_ = v___x_5002_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5010_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5010_, 0, v___x_4885_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5010_, 1, v_k_4875_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5010_, 2, v_v_4876_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5010_, 3, v_l_4969_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5010_, 4, v_l_4969_);
                    v___x_5006_ = v_reuseFailAlloc_5010_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_4881_ == 0 {
                    leanh::lean_ctor_set(v___x_4880_, 4, v_r_4998_);
                    leanh::lean_ctor_set(v___x_4880_, 3, v___x_5006_);
                    leanh::lean_ctor_set(v___x_4880_, 2, v_v_5000_);
                    leanh::lean_ctor_set(v___x_4880_, 1, v_k_4999_);
                    leanh::lean_ctor_set(v___x_4880_, 0, v___x_5004_);
                    v___x_5008_ = v___x_4880_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5009_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5009_, 0, v___x_5004_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5009_, 1, v_k_4999_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5009_, 2, v_v_5000_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5009_, 3, v___x_5006_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5009_, 4, v_r_4998_);
                    v___x_5008_ = v_reuseFailAlloc_5009_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5008_;
            }
            21 => {
                return v___x_5017_;
            }
            22 => {
                return v___x_5020_;
            }
            23 => {
                return v___x_5036_;
            }
            24 => {
                v_size_5041_ = leanh::lean_ctor_get(v_l_5028_, 0);
                v_size_5042_ = leanh::lean_ctor_get(v_r_5029_, 0);
                v_k_5043_ = leanh::lean_ctor_get(v_r_5029_, 1);
                v_v_5044_ = leanh::lean_ctor_get(v_r_5029_, 2);
                v_l_5045_ = leanh::lean_ctor_get(v_r_5029_, 3);
                v_r_5046_ = leanh::lean_ctor_get(v_r_5029_, 4);
                v___x_5047_ = leanh::lean_unsigned_to_nat(2);
                v___x_5048_ = lean_nat_mul(v___x_5047_, v_size_5041_);
                v___x_5049_ = lean_nat_dec_lt(v_size_5042_, v___x_5048_);
                leanh::lean_dec(v___x_5048_);
                if v___x_5049_ == 0 {
                    leanh::lean_inc(v_r_5046_);
                    leanh::lean_inc(v_l_5045_);
                    leanh::lean_inc(v_v_5044_);
                    leanh::lean_inc(v_k_5043_);
                    v_isSharedCheck_5078_ = (!leanh::lean_is_exclusive(v_r_5029_)) as u8;
                    if v_isSharedCheck_5078_ == 0 {
                        v_unused_5079_ = leanh::lean_ctor_get(v_r_5029_, 4);
                        leanh::lean_dec(v_unused_5079_);
                        v_unused_5080_ = leanh::lean_ctor_get(v_r_5029_, 3);
                        leanh::lean_dec(v_unused_5080_);
                        v_unused_5081_ = leanh::lean_ctor_get(v_r_5029_, 2);
                        leanh::lean_dec(v_unused_5081_);
                        v_unused_5082_ = leanh::lean_ctor_get(v_r_5029_, 1);
                        leanh::lean_dec(v_unused_5082_);
                        v_unused_5083_ = leanh::lean_ctor_get(v_r_5029_, 0);
                        leanh::lean_dec(v_unused_5083_);
                        v___x_5051_ = v_r_5029_;
                        v_isShared_5052_ = v_isSharedCheck_5078_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_5029_);
                        v___x_5051_ = leanh::lean_box(0);
                        v_isShared_5052_ = v_isSharedCheck_5078_;
                        state = 25;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4880_);
                    v___x_5084_ = lean_nat_add(v___x_5023_, v_size_5025_);
                    leanh::lean_dec(v_size_5025_);
                    v___x_5085_ = lean_nat_add(v___x_5084_, v_size_5024_);
                    leanh::lean_dec(v___x_5084_);
                    v___x_5086_ = lean_nat_add(v___x_5023_, v_size_5024_);
                    v___x_5087_ = lean_nat_add(v___x_5086_, v_size_5042_);
                    leanh::lean_dec(v___x_5086_);
                    leanh::lean_inc_ref(v_r_4878_);
                    if v_isShared_5040_ == 0 {
                        leanh::lean_ctor_set(v___x_5039_, 4, v_r_4878_);
                        leanh::lean_ctor_set(v___x_5039_, 3, v_r_5029_);
                        leanh::lean_ctor_set(v___x_5039_, 2, v_v_4876_);
                        leanh::lean_ctor_set(v___x_5039_, 1, v_k_4875_);
                        leanh::lean_ctor_set(v___x_5039_, 0, v___x_5087_);
                        v___x_5089_ = v___x_5039_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_5102_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5102_, 0, v___x_5087_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5102_, 1, v_k_4875_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5102_, 2, v_v_4876_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5102_, 3, v_r_5029_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5102_, 4, v_r_4878_);
                        v___x_5089_ = v_reuseFailAlloc_5102_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_5053_ = lean_nat_add(v___x_5023_, v_size_5025_);
                leanh::lean_dec(v_size_5025_);
                v___x_5054_ = lean_nat_add(v___x_5053_, v_size_5024_);
                leanh::lean_dec(v___x_5053_);
                v___x_5066_ = lean_nat_add(v___x_5023_, v_size_5041_);
                if leanh::lean_obj_tag(v_l_5045_) == 0 {
                    v_size_5076_ = leanh::lean_ctor_get(v_l_5045_, 0);
                    leanh::lean_inc(v_size_5076_);
                    v___y_5068_ = v_size_5076_;
                    state = 29;
                    continue;
                } else {
                    v___x_5077_ = leanh::lean_unsigned_to_nat(0);
                    v___y_5068_ = v___x_5077_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_5059_ = lean_nat_add(v___y_5057_, v___y_5058_);
                leanh::lean_dec(v___y_5058_);
                leanh::lean_dec(v___y_5057_);
                if v_isShared_5052_ == 0 {
                    leanh::lean_ctor_set(v___x_5051_, 4, v_r_4878_);
                    leanh::lean_ctor_set(v___x_5051_, 3, v_r_5046_);
                    leanh::lean_ctor_set(v___x_5051_, 2, v_v_4876_);
                    leanh::lean_ctor_set(v___x_5051_, 1, v_k_4875_);
                    leanh::lean_ctor_set(v___x_5051_, 0, v___x_5059_);
                    v___x_5061_ = v___x_5051_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_5065_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5065_, 0, v___x_5059_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5065_, 1, v_k_4875_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5065_, 2, v_v_4876_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5065_, 3, v_r_5046_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5065_, 4, v_r_4878_);
                    v___x_5061_ = v_reuseFailAlloc_5065_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_5040_ == 0 {
                    leanh::lean_ctor_set(v___x_5039_, 4, v___x_5061_);
                    leanh::lean_ctor_set(v___x_5039_, 3, v___y_5056_);
                    leanh::lean_ctor_set(v___x_5039_, 2, v_v_5044_);
                    leanh::lean_ctor_set(v___x_5039_, 1, v_k_5043_);
                    leanh::lean_ctor_set(v___x_5039_, 0, v___x_5054_);
                    v___x_5063_ = v___x_5039_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5064_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5064_, 0, v___x_5054_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5064_, 1, v_k_5043_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5064_, 2, v_v_5044_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5064_, 3, v___y_5056_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5064_, 4, v___x_5061_);
                    v___x_5063_ = v_reuseFailAlloc_5064_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_5063_;
            }
            29 => {
                v___x_5069_ = lean_nat_add(v___x_5066_, v___y_5068_);
                leanh::lean_dec(v___y_5068_);
                leanh::lean_dec(v___x_5066_);
                if v_isShared_4881_ == 0 {
                    leanh::lean_ctor_set(v___x_4880_, 4, v_l_5045_);
                    leanh::lean_ctor_set(v___x_4880_, 3, v_l_5028_);
                    leanh::lean_ctor_set(v___x_4880_, 2, v_v_5027_);
                    leanh::lean_ctor_set(v___x_4880_, 1, v_k_5026_);
                    leanh::lean_ctor_set(v___x_4880_, 0, v___x_5069_);
                    v___x_5071_ = v___x_4880_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_5075_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 0, v___x_5069_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 1, v_k_5026_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 2, v_v_5027_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 3, v_l_5028_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 4, v_l_5045_);
                    v___x_5071_ = v_reuseFailAlloc_5075_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_5072_ = lean_nat_add(v___x_5023_, v_size_5024_);
                if leanh::lean_obj_tag(v_r_5046_) == 0 {
                    v_size_5073_ = leanh::lean_ctor_get(v_r_5046_, 0);
                    leanh::lean_inc(v_size_5073_);
                    v___y_5056_ = v___x_5071_;
                    v___y_5057_ = v___x_5072_;
                    v___y_5058_ = v_size_5073_;
                    state = 26;
                    continue;
                } else {
                    v___x_5074_ = leanh::lean_unsigned_to_nat(0);
                    v___y_5056_ = v___x_5071_;
                    v___y_5057_ = v___x_5072_;
                    v___y_5058_ = v___x_5074_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_5096_ = (!leanh::lean_is_exclusive(v_r_4878_)) as u8;
                if v_isSharedCheck_5096_ == 0 {
                    v_unused_5097_ = leanh::lean_ctor_get(v_r_4878_, 4);
                    leanh::lean_dec(v_unused_5097_);
                    v_unused_5098_ = leanh::lean_ctor_get(v_r_4878_, 3);
                    leanh::lean_dec(v_unused_5098_);
                    v_unused_5099_ = leanh::lean_ctor_get(v_r_4878_, 2);
                    leanh::lean_dec(v_unused_5099_);
                    v_unused_5100_ = leanh::lean_ctor_get(v_r_4878_, 1);
                    leanh::lean_dec(v_unused_5100_);
                    v_unused_5101_ = leanh::lean_ctor_get(v_r_4878_, 0);
                    leanh::lean_dec(v_unused_5101_);
                    v___x_5091_ = v_r_4878_;
                    v_isShared_5092_ = v_isSharedCheck_5096_;
                    state = 32;
                    continue;
                } else {
                    leanh::lean_dec(v_r_4878_);
                    v___x_5091_ = leanh::lean_box(0);
                    v_isShared_5092_ = v_isSharedCheck_5096_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_5092_ == 0 {
                    leanh::lean_ctor_set(v___x_5091_, 4, v___x_5089_);
                    leanh::lean_ctor_set(v___x_5091_, 3, v_l_5028_);
                    leanh::lean_ctor_set(v___x_5091_, 2, v_v_5027_);
                    leanh::lean_ctor_set(v___x_5091_, 1, v_k_5026_);
                    leanh::lean_ctor_set(v___x_5091_, 0, v___x_5085_);
                    v___x_5094_ = v___x_5091_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_5095_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5095_, 0, v___x_5085_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5095_, 1, v_k_5026_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5095_, 2, v_v_5027_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5095_, 3, v_l_5028_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5095_, 4, v___x_5089_);
                    v___x_5094_ = v_reuseFailAlloc_5095_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_5094_;
            }
            34 => {
                v___x_5116_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc(v_r_5110_);
                if v_isShared_5115_ == 0 {
                    leanh::lean_ctor_set(v___x_5114_, 3, v_r_5110_);
                    leanh::lean_ctor_set(v___x_5114_, 2, v_v_4876_);
                    leanh::lean_ctor_set(v___x_5114_, 1, v_k_4875_);
                    leanh::lean_ctor_set(v___x_5114_, 0, v___x_5023_);
                    v___x_5118_ = v___x_5114_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_5122_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5122_, 0, v___x_5023_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5122_, 1, v_k_4875_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5122_, 2, v_v_4876_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5122_, 3, v_r_5110_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5122_, 4, v_r_5110_);
                    v___x_5118_ = v_reuseFailAlloc_5122_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_4881_ == 0 {
                    leanh::lean_ctor_set(v___x_4880_, 4, v___x_5118_);
                    leanh::lean_ctor_set(v___x_4880_, 3, v_l_5109_);
                    leanh::lean_ctor_set(v___x_4880_, 2, v_v_5112_);
                    leanh::lean_ctor_set(v___x_4880_, 1, v_k_5111_);
                    leanh::lean_ctor_set(v___x_4880_, 0, v___x_5116_);
                    v___x_5120_ = v___x_4880_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_5121_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5121_, 0, v___x_5116_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5121_, 1, v_k_5111_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5121_, 2, v_v_5112_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5121_, 3, v_l_5109_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5121_, 4, v___x_5118_);
                    v___x_5120_ = v_reuseFailAlloc_5121_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_5120_;
            }
            37 => {
                v_k_5132_ = leanh::lean_ctor_get(v_r_5126_, 1);
                v_v_5133_ = leanh::lean_ctor_get(v_r_5126_, 2);
                v_isSharedCheck_5147_ = (!leanh::lean_is_exclusive(v_r_5126_)) as u8;
                if v_isSharedCheck_5147_ == 0 {
                    v_unused_5148_ = leanh::lean_ctor_get(v_r_5126_, 4);
                    leanh::lean_dec(v_unused_5148_);
                    v_unused_5149_ = leanh::lean_ctor_get(v_r_5126_, 3);
                    leanh::lean_dec(v_unused_5149_);
                    v_unused_5150_ = leanh::lean_ctor_get(v_r_5126_, 0);
                    leanh::lean_dec(v_unused_5150_);
                    v___x_5135_ = v_r_5126_;
                    v_isShared_5136_ = v_isSharedCheck_5147_;
                    state = 38;
                    continue;
                } else {
                    leanh::lean_inc(v_v_5133_);
                    leanh::lean_inc(v_k_5132_);
                    leanh::lean_dec(v_r_5126_);
                    v___x_5135_ = leanh::lean_box(0);
                    v_isShared_5136_ = v_isSharedCheck_5147_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_5137_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_5136_ == 0 {
                    leanh::lean_ctor_set(v___x_5135_, 4, v_l_5109_);
                    leanh::lean_ctor_set(v___x_5135_, 3, v_l_5109_);
                    leanh::lean_ctor_set(v___x_5135_, 2, v_v_5128_);
                    leanh::lean_ctor_set(v___x_5135_, 1, v_k_5127_);
                    leanh::lean_ctor_set(v___x_5135_, 0, v___x_5023_);
                    v___x_5139_ = v___x_5135_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_5146_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 0, v___x_5023_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 1, v_k_5127_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 2, v_v_5128_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 3, v_l_5109_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 4, v_l_5109_);
                    v___x_5139_ = v_reuseFailAlloc_5146_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                if v_isShared_5131_ == 0 {
                    leanh::lean_ctor_set(v___x_5130_, 4, v_l_5109_);
                    leanh::lean_ctor_set(v___x_5130_, 2, v_v_4876_);
                    leanh::lean_ctor_set(v___x_5130_, 1, v_k_4875_);
                    leanh::lean_ctor_set(v___x_5130_, 0, v___x_5023_);
                    v___x_5141_ = v___x_5130_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_5145_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5145_, 0, v___x_5023_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5145_, 1, v_k_4875_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5145_, 2, v_v_4876_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5145_, 3, v_l_5109_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5145_, 4, v_l_5109_);
                    v___x_5141_ = v_reuseFailAlloc_5145_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_4881_ == 0 {
                    leanh::lean_ctor_set(v___x_4880_, 4, v___x_5141_);
                    leanh::lean_ctor_set(v___x_4880_, 3, v___x_5139_);
                    leanh::lean_ctor_set(v___x_4880_, 2, v_v_5133_);
                    leanh::lean_ctor_set(v___x_4880_, 1, v_k_5132_);
                    leanh::lean_ctor_set(v___x_4880_, 0, v___x_5137_);
                    v___x_5143_ = v___x_4880_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_5144_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5144_, 0, v___x_5137_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5144_, 1, v_k_5132_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5144_, 2, v_v_5133_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5144_, 3, v___x_5139_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5144_, 4, v___x_5141_);
                    v___x_5143_ = v_reuseFailAlloc_5144_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_5143_;
            }
            42 => {
                return v___x_5157_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(
    mut v_k_5162_: *mut leanh::LeanObject,
    mut v_t_5163_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_k_5164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: u8 = 0;
    let mut v___x_5168_: u8 = 0;
    let mut v___x_5171_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_5163_) == 0 {
                    v_k_5164_ = leanh::lean_ctor_get(v_t_5163_, 1);
                    v_l_5165_ = leanh::lean_ctor_get(v_t_5163_, 3);
                    v_r_5166_ = leanh::lean_ctor_get(v_t_5163_, 4);
                    v___x_5167_ = lean_nat_dec_lt(v_k_5162_, v_k_5164_);
                    if v___x_5167_ == 0 {
                        v___x_5168_ = lean_nat_dec_eq(v_k_5162_, v_k_5164_);
                        if v___x_5168_ == 0 {
                            v_t_5163_ = v_r_5166_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_5168_;
                        }
                    } else {
                        v_t_5163_ = v_l_5165_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_5171_ = 0;
                    return v___x_5171_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg___boxed(
    mut v_k_5172_: *mut leanh::LeanObject,
    mut v_t_5173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5174_: u8 = 0;
    let mut v_r_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5174_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_k_5172_, v_t_5173_);
    leanh::lean_dec(v_t_5173_);
    leanh::lean_dec(v_k_5172_);
    v_r_5175_ = leanh::lean_box((v_res_5174_) as usize);
    return v_r_5175_;
}
pub unsafe fn l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(
    mut v_y_5176_: *mut leanh::LeanObject,
    mut v_x_5177_: *mut leanh::LeanObject,
    mut v_x_5178_: usize,
    mut v_x_5179_: usize,
) -> *mut leanh::LeanObject {
    let mut v_cs_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_5181_: usize = 0;
    let mut v___x_5182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: u8 = 0;
    let mut v___x_5186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5187_: u8 = 0;
    let mut v___x_5188_: usize = 0;
    let mut v___x_5189_: usize = 0;
    let mut v___x_5190_: usize = 0;
    let mut v_i_5191_: usize = 0;
    let mut v___x_5192_: usize = 0;
    let mut v_shift_5193_: usize = 0;
    let mut v_v_5194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5202_: u8 = 0;
    let mut v_unused_5203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: u8 = 0;
    let mut v___x_5209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5210_: u8 = 0;
    let mut v_v_5211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: u8 = 0;
    let mut v___x_5221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5222_: u8 = 0;
    let mut v_unused_5223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5177_) == 0 {
                    v_cs_5180_ = leanh::lean_ctor_get(v_x_5177_, 0);
                    v_j_5181_ = lean_usize_shift_right(v_x_5178_, v_x_5179_);
                    v___x_5182_ = lean_usize_to_nat(v_j_5181_);
                    v___x_5183_ = lean_array_get_size(v_cs_5180_);
                    v___x_5184_ = lean_nat_dec_lt(v___x_5182_, v___x_5183_);
                    if v___x_5184_ == 0 {
                        leanh::lean_dec(v___x_5182_);
                        leanh::lean_dec(v_y_5176_);
                        return v_x_5177_;
                    } else {
                        leanh::lean_inc_ref(v_cs_5180_);
                        v_isSharedCheck_5202_ = (!leanh::lean_is_exclusive(v_x_5177_)) as u8;
                        if v_isSharedCheck_5202_ == 0 {
                            v_unused_5203_ = leanh::lean_ctor_get(v_x_5177_, 0);
                            leanh::lean_dec(v_unused_5203_);
                            v___x_5186_ = v_x_5177_;
                            v_isShared_5187_ = v_isSharedCheck_5202_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_5177_);
                            v___x_5186_ = leanh::lean_box(0);
                            v_isShared_5187_ = v_isSharedCheck_5202_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_vs_5204_ = leanh::lean_ctor_get(v_x_5177_, 0);
                    v___x_5205_ = lean_usize_to_nat(v_x_5178_);
                    v___x_5206_ = lean_array_get_size(v_vs_5204_);
                    v___x_5207_ = lean_nat_dec_lt(v___x_5205_, v___x_5206_);
                    if v___x_5207_ == 0 {
                        leanh::lean_dec(v___x_5205_);
                        leanh::lean_dec(v_y_5176_);
                        return v_x_5177_;
                    } else {
                        leanh::lean_inc_ref(v_vs_5204_);
                        v_isSharedCheck_5222_ = (!leanh::lean_is_exclusive(v_x_5177_)) as u8;
                        if v_isSharedCheck_5222_ == 0 {
                            v_unused_5223_ = leanh::lean_ctor_get(v_x_5177_, 0);
                            leanh::lean_dec(v_unused_5223_);
                            v___x_5209_ = v_x_5177_;
                            v_isShared_5210_ = v_isSharedCheck_5222_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_5177_);
                            v___x_5209_ = leanh::lean_box(0);
                            v_isShared_5210_ = v_isSharedCheck_5222_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5188_ = 1usize;
                v___x_5189_ = lean_usize_shift_left(v___x_5188_, v_x_5179_);
                v___x_5190_ = lean_usize_sub(v___x_5189_, v___x_5188_);
                v_i_5191_ = lean_usize_land(v_x_5178_, v___x_5190_);
                v___x_5192_ = 5usize;
                v_shift_5193_ = lean_usize_sub(v_x_5179_, v___x_5192_);
                v_v_5194_ = lean_array_fget(v_cs_5180_, v___x_5182_);
                v___x_5195_ = leanh::lean_box(0);
                v_xs_x27_5196_ = lean_array_fset(v_cs_5180_, v___x_5182_, v___x_5195_);
                v___x_5197_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_5176_, v_v_5194_, v_i_5191_, v_shift_5193_);
                v___x_5198_ = lean_array_fset(v_xs_x27_5196_, v___x_5182_, v___x_5197_);
                leanh::lean_dec(v___x_5182_);
                if v_isShared_5187_ == 0 {
                    leanh::lean_ctor_set(v___x_5186_, 0, v___x_5198_);
                    v___x_5200_ = v___x_5186_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5201_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5201_, 0, v___x_5198_);
                    v___x_5200_ = v_reuseFailAlloc_5201_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5200_;
            }
            3 => {
                v_v_5211_ = lean_array_fget(v_vs_5204_, v___x_5205_);
                v___x_5212_ = leanh::lean_box(0);
                v_xs_x27_5213_ = lean_array_fset(v_vs_5204_, v___x_5205_, v___x_5212_);
                v___x_5220_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_5176_, v_v_5211_);
                if v___x_5220_ == 0 {
                    v___x_5221_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_y_5176_, v___x_5212_, v_v_5211_);
                    v___y_5215_ = v___x_5221_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_dec(v_y_5176_);
                    v___y_5215_ = v_v_5211_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5216_ = lean_array_fset(v_xs_x27_5213_, v___x_5205_, v___y_5215_);
                leanh::lean_dec(v___x_5205_);
                if v_isShared_5210_ == 0 {
                    leanh::lean_ctor_set(v___x_5209_, 0, v___x_5216_);
                    v___x_5218_ = v___x_5209_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5219_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5219_, 0, v___x_5216_);
                    v___x_5218_ = v_reuseFailAlloc_5219_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5218_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2___boxed(
    mut v_y_5224_: *mut leanh::LeanObject,
    mut v_x_5225_: *mut leanh::LeanObject,
    mut v_x_5226_: *mut leanh::LeanObject,
    mut v_x_5227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4518__boxed_5228_: usize = 0;
    let mut v_x_4519__boxed_5229_: usize = 0;
    let mut v_res_5230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4518__boxed_5228_ = leanh::lean_unbox_usize(v_x_5226_);
    leanh::lean_dec(v_x_5226_);
    v_x_4519__boxed_5229_ = leanh::lean_unbox_usize(v_x_5227_);
    leanh::lean_dec(v_x_5227_);
    v_res_5230_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_5224_, v_x_5225_, v_x_4518__boxed_5228_, v_x_4519__boxed_5229_);
    return v_res_5230_;
}
pub unsafe fn l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(
    mut v_y_5231_: *mut leanh::LeanObject,
    mut v_t_5232_: *mut leanh::LeanObject,
    mut v_i_5233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_5234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shift_5237_: usize = 0;
    let mut v_tailOff_5238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5241_: u8 = 0;
    let mut v___x_5242_: u8 = 0;
    let mut v___x_5243_: usize = 0;
    let mut v___x_5244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: u8 = 0;
    let mut v___x_5252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: u8 = 0;
    let mut v___x_5264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5265_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_5234_ = leanh::lean_ctor_get(v_t_5232_, 0);
                v_tail_5235_ = leanh::lean_ctor_get(v_t_5232_, 1);
                v_size_5236_ = leanh::lean_ctor_get(v_t_5232_, 2);
                v_shift_5237_ = leanh::lean_ctor_get_usize(v_t_5232_, 4);
                v_tailOff_5238_ = leanh::lean_ctor_get(v_t_5232_, 3);
                v_isSharedCheck_5265_ = (!leanh::lean_is_exclusive(v_t_5232_)) as u8;
                if v_isSharedCheck_5265_ == 0 {
                    v___x_5240_ = v_t_5232_;
                    v_isShared_5241_ = v_isSharedCheck_5265_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_tailOff_5238_);
                    leanh::lean_inc(v_size_5236_);
                    leanh::lean_inc(v_tail_5235_);
                    leanh::lean_inc(v_root_5234_);
                    leanh::lean_dec(v_t_5232_);
                    v___x_5240_ = leanh::lean_box(0);
                    v_isShared_5241_ = v_isSharedCheck_5265_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5242_ = lean_nat_dec_le(v_tailOff_5238_, v_i_5233_);
                if v___x_5242_ == 0 {
                    v___x_5243_ = lean_usize_of_nat(v_i_5233_);
                    v___x_5244_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_5231_, v_root_5234_, v___x_5243_, v_shift_5237_);
                    if v_isShared_5241_ == 0 {
                        leanh::lean_ctor_set(v___x_5240_, 0, v___x_5244_);
                        v___x_5246_ = v___x_5240_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5247_ = leanh::lean_alloc_ctor(
                            0,
                            4,
                            (core::mem::size_of::<usize>() * 1) as u32,
                        );
                        leanh::lean_ctor_set(v_reuseFailAlloc_5247_, 0, v___x_5244_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5247_, 1, v_tail_5235_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5247_, 2, v_size_5236_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5247_, 3, v_tailOff_5238_);
                        leanh::lean_ctor_set_usize(v_reuseFailAlloc_5247_, 4, v_shift_5237_);
                        v___x_5246_ = v_reuseFailAlloc_5247_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5248_ = lean_nat_sub(v_i_5233_, v_tailOff_5238_);
                    v___x_5249_ = lean_array_get_size(v_tail_5235_);
                    v___x_5250_ = lean_nat_dec_lt(v___x_5248_, v___x_5249_);
                    if v___x_5250_ == 0 {
                        leanh::lean_dec(v___x_5248_);
                        leanh::lean_dec(v_y_5231_);
                        if v_isShared_5241_ == 0 {
                            v___x_5252_ = v___x_5240_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5253_ = leanh::lean_alloc_ctor(
                                0,
                                4,
                                (core::mem::size_of::<usize>() * 1) as u32,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_5253_, 0, v_root_5234_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5253_, 1, v_tail_5235_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5253_, 2, v_size_5236_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5253_, 3, v_tailOff_5238_);
                            leanh::lean_ctor_set_usize(
                                v_reuseFailAlloc_5253_,
                                4,
                                v_shift_5237_,
                            );
                            v___x_5252_ = v_reuseFailAlloc_5253_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_v_5254_ = lean_array_fget(v_tail_5235_, v___x_5248_);
                        v___x_5255_ = leanh::lean_box(0);
                        v_xs_x27_5256_ = lean_array_fset(v_tail_5235_, v___x_5248_, v___x_5255_);
                        v___x_5263_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_5231_, v_v_5254_);
                        if v___x_5263_ == 0 {
                            v___x_5264_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_y_5231_, v___x_5255_, v_v_5254_);
                            v___y_5258_ = v___x_5264_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_dec(v_y_5231_);
                            v___y_5258_ = v_v_5254_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5246_;
            }
            3 => {
                return v___x_5252_;
            }
            4 => {
                v___x_5259_ = lean_array_fset(v_xs_x27_5256_, v___x_5248_, v___y_5258_);
                leanh::lean_dec(v___x_5248_);
                if v_isShared_5241_ == 0 {
                    leanh::lean_ctor_set(v___x_5240_, 1, v___x_5259_);
                    v___x_5261_ = v___x_5240_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5262_ = leanh::lean_alloc_ctor(
                        0,
                        4,
                        (core::mem::size_of::<usize>() * 1) as u32,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5262_, 0, v_root_5234_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5262_, 1, v___x_5259_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5262_, 2, v_size_5236_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5262_, 3, v_tailOff_5238_);
                    leanh::lean_ctor_set_usize(v_reuseFailAlloc_5262_, 4, v_shift_5237_);
                    v___x_5261_ = v_reuseFailAlloc_5262_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5261_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2___boxed(
    mut v_y_5266_: *mut leanh::LeanObject,
    mut v_t_5267_: *mut leanh::LeanObject,
    mut v_i_5268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5269_ =
        l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(
            v_y_5266_, v_t_5267_, v_i_5268_,
        );
    leanh::lean_dec(v_i_5268_);
    return v_res_5269_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0(
    mut v_y_5270_: *mut leanh::LeanObject,
    mut v_x_5271_: *mut leanh::LeanObject,
    mut v_s_5272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_vars_5273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_5274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_x27_5275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_x27_5276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natToIntMap_5277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natDef_5278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dvds_5279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lowers_5280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uppers_5281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_elimEqs_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_elimStack_5284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_occurs_5285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignment_5286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextCnstrId_5287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_caseSplits_5288_: u8 = 0;
    let mut v_conflict_x3f_5289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqSplits_5290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_divMod_5291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntIds_5292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntInfos_5293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntTermMap_5294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntVarMap_5295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedCommRing_5296_: u8 = 0;
    let mut v_nonlinearOccs_5297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5300_: u8 = 0;
    let mut v___x_5301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5305_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vars_5273_ = leanh::lean_ctor_get(v_s_5272_, 0);
                v_varMap_5274_ = leanh::lean_ctor_get(v_s_5272_, 1);
                v_vars_x27_5275_ = leanh::lean_ctor_get(v_s_5272_, 2);
                v_varMap_x27_5276_ = leanh::lean_ctor_get(v_s_5272_, 3);
                v_natToIntMap_5277_ = leanh::lean_ctor_get(v_s_5272_, 4);
                v_natDef_5278_ = leanh::lean_ctor_get(v_s_5272_, 5);
                v_dvds_5279_ = leanh::lean_ctor_get(v_s_5272_, 6);
                v_lowers_5280_ = leanh::lean_ctor_get(v_s_5272_, 7);
                v_uppers_5281_ = leanh::lean_ctor_get(v_s_5272_, 8);
                v_diseqs_5282_ = leanh::lean_ctor_get(v_s_5272_, 9);
                v_elimEqs_5283_ = leanh::lean_ctor_get(v_s_5272_, 10);
                v_elimStack_5284_ = leanh::lean_ctor_get(v_s_5272_, 11);
                v_occurs_5285_ = leanh::lean_ctor_get(v_s_5272_, 12);
                v_assignment_5286_ = leanh::lean_ctor_get(v_s_5272_, 13);
                v_nextCnstrId_5287_ = leanh::lean_ctor_get(v_s_5272_, 14);
                v_caseSplits_5288_ = leanh::lean_ctor_get_uint8(
                    v_s_5272_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 23) as u32,
                );
                v_conflict_x3f_5289_ = leanh::lean_ctor_get(v_s_5272_, 15);
                v_diseqSplits_5290_ = leanh::lean_ctor_get(v_s_5272_, 16);
                v_divMod_5291_ = leanh::lean_ctor_get(v_s_5272_, 17);
                v_toIntIds_5292_ = leanh::lean_ctor_get(v_s_5272_, 18);
                v_toIntInfos_5293_ = leanh::lean_ctor_get(v_s_5272_, 19);
                v_toIntTermMap_5294_ = leanh::lean_ctor_get(v_s_5272_, 20);
                v_toIntVarMap_5295_ = leanh::lean_ctor_get(v_s_5272_, 21);
                v_usedCommRing_5296_ = leanh::lean_ctor_get_uint8(
                    v_s_5272_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 23 + 1) as u32,
                );
                v_nonlinearOccs_5297_ = leanh::lean_ctor_get(v_s_5272_, 22);
                v_isSharedCheck_5305_ = (!leanh::lean_is_exclusive(v_s_5272_)) as u8;
                if v_isSharedCheck_5305_ == 0 {
                    v___x_5299_ = v_s_5272_;
                    v_isShared_5300_ = v_isSharedCheck_5305_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_nonlinearOccs_5297_);
                    leanh::lean_inc(v_toIntVarMap_5295_);
                    leanh::lean_inc(v_toIntTermMap_5294_);
                    leanh::lean_inc(v_toIntInfos_5293_);
                    leanh::lean_inc(v_toIntIds_5292_);
                    leanh::lean_inc(v_divMod_5291_);
                    leanh::lean_inc(v_diseqSplits_5290_);
                    leanh::lean_inc(v_conflict_x3f_5289_);
                    leanh::lean_inc(v_nextCnstrId_5287_);
                    leanh::lean_inc(v_assignment_5286_);
                    leanh::lean_inc(v_occurs_5285_);
                    leanh::lean_inc(v_elimStack_5284_);
                    leanh::lean_inc(v_elimEqs_5283_);
                    leanh::lean_inc(v_diseqs_5282_);
                    leanh::lean_inc(v_uppers_5281_);
                    leanh::lean_inc(v_lowers_5280_);
                    leanh::lean_inc(v_dvds_5279_);
                    leanh::lean_inc(v_natDef_5278_);
                    leanh::lean_inc(v_natToIntMap_5277_);
                    leanh::lean_inc(v_varMap_x27_5276_);
                    leanh::lean_inc(v_vars_x27_5275_);
                    leanh::lean_inc(v_varMap_5274_);
                    leanh::lean_inc(v_vars_5273_);
                    leanh::lean_dec(v_s_5272_);
                    v___x_5299_ = leanh::lean_box(0);
                    v_isShared_5300_ = v_isSharedCheck_5305_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5301_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(v_y_5270_, v_occurs_5285_, v_x_5271_);
                if v_isShared_5300_ == 0 {
                    leanh::lean_ctor_set(v___x_5299_, 12, v___x_5301_);
                    v___x_5303_ = v___x_5299_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5304_ = leanh::lean_alloc_ctor(0, 23, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 0, v_vars_5273_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 1, v_varMap_5274_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 2, v_vars_x27_5275_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 3, v_varMap_x27_5276_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 4, v_natToIntMap_5277_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 5, v_natDef_5278_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 6, v_dvds_5279_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 7, v_lowers_5280_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 8, v_uppers_5281_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 9, v_diseqs_5282_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 10, v_elimEqs_5283_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 11, v_elimStack_5284_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 12, v___x_5301_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 13, v_assignment_5286_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 14, v_nextCnstrId_5287_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 15, v_conflict_x3f_5289_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 16, v_diseqSplits_5290_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 17, v_divMod_5291_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 18, v_toIntIds_5292_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 19, v_toIntInfos_5293_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 20, v_toIntTermMap_5294_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 21, v_toIntVarMap_5295_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 22, v_nonlinearOccs_5297_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5304_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 23) as u32,
                        v_caseSplits_5288_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5304_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 23 + 1) as u32,
                        v_usedCommRing_5296_,
                    );
                    v___x_5303_ = v_reuseFailAlloc_5304_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5303_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0___boxed(
    mut v_y_5306_: *mut leanh::LeanObject,
    mut v_x_5307_: *mut leanh::LeanObject,
    mut v_s_5308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5309_ =
        l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0(v_y_5306_, v_x_5307_, v_s_5308_);
    leanh::lean_dec(v_x_5307_);
    return v_res_5309_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(
    mut v_x_5310_: *mut leanh::LeanObject,
    mut v_y_5311_: *mut leanh::LeanObject,
    mut v_a_5312_: *mut leanh::LeanObject,
    mut v_a_5313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5319_: u8 = 0;
    let mut v___x_5320_: u8 = 0;
    let mut v___f_5321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5328_: u8 = 0;
    let mut v_a_5329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5332_: u8 = 0;
    let mut v___x_5334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5336_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5315_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(
                    v_x_5310_, v_a_5312_, v_a_5313_,
                );
                if leanh::lean_obj_tag(v___x_5315_) == 0 {
                    v_a_5316_ = leanh::lean_ctor_get(v___x_5315_, 0);
                    v_isSharedCheck_5328_ = (!leanh::lean_is_exclusive(v___x_5315_)) as u8;
                    if v_isSharedCheck_5328_ == 0 {
                        v___x_5318_ = v___x_5315_;
                        v_isShared_5319_ = v_isSharedCheck_5328_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5316_);
                        leanh::lean_dec(v___x_5315_);
                        v___x_5318_ = leanh::lean_box(0);
                        v_isShared_5319_ = v_isSharedCheck_5328_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_y_5311_);
                    leanh::lean_dec(v_x_5310_);
                    v_a_5329_ = leanh::lean_ctor_get(v___x_5315_, 0);
                    v_isSharedCheck_5336_ = (!leanh::lean_is_exclusive(v___x_5315_)) as u8;
                    if v_isSharedCheck_5336_ == 0 {
                        v___x_5331_ = v___x_5315_;
                        v_isShared_5332_ = v_isSharedCheck_5336_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5329_);
                        leanh::lean_dec(v___x_5315_);
                        v___x_5331_ = leanh::lean_box(0);
                        v_isShared_5332_ = v_isSharedCheck_5336_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5320_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_5311_, v_a_5316_);
                leanh::lean_dec(v_a_5316_);
                if v___x_5320_ == 0 {
                    leanh::lean_del_object(v___x_5318_);
                    v___f_5321_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    leanh::lean_closure_set(v___f_5321_, 0, v_y_5311_);
                    leanh::lean_closure_set(v___f_5321_, 1, v_x_5310_);
                    v___x_5322_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
                    v___x_5323_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_5322_, v___f_5321_, v_a_5312_);
                    return v___x_5323_;
                } else {
                    leanh::lean_dec(v_y_5311_);
                    leanh::lean_dec(v_x_5310_);
                    v___x_5324_ = leanh::lean_box(0);
                    if v_isShared_5319_ == 0 {
                        leanh::lean_ctor_set(v___x_5318_, 0, v___x_5324_);
                        v___x_5326_ = v___x_5318_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5327_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5327_, 0, v___x_5324_);
                        v___x_5326_ = v_reuseFailAlloc_5327_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5326_;
            }
            3 => {
                if v_isShared_5332_ == 0 {
                    v___x_5334_ = v___x_5331_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5335_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5335_, 0, v_a_5329_);
                    v___x_5334_ = v_reuseFailAlloc_5335_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5334_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___boxed(
    mut v_x_5337_: *mut leanh::LeanObject,
    mut v_y_5338_: *mut leanh::LeanObject,
    mut v_a_5339_: *mut leanh::LeanObject,
    mut v_a_5340_: *mut leanh::LeanObject,
    mut v_a_5341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5342_ =
        l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_x_5337_, v_y_5338_, v_a_5339_, v_a_5340_);
    leanh::lean_dec_ref(v_a_5340_);
    leanh::lean_dec(v_a_5339_);
    return v_res_5342_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_addOcc(
    mut v_x_5343_: *mut leanh::LeanObject,
    mut v_y_5344_: *mut leanh::LeanObject,
    mut v_a_5345_: *mut leanh::LeanObject,
    mut v_a_5346_: *mut leanh::LeanObject,
    mut v_a_5347_: *mut leanh::LeanObject,
    mut v_a_5348_: *mut leanh::LeanObject,
    mut v_a_5349_: *mut leanh::LeanObject,
    mut v_a_5350_: *mut leanh::LeanObject,
    mut v_a_5351_: *mut leanh::LeanObject,
    mut v_a_5352_: *mut leanh::LeanObject,
    mut v_a_5353_: *mut leanh::LeanObject,
    mut v_a_5354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5356_ =
        l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_x_5343_, v_y_5344_, v_a_5345_, v_a_5353_);
    return v___x_5356_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_addOcc___boxed(
    mut v_x_5357_: *mut leanh::LeanObject,
    mut v_y_5358_: *mut leanh::LeanObject,
    mut v_a_5359_: *mut leanh::LeanObject,
    mut v_a_5360_: *mut leanh::LeanObject,
    mut v_a_5361_: *mut leanh::LeanObject,
    mut v_a_5362_: *mut leanh::LeanObject,
    mut v_a_5363_: *mut leanh::LeanObject,
    mut v_a_5364_: *mut leanh::LeanObject,
    mut v_a_5365_: *mut leanh::LeanObject,
    mut v_a_5366_: *mut leanh::LeanObject,
    mut v_a_5367_: *mut leanh::LeanObject,
    mut v_a_5368_: *mut leanh::LeanObject,
    mut v_a_5369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5370_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc(
        v_x_5357_, v_y_5358_, v_a_5359_, v_a_5360_, v_a_5361_, v_a_5362_, v_a_5363_, v_a_5364_,
        v_a_5365_, v_a_5366_, v_a_5367_, v_a_5368_,
    );
    leanh::lean_dec(v_a_5368_);
    leanh::lean_dec_ref(v_a_5367_);
    leanh::lean_dec(v_a_5366_);
    leanh::lean_dec_ref(v_a_5365_);
    leanh::lean_dec(v_a_5364_);
    leanh::lean_dec_ref(v_a_5363_);
    leanh::lean_dec(v_a_5362_);
    leanh::lean_dec_ref(v_a_5361_);
    leanh::lean_dec(v_a_5360_);
    leanh::lean_dec(v_a_5359_);
    return v_res_5370_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0(
    mut v_00_u03b2_5371_: *mut leanh::LeanObject,
    mut v_k_5372_: *mut leanh::LeanObject,
    mut v_t_5373_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5374_: u8 = 0;
    v___x_5374_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_k_5372_, v_t_5373_);
    return v___x_5374_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___boxed(
    mut v_00_u03b2_5375_: *mut leanh::LeanObject,
    mut v_k_5376_: *mut leanh::LeanObject,
    mut v_t_5377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5378_: u8 = 0;
    let mut v_r_5379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5378_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0(
            v_00_u03b2_5375_,
            v_k_5376_,
            v_t_5377_,
        );
    leanh::lean_dec(v_t_5377_);
    leanh::lean_dec(v_k_5376_);
    v_r_5379_ = leanh::lean_box((v_res_5378_) as usize);
    return v_r_5379_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1(
    mut v_00_u03b2_5380_: *mut leanh::LeanObject,
    mut v_k_5381_: *mut leanh::LeanObject,
    mut v_v_5382_: *mut leanh::LeanObject,
    mut v_t_5383_: *mut leanh::LeanObject,
    mut v_hl_5384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5385_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_5381_, v_v_5382_, v_t_5383_);
    return v___x_5385_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___redArg(
    mut v_y_5386_: *mut leanh::LeanObject,
    mut v_p_5387_: *mut leanh::LeanObject,
    mut v_a_5388_: *mut leanh::LeanObject,
    mut v_a_5389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_5391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_p_5387_) == 1 {
                    v_v_5391_ = leanh::lean_ctor_get(v_p_5387_, 1);
                    leanh::lean_inc(v_v_5391_);
                    v_p_5392_ = leanh::lean_ctor_get(v_p_5387_, 2);
                    leanh::lean_inc_ref(v_p_5392_);
                    leanh::lean_dec_ref_known(v_p_5387_, 3);
                    leanh::lean_inc(v_y_5386_);
                    v___x_5393_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(
                        v_v_5391_, v_y_5386_, v_a_5388_, v_a_5389_,
                    );
                    if leanh::lean_obj_tag(v___x_5393_) == 0 {
                        leanh::lean_dec_ref_known(v___x_5393_, 1);
                        v_p_5387_ = v_p_5392_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_p_5392_);
                        leanh::lean_dec(v_y_5386_);
                        return v___x_5393_;
                    }
                } else {
                    leanh::lean_dec_ref(v_p_5387_);
                    leanh::lean_dec(v_y_5386_);
                    v___x_5395_ = leanh::lean_box(0);
                    v___x_5396_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5396_, 0, v___x_5395_);
                    return v___x_5396_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___redArg___boxed(
    mut v_y_5397_: *mut leanh::LeanObject,
    mut v_p_5398_: *mut leanh::LeanObject,
    mut v_a_5399_: *mut leanh::LeanObject,
    mut v_a_5400_: *mut leanh::LeanObject,
    mut v_a_5401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5402_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___redArg(v_y_5397_, v_p_5398_, v_a_5399_, v_a_5400_);
    leanh::lean_dec_ref(v_a_5400_);
    leanh::lean_dec(v_a_5399_);
    return v_res_5402_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go(
    mut v_y_5403_: *mut leanh::LeanObject,
    mut v_p_5404_: *mut leanh::LeanObject,
    mut v_a_5405_: *mut leanh::LeanObject,
    mut v_a_5406_: *mut leanh::LeanObject,
    mut v_a_5407_: *mut leanh::LeanObject,
    mut v_a_5408_: *mut leanh::LeanObject,
    mut v_a_5409_: *mut leanh::LeanObject,
    mut v_a_5410_: *mut leanh::LeanObject,
    mut v_a_5411_: *mut leanh::LeanObject,
    mut v_a_5412_: *mut leanh::LeanObject,
    mut v_a_5413_: *mut leanh::LeanObject,
    mut v_a_5414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5416_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___redArg(v_y_5403_, v_p_5404_, v_a_5405_, v_a_5413_);
    return v___x_5416_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___boxed(
    mut v_y_5417_: *mut leanh::LeanObject,
    mut v_p_5418_: *mut leanh::LeanObject,
    mut v_a_5419_: *mut leanh::LeanObject,
    mut v_a_5420_: *mut leanh::LeanObject,
    mut v_a_5421_: *mut leanh::LeanObject,
    mut v_a_5422_: *mut leanh::LeanObject,
    mut v_a_5423_: *mut leanh::LeanObject,
    mut v_a_5424_: *mut leanh::LeanObject,
    mut v_a_5425_: *mut leanh::LeanObject,
    mut v_a_5426_: *mut leanh::LeanObject,
    mut v_a_5427_: *mut leanh::LeanObject,
    mut v_a_5428_: *mut leanh::LeanObject,
    mut v_a_5429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5430_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go(
            v_y_5417_, v_p_5418_, v_a_5419_, v_a_5420_, v_a_5421_, v_a_5422_, v_a_5423_, v_a_5424_,
            v_a_5425_, v_a_5426_, v_a_5427_, v_a_5428_,
        );
    leanh::lean_dec(v_a_5428_);
    leanh::lean_dec_ref(v_a_5427_);
    leanh::lean_dec(v_a_5426_);
    leanh::lean_dec_ref(v_a_5425_);
    leanh::lean_dec(v_a_5424_);
    leanh::lean_dec_ref(v_a_5423_);
    leanh::lean_dec(v_a_5422_);
    leanh::lean_dec_ref(v_a_5421_);
    leanh::lean_dec(v_a_5420_);
    leanh::lean_dec(v_a_5419_);
    return v_res_5430_;
}
pub unsafe fn _init_l_Int_Linear_Poly_updateOccs___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5432_ = l_Int_Linear_Poly_updateOccs___redArg___closed__0;
    v___x_5433_ = l_Lean_stringToMessageData(v___x_5432_);
    return v___x_5433_;
}
pub unsafe fn l_Int_Linear_Poly_updateOccs___redArg(
    mut v_p_5434_: *mut leanh::LeanObject,
    mut v_a_5435_: *mut leanh::LeanObject,
    mut v_a_5436_: *mut leanh::LeanObject,
    mut v_a_5437_: *mut leanh::LeanObject,
    mut v_a_5438_: *mut leanh::LeanObject,
    mut v_a_5439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_p_5434_) == 1 {
        let mut v_v_5441_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_5442_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5443_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_v_5441_ = leanh::lean_ctor_get(v_p_5434_, 1);
        leanh::lean_inc(v_v_5441_);
        v_p_5442_ = leanh::lean_ctor_get(v_p_5434_, 2);
        leanh::lean_inc_ref(v_p_5442_);
        leanh::lean_dec_ref_known(v_p_5434_, 3);
        v___x_5443_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___redArg(v_v_5441_, v_p_5442_, v_a_5435_, v_a_5438_);
        return v___x_5443_;
    } else {
        let mut v___x_5444_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5445_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_p_5434_);
        v___x_5444_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_Linear_Poly_updateOccs___redArg___closed__1),
            core::ptr::addr_of_mut!(l_Int_Linear_Poly_updateOccs___redArg___closed__1_once),
            _init_l_Int_Linear_Poly_updateOccs___redArg___closed__1,
        );
        v___x_5445_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_5444_, v_a_5436_, v_a_5437_, v_a_5438_, v_a_5439_);
        return v___x_5445_;
    }
}
pub unsafe fn l_Int_Linear_Poly_updateOccs___redArg___boxed(
    mut v_p_5446_: *mut leanh::LeanObject,
    mut v_a_5447_: *mut leanh::LeanObject,
    mut v_a_5448_: *mut leanh::LeanObject,
    mut v_a_5449_: *mut leanh::LeanObject,
    mut v_a_5450_: *mut leanh::LeanObject,
    mut v_a_5451_: *mut leanh::LeanObject,
    mut v_a_5452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5453_ = l_Int_Linear_Poly_updateOccs___redArg(
        v_p_5446_, v_a_5447_, v_a_5448_, v_a_5449_, v_a_5450_, v_a_5451_,
    );
    leanh::lean_dec(v_a_5451_);
    leanh::lean_dec_ref(v_a_5450_);
    leanh::lean_dec(v_a_5449_);
    leanh::lean_dec_ref(v_a_5448_);
    leanh::lean_dec(v_a_5447_);
    return v_res_5453_;
}
pub unsafe fn l_Int_Linear_Poly_updateOccs(
    mut v_p_5454_: *mut leanh::LeanObject,
    mut v_a_5455_: *mut leanh::LeanObject,
    mut v_a_5456_: *mut leanh::LeanObject,
    mut v_a_5457_: *mut leanh::LeanObject,
    mut v_a_5458_: *mut leanh::LeanObject,
    mut v_a_5459_: *mut leanh::LeanObject,
    mut v_a_5460_: *mut leanh::LeanObject,
    mut v_a_5461_: *mut leanh::LeanObject,
    mut v_a_5462_: *mut leanh::LeanObject,
    mut v_a_5463_: *mut leanh::LeanObject,
    mut v_a_5464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5466_ = l_Int_Linear_Poly_updateOccs___redArg(
        v_p_5454_, v_a_5455_, v_a_5461_, v_a_5462_, v_a_5463_, v_a_5464_,
    );
    return v___x_5466_;
}
pub unsafe fn l_Int_Linear_Poly_updateOccs___boxed(
    mut v_p_5467_: *mut leanh::LeanObject,
    mut v_a_5468_: *mut leanh::LeanObject,
    mut v_a_5469_: *mut leanh::LeanObject,
    mut v_a_5470_: *mut leanh::LeanObject,
    mut v_a_5471_: *mut leanh::LeanObject,
    mut v_a_5472_: *mut leanh::LeanObject,
    mut v_a_5473_: *mut leanh::LeanObject,
    mut v_a_5474_: *mut leanh::LeanObject,
    mut v_a_5475_: *mut leanh::LeanObject,
    mut v_a_5476_: *mut leanh::LeanObject,
    mut v_a_5477_: *mut leanh::LeanObject,
    mut v_a_5478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5479_ = l_Int_Linear_Poly_updateOccs(
        v_p_5467_, v_a_5468_, v_a_5469_, v_a_5470_, v_a_5471_, v_a_5472_, v_a_5473_, v_a_5474_,
        v_a_5475_, v_a_5476_, v_a_5477_,
    );
    leanh::lean_dec(v_a_5477_);
    leanh::lean_dec_ref(v_a_5476_);
    leanh::lean_dec(v_a_5475_);
    leanh::lean_dec_ref(v_a_5474_);
    leanh::lean_dec(v_a_5473_);
    leanh::lean_dec_ref(v_a_5472_);
    leanh::lean_dec(v_a_5471_);
    leanh::lean_dec_ref(v_a_5470_);
    leanh::lean_dec(v_a_5469_);
    leanh::lean_dec(v_a_5468_);
    return v_res_5479_;
}
pub unsafe fn l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_eval_x3f_go_spec__0(
    mut v_a_5480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5481_ = l_Rat_ofInt(v_a_5480_);
    return v___x_5481_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_eval_x3f_go(
    mut v_a_5482_: *mut leanh::LeanObject,
    mut v_v_5483_: *mut leanh::LeanObject,
    mut v_a_5484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_5485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5488_: u8 = 0;
    let mut v___x_5489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5494_: u8 = 0;
    let mut v_k_5495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: u8 = 0;
    let mut v___x_5500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_5484_) == 0 {
                    v_k_5485_ = leanh::lean_ctor_get(v_a_5484_, 0);
                    v_isSharedCheck_5494_ = (!leanh::lean_is_exclusive(v_a_5484_)) as u8;
                    if v_isSharedCheck_5494_ == 0 {
                        v___x_5487_ = v_a_5484_;
                        v_isShared_5488_ = v_isSharedCheck_5494_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_5485_);
                        leanh::lean_dec(v_a_5484_);
                        v___x_5487_ = leanh::lean_box(0);
                        v_isShared_5488_ = v_isSharedCheck_5494_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_5495_ = leanh::lean_ctor_get(v_a_5484_, 0);
                    leanh::lean_inc(v_k_5495_);
                    v_v_5496_ = leanh::lean_ctor_get(v_a_5484_, 1);
                    leanh::lean_inc(v_v_5496_);
                    v_p_5497_ = leanh::lean_ctor_get(v_a_5484_, 2);
                    leanh::lean_inc_ref(v_p_5497_);
                    leanh::lean_dec_ref_known(v_a_5484_, 3);
                    v_size_5498_ = leanh::lean_ctor_get(v_a_5482_, 2);
                    v___x_5499_ = lean_nat_dec_lt(v_v_5496_, v_size_5498_);
                    if v___x_5499_ == 0 {
                        leanh::lean_dec_ref(v_p_5497_);
                        leanh::lean_dec(v_v_5496_);
                        leanh::lean_dec(v_k_5495_);
                        leanh::lean_dec_ref(v_v_5483_);
                        v___x_5500_ = leanh::lean_box(0);
                        return v___x_5500_;
                    } else {
                        v___x_5501_ = l_Rat_ofInt(v_k_5495_);
                        v___x_5502_ = l_instInhabitedRat;
                        v___x_5503_ = l_Lean_PersistentArray_get_x21___redArg(
                            v___x_5502_,
                            v_a_5482_,
                            v_v_5496_,
                        );
                        leanh::lean_dec(v_v_5496_);
                        v___x_5504_ = l_Rat_mul(v___x_5501_, v___x_5503_);
                        leanh::lean_dec_ref(v___x_5501_);
                        v___x_5505_ = l_Rat_add(v_v_5483_, v___x_5504_);
                        v_v_5483_ = v___x_5505_;
                        v_a_5484_ = v_p_5497_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5489_ = l_Rat_ofInt(v_k_5485_);
                v___x_5490_ = l_Rat_add(v_v_5483_, v___x_5489_);
                if v_isShared_5488_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5487_, 1);
                    leanh::lean_ctor_set(v___x_5487_, 0, v___x_5490_);
                    v___x_5492_ = v___x_5487_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5493_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5493_, 0, v___x_5490_);
                    v___x_5492_ = v_reuseFailAlloc_5493_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5492_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_eval_x3f_go___boxed(
    mut v_a_5507_: *mut leanh::LeanObject,
    mut v_v_5508_: *mut leanh::LeanObject,
    mut v_a_5509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5510_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_eval_x3f_go(
            v_a_5507_, v_v_5508_, v_a_5509_,
        );
    leanh::lean_dec_ref(v_a_5507_);
    return v_res_5510_;
}
pub unsafe fn l_Nat_cast___at___00Int_Linear_Poly_eval_x3f_spec__0(
    mut v_a_5511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5512_ = lean_nat_to_int(v_a_5511_);
    v___x_5513_ = l_Rat_ofInt(v___x_5512_);
    return v___x_5513_;
}
pub unsafe fn _init_l_Int_Linear_Poly_eval_x3f___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5514_ = leanh::lean_unsigned_to_nat(0);
    v___x_5515_ = l_Nat_cast___at___00Int_Linear_Poly_eval_x3f_spec__0(v___x_5514_);
    return v___x_5515_;
}
pub unsafe fn l_Int_Linear_Poly_eval_x3f___redArg(
    mut v_p_5516_: *mut leanh::LeanObject,
    mut v_a_5517_: *mut leanh::LeanObject,
    mut v_a_5518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5524_: u8 = 0;
    let mut v_assignment_5525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5531_: u8 = 0;
    let mut v_a_5532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5535_: u8 = 0;
    let mut v___x_5537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5539_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5520_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_5517_, v_a_5518_);
                if leanh::lean_obj_tag(v___x_5520_) == 0 {
                    v_a_5521_ = leanh::lean_ctor_get(v___x_5520_, 0);
                    v_isSharedCheck_5531_ = (!leanh::lean_is_exclusive(v___x_5520_)) as u8;
                    if v_isSharedCheck_5531_ == 0 {
                        v___x_5523_ = v___x_5520_;
                        v_isShared_5524_ = v_isSharedCheck_5531_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5521_);
                        leanh::lean_dec(v___x_5520_);
                        v___x_5523_ = leanh::lean_box(0);
                        v_isShared_5524_ = v_isSharedCheck_5531_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_p_5516_);
                    v_a_5532_ = leanh::lean_ctor_get(v___x_5520_, 0);
                    v_isSharedCheck_5539_ = (!leanh::lean_is_exclusive(v___x_5520_)) as u8;
                    if v_isSharedCheck_5539_ == 0 {
                        v___x_5534_ = v___x_5520_;
                        v_isShared_5535_ = v_isSharedCheck_5539_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5532_);
                        leanh::lean_dec(v___x_5520_);
                        v___x_5534_ = leanh::lean_box(0);
                        v_isShared_5535_ = v_isSharedCheck_5539_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_assignment_5525_ = leanh::lean_ctor_get(v_a_5521_, 13);
                leanh::lean_inc_ref(v_assignment_5525_);
                leanh::lean_dec(v_a_5521_);
                v___x_5526_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Int_Linear_Poly_eval_x3f___redArg___closed__0),
                    core::ptr::addr_of_mut!(l_Int_Linear_Poly_eval_x3f___redArg___closed__0_once),
                    _init_l_Int_Linear_Poly_eval_x3f___redArg___closed__0,
                );
                v___x_5527_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_eval_x3f_go(v_assignment_5525_, v___x_5526_, v_p_5516_);
                leanh::lean_dec_ref(v_assignment_5525_);
                if v_isShared_5524_ == 0 {
                    leanh::lean_ctor_set(v___x_5523_, 0, v___x_5527_);
                    v___x_5529_ = v___x_5523_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5530_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5530_, 0, v___x_5527_);
                    v___x_5529_ = v_reuseFailAlloc_5530_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5529_;
            }
            3 => {
                if v_isShared_5535_ == 0 {
                    v___x_5537_ = v___x_5534_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5538_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5538_, 0, v_a_5532_);
                    v___x_5537_ = v_reuseFailAlloc_5538_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5537_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Poly_eval_x3f___redArg___boxed(
    mut v_p_5540_: *mut leanh::LeanObject,
    mut v_a_5541_: *mut leanh::LeanObject,
    mut v_a_5542_: *mut leanh::LeanObject,
    mut v_a_5543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5544_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_5540_, v_a_5541_, v_a_5542_);
    leanh::lean_dec_ref(v_a_5542_);
    leanh::lean_dec(v_a_5541_);
    return v_res_5544_;
}
pub unsafe fn l_Int_Linear_Poly_eval_x3f(
    mut v_p_5545_: *mut leanh::LeanObject,
    mut v_a_5546_: *mut leanh::LeanObject,
    mut v_a_5547_: *mut leanh::LeanObject,
    mut v_a_5548_: *mut leanh::LeanObject,
    mut v_a_5549_: *mut leanh::LeanObject,
    mut v_a_5550_: *mut leanh::LeanObject,
    mut v_a_5551_: *mut leanh::LeanObject,
    mut v_a_5552_: *mut leanh::LeanObject,
    mut v_a_5553_: *mut leanh::LeanObject,
    mut v_a_5554_: *mut leanh::LeanObject,
    mut v_a_5555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5557_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_5545_, v_a_5546_, v_a_5554_);
    return v___x_5557_;
}
pub unsafe fn l_Int_Linear_Poly_eval_x3f___boxed(
    mut v_p_5558_: *mut leanh::LeanObject,
    mut v_a_5559_: *mut leanh::LeanObject,
    mut v_a_5560_: *mut leanh::LeanObject,
    mut v_a_5561_: *mut leanh::LeanObject,
    mut v_a_5562_: *mut leanh::LeanObject,
    mut v_a_5563_: *mut leanh::LeanObject,
    mut v_a_5564_: *mut leanh::LeanObject,
    mut v_a_5565_: *mut leanh::LeanObject,
    mut v_a_5566_: *mut leanh::LeanObject,
    mut v_a_5567_: *mut leanh::LeanObject,
    mut v_a_5568_: *mut leanh::LeanObject,
    mut v_a_5569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5570_ = l_Int_Linear_Poly_eval_x3f(
        v_p_5558_, v_a_5559_, v_a_5560_, v_a_5561_, v_a_5562_, v_a_5563_, v_a_5564_, v_a_5565_,
        v_a_5566_, v_a_5567_, v_a_5568_,
    );
    leanh::lean_dec(v_a_5568_);
    leanh::lean_dec_ref(v_a_5567_);
    leanh::lean_dec(v_a_5566_);
    leanh::lean_dec_ref(v_a_5565_);
    leanh::lean_dec(v_a_5564_);
    leanh::lean_dec_ref(v_a_5563_);
    leanh::lean_dec(v_a_5562_);
    leanh::lean_dec_ref(v_a_5561_);
    leanh::lean_dec(v_a_5560_);
    leanh::lean_dec(v_a_5559_);
    return v_res_5570_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(
    mut v_c_5571_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_p_5572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: u8 = 0;
    v_p_5572_ = leanh::lean_ctor_get(v_c_5571_, 0);
    v___x_5573_ = l_Int_Linear_Poly_isUnsatLe(v_p_5572_);
    return v___x_5573_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat___boxed(
    mut v_c_5574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5575_: u8 = 0;
    let mut v_r_5576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5575_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(v_c_5574_);
    leanh::lean_dec_ref(v_c_5574_);
    v_r_5576_ = leanh::lean_box((v_res_5575_) as usize);
    return v_r_5576_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(
    mut v_c_5577_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_d_5578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5580_: u8 = 0;
    v_d_5578_ = leanh::lean_ctor_get(v_c_5577_, 0);
    leanh::lean_inc(v_d_5578_);
    v_p_5579_ = leanh::lean_ctor_get(v_c_5577_, 1);
    leanh::lean_inc_ref(v_p_5579_);
    leanh::lean_dec_ref(v_c_5577_);
    v___x_5580_ = l_Int_Linear_Poly_isUnsatDvd(v_d_5578_, v_p_5579_);
    leanh::lean_dec_ref(v_p_5579_);
    return v___x_5580_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat___boxed(
    mut v_c_5581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5582_: u8 = 0;
    let mut v_r_5583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5582_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(v_c_5581_);
    v_r_5583_ = leanh::lean_box((v_res_5582_) as usize);
    return v_r_5583_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(
    mut v_c_5584_: *mut leanh::LeanObject,
    mut v_a_5585_: *mut leanh::LeanObject,
    mut v_a_5586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_d_5588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5594_: u8 = 0;
    let mut v_val_5595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_num_5596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_den_5597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: u8 = 0;
    let mut v___x_5600_: u8 = 0;
    let mut v___x_5601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: u8 = 0;
    let mut v___x_5606_: u8 = 0;
    let mut v___x_5607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: u8 = 0;
    let mut v___x_5612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5616_: u8 = 0;
    let mut v_a_5617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5620_: u8 = 0;
    let mut v___x_5622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5624_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_d_5588_ = leanh::lean_ctor_get(v_c_5584_, 0);
                leanh::lean_inc(v_d_5588_);
                v_p_5589_ = leanh::lean_ctor_get(v_c_5584_, 1);
                leanh::lean_inc_ref(v_p_5589_);
                leanh::lean_dec_ref(v_c_5584_);
                v___x_5590_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_5589_, v_a_5585_, v_a_5586_);
                if leanh::lean_obj_tag(v___x_5590_) == 0 {
                    v_a_5591_ = leanh::lean_ctor_get(v___x_5590_, 0);
                    v_isSharedCheck_5616_ = (!leanh::lean_is_exclusive(v___x_5590_)) as u8;
                    if v_isSharedCheck_5616_ == 0 {
                        v___x_5593_ = v___x_5590_;
                        v_isShared_5594_ = v_isSharedCheck_5616_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5591_);
                        leanh::lean_dec(v___x_5590_);
                        v___x_5593_ = leanh::lean_box(0);
                        v_isShared_5594_ = v_isSharedCheck_5616_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_d_5588_);
                    v_a_5617_ = leanh::lean_ctor_get(v___x_5590_, 0);
                    v_isSharedCheck_5624_ = (!leanh::lean_is_exclusive(v___x_5590_)) as u8;
                    if v_isSharedCheck_5624_ == 0 {
                        v___x_5619_ = v___x_5590_;
                        v_isShared_5620_ = v_isSharedCheck_5624_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5617_);
                        leanh::lean_dec(v___x_5590_);
                        v___x_5619_ = leanh::lean_box(0);
                        v_isShared_5620_ = v_isSharedCheck_5624_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_5591_) == 1 {
                    v_val_5595_ = leanh::lean_ctor_get(v_a_5591_, 0);
                    leanh::lean_inc(v_val_5595_);
                    leanh::lean_dec_ref_known(v_a_5591_, 1);
                    v_num_5596_ = leanh::lean_ctor_get(v_val_5595_, 0);
                    leanh::lean_inc(v_num_5596_);
                    v_den_5597_ = leanh::lean_ctor_get(v_val_5595_, 1);
                    leanh::lean_inc(v_den_5597_);
                    leanh::lean_dec(v_val_5595_);
                    v___x_5598_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5599_ = lean_nat_dec_eq(v_den_5597_, v___x_5598_);
                    leanh::lean_dec(v_den_5597_);
                    if v___x_5599_ == 0 {
                        leanh::lean_dec(v_num_5596_);
                        leanh::lean_dec(v_d_5588_);
                        v___x_5600_ = 0;
                        v___x_5601_ = leanh::lean_box((v___x_5600_) as usize);
                        if v_isShared_5594_ == 0 {
                            leanh::lean_ctor_set(v___x_5593_, 0, v___x_5601_);
                            v___x_5603_ = v___x_5593_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_5604_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5604_, 0, v___x_5601_);
                            v___x_5603_ = v_reuseFailAlloc_5604_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_5605_ = l_Int_decidableDvd(v_d_5588_, v_num_5596_);
                        leanh::lean_dec(v_num_5596_);
                        leanh::lean_dec(v_d_5588_);
                        v___x_5606_ = l_Bool_toLBool(v___x_5605_);
                        v___x_5607_ = leanh::lean_box((v___x_5606_) as usize);
                        if v_isShared_5594_ == 0 {
                            leanh::lean_ctor_set(v___x_5593_, 0, v___x_5607_);
                            v___x_5609_ = v___x_5593_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5610_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5610_, 0, v___x_5607_);
                            v___x_5609_ = v_reuseFailAlloc_5610_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_5591_);
                    leanh::lean_dec(v_d_5588_);
                    v___x_5611_ = 2;
                    v___x_5612_ = leanh::lean_box((v___x_5611_) as usize);
                    if v_isShared_5594_ == 0 {
                        leanh::lean_ctor_set(v___x_5593_, 0, v___x_5612_);
                        v___x_5614_ = v___x_5593_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5615_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5615_, 0, v___x_5612_);
                        v___x_5614_ = v_reuseFailAlloc_5615_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5603_;
            }
            3 => {
                return v___x_5609_;
            }
            4 => {
                return v___x_5614_;
            }
            5 => {
                if v_isShared_5620_ == 0 {
                    v___x_5622_ = v___x_5619_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5623_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5623_, 0, v_a_5617_);
                    v___x_5622_ = v_reuseFailAlloc_5623_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5622_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg___boxed(
    mut v_c_5625_: *mut leanh::LeanObject,
    mut v_a_5626_: *mut leanh::LeanObject,
    mut v_a_5627_: *mut leanh::LeanObject,
    mut v_a_5628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5629_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_c_5625_, v_a_5626_, v_a_5627_);
    leanh::lean_dec_ref(v_a_5627_);
    leanh::lean_dec(v_a_5626_);
    return v_res_5629_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(
    mut v_c_5630_: *mut leanh::LeanObject,
    mut v_a_5631_: *mut leanh::LeanObject,
    mut v_a_5632_: *mut leanh::LeanObject,
    mut v_a_5633_: *mut leanh::LeanObject,
    mut v_a_5634_: *mut leanh::LeanObject,
    mut v_a_5635_: *mut leanh::LeanObject,
    mut v_a_5636_: *mut leanh::LeanObject,
    mut v_a_5637_: *mut leanh::LeanObject,
    mut v_a_5638_: *mut leanh::LeanObject,
    mut v_a_5639_: *mut leanh::LeanObject,
    mut v_a_5640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5642_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_c_5630_, v_a_5631_, v_a_5639_);
    return v___x_5642_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___boxed(
    mut v_c_5643_: *mut leanh::LeanObject,
    mut v_a_5644_: *mut leanh::LeanObject,
    mut v_a_5645_: *mut leanh::LeanObject,
    mut v_a_5646_: *mut leanh::LeanObject,
    mut v_a_5647_: *mut leanh::LeanObject,
    mut v_a_5648_: *mut leanh::LeanObject,
    mut v_a_5649_: *mut leanh::LeanObject,
    mut v_a_5650_: *mut leanh::LeanObject,
    mut v_a_5651_: *mut leanh::LeanObject,
    mut v_a_5652_: *mut leanh::LeanObject,
    mut v_a_5653_: *mut leanh::LeanObject,
    mut v_a_5654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5655_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(
        v_c_5643_, v_a_5644_, v_a_5645_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_,
        v_a_5651_, v_a_5652_, v_a_5653_,
    );
    leanh::lean_dec(v_a_5653_);
    leanh::lean_dec_ref(v_a_5652_);
    leanh::lean_dec(v_a_5651_);
    leanh::lean_dec_ref(v_a_5650_);
    leanh::lean_dec(v_a_5649_);
    leanh::lean_dec_ref(v_a_5648_);
    leanh::lean_dec(v_a_5647_);
    leanh::lean_dec_ref(v_a_5646_);
    leanh::lean_dec(v_a_5645_);
    leanh::lean_dec(v_a_5644_);
    return v_res_5655_;
}
pub unsafe fn l_Int_Linear_Poly_satisfiedLe___redArg(
    mut v_p_5656_: *mut leanh::LeanObject,
    mut v_a_5657_: *mut leanh::LeanObject,
    mut v_a_5658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5664_: u8 = 0;
    let mut v_val_5665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: u8 = 0;
    let mut v___x_5668_: u8 = 0;
    let mut v___x_5669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: u8 = 0;
    let mut v___x_5674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5678_: u8 = 0;
    let mut v_a_5679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5682_: u8 = 0;
    let mut v___x_5684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5686_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5660_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_5656_, v_a_5657_, v_a_5658_);
                if leanh::lean_obj_tag(v___x_5660_) == 0 {
                    v_a_5661_ = leanh::lean_ctor_get(v___x_5660_, 0);
                    v_isSharedCheck_5678_ = (!leanh::lean_is_exclusive(v___x_5660_)) as u8;
                    if v_isSharedCheck_5678_ == 0 {
                        v___x_5663_ = v___x_5660_;
                        v_isShared_5664_ = v_isSharedCheck_5678_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5661_);
                        leanh::lean_dec(v___x_5660_);
                        v___x_5663_ = leanh::lean_box(0);
                        v_isShared_5664_ = v_isSharedCheck_5678_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5679_ = leanh::lean_ctor_get(v___x_5660_, 0);
                    v_isSharedCheck_5686_ = (!leanh::lean_is_exclusive(v___x_5660_)) as u8;
                    if v_isSharedCheck_5686_ == 0 {
                        v___x_5681_ = v___x_5660_;
                        v_isShared_5682_ = v_isSharedCheck_5686_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5679_);
                        leanh::lean_dec(v___x_5660_);
                        v___x_5681_ = leanh::lean_box(0);
                        v_isShared_5682_ = v_isSharedCheck_5686_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_5661_) == 1 {
                    v_val_5665_ = leanh::lean_ctor_get(v_a_5661_, 0);
                    leanh::lean_inc(v_val_5665_);
                    leanh::lean_dec_ref_known(v_a_5661_, 1);
                    v___x_5666_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Int_Linear_Poly_eval_x3f___redArg___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Int_Linear_Poly_eval_x3f___redArg___closed__0_once
                        ),
                        _init_l_Int_Linear_Poly_eval_x3f___redArg___closed__0,
                    );
                    v___x_5667_ = l_Rat_instDecidableLe(v_val_5665_, v___x_5666_);
                    v___x_5668_ = l_Bool_toLBool(v___x_5667_);
                    v___x_5669_ = leanh::lean_box((v___x_5668_) as usize);
                    if v_isShared_5664_ == 0 {
                        leanh::lean_ctor_set(v___x_5663_, 0, v___x_5669_);
                        v___x_5671_ = v___x_5663_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5672_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5672_, 0, v___x_5669_);
                        v___x_5671_ = v_reuseFailAlloc_5672_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_5661_);
                    v___x_5673_ = 2;
                    v___x_5674_ = leanh::lean_box((v___x_5673_) as usize);
                    if v_isShared_5664_ == 0 {
                        leanh::lean_ctor_set(v___x_5663_, 0, v___x_5674_);
                        v___x_5676_ = v___x_5663_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5677_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5677_, 0, v___x_5674_);
                        v___x_5676_ = v_reuseFailAlloc_5677_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5671_;
            }
            3 => {
                return v___x_5676_;
            }
            4 => {
                if v_isShared_5682_ == 0 {
                    v___x_5684_ = v___x_5681_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5685_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5685_, 0, v_a_5679_);
                    v___x_5684_ = v_reuseFailAlloc_5685_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5684_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Poly_satisfiedLe___redArg___boxed(
    mut v_p_5687_: *mut leanh::LeanObject,
    mut v_a_5688_: *mut leanh::LeanObject,
    mut v_a_5689_: *mut leanh::LeanObject,
    mut v_a_5690_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5691_ = l_Int_Linear_Poly_satisfiedLe___redArg(v_p_5687_, v_a_5688_, v_a_5689_);
    leanh::lean_dec_ref(v_a_5689_);
    leanh::lean_dec(v_a_5688_);
    return v_res_5691_;
}
pub unsafe fn l_Int_Linear_Poly_satisfiedLe(
    mut v_p_5692_: *mut leanh::LeanObject,
    mut v_a_5693_: *mut leanh::LeanObject,
    mut v_a_5694_: *mut leanh::LeanObject,
    mut v_a_5695_: *mut leanh::LeanObject,
    mut v_a_5696_: *mut leanh::LeanObject,
    mut v_a_5697_: *mut leanh::LeanObject,
    mut v_a_5698_: *mut leanh::LeanObject,
    mut v_a_5699_: *mut leanh::LeanObject,
    mut v_a_5700_: *mut leanh::LeanObject,
    mut v_a_5701_: *mut leanh::LeanObject,
    mut v_a_5702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5704_ = l_Int_Linear_Poly_satisfiedLe___redArg(v_p_5692_, v_a_5693_, v_a_5701_);
    return v___x_5704_;
}
pub unsafe fn l_Int_Linear_Poly_satisfiedLe___boxed(
    mut v_p_5705_: *mut leanh::LeanObject,
    mut v_a_5706_: *mut leanh::LeanObject,
    mut v_a_5707_: *mut leanh::LeanObject,
    mut v_a_5708_: *mut leanh::LeanObject,
    mut v_a_5709_: *mut leanh::LeanObject,
    mut v_a_5710_: *mut leanh::LeanObject,
    mut v_a_5711_: *mut leanh::LeanObject,
    mut v_a_5712_: *mut leanh::LeanObject,
    mut v_a_5713_: *mut leanh::LeanObject,
    mut v_a_5714_: *mut leanh::LeanObject,
    mut v_a_5715_: *mut leanh::LeanObject,
    mut v_a_5716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5717_ = l_Int_Linear_Poly_satisfiedLe(
        v_p_5705_, v_a_5706_, v_a_5707_, v_a_5708_, v_a_5709_, v_a_5710_, v_a_5711_, v_a_5712_,
        v_a_5713_, v_a_5714_, v_a_5715_,
    );
    leanh::lean_dec(v_a_5715_);
    leanh::lean_dec_ref(v_a_5714_);
    leanh::lean_dec(v_a_5713_);
    leanh::lean_dec_ref(v_a_5712_);
    leanh::lean_dec(v_a_5711_);
    leanh::lean_dec_ref(v_a_5710_);
    leanh::lean_dec(v_a_5709_);
    leanh::lean_dec_ref(v_a_5708_);
    leanh::lean_dec(v_a_5707_);
    leanh::lean_dec(v_a_5706_);
    return v_res_5717_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(
    mut v_c_5718_: *mut leanh::LeanObject,
    mut v_a_5719_: *mut leanh::LeanObject,
    mut v_a_5720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_p_5722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_p_5722_ = leanh::lean_ctor_get(v_c_5718_, 0);
    leanh::lean_inc_ref(v_p_5722_);
    leanh::lean_dec_ref(v_c_5718_);
    v___x_5723_ = l_Int_Linear_Poly_satisfiedLe___redArg(v_p_5722_, v_a_5719_, v_a_5720_);
    return v___x_5723_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg___boxed(
    mut v_c_5724_: *mut leanh::LeanObject,
    mut v_a_5725_: *mut leanh::LeanObject,
    mut v_a_5726_: *mut leanh::LeanObject,
    mut v_a_5727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5728_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v_c_5724_, v_a_5725_, v_a_5726_);
    leanh::lean_dec_ref(v_a_5726_);
    leanh::lean_dec(v_a_5725_);
    return v_res_5728_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(
    mut v_c_5729_: *mut leanh::LeanObject,
    mut v_a_5730_: *mut leanh::LeanObject,
    mut v_a_5731_: *mut leanh::LeanObject,
    mut v_a_5732_: *mut leanh::LeanObject,
    mut v_a_5733_: *mut leanh::LeanObject,
    mut v_a_5734_: *mut leanh::LeanObject,
    mut v_a_5735_: *mut leanh::LeanObject,
    mut v_a_5736_: *mut leanh::LeanObject,
    mut v_a_5737_: *mut leanh::LeanObject,
    mut v_a_5738_: *mut leanh::LeanObject,
    mut v_a_5739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5741_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v_c_5729_, v_a_5730_, v_a_5738_);
    return v___x_5741_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___boxed(
    mut v_c_5742_: *mut leanh::LeanObject,
    mut v_a_5743_: *mut leanh::LeanObject,
    mut v_a_5744_: *mut leanh::LeanObject,
    mut v_a_5745_: *mut leanh::LeanObject,
    mut v_a_5746_: *mut leanh::LeanObject,
    mut v_a_5747_: *mut leanh::LeanObject,
    mut v_a_5748_: *mut leanh::LeanObject,
    mut v_a_5749_: *mut leanh::LeanObject,
    mut v_a_5750_: *mut leanh::LeanObject,
    mut v_a_5751_: *mut leanh::LeanObject,
    mut v_a_5752_: *mut leanh::LeanObject,
    mut v_a_5753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5754_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(
        v_c_5742_, v_a_5743_, v_a_5744_, v_a_5745_, v_a_5746_, v_a_5747_, v_a_5748_, v_a_5749_,
        v_a_5750_, v_a_5751_, v_a_5752_,
    );
    leanh::lean_dec(v_a_5752_);
    leanh::lean_dec_ref(v_a_5751_);
    leanh::lean_dec(v_a_5750_);
    leanh::lean_dec_ref(v_a_5749_);
    leanh::lean_dec(v_a_5748_);
    leanh::lean_dec_ref(v_a_5747_);
    leanh::lean_dec(v_a_5746_);
    leanh::lean_dec_ref(v_a_5745_);
    leanh::lean_dec(v_a_5744_);
    leanh::lean_dec(v_a_5743_);
    return v_res_5754_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(
    mut v_c_5755_: *mut leanh::LeanObject,
    mut v_a_5756_: *mut leanh::LeanObject,
    mut v_a_5757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_p_5759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5764_: u8 = 0;
    let mut v___y_5766_: u8 = 0;
    let mut v___x_5767_: u8 = 0;
    let mut v___x_5768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: u8 = 0;
    let mut v___x_5775_: u8 = 0;
    let mut v___x_5776_: u8 = 0;
    let mut v___x_5777_: u8 = 0;
    let mut v___x_5778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5780_: u8 = 0;
    let mut v_a_5781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5784_: u8 = 0;
    let mut v___x_5786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5788_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_p_5759_ = leanh::lean_ctor_get(v_c_5755_, 0);
                leanh::lean_inc_ref(v_p_5759_);
                leanh::lean_dec_ref(v_c_5755_);
                v___x_5760_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_5759_, v_a_5756_, v_a_5757_);
                if leanh::lean_obj_tag(v___x_5760_) == 0 {
                    v_a_5761_ = leanh::lean_ctor_get(v___x_5760_, 0);
                    v_isSharedCheck_5780_ = (!leanh::lean_is_exclusive(v___x_5760_)) as u8;
                    if v_isSharedCheck_5780_ == 0 {
                        v___x_5763_ = v___x_5760_;
                        v_isShared_5764_ = v_isSharedCheck_5780_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5761_);
                        leanh::lean_dec(v___x_5760_);
                        v___x_5763_ = leanh::lean_box(0);
                        v_isShared_5764_ = v_isSharedCheck_5780_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5781_ = leanh::lean_ctor_get(v___x_5760_, 0);
                    v_isSharedCheck_5788_ = (!leanh::lean_is_exclusive(v___x_5760_)) as u8;
                    if v_isSharedCheck_5788_ == 0 {
                        v___x_5783_ = v___x_5760_;
                        v_isShared_5784_ = v_isSharedCheck_5788_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5781_);
                        leanh::lean_dec(v___x_5760_);
                        v___x_5783_ = leanh::lean_box(0);
                        v_isShared_5784_ = v_isSharedCheck_5788_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_5761_) == 1 {
                    v_val_5772_ = leanh::lean_ctor_get(v_a_5761_, 0);
                    leanh::lean_inc(v_val_5772_);
                    leanh::lean_dec_ref_known(v_a_5761_, 1);
                    v___x_5773_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Int_Linear_Poly_eval_x3f___redArg___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Int_Linear_Poly_eval_x3f___redArg___closed__0_once
                        ),
                        _init_l_Int_Linear_Poly_eval_x3f___redArg___closed__0,
                    );
                    v___x_5774_ = l_instDecidableEqRat_decEq(v_val_5772_, v___x_5773_);
                    leanh::lean_dec(v_val_5772_);
                    if v___x_5774_ == 0 {
                        v___x_5775_ = 1;
                        v___y_5766_ = v___x_5775_;
                        state = 2;
                        continue;
                    } else {
                        v___x_5776_ = 0;
                        v___y_5766_ = v___x_5776_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5763_);
                    leanh::lean_dec(v_a_5761_);
                    v___x_5777_ = 2;
                    v___x_5778_ = leanh::lean_box((v___x_5777_) as usize);
                    v___x_5779_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5779_, 0, v___x_5778_);
                    return v___x_5779_;
                }
            }
            2 => {
                v___x_5767_ = l_Bool_toLBool(v___y_5766_);
                v___x_5768_ = leanh::lean_box((v___x_5767_) as usize);
                if v_isShared_5764_ == 0 {
                    leanh::lean_ctor_set(v___x_5763_, 0, v___x_5768_);
                    v___x_5770_ = v___x_5763_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5771_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5771_, 0, v___x_5768_);
                    v___x_5770_ = v_reuseFailAlloc_5771_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5770_;
            }
            4 => {
                if v_isShared_5784_ == 0 {
                    v___x_5786_ = v___x_5783_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5787_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 0, v_a_5781_);
                    v___x_5786_ = v_reuseFailAlloc_5787_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5786_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg___boxed(
    mut v_c_5789_: *mut leanh::LeanObject,
    mut v_a_5790_: *mut leanh::LeanObject,
    mut v_a_5791_: *mut leanh::LeanObject,
    mut v_a_5792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5793_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(
        v_c_5789_, v_a_5790_, v_a_5791_,
    );
    leanh::lean_dec_ref(v_a_5791_);
    leanh::lean_dec(v_a_5790_);
    return v_res_5793_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(
    mut v_c_5794_: *mut leanh::LeanObject,
    mut v_a_5795_: *mut leanh::LeanObject,
    mut v_a_5796_: *mut leanh::LeanObject,
    mut v_a_5797_: *mut leanh::LeanObject,
    mut v_a_5798_: *mut leanh::LeanObject,
    mut v_a_5799_: *mut leanh::LeanObject,
    mut v_a_5800_: *mut leanh::LeanObject,
    mut v_a_5801_: *mut leanh::LeanObject,
    mut v_a_5802_: *mut leanh::LeanObject,
    mut v_a_5803_: *mut leanh::LeanObject,
    mut v_a_5804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5806_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(
        v_c_5794_, v_a_5795_, v_a_5803_,
    );
    return v___x_5806_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___boxed(
    mut v_c_5807_: *mut leanh::LeanObject,
    mut v_a_5808_: *mut leanh::LeanObject,
    mut v_a_5809_: *mut leanh::LeanObject,
    mut v_a_5810_: *mut leanh::LeanObject,
    mut v_a_5811_: *mut leanh::LeanObject,
    mut v_a_5812_: *mut leanh::LeanObject,
    mut v_a_5813_: *mut leanh::LeanObject,
    mut v_a_5814_: *mut leanh::LeanObject,
    mut v_a_5815_: *mut leanh::LeanObject,
    mut v_a_5816_: *mut leanh::LeanObject,
    mut v_a_5817_: *mut leanh::LeanObject,
    mut v_a_5818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5819_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(
        v_c_5807_, v_a_5808_, v_a_5809_, v_a_5810_, v_a_5811_, v_a_5812_, v_a_5813_, v_a_5814_,
        v_a_5815_, v_a_5816_, v_a_5817_,
    );
    leanh::lean_dec(v_a_5817_);
    leanh::lean_dec_ref(v_a_5816_);
    leanh::lean_dec(v_a_5815_);
    leanh::lean_dec_ref(v_a_5814_);
    leanh::lean_dec(v_a_5813_);
    leanh::lean_dec_ref(v_a_5812_);
    leanh::lean_dec(v_a_5811_);
    leanh::lean_dec_ref(v_a_5810_);
    leanh::lean_dec(v_a_5809_);
    leanh::lean_dec(v_a_5808_);
    return v_res_5819_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(
    mut v_c_5820_: *mut leanh::LeanObject,
    mut v_a_5821_: *mut leanh::LeanObject,
    mut v_a_5822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_p_5824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5829_: u8 = 0;
    let mut v_val_5830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: u8 = 0;
    let mut v___x_5833_: u8 = 0;
    let mut v___x_5834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5838_: u8 = 0;
    let mut v___x_5839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5843_: u8 = 0;
    let mut v_a_5844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5847_: u8 = 0;
    let mut v___x_5849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5851_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_p_5824_ = leanh::lean_ctor_get(v_c_5820_, 0);
                leanh::lean_inc_ref(v_p_5824_);
                leanh::lean_dec_ref(v_c_5820_);
                v___x_5825_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_5824_, v_a_5821_, v_a_5822_);
                if leanh::lean_obj_tag(v___x_5825_) == 0 {
                    v_a_5826_ = leanh::lean_ctor_get(v___x_5825_, 0);
                    v_isSharedCheck_5843_ = (!leanh::lean_is_exclusive(v___x_5825_)) as u8;
                    if v_isSharedCheck_5843_ == 0 {
                        v___x_5828_ = v___x_5825_;
                        v_isShared_5829_ = v_isSharedCheck_5843_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5826_);
                        leanh::lean_dec(v___x_5825_);
                        v___x_5828_ = leanh::lean_box(0);
                        v_isShared_5829_ = v_isSharedCheck_5843_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5844_ = leanh::lean_ctor_get(v___x_5825_, 0);
                    v_isSharedCheck_5851_ = (!leanh::lean_is_exclusive(v___x_5825_)) as u8;
                    if v_isSharedCheck_5851_ == 0 {
                        v___x_5846_ = v___x_5825_;
                        v_isShared_5847_ = v_isSharedCheck_5851_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5844_);
                        leanh::lean_dec(v___x_5825_);
                        v___x_5846_ = leanh::lean_box(0);
                        v_isShared_5847_ = v_isSharedCheck_5851_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_5826_) == 1 {
                    v_val_5830_ = leanh::lean_ctor_get(v_a_5826_, 0);
                    leanh::lean_inc(v_val_5830_);
                    leanh::lean_dec_ref_known(v_a_5826_, 1);
                    v___x_5831_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Int_Linear_Poly_eval_x3f___redArg___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Int_Linear_Poly_eval_x3f___redArg___closed__0_once
                        ),
                        _init_l_Int_Linear_Poly_eval_x3f___redArg___closed__0,
                    );
                    v___x_5832_ = l_instDecidableEqRat_decEq(v_val_5830_, v___x_5831_);
                    leanh::lean_dec(v_val_5830_);
                    v___x_5833_ = l_Bool_toLBool(v___x_5832_);
                    v___x_5834_ = leanh::lean_box((v___x_5833_) as usize);
                    if v_isShared_5829_ == 0 {
                        leanh::lean_ctor_set(v___x_5828_, 0, v___x_5834_);
                        v___x_5836_ = v___x_5828_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5837_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5837_, 0, v___x_5834_);
                        v___x_5836_ = v_reuseFailAlloc_5837_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_5826_);
                    v___x_5838_ = 2;
                    v___x_5839_ = leanh::lean_box((v___x_5838_) as usize);
                    if v_isShared_5829_ == 0 {
                        leanh::lean_ctor_set(v___x_5828_, 0, v___x_5839_);
                        v___x_5841_ = v___x_5828_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5842_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5842_, 0, v___x_5839_);
                        v___x_5841_ = v_reuseFailAlloc_5842_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5836_;
            }
            3 => {
                return v___x_5841_;
            }
            4 => {
                if v_isShared_5847_ == 0 {
                    v___x_5849_ = v___x_5846_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5850_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5850_, 0, v_a_5844_);
                    v___x_5849_ = v_reuseFailAlloc_5850_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5849_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg___boxed(
    mut v_c_5852_: *mut leanh::LeanObject,
    mut v_a_5853_: *mut leanh::LeanObject,
    mut v_a_5854_: *mut leanh::LeanObject,
    mut v_a_5855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5856_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(v_c_5852_, v_a_5853_, v_a_5854_);
    leanh::lean_dec_ref(v_a_5854_);
    leanh::lean_dec(v_a_5853_);
    return v_res_5856_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(
    mut v_c_5857_: *mut leanh::LeanObject,
    mut v_a_5858_: *mut leanh::LeanObject,
    mut v_a_5859_: *mut leanh::LeanObject,
    mut v_a_5860_: *mut leanh::LeanObject,
    mut v_a_5861_: *mut leanh::LeanObject,
    mut v_a_5862_: *mut leanh::LeanObject,
    mut v_a_5863_: *mut leanh::LeanObject,
    mut v_a_5864_: *mut leanh::LeanObject,
    mut v_a_5865_: *mut leanh::LeanObject,
    mut v_a_5866_: *mut leanh::LeanObject,
    mut v_a_5867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5869_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(v_c_5857_, v_a_5858_, v_a_5866_);
    return v___x_5869_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___boxed(
    mut v_c_5870_: *mut leanh::LeanObject,
    mut v_a_5871_: *mut leanh::LeanObject,
    mut v_a_5872_: *mut leanh::LeanObject,
    mut v_a_5873_: *mut leanh::LeanObject,
    mut v_a_5874_: *mut leanh::LeanObject,
    mut v_a_5875_: *mut leanh::LeanObject,
    mut v_a_5876_: *mut leanh::LeanObject,
    mut v_a_5877_: *mut leanh::LeanObject,
    mut v_a_5878_: *mut leanh::LeanObject,
    mut v_a_5879_: *mut leanh::LeanObject,
    mut v_a_5880_: *mut leanh::LeanObject,
    mut v_a_5881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5882_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(
        v_c_5870_, v_a_5871_, v_a_5872_, v_a_5873_, v_a_5874_, v_a_5875_, v_a_5876_, v_a_5877_,
        v_a_5878_, v_a_5879_, v_a_5880_,
    );
    leanh::lean_dec(v_a_5880_);
    leanh::lean_dec_ref(v_a_5879_);
    leanh::lean_dec(v_a_5878_);
    leanh::lean_dec_ref(v_a_5877_);
    leanh::lean_dec(v_a_5876_);
    leanh::lean_dec_ref(v_a_5875_);
    leanh::lean_dec(v_a_5874_);
    leanh::lean_dec_ref(v_a_5873_);
    leanh::lean_dec(v_a_5872_);
    leanh::lean_dec(v_a_5871_);
    return v_res_5882_;
}
pub unsafe fn l_Int_Linear_Poly_findVarToSubst___redArg(
    mut v_p_5883_: *mut leanh::LeanObject,
    mut v_a_5884_: *mut leanh::LeanObject,
    mut v_a_5885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5889_: u8 = 0;
    let mut v___x_5890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5894_: u8 = 0;
    let mut v_unused_5895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5903_: u8 = 0;
    let mut v___y_5905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5909_: u8 = 0;
    let mut v___x_5910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5918_: u8 = 0;
    let mut v_elimEqs_5920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5923_: u8 = 0;
    let mut v___x_5924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5926_: u8 = 0;
    let mut v_a_5927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5930_: u8 = 0;
    let mut v___x_5932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5934_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_p_5883_) == 0 {
                    v_isSharedCheck_5894_ = (!leanh::lean_is_exclusive(v_p_5883_)) as u8;
                    if v_isSharedCheck_5894_ == 0 {
                        v_unused_5895_ = leanh::lean_ctor_get(v_p_5883_, 0);
                        leanh::lean_dec(v_unused_5895_);
                        v___x_5888_ = v_p_5883_;
                        v_isShared_5889_ = v_isSharedCheck_5894_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_p_5883_);
                        v___x_5888_ = leanh::lean_box(0);
                        v_isShared_5889_ = v_isSharedCheck_5894_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_5896_ = leanh::lean_ctor_get(v_p_5883_, 0);
                    leanh::lean_inc(v_k_5896_);
                    v_v_5897_ = leanh::lean_ctor_get(v_p_5883_, 1);
                    leanh::lean_inc(v_v_5897_);
                    v_p_5898_ = leanh::lean_ctor_get(v_p_5883_, 2);
                    leanh::lean_inc_ref(v_p_5898_);
                    leanh::lean_dec_ref_known(v_p_5883_, 3);
                    v___x_5899_ =
                        l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_5884_, v_a_5885_);
                    if leanh::lean_obj_tag(v___x_5899_) == 0 {
                        v_a_5900_ = leanh::lean_ctor_get(v___x_5899_, 0);
                        v_isSharedCheck_5926_ =
                            (!leanh::lean_is_exclusive(v___x_5899_)) as u8;
                        if v_isSharedCheck_5926_ == 0 {
                            v___x_5902_ = v___x_5899_;
                            v_isShared_5903_ = v_isSharedCheck_5926_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5900_);
                            leanh::lean_dec(v___x_5899_);
                            v___x_5902_ = leanh::lean_box(0);
                            v_isShared_5903_ = v_isSharedCheck_5926_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_p_5898_);
                        leanh::lean_dec(v_v_5897_);
                        leanh::lean_dec(v_k_5896_);
                        v_a_5927_ = leanh::lean_ctor_get(v___x_5899_, 0);
                        v_isSharedCheck_5934_ =
                            (!leanh::lean_is_exclusive(v___x_5899_)) as u8;
                        if v_isSharedCheck_5934_ == 0 {
                            v___x_5929_ = v___x_5899_;
                            v_isShared_5930_ = v_isSharedCheck_5934_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5927_);
                            leanh::lean_dec(v___x_5899_);
                            v___x_5929_ = leanh::lean_box(0);
                            v_isShared_5930_ = v_isSharedCheck_5934_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5890_ = leanh::lean_box(0);
                if v_isShared_5889_ == 0 {
                    leanh::lean_ctor_set(v___x_5888_, 0, v___x_5890_);
                    v___x_5892_ = v___x_5888_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5893_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5893_, 0, v___x_5890_);
                    v___x_5892_ = v_reuseFailAlloc_5893_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5892_;
            }
            3 => {
                v_elimEqs_5920_ = leanh::lean_ctor_get(v_a_5900_, 10);
                leanh::lean_inc_ref(v_elimEqs_5920_);
                leanh::lean_dec(v_a_5900_);
                v_size_5921_ = leanh::lean_ctor_get(v_elimEqs_5920_, 2);
                v___x_5922_ = leanh::lean_box(0);
                v___x_5923_ = lean_nat_dec_lt(v_v_5897_, v_size_5921_);
                if v___x_5923_ == 0 {
                    leanh::lean_dec_ref(v_elimEqs_5920_);
                    v___x_5924_ = l_outOfBounds___redArg(v___x_5922_);
                    v___y_5905_ = v___x_5924_;
                    state = 4;
                    continue;
                } else {
                    v___x_5925_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_5922_,
                        v_elimEqs_5920_,
                        v_v_5897_,
                    );
                    leanh::lean_dec_ref(v_elimEqs_5920_);
                    v___y_5905_ = v___x_5925_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if leanh::lean_obj_tag(v___y_5905_) == 1 {
                    leanh::lean_dec_ref(v_p_5898_);
                    v_val_5906_ = leanh::lean_ctor_get(v___y_5905_, 0);
                    v_isSharedCheck_5918_ = (!leanh::lean_is_exclusive(v___y_5905_)) as u8;
                    if v_isSharedCheck_5918_ == 0 {
                        v___x_5908_ = v___y_5905_;
                        v_isShared_5909_ = v_isSharedCheck_5918_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5906_);
                        leanh::lean_dec(v___y_5905_);
                        v___x_5908_ = leanh::lean_box(0);
                        v_isShared_5909_ = v_isSharedCheck_5918_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_5905_);
                    leanh::lean_del_object(v___x_5902_);
                    leanh::lean_dec(v_v_5897_);
                    leanh::lean_dec(v_k_5896_);
                    v_p_5883_ = v_p_5898_;
                    state = 0;
                    continue;
                }
            }
            5 => {
                v___x_5910_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5910_, 0, v_v_5897_);
                leanh::lean_ctor_set(v___x_5910_, 1, v_val_5906_);
                v___x_5911_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5911_, 0, v_k_5896_);
                leanh::lean_ctor_set(v___x_5911_, 1, v___x_5910_);
                if v_isShared_5909_ == 0 {
                    leanh::lean_ctor_set(v___x_5908_, 0, v___x_5911_);
                    v___x_5913_ = v___x_5908_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5917_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5917_, 0, v___x_5911_);
                    v___x_5913_ = v_reuseFailAlloc_5917_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_5903_ == 0 {
                    leanh::lean_ctor_set(v___x_5902_, 0, v___x_5913_);
                    v___x_5915_ = v___x_5902_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5916_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5916_, 0, v___x_5913_);
                    v___x_5915_ = v_reuseFailAlloc_5916_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5915_;
            }
            8 => {
                if v_isShared_5930_ == 0 {
                    v___x_5932_ = v___x_5929_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5933_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5933_, 0, v_a_5927_);
                    v___x_5932_ = v_reuseFailAlloc_5933_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5932_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Poly_findVarToSubst___redArg___boxed(
    mut v_p_5935_: *mut leanh::LeanObject,
    mut v_a_5936_: *mut leanh::LeanObject,
    mut v_a_5937_: *mut leanh::LeanObject,
    mut v_a_5938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5939_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5939_ = l_Int_Linear_Poly_findVarToSubst___redArg(v_p_5935_, v_a_5936_, v_a_5937_);
    leanh::lean_dec_ref(v_a_5937_);
    leanh::lean_dec(v_a_5936_);
    return v_res_5939_;
}
pub unsafe fn l_Int_Linear_Poly_findVarToSubst(
    mut v_p_5940_: *mut leanh::LeanObject,
    mut v_a_5941_: *mut leanh::LeanObject,
    mut v_a_5942_: *mut leanh::LeanObject,
    mut v_a_5943_: *mut leanh::LeanObject,
    mut v_a_5944_: *mut leanh::LeanObject,
    mut v_a_5945_: *mut leanh::LeanObject,
    mut v_a_5946_: *mut leanh::LeanObject,
    mut v_a_5947_: *mut leanh::LeanObject,
    mut v_a_5948_: *mut leanh::LeanObject,
    mut v_a_5949_: *mut leanh::LeanObject,
    mut v_a_5950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5952_ = l_Int_Linear_Poly_findVarToSubst___redArg(v_p_5940_, v_a_5941_, v_a_5949_);
    return v___x_5952_;
}
pub unsafe fn l_Int_Linear_Poly_findVarToSubst___boxed(
    mut v_p_5953_: *mut leanh::LeanObject,
    mut v_a_5954_: *mut leanh::LeanObject,
    mut v_a_5955_: *mut leanh::LeanObject,
    mut v_a_5956_: *mut leanh::LeanObject,
    mut v_a_5957_: *mut leanh::LeanObject,
    mut v_a_5958_: *mut leanh::LeanObject,
    mut v_a_5959_: *mut leanh::LeanObject,
    mut v_a_5960_: *mut leanh::LeanObject,
    mut v_a_5961_: *mut leanh::LeanObject,
    mut v_a_5962_: *mut leanh::LeanObject,
    mut v_a_5963_: *mut leanh::LeanObject,
    mut v_a_5964_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5965_ = l_Int_Linear_Poly_findVarToSubst(
        v_p_5953_, v_a_5954_, v_a_5955_, v_a_5956_, v_a_5957_, v_a_5958_, v_a_5959_, v_a_5960_,
        v_a_5961_, v_a_5962_, v_a_5963_,
    );
    leanh::lean_dec(v_a_5963_);
    leanh::lean_dec_ref(v_a_5962_);
    leanh::lean_dec(v_a_5961_);
    leanh::lean_dec_ref(v_a_5960_);
    leanh::lean_dec(v_a_5959_);
    leanh::lean_dec_ref(v_a_5958_);
    leanh::lean_dec(v_a_5957_);
    leanh::lean_dec_ref(v_a_5956_);
    leanh::lean_dec(v_a_5955_);
    leanh::lean_dec(v_a_5954_);
    return v_res_5965_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(
    mut v_pred_5966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_u2081_5967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_u2082_5968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_left_5969_: u8 = 0;
    let mut v_c_u2083_x3f_5970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_u2081_5967_ = leanh::lean_ctor_get(v_pred_5966_, 0);
    v_c_u2082_5968_ = leanh::lean_ctor_get(v_pred_5966_, 1);
    v_left_5969_ = leanh::lean_ctor_get_uint8(
        v_pred_5966_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
    );
    v_c_u2083_x3f_5970_ = leanh::lean_ctor_get(v_pred_5966_, 2);
    v_p_5971_ = leanh::lean_ctor_get(v_c_u2081_5967_, 0);
    v_p_5972_ = leanh::lean_ctor_get(v_c_u2082_5968_, 0);
    v_a_5973_ = l_Int_Linear_Poly_leadCoeff(v_p_5971_);
    v_b_5974_ = l_Int_Linear_Poly_leadCoeff(v_p_5972_);
    if leanh::lean_obj_tag(v_c_u2083_x3f_5970_) == 0 {
        if v_left_5969_ == 0 {
            let mut v___x_5975_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_a_5973_);
            v___x_5975_ = lean_nat_abs(v_b_5974_);
            leanh::lean_dec(v_b_5974_);
            return v___x_5975_;
        } else {
            let mut v___x_5976_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_b_5974_);
            v___x_5976_ = lean_nat_abs(v_a_5973_);
            leanh::lean_dec(v_a_5973_);
            return v___x_5976_;
        }
    } else {
        let mut v_val_5977_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_d_5978_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_5979_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_c_5980_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5977_ = leanh::lean_ctor_get(v_c_u2083_x3f_5970_, 0);
        v_d_5978_ = leanh::lean_ctor_get(v_val_5977_, 0);
        v_p_5979_ = leanh::lean_ctor_get(v_val_5977_, 1);
        v_c_5980_ = l_Int_Linear_Poly_leadCoeff(v_p_5979_);
        if v_left_5969_ == 0 {
            let mut v___x_5981_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5982_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5983_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5984_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5985_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_a_5973_);
            v___x_5981_ = lean_int_mul(v_b_5974_, v_d_5978_);
            v___x_5982_ = l_Int_gcd(v___x_5981_, v_c_5980_);
            leanh::lean_dec(v_c_5980_);
            v___x_5983_ = lean_nat_to_int(v___x_5982_);
            v___x_5984_ = lean_int_ediv(v___x_5981_, v___x_5983_);
            leanh::lean_dec(v___x_5983_);
            leanh::lean_dec(v___x_5981_);
            v___x_5985_ = l_Int_lcm(v_b_5974_, v___x_5984_);
            leanh::lean_dec(v___x_5984_);
            leanh::lean_dec(v_b_5974_);
            return v___x_5985_;
        } else {
            let mut v___x_5986_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5987_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5988_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5989_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5990_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_b_5974_);
            v___x_5986_ = lean_int_mul(v_a_5973_, v_d_5978_);
            v___x_5987_ = l_Int_gcd(v___x_5986_, v_c_5980_);
            leanh::lean_dec(v_c_5980_);
            v___x_5988_ = lean_nat_to_int(v___x_5987_);
            v___x_5989_ = lean_int_ediv(v___x_5986_, v___x_5988_);
            leanh::lean_dec(v___x_5988_);
            leanh::lean_dec(v___x_5986_);
            v___x_5990_ = l_Int_lcm(v_a_5973_, v___x_5989_);
            leanh::lean_dec(v___x_5989_);
            leanh::lean_dec(v_a_5973_);
            return v___x_5990_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases___boxed(
    mut v_pred_5991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5992_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5992_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(v_pred_5991_);
    leanh::lean_dec_ref(v_pred_5991_);
    return v_res_5992_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5994_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__0;
    v___x_5995_ = l_Lean_stringToMessageData(v___x_5994_);
    return v___x_5995_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_5999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5999_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__3;
    v___x_6000_ = l_Lean_MessageData_ofFormat(v___x_5999_);
    return v___x_6000_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(
    mut v_pred_6001_: *mut leanh::LeanObject,
    mut v_a_6002_: *mut leanh::LeanObject,
    mut v_a_6003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_u2081_6005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_u2082_6006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_u2083_x3f_6007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6014_: u8 = 0;
    let mut v_a_6016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6029_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_c_u2081_6005_ = leanh::lean_ctor_get(v_pred_6001_, 0);
                leanh::lean_inc_ref(v_c_u2081_6005_);
                v_c_u2082_6006_ = leanh::lean_ctor_get(v_pred_6001_, 1);
                leanh::lean_inc_ref(v_c_u2082_6006_);
                v_c_u2083_x3f_6007_ = leanh::lean_ctor_get(v_pred_6001_, 2);
                leanh::lean_inc(v_c_u2083_x3f_6007_);
                leanh::lean_dec_ref(v_pred_6001_);
                v___x_6008_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(
                    v_c_u2081_6005_,
                    v_a_6002_,
                    v_a_6003_,
                );
                if leanh::lean_obj_tag(v___x_6008_) == 0 {
                    v_a_6009_ = leanh::lean_ctor_get(v___x_6008_, 0);
                    leanh::lean_inc(v_a_6009_);
                    leanh::lean_dec_ref_known(v___x_6008_, 1);
                    v___x_6010_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(
                        v_c_u2082_6006_,
                        v_a_6002_,
                        v_a_6003_,
                    );
                    if leanh::lean_obj_tag(v___x_6010_) == 0 {
                        v_a_6011_ = leanh::lean_ctor_get(v___x_6010_, 0);
                        v_isSharedCheck_6029_ =
                            (!leanh::lean_is_exclusive(v___x_6010_)) as u8;
                        if v_isSharedCheck_6029_ == 0 {
                            v___x_6013_ = v___x_6010_;
                            v_isShared_6014_ = v_isSharedCheck_6029_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6011_);
                            leanh::lean_dec(v___x_6010_);
                            v___x_6013_ = leanh::lean_box(0);
                            v_isShared_6014_ = v_isSharedCheck_6029_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_6009_);
                        leanh::lean_dec(v_c_u2083_x3f_6007_);
                        return v___x_6010_;
                    }
                } else {
                    leanh::lean_dec(v_c_u2083_x3f_6007_);
                    leanh::lean_dec_ref(v_c_u2082_6006_);
                    return v___x_6008_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_c_u2083_x3f_6007_) == 1 {
                    v_val_6025_ = leanh::lean_ctor_get(v_c_u2083_x3f_6007_, 0);
                    leanh::lean_inc(v_val_6025_);
                    leanh::lean_dec_ref_known(v_c_u2083_x3f_6007_, 1);
                    v___x_6026_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(
                        v_val_6025_,
                        v_a_6002_,
                        v_a_6003_,
                    );
                    if leanh::lean_obj_tag(v___x_6026_) == 0 {
                        v_a_6027_ = leanh::lean_ctor_get(v___x_6026_, 0);
                        leanh::lean_inc(v_a_6027_);
                        leanh::lean_dec_ref_known(v___x_6026_, 1);
                        v_a_6016_ = v_a_6027_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_6013_);
                        leanh::lean_dec(v_a_6011_);
                        leanh::lean_dec(v_a_6009_);
                        return v___x_6026_;
                    }
                } else {
                    leanh::lean_dec(v_c_u2083_x3f_6007_);
                    v___x_6028_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4);
                    v_a_6016_ = v___x_6028_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6017_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1,
                );
                v___x_6018_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6018_, 0, v_a_6009_);
                leanh::lean_ctor_set(v___x_6018_, 1, v___x_6017_);
                v___x_6019_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6019_, 0, v___x_6018_);
                leanh::lean_ctor_set(v___x_6019_, 1, v_a_6011_);
                v___x_6020_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6020_, 0, v___x_6019_);
                leanh::lean_ctor_set(v___x_6020_, 1, v___x_6017_);
                v___x_6021_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6021_, 0, v___x_6020_);
                leanh::lean_ctor_set(v___x_6021_, 1, v_a_6016_);
                if v_isShared_6014_ == 0 {
                    leanh::lean_ctor_set(v___x_6013_, 0, v___x_6021_);
                    v___x_6023_ = v___x_6013_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6024_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6024_, 0, v___x_6021_);
                    v___x_6023_ = v_reuseFailAlloc_6024_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6023_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___boxed(
    mut v_pred_6030_: *mut leanh::LeanObject,
    mut v_a_6031_: *mut leanh::LeanObject,
    mut v_a_6032_: *mut leanh::LeanObject,
    mut v_a_6033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6034_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6034_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(
        v_pred_6030_,
        v_a_6031_,
        v_a_6032_,
    );
    leanh::lean_dec_ref(v_a_6032_);
    leanh::lean_dec(v_a_6031_);
    return v_res_6034_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp(
    mut v_pred_6035_: *mut leanh::LeanObject,
    mut v_a_6036_: *mut leanh::LeanObject,
    mut v_a_6037_: *mut leanh::LeanObject,
    mut v_a_6038_: *mut leanh::LeanObject,
    mut v_a_6039_: *mut leanh::LeanObject,
    mut v_a_6040_: *mut leanh::LeanObject,
    mut v_a_6041_: *mut leanh::LeanObject,
    mut v_a_6042_: *mut leanh::LeanObject,
    mut v_a_6043_: *mut leanh::LeanObject,
    mut v_a_6044_: *mut leanh::LeanObject,
    mut v_a_6045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6047_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(
        v_pred_6035_,
        v_a_6036_,
        v_a_6044_,
    );
    return v___x_6047_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___boxed(
    mut v_pred_6048_: *mut leanh::LeanObject,
    mut v_a_6049_: *mut leanh::LeanObject,
    mut v_a_6050_: *mut leanh::LeanObject,
    mut v_a_6051_: *mut leanh::LeanObject,
    mut v_a_6052_: *mut leanh::LeanObject,
    mut v_a_6053_: *mut leanh::LeanObject,
    mut v_a_6054_: *mut leanh::LeanObject,
    mut v_a_6055_: *mut leanh::LeanObject,
    mut v_a_6056_: *mut leanh::LeanObject,
    mut v_a_6057_: *mut leanh::LeanObject,
    mut v_a_6058_: *mut leanh::LeanObject,
    mut v_a_6059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6060_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp(
        v_pred_6048_,
        v_a_6049_,
        v_a_6050_,
        v_a_6051_,
        v_a_6052_,
        v_a_6053_,
        v_a_6054_,
        v_a_6055_,
        v_a_6056_,
        v_a_6057_,
        v_a_6058_,
    );
    leanh::lean_dec(v_a_6058_);
    leanh::lean_dec_ref(v_a_6057_);
    leanh::lean_dec(v_a_6056_);
    leanh::lean_dec_ref(v_a_6055_);
    leanh::lean_dec(v_a_6054_);
    leanh::lean_dec_ref(v_a_6053_);
    leanh::lean_dec(v_a_6052_);
    leanh::lean_dec_ref(v_a_6051_);
    leanh::lean_dec(v_a_6050_);
    leanh::lean_dec(v_a_6049_);
    return v_res_6060_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(
    mut v_h_6061_: *mut leanh::LeanObject,
    mut v_a_6062_: *mut leanh::LeanObject,
    mut v_a_6063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_6065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_6067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_6069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_6071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_u2081_6073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_u2082_6074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_u2083_6075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6084_: u8 = 0;
    let mut v___x_6085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6093_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_h_6061_) {
                0 => {
                    v_c_6065_ = leanh::lean_ctor_get(v_h_6061_, 0);
                    leanh::lean_inc_ref(v_c_6065_);
                    leanh::lean_dec_ref_known(v_h_6061_, 1);
                    v___x_6066_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(
                        v_c_6065_, v_a_6062_, v_a_6063_,
                    );
                    return v___x_6066_;
                }
                1 => {
                    v_c_6067_ = leanh::lean_ctor_get(v_h_6061_, 0);
                    leanh::lean_inc_ref(v_c_6067_);
                    leanh::lean_dec_ref_known(v_h_6061_, 1);
                    v___x_6068_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(
                        v_c_6067_, v_a_6062_, v_a_6063_,
                    );
                    return v___x_6068_;
                }
                2 => {
                    v_c_6069_ = leanh::lean_ctor_get(v_h_6061_, 0);
                    leanh::lean_inc_ref(v_c_6069_);
                    leanh::lean_dec_ref_known(v_h_6061_, 1);
                    v___x_6070_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(
                        v_c_6069_, v_a_6062_, v_a_6063_,
                    );
                    return v___x_6070_;
                }
                3 => {
                    v_c_6071_ = leanh::lean_ctor_get(v_h_6061_, 0);
                    leanh::lean_inc_ref(v_c_6071_);
                    leanh::lean_dec_ref_known(v_h_6061_, 1);
                    v___x_6072_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(
                        v_c_6071_, v_a_6062_, v_a_6063_,
                    );
                    return v___x_6072_;
                }
                _ => {
                    v_c_u2081_6073_ = leanh::lean_ctor_get(v_h_6061_, 0);
                    leanh::lean_inc_ref(v_c_u2081_6073_);
                    v_c_u2082_6074_ = leanh::lean_ctor_get(v_h_6061_, 1);
                    leanh::lean_inc_ref(v_c_u2082_6074_);
                    v_c_u2083_6075_ = leanh::lean_ctor_get(v_h_6061_, 2);
                    leanh::lean_inc_ref(v_c_u2083_6075_);
                    leanh::lean_dec_ref_known(v_h_6061_, 3);
                    v___x_6076_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(
                        v_c_u2081_6073_,
                        v_a_6062_,
                        v_a_6063_,
                    );
                    if leanh::lean_obj_tag(v___x_6076_) == 0 {
                        v_a_6077_ = leanh::lean_ctor_get(v___x_6076_, 0);
                        leanh::lean_inc(v_a_6077_);
                        leanh::lean_dec_ref_known(v___x_6076_, 1);
                        v___x_6078_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(
                            v_c_u2082_6074_,
                            v_a_6062_,
                            v_a_6063_,
                        );
                        if leanh::lean_obj_tag(v___x_6078_) == 0 {
                            v_a_6079_ = leanh::lean_ctor_get(v___x_6078_, 0);
                            leanh::lean_inc(v_a_6079_);
                            leanh::lean_dec_ref_known(v___x_6078_, 1);
                            v___x_6080_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(
                                v_c_u2083_6075_,
                                v_a_6062_,
                                v_a_6063_,
                            );
                            if leanh::lean_obj_tag(v___x_6080_) == 0 {
                                v_a_6081_ = leanh::lean_ctor_get(v___x_6080_, 0);
                                v_isSharedCheck_6093_ =
                                    (!leanh::lean_is_exclusive(v___x_6080_)) as u8;
                                if v_isSharedCheck_6093_ == 0 {
                                    v___x_6083_ = v___x_6080_;
                                    v_isShared_6084_ = v_isSharedCheck_6093_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6081_);
                                    leanh::lean_dec(v___x_6080_);
                                    v___x_6083_ = leanh::lean_box(0);
                                    v_isShared_6084_ = v_isSharedCheck_6093_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_6079_);
                                leanh::lean_dec(v_a_6077_);
                                return v___x_6080_;
                            }
                        } else {
                            leanh::lean_dec(v_a_6077_);
                            leanh::lean_dec_ref(v_c_u2083_6075_);
                            return v___x_6078_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_c_u2083_6075_);
                        leanh::lean_dec_ref(v_c_u2082_6074_);
                        return v___x_6076_;
                    }
                }
            },
            1 => {
                v___x_6085_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1,
                );
                v___x_6086_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6086_, 0, v_a_6077_);
                leanh::lean_ctor_set(v___x_6086_, 1, v___x_6085_);
                v___x_6087_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6087_, 0, v___x_6086_);
                leanh::lean_ctor_set(v___x_6087_, 1, v_a_6079_);
                v___x_6088_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6088_, 0, v___x_6087_);
                leanh::lean_ctor_set(v___x_6088_, 1, v___x_6085_);
                v___x_6089_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6089_, 0, v___x_6088_);
                leanh::lean_ctor_set(v___x_6089_, 1, v_a_6081_);
                if v_isShared_6084_ == 0 {
                    leanh::lean_ctor_set(v___x_6083_, 0, v___x_6089_);
                    v___x_6091_ = v___x_6083_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6092_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6092_, 0, v___x_6089_);
                    v___x_6091_ = v_reuseFailAlloc_6092_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6091_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg___boxed(
    mut v_h_6094_: *mut leanh::LeanObject,
    mut v_a_6095_: *mut leanh::LeanObject,
    mut v_a_6096_: *mut leanh::LeanObject,
    mut v_a_6097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6098_ =
        l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(v_h_6094_, v_a_6095_, v_a_6096_);
    leanh::lean_dec_ref(v_a_6096_);
    leanh::lean_dec(v_a_6095_);
    return v_res_6098_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(
    mut v_h_6099_: *mut leanh::LeanObject,
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
) -> *mut leanh::LeanObject {
    let mut v___x_6111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6111_ =
        l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(v_h_6099_, v_a_6100_, v_a_6108_);
    return v___x_6111_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___boxed(
    mut v_h_6112_: *mut leanh::LeanObject,
    mut v_a_6113_: *mut leanh::LeanObject,
    mut v_a_6114_: *mut leanh::LeanObject,
    mut v_a_6115_: *mut leanh::LeanObject,
    mut v_a_6116_: *mut leanh::LeanObject,
    mut v_a_6117_: *mut leanh::LeanObject,
    mut v_a_6118_: *mut leanh::LeanObject,
    mut v_a_6119_: *mut leanh::LeanObject,
    mut v_a_6120_: *mut leanh::LeanObject,
    mut v_a_6121_: *mut leanh::LeanObject,
    mut v_a_6122_: *mut leanh::LeanObject,
    mut v_a_6123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6124_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6124_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(
        v_h_6112_, v_a_6113_, v_a_6114_, v_a_6115_, v_a_6116_, v_a_6117_, v_a_6118_, v_a_6119_,
        v_a_6120_, v_a_6121_, v_a_6122_,
    );
    leanh::lean_dec(v_a_6122_);
    leanh::lean_dec_ref(v_a_6121_);
    leanh::lean_dec(v_a_6120_);
    leanh::lean_dec_ref(v_a_6119_);
    leanh::lean_dec(v_a_6118_);
    leanh::lean_dec_ref(v_a_6117_);
    leanh::lean_dec(v_a_6116_);
    leanh::lean_dec_ref(v_a_6115_);
    leanh::lean_dec(v_a_6114_);
    leanh::lean_dec(v_a_6113_);
    return v_res_6124_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
}