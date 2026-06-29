// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
// Imports: Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Lean.Meta.Tactic.Simp.Arith.Int.Simp
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
use crate::ffi::lean_array_fset;
use crate::ffi::{
    lean_int_dec_eq, lean_int_dec_le, lean_int_mul, lean_int_neg, lean_nat_abs, lean_nat_to_int,
};
use crate::ffi::{lean_int_ediv, lean_int_emod};
use crate::ffi::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::ffi::{
    lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul, lean_nat_sub,
};
use crate::ffi::lean_st_ref_get;
use crate::ffi::{
    lean_grind_cutsat_assert_eq, lean_grind_cutsat_assert_le, lean_grind_cutsat_mk_var,
};
static mut l_Int_Linear_Poly_isZero___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int_Linear_Poly_isZero___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__1: usize = 0;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 43, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__3_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [42, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__0_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__0_value:
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
    m_data: [78, 101, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__1_value:
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
    m_data: [110, 101, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__2_value_aux_0:
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
            l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        9626815015619986526 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__2_value:
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
            l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__2_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        17185717442815859305 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__6_value:
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
    m_data: [73, 110, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__7_value:
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
            l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__6_value
        ) as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__7_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__9_value:
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
    m_data: [105, 110, 115, 116, 78, 101, 103, 73, 110, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__9_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__10_value_aux_0:
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
            l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__6_value
        ) as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__10_value:
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
            l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__10_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__9_value
        ) as *mut crate::leanh::LeanObject,
        6362876895233142233 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__10_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__0_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__2_value:
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
    m_data: [32, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__0_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__0_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__0_value:
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
    m_data: [32, 61, 32, 48, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Int_Linear_Poly_updateOccs___redArg___closed__0_value: crate::leanh::LeanStringObject<
    55,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Int_Linear_Poly_updateOccs___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Int_Linear_Poly_updateOccs___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Int_Linear_Poly_updateOccs___redArg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int_Linear_Poly_updateOccs___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Int_Linear_Poly_eval_x3f___redArg___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int_Linear_Poly_eval_x3f___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__0_value:
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
    m_data: [44, 32, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__2_value:
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
    m_data: [110, 111, 110, 101, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Int_Linear_Poly_isZero___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3063_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3064_ = lean_nat_to_int(v___x_3063_);
    return v___x_3064_;
}
pub unsafe fn l_Int_Linear_Poly_isZero(mut v_x_3065_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_3065_) == 0 {
        let mut v_k_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3068_: u8 = 0;
        v_k_3066_ = crate::leanh::lean_ctor_get(v_x_3065_, 0);
        v___x_3067_ = crate::leanh::lean_obj_once(
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
    mut v_x_3070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3071_: u8 = 0;
    let mut v_r_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3071_ = l_Int_Linear_Poly_isZero(v_x_3070_);
    crate::leanh::lean_dec_ref(v_x_3070_);
    v_r_3072_ = crate::leanh::lean_box((v_res_3071_) as usize);
    return v_r_3072_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_isSorted_go(
    mut v_a_3073_: *mut crate::leanh::LeanObject,
    mut v_a_3074_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3075_: u8 = 0;
    let mut v_v_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3085_: u8 = 0;
    let mut v___x_3086_: u8 = 0;
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3091_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3074_) == 0 {
                    crate::leanh::lean_dec(v_a_3073_);
                    v___x_3075_ = 1;
                    return v___x_3075_;
                } else {
                    if crate::leanh::lean_obj_tag(v_a_3073_) == 0 {
                        v_v_3076_ = crate::leanh::lean_ctor_get(v_a_3074_, 1);
                        v_p_3077_ = crate::leanh::lean_ctor_get(v_a_3074_, 2);
                        crate::leanh::lean_inc(v_v_3076_);
                        v___x_3078_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3078_, 0, v_v_3076_);
                        v_a_3073_ = v___x_3078_;
                        v_a_3074_ = v_p_3077_;
                        state = 0;
                        continue;
                    } else {
                        v_v_3080_ = crate::leanh::lean_ctor_get(v_a_3074_, 1);
                        v_p_3081_ = crate::leanh::lean_ctor_get(v_a_3074_, 2);
                        v_val_3082_ = crate::leanh::lean_ctor_get(v_a_3073_, 0);
                        v_isSharedCheck_3091_ = (!crate::leanh::lean_is_exclusive(v_a_3073_)) as u8;
                        if v_isSharedCheck_3091_ == 0 {
                            v___x_3084_ = v_a_3073_;
                            v_isShared_3085_ = v_isSharedCheck_3091_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_3082_);
                            crate::leanh::lean_dec(v_a_3073_);
                            v___x_3084_ = crate::leanh::lean_box(0);
                            v_isShared_3085_ = v_isSharedCheck_3091_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3086_ = lean_nat_dec_lt(v_v_3080_, v_val_3082_);
                crate::leanh::lean_dec(v_val_3082_);
                if v___x_3086_ == 0 {
                    crate::leanh::lean_del_object(v___x_3084_);
                    return v___x_3086_;
                } else {
                    crate::leanh::lean_inc(v_v_3080_);
                    if v_isShared_3085_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3084_, 0, v_v_3080_);
                        v___x_3088_ = v___x_3084_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3090_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_v_3080_);
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
    mut v_a_3092_: *mut crate::leanh::LeanObject,
    mut v_a_3093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3094_: u8 = 0;
    let mut v_r_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3094_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_isSorted_go(
            v_a_3092_, v_a_3093_,
        );
    crate::leanh::lean_dec_ref(v_a_3093_);
    v_r_3095_ = crate::leanh::lean_box((v_res_3094_) as usize);
    return v_r_3095_;
}
pub unsafe fn l_Int_Linear_Poly_isSorted(mut v_p_3096_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: u8 = 0;
    v___x_3097_ = crate::leanh::lean_box(0);
    v___x_3098_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_isSorted_go(
            v___x_3097_,
            v_p_3096_,
        );
    return v___x_3098_;
}
pub unsafe fn l_Int_Linear_Poly_isSorted___boxed(
    mut v_p_3099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3100_: u8 = 0;
    let mut v_r_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3100_ = l_Int_Linear_Poly_isSorted(v_p_3099_);
    crate::leanh::lean_dec_ref(v_p_3099_);
    v_r_3101_ = crate::leanh::lean_box((v_res_3100_) as usize);
    return v_r_3101_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(
    mut v_a_3102_: *mut crate::leanh::LeanObject,
    mut v_a_3103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3105_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
    v___x_3106_ =
        l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_3105_, v_a_3102_, v_a_3103_);
    return v___x_3106_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg___boxed(
    mut v_a_3107_: *mut crate::leanh::LeanObject,
    mut v_a_3108_: *mut crate::leanh::LeanObject,
    mut v_a_3109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3110_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3107_, v_a_3108_);
    crate::leanh::lean_dec_ref(v_a_3108_);
    crate::leanh::lean_dec(v_a_3107_);
    return v_res_3110_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_get_x27(
    mut v_a_3111_: *mut crate::leanh::LeanObject,
    mut v_a_3112_: *mut crate::leanh::LeanObject,
    mut v_a_3113_: *mut crate::leanh::LeanObject,
    mut v_a_3114_: *mut crate::leanh::LeanObject,
    mut v_a_3115_: *mut crate::leanh::LeanObject,
    mut v_a_3116_: *mut crate::leanh::LeanObject,
    mut v_a_3117_: *mut crate::leanh::LeanObject,
    mut v_a_3118_: *mut crate::leanh::LeanObject,
    mut v_a_3119_: *mut crate::leanh::LeanObject,
    mut v_a_3120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3122_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3111_, v_a_3119_);
    return v___x_3122_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_get_x27___boxed(
    mut v_a_3123_: *mut crate::leanh::LeanObject,
    mut v_a_3124_: *mut crate::leanh::LeanObject,
    mut v_a_3125_: *mut crate::leanh::LeanObject,
    mut v_a_3126_: *mut crate::leanh::LeanObject,
    mut v_a_3127_: *mut crate::leanh::LeanObject,
    mut v_a_3128_: *mut crate::leanh::LeanObject,
    mut v_a_3129_: *mut crate::leanh::LeanObject,
    mut v_a_3130_: *mut crate::leanh::LeanObject,
    mut v_a_3131_: *mut crate::leanh::LeanObject,
    mut v_a_3132_: *mut crate::leanh::LeanObject,
    mut v_a_3133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3134_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(
        v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_,
        v_a_3131_, v_a_3132_,
    );
    crate::leanh::lean_dec(v_a_3132_);
    crate::leanh::lean_dec_ref(v_a_3131_);
    crate::leanh::lean_dec(v_a_3130_);
    crate::leanh::lean_dec_ref(v_a_3129_);
    crate::leanh::lean_dec(v_a_3128_);
    crate::leanh::lean_dec_ref(v_a_3127_);
    crate::leanh::lean_dec(v_a_3126_);
    crate::leanh::lean_dec_ref(v_a_3125_);
    crate::leanh::lean_dec(v_a_3124_);
    crate::leanh::lean_dec(v_a_3123_);
    return v_res_3134_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_modify_x27___redArg(
    mut v_f_3135_: *mut crate::leanh::LeanObject,
    mut v_a_3136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3138_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
    v___x_3139_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3138_, v_f_3135_, v_a_3136_);
    return v___x_3139_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_modify_x27___redArg___boxed(
    mut v_f_3140_: *mut crate::leanh::LeanObject,
    mut v_a_3141_: *mut crate::leanh::LeanObject,
    mut v_a_3142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3143_ = l_Lean_Meta_Grind_Arith_Cutsat_modify_x27___redArg(v_f_3140_, v_a_3141_);
    crate::leanh::lean_dec(v_a_3141_);
    return v_res_3143_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_modify_x27(
    mut v_f_3144_: *mut crate::leanh::LeanObject,
    mut v_a_3145_: *mut crate::leanh::LeanObject,
    mut v_a_3146_: *mut crate::leanh::LeanObject,
    mut v_a_3147_: *mut crate::leanh::LeanObject,
    mut v_a_3148_: *mut crate::leanh::LeanObject,
    mut v_a_3149_: *mut crate::leanh::LeanObject,
    mut v_a_3150_: *mut crate::leanh::LeanObject,
    mut v_a_3151_: *mut crate::leanh::LeanObject,
    mut v_a_3152_: *mut crate::leanh::LeanObject,
    mut v_a_3153_: *mut crate::leanh::LeanObject,
    mut v_a_3154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3156_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
    v___x_3157_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3156_, v_f_3144_, v_a_3145_);
    return v___x_3157_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_modify_x27___boxed(
    mut v_f_3158_: *mut crate::leanh::LeanObject,
    mut v_a_3159_: *mut crate::leanh::LeanObject,
    mut v_a_3160_: *mut crate::leanh::LeanObject,
    mut v_a_3161_: *mut crate::leanh::LeanObject,
    mut v_a_3162_: *mut crate::leanh::LeanObject,
    mut v_a_3163_: *mut crate::leanh::LeanObject,
    mut v_a_3164_: *mut crate::leanh::LeanObject,
    mut v_a_3165_: *mut crate::leanh::LeanObject,
    mut v_a_3166_: *mut crate::leanh::LeanObject,
    mut v_a_3167_: *mut crate::leanh::LeanObject,
    mut v_a_3168_: *mut crate::leanh::LeanObject,
    mut v_a_3169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3170_ = l_Lean_Meta_Grind_Arith_Cutsat_modify_x27(
        v_f_3158_, v_a_3159_, v_a_3160_, v_a_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_,
        v_a_3166_, v_a_3167_, v_a_3168_,
    );
    crate::leanh::lean_dec(v_a_3168_);
    crate::leanh::lean_dec_ref(v_a_3167_);
    crate::leanh::lean_dec(v_a_3166_);
    crate::leanh::lean_dec_ref(v_a_3165_);
    crate::leanh::lean_dec(v_a_3164_);
    crate::leanh::lean_dec_ref(v_a_3163_);
    crate::leanh::lean_dec(v_a_3162_);
    crate::leanh::lean_dec_ref(v_a_3161_);
    crate::leanh::lean_dec(v_a_3160_);
    crate::leanh::lean_dec(v_a_3159_);
    return v_res_3170_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(
    mut v_a_3171_: *mut crate::leanh::LeanObject,
    mut v_a_3172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: u8 = 0;
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3181_: u8 = 0;
    let mut v_conflict_x3f_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: u8 = 0;
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3191_: u8 = 0;
    let mut v_a_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3195_: u8 = 0;
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3199_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3174_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_3171_);
                if crate::leanh::lean_obj_tag(v___x_3174_) == 0 {
                    v_a_3175_ = crate::leanh::lean_ctor_get(v___x_3174_, 0);
                    crate::leanh::lean_inc(v_a_3175_);
                    v___x_3176_ = (crate::leanh::lean_unbox(v_a_3175_) as u8);
                    if v___x_3176_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3174_, 1);
                        v___x_3177_ =
                            l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3171_, v_a_3172_);
                        if crate::leanh::lean_obj_tag(v___x_3177_) == 0 {
                            v_a_3178_ = crate::leanh::lean_ctor_get(v___x_3177_, 0);
                            v_isSharedCheck_3191_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3177_)) as u8;
                            if v_isSharedCheck_3191_ == 0 {
                                v___x_3180_ = v___x_3177_;
                                v_isShared_3181_ = v_isSharedCheck_3191_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3178_);
                                crate::leanh::lean_dec(v___x_3177_);
                                v___x_3180_ = crate::leanh::lean_box(0);
                                v_isShared_3181_ = v_isSharedCheck_3191_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3175_);
                            v_a_3192_ = crate::leanh::lean_ctor_get(v___x_3177_, 0);
                            v_isSharedCheck_3199_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3177_)) as u8;
                            if v_isSharedCheck_3199_ == 0 {
                                v___x_3194_ = v___x_3177_;
                                v_isShared_3195_ = v_isSharedCheck_3199_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3192_);
                                crate::leanh::lean_dec(v___x_3177_);
                                v___x_3194_ = crate::leanh::lean_box(0);
                                v_isShared_3195_ = v_isSharedCheck_3199_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3175_);
                        return v___x_3174_;
                    }
                } else {
                    return v___x_3174_;
                }
            }
            1 => {
                v_conflict_x3f_3182_ = crate::leanh::lean_ctor_get(v_a_3178_, 15);
                crate::leanh::lean_inc(v_conflict_x3f_3182_);
                crate::leanh::lean_dec(v_a_3178_);
                if crate::leanh::lean_obj_tag(v_conflict_x3f_3182_) == 0 {
                    if v_isShared_3181_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3180_, 0, v_a_3175_);
                        v___x_3184_ = v___x_3180_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3185_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3175_);
                        v___x_3184_ = v_reuseFailAlloc_3185_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_conflict_x3f_3182_, 1);
                    crate::leanh::lean_dec(v_a_3175_);
                    v___x_3186_ = 1;
                    v___x_3187_ = crate::leanh::lean_box((v___x_3186_) as usize);
                    if v_isShared_3181_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3180_, 0, v___x_3187_);
                        v___x_3189_ = v___x_3180_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3190_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3187_);
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
                    v_reuseFailAlloc_3198_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3192_);
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
    mut v_a_3200_: *mut crate::leanh::LeanObject,
    mut v_a_3201_: *mut crate::leanh::LeanObject,
    mut v_a_3202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3203_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_3200_, v_a_3201_);
    crate::leanh::lean_dec_ref(v_a_3201_);
    crate::leanh::lean_dec(v_a_3200_);
    return v_res_3203_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_inconsistent(
    mut v_a_3204_: *mut crate::leanh::LeanObject,
    mut v_a_3205_: *mut crate::leanh::LeanObject,
    mut v_a_3206_: *mut crate::leanh::LeanObject,
    mut v_a_3207_: *mut crate::leanh::LeanObject,
    mut v_a_3208_: *mut crate::leanh::LeanObject,
    mut v_a_3209_: *mut crate::leanh::LeanObject,
    mut v_a_3210_: *mut crate::leanh::LeanObject,
    mut v_a_3211_: *mut crate::leanh::LeanObject,
    mut v_a_3212_: *mut crate::leanh::LeanObject,
    mut v_a_3213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3215_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_3204_, v_a_3212_);
    return v___x_3215_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___boxed(
    mut v_a_3216_: *mut crate::leanh::LeanObject,
    mut v_a_3217_: *mut crate::leanh::LeanObject,
    mut v_a_3218_: *mut crate::leanh::LeanObject,
    mut v_a_3219_: *mut crate::leanh::LeanObject,
    mut v_a_3220_: *mut crate::leanh::LeanObject,
    mut v_a_3221_: *mut crate::leanh::LeanObject,
    mut v_a_3222_: *mut crate::leanh::LeanObject,
    mut v_a_3223_: *mut crate::leanh::LeanObject,
    mut v_a_3224_: *mut crate::leanh::LeanObject,
    mut v_a_3225_: *mut crate::leanh::LeanObject,
    mut v_a_3226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3227_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent(
        v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_,
        v_a_3224_, v_a_3225_,
    );
    crate::leanh::lean_dec(v_a_3225_);
    crate::leanh::lean_dec_ref(v_a_3224_);
    crate::leanh::lean_dec(v_a_3223_);
    crate::leanh::lean_dec_ref(v_a_3222_);
    crate::leanh::lean_dec(v_a_3221_);
    crate::leanh::lean_dec_ref(v_a_3220_);
    crate::leanh::lean_dec(v_a_3219_);
    crate::leanh::lean_dec_ref(v_a_3218_);
    crate::leanh::lean_dec(v_a_3217_);
    crate::leanh::lean_dec(v_a_3216_);
    return v_res_3227_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_mkVar___boxed(
    mut v_e_3240_: *mut crate::leanh::LeanObject,
    mut v_a_3241_: *mut crate::leanh::LeanObject,
    mut v_a_3242_: *mut crate::leanh::LeanObject,
    mut v_a_3243_: *mut crate::leanh::LeanObject,
    mut v_a_3244_: *mut crate::leanh::LeanObject,
    mut v_a_3245_: *mut crate::leanh::LeanObject,
    mut v_a_3246_: *mut crate::leanh::LeanObject,
    mut v_a_3247_: *mut crate::leanh::LeanObject,
    mut v_a_3248_: *mut crate::leanh::LeanObject,
    mut v_a_3249_: *mut crate::leanh::LeanObject,
    mut v_a_3250_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_3251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3252_ = lean_grind_cutsat_mk_var(
        v_e_3240_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_,
        v_a_3248_, v_a_3249_, v_a_3250_,
    );
    return v_res_3252_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(
    mut v_a_3253_: *mut crate::leanh::LeanObject,
    mut v_a_3254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3260_: u8 = 0;
    let mut v_vars_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3265_: u8 = 0;
    let mut v_a_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3269_: u8 = 0;
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3273_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3256_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3253_, v_a_3254_);
                if crate::leanh::lean_obj_tag(v___x_3256_) == 0 {
                    v_a_3257_ = crate::leanh::lean_ctor_get(v___x_3256_, 0);
                    v_isSharedCheck_3265_ = (!crate::leanh::lean_is_exclusive(v___x_3256_)) as u8;
                    if v_isSharedCheck_3265_ == 0 {
                        v___x_3259_ = v___x_3256_;
                        v_isShared_3260_ = v_isSharedCheck_3265_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3257_);
                        crate::leanh::lean_dec(v___x_3256_);
                        v___x_3259_ = crate::leanh::lean_box(0);
                        v_isShared_3260_ = v_isSharedCheck_3265_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3266_ = crate::leanh::lean_ctor_get(v___x_3256_, 0);
                    v_isSharedCheck_3273_ = (!crate::leanh::lean_is_exclusive(v___x_3256_)) as u8;
                    if v_isSharedCheck_3273_ == 0 {
                        v___x_3268_ = v___x_3256_;
                        v_isShared_3269_ = v_isSharedCheck_3273_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3266_);
                        crate::leanh::lean_dec(v___x_3256_);
                        v___x_3268_ = crate::leanh::lean_box(0);
                        v_isShared_3269_ = v_isSharedCheck_3273_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_vars_3261_ = crate::leanh::lean_ctor_get(v_a_3257_, 0);
                crate::leanh::lean_inc_ref(v_vars_3261_);
                crate::leanh::lean_dec(v_a_3257_);
                if v_isShared_3260_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3259_, 0, v_vars_3261_);
                    v___x_3263_ = v___x_3259_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3264_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_vars_3261_);
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
                    v_reuseFailAlloc_3272_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3266_);
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
    mut v_a_3274_: *mut crate::leanh::LeanObject,
    mut v_a_3275_: *mut crate::leanh::LeanObject,
    mut v_a_3276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3277_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(v_a_3274_, v_a_3275_);
    crate::leanh::lean_dec_ref(v_a_3275_);
    crate::leanh::lean_dec(v_a_3274_);
    return v_res_3277_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_getVars(
    mut v_a_3278_: *mut crate::leanh::LeanObject,
    mut v_a_3279_: *mut crate::leanh::LeanObject,
    mut v_a_3280_: *mut crate::leanh::LeanObject,
    mut v_a_3281_: *mut crate::leanh::LeanObject,
    mut v_a_3282_: *mut crate::leanh::LeanObject,
    mut v_a_3283_: *mut crate::leanh::LeanObject,
    mut v_a_3284_: *mut crate::leanh::LeanObject,
    mut v_a_3285_: *mut crate::leanh::LeanObject,
    mut v_a_3286_: *mut crate::leanh::LeanObject,
    mut v_a_3287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3289_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(v_a_3278_, v_a_3286_);
    return v___x_3289_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_getVars___boxed(
    mut v_a_3290_: *mut crate::leanh::LeanObject,
    mut v_a_3291_: *mut crate::leanh::LeanObject,
    mut v_a_3292_: *mut crate::leanh::LeanObject,
    mut v_a_3293_: *mut crate::leanh::LeanObject,
    mut v_a_3294_: *mut crate::leanh::LeanObject,
    mut v_a_3295_: *mut crate::leanh::LeanObject,
    mut v_a_3296_: *mut crate::leanh::LeanObject,
    mut v_a_3297_: *mut crate::leanh::LeanObject,
    mut v_a_3298_: *mut crate::leanh::LeanObject,
    mut v_a_3299_: *mut crate::leanh::LeanObject,
    mut v_a_3300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3301_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars(
        v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_,
        v_a_3298_, v_a_3299_,
    );
    crate::leanh::lean_dec(v_a_3299_);
    crate::leanh::lean_dec_ref(v_a_3298_);
    crate::leanh::lean_dec(v_a_3297_);
    crate::leanh::lean_dec_ref(v_a_3296_);
    crate::leanh::lean_dec(v_a_3295_);
    crate::leanh::lean_dec_ref(v_a_3294_);
    crate::leanh::lean_dec(v_a_3293_);
    crate::leanh::lean_dec_ref(v_a_3292_);
    crate::leanh::lean_dec(v_a_3291_);
    crate::leanh::lean_dec(v_a_3290_);
    return v_res_3301_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(
    mut v_x_3302_: *mut crate::leanh::LeanObject,
    mut v_a_3303_: *mut crate::leanh::LeanObject,
    mut v_a_3304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3310_: u8 = 0;
    let mut v_vars_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: u8 = 0;
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3323_: u8 = 0;
    let mut v_a_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3327_: u8 = 0;
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3331_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3306_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3303_, v_a_3304_);
                if crate::leanh::lean_obj_tag(v___x_3306_) == 0 {
                    v_a_3307_ = crate::leanh::lean_ctor_get(v___x_3306_, 0);
                    v_isSharedCheck_3323_ = (!crate::leanh::lean_is_exclusive(v___x_3306_)) as u8;
                    if v_isSharedCheck_3323_ == 0 {
                        v___x_3309_ = v___x_3306_;
                        v_isShared_3310_ = v_isSharedCheck_3323_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3307_);
                        crate::leanh::lean_dec(v___x_3306_);
                        v___x_3309_ = crate::leanh::lean_box(0);
                        v_isShared_3310_ = v_isSharedCheck_3323_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3324_ = crate::leanh::lean_ctor_get(v___x_3306_, 0);
                    v_isSharedCheck_3331_ = (!crate::leanh::lean_is_exclusive(v___x_3306_)) as u8;
                    if v_isSharedCheck_3331_ == 0 {
                        v___x_3326_ = v___x_3306_;
                        v_isShared_3327_ = v_isSharedCheck_3331_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3324_);
                        crate::leanh::lean_dec(v___x_3306_);
                        v___x_3326_ = crate::leanh::lean_box(0);
                        v_isShared_3327_ = v_isSharedCheck_3331_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_vars_3311_ = crate::leanh::lean_ctor_get(v_a_3307_, 0);
                crate::leanh::lean_inc_ref(v_vars_3311_);
                crate::leanh::lean_dec(v_a_3307_);
                v_size_3312_ = crate::leanh::lean_ctor_get(v_vars_3311_, 2);
                v___x_3313_ = l_Lean_instInhabitedExpr;
                v___x_3314_ = lean_nat_dec_lt(v_x_3302_, v_size_3312_);
                if v___x_3314_ == 0 {
                    crate::leanh::lean_dec_ref(v_vars_3311_);
                    v___x_3315_ = l_outOfBounds___redArg(v___x_3313_);
                    if v_isShared_3310_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3309_, 0, v___x_3315_);
                        v___x_3317_ = v___x_3309_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3318_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3318_, 0, v___x_3315_);
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
                    crate::leanh::lean_dec_ref(v_vars_3311_);
                    if v_isShared_3310_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3309_, 0, v___x_3319_);
                        v___x_3321_ = v___x_3309_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3322_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3322_, 0, v___x_3319_);
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
                    v_reuseFailAlloc_3330_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3324_);
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
    mut v_x_3332_: *mut crate::leanh::LeanObject,
    mut v_a_3333_: *mut crate::leanh::LeanObject,
    mut v_a_3334_: *mut crate::leanh::LeanObject,
    mut v_a_3335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3336_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_3332_, v_a_3333_, v_a_3334_);
    crate::leanh::lean_dec_ref(v_a_3334_);
    crate::leanh::lean_dec(v_a_3333_);
    crate::leanh::lean_dec(v_x_3332_);
    return v_res_3336_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_getVar(
    mut v_x_3337_: *mut crate::leanh::LeanObject,
    mut v_a_3338_: *mut crate::leanh::LeanObject,
    mut v_a_3339_: *mut crate::leanh::LeanObject,
    mut v_a_3340_: *mut crate::leanh::LeanObject,
    mut v_a_3341_: *mut crate::leanh::LeanObject,
    mut v_a_3342_: *mut crate::leanh::LeanObject,
    mut v_a_3343_: *mut crate::leanh::LeanObject,
    mut v_a_3344_: *mut crate::leanh::LeanObject,
    mut v_a_3345_: *mut crate::leanh::LeanObject,
    mut v_a_3346_: *mut crate::leanh::LeanObject,
    mut v_a_3347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3349_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_3337_, v_a_3338_, v_a_3346_);
    return v___x_3349_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_getVar___boxed(
    mut v_x_3350_: *mut crate::leanh::LeanObject,
    mut v_a_3351_: *mut crate::leanh::LeanObject,
    mut v_a_3352_: *mut crate::leanh::LeanObject,
    mut v_a_3353_: *mut crate::leanh::LeanObject,
    mut v_a_3354_: *mut crate::leanh::LeanObject,
    mut v_a_3355_: *mut crate::leanh::LeanObject,
    mut v_a_3356_: *mut crate::leanh::LeanObject,
    mut v_a_3357_: *mut crate::leanh::LeanObject,
    mut v_a_3358_: *mut crate::leanh::LeanObject,
    mut v_a_3359_: *mut crate::leanh::LeanObject,
    mut v_a_3360_: *mut crate::leanh::LeanObject,
    mut v_a_3361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3362_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar(
        v_x_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_,
        v_a_3358_, v_a_3359_, v_a_3360_,
    );
    crate::leanh::lean_dec(v_a_3360_);
    crate::leanh::lean_dec_ref(v_a_3359_);
    crate::leanh::lean_dec(v_a_3358_);
    crate::leanh::lean_dec_ref(v_a_3357_);
    crate::leanh::lean_dec(v_a_3356_);
    crate::leanh::lean_dec_ref(v_a_3355_);
    crate::leanh::lean_dec(v_a_3354_);
    crate::leanh::lean_dec_ref(v_a_3353_);
    crate::leanh::lean_dec(v_a_3352_);
    crate::leanh::lean_dec(v_a_3351_);
    crate::leanh::lean_dec(v_x_3350_);
    return v_res_3362_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(
    mut v_keys_3363_: *mut crate::leanh::LeanObject,
    mut v_i_3364_: *mut crate::leanh::LeanObject,
    mut v_k_3365_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: u8 = 0;
    let mut v_k_x27_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: u8 = 0;
    let mut v___x_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3366_ = lean_array_get_size(v_keys_3363_);
                v___x_3367_ = lean_nat_dec_lt(v_i_3364_, v___x_3366_);
                if v___x_3367_ == 0 {
                    crate::leanh::lean_dec(v_i_3364_);
                    return v___x_3367_;
                } else {
                    v_k_x27_3368_ = lean_array_fget_borrowed(v_keys_3363_, v_i_3364_);
                    v___x_3369_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_3365_,
                            v_k_x27_3368_,
                        );
                    if v___x_3369_ == 0 {
                        v___x_3370_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3371_ = lean_nat_add(v_i_3364_, v___x_3370_);
                        crate::leanh::lean_dec(v_i_3364_);
                        v_i_3364_ = v___x_3371_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_3364_);
                        return v___x_3369_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_3373_: *mut crate::leanh::LeanObject,
    mut v_i_3374_: *mut crate::leanh::LeanObject,
    mut v_k_3375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3376_: u8 = 0;
    let mut v_r_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3376_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(v_keys_3373_, v_i_3374_, v_k_3375_);
    crate::leanh::lean_dec_ref(v_k_3375_);
    crate::leanh::lean_dec_ref(v_keys_3373_);
    v_r_3377_ = crate::leanh::lean_box((v_res_3376_) as usize);
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
    v___x_3382_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__0);
    v___x_3383_ = lean_usize_sub(v___x_3382_, v___x_3381_);
    return v___x_3383_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(
    mut v_x_3384_: *mut crate::leanh::LeanObject,
    mut v_x_3385_: usize,
    mut v_x_3386_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: usize = 0;
    let mut v___x_3390_: usize = 0;
    let mut v___x_3391_: usize = 0;
    let mut v_j_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: u8 = 0;
    let mut v_node_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: usize = 0;
    let mut v___x_3399_: u8 = 0;
    let mut v_ks_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3384_) == 0 {
                    v_es_3387_ = crate::leanh::lean_ctor_get(v_x_3384_, 0);
                    v___x_3388_ = crate::leanh::lean_box(2);
                    v___x_3389_ = 5usize;
                    v___x_3390_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___closed__1);
                    v___x_3391_ = lean_usize_land(v_x_3385_, v___x_3390_);
                    v_j_3392_ = lean_usize_to_nat(v___x_3391_);
                    v___x_3393_ = lean_array_get_borrowed(v___x_3388_, v_es_3387_, v_j_3392_);
                    crate::leanh::lean_dec(v_j_3392_);
                    match crate::leanh::lean_obj_tag(v___x_3393_) {
                        0 => {
                            v_key_3394_ = crate::leanh::lean_ctor_get(v___x_3393_, 0);
                            v___x_3395_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_3386_, v_key_3394_);
                            return v___x_3395_;
                        }
                        1 => {
                            v_node_3396_ = crate::leanh::lean_ctor_get(v___x_3393_, 0);
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
                    v_ks_3400_ = crate::leanh::lean_ctor_get(v_x_3384_, 0);
                    v___x_3401_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3402_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(v_ks_3400_, v___x_3401_, v_x_3386_);
                    return v___x_3402_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg___boxed(
    mut v_x_3403_: *mut crate::leanh::LeanObject,
    mut v_x_3404_: *mut crate::leanh::LeanObject,
    mut v_x_3405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_853__boxed_3406_: usize = 0;
    let mut v_res_3407_: u8 = 0;
    let mut v_r_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_853__boxed_3406_ = crate::leanh::lean_unbox_usize(v_x_3404_);
    crate::leanh::lean_dec(v_x_3404_);
    v_res_3407_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(v_x_3403_, v_x_853__boxed_3406_, v_x_3405_);
    crate::leanh::lean_dec_ref(v_x_3405_);
    crate::leanh::lean_dec_ref(v_x_3403_);
    v_r_3408_ = crate::leanh::lean_box((v_res_3407_) as usize);
    return v_r_3408_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(
    mut v_x_3409_: *mut crate::leanh::LeanObject,
    mut v_x_3410_: *mut crate::leanh::LeanObject,
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
    mut v_x_3414_: *mut crate::leanh::LeanObject,
    mut v_x_3415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3416_: u8 = 0;
    let mut v_r_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3416_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(v_x_3414_, v_x_3415_);
    crate::leanh::lean_dec_ref(v_x_3415_);
    crate::leanh::lean_dec_ref(v_x_3414_);
    v_r_3417_ = crate::leanh::lean_box((v_res_3416_) as usize);
    return v_r_3417_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(
    mut v_e_3418_: *mut crate::leanh::LeanObject,
    mut v_a_3419_: *mut crate::leanh::LeanObject,
    mut v_a_3420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3426_: u8 = 0;
    let mut v_varMap_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: u8 = 0;
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3433_: u8 = 0;
    let mut v_a_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3437_: u8 = 0;
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3441_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3422_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3419_, v_a_3420_);
                if crate::leanh::lean_obj_tag(v___x_3422_) == 0 {
                    v_a_3423_ = crate::leanh::lean_ctor_get(v___x_3422_, 0);
                    v_isSharedCheck_3433_ = (!crate::leanh::lean_is_exclusive(v___x_3422_)) as u8;
                    if v_isSharedCheck_3433_ == 0 {
                        v___x_3425_ = v___x_3422_;
                        v_isShared_3426_ = v_isSharedCheck_3433_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3423_);
                        crate::leanh::lean_dec(v___x_3422_);
                        v___x_3425_ = crate::leanh::lean_box(0);
                        v_isShared_3426_ = v_isSharedCheck_3433_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3434_ = crate::leanh::lean_ctor_get(v___x_3422_, 0);
                    v_isSharedCheck_3441_ = (!crate::leanh::lean_is_exclusive(v___x_3422_)) as u8;
                    if v_isSharedCheck_3441_ == 0 {
                        v___x_3436_ = v___x_3422_;
                        v_isShared_3437_ = v_isSharedCheck_3441_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3434_);
                        crate::leanh::lean_dec(v___x_3422_);
                        v___x_3436_ = crate::leanh::lean_box(0);
                        v_isShared_3437_ = v_isSharedCheck_3441_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_varMap_3427_ = crate::leanh::lean_ctor_get(v_a_3423_, 1);
                crate::leanh::lean_inc_ref(v_varMap_3427_);
                crate::leanh::lean_dec(v_a_3423_);
                v___x_3428_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(v_varMap_3427_, v_e_3418_);
                crate::leanh::lean_dec_ref(v_varMap_3427_);
                v___x_3429_ = crate::leanh::lean_box((v___x_3428_) as usize);
                if v_isShared_3426_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3425_, 0, v___x_3429_);
                    v___x_3431_ = v___x_3425_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3432_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3432_, 0, v___x_3429_);
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
                    v_reuseFailAlloc_3440_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
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
    mut v_e_3442_: *mut crate::leanh::LeanObject,
    mut v_a_3443_: *mut crate::leanh::LeanObject,
    mut v_a_3444_: *mut crate::leanh::LeanObject,
    mut v_a_3445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3446_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_3442_, v_a_3443_, v_a_3444_);
    crate::leanh::lean_dec_ref(v_a_3444_);
    crate::leanh::lean_dec(v_a_3443_);
    crate::leanh::lean_dec_ref(v_e_3442_);
    return v_res_3446_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_hasVar(
    mut v_e_3447_: *mut crate::leanh::LeanObject,
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
    let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3459_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_3447_, v_a_3448_, v_a_3456_);
    return v___x_3459_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_hasVar___boxed(
    mut v_e_3460_: *mut crate::leanh::LeanObject,
    mut v_a_3461_: *mut crate::leanh::LeanObject,
    mut v_a_3462_: *mut crate::leanh::LeanObject,
    mut v_a_3463_: *mut crate::leanh::LeanObject,
    mut v_a_3464_: *mut crate::leanh::LeanObject,
    mut v_a_3465_: *mut crate::leanh::LeanObject,
    mut v_a_3466_: *mut crate::leanh::LeanObject,
    mut v_a_3467_: *mut crate::leanh::LeanObject,
    mut v_a_3468_: *mut crate::leanh::LeanObject,
    mut v_a_3469_: *mut crate::leanh::LeanObject,
    mut v_a_3470_: *mut crate::leanh::LeanObject,
    mut v_a_3471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3472_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar(
        v_e_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_,
        v_a_3468_, v_a_3469_, v_a_3470_,
    );
    crate::leanh::lean_dec(v_a_3470_);
    crate::leanh::lean_dec_ref(v_a_3469_);
    crate::leanh::lean_dec(v_a_3468_);
    crate::leanh::lean_dec_ref(v_a_3467_);
    crate::leanh::lean_dec(v_a_3466_);
    crate::leanh::lean_dec_ref(v_a_3465_);
    crate::leanh::lean_dec(v_a_3464_);
    crate::leanh::lean_dec_ref(v_a_3463_);
    crate::leanh::lean_dec(v_a_3462_);
    crate::leanh::lean_dec(v_a_3461_);
    crate::leanh::lean_dec_ref(v_e_3460_);
    return v_res_3472_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0(
    mut v_00_u03b2_3473_: *mut crate::leanh::LeanObject,
    mut v_x_3474_: *mut crate::leanh::LeanObject,
    mut v_x_3475_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3476_: u8 = 0;
    v___x_3476_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___redArg(v_x_3474_, v_x_3475_);
    return v___x_3476_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0___boxed(
    mut v_00_u03b2_3477_: *mut crate::leanh::LeanObject,
    mut v_x_3478_: *mut crate::leanh::LeanObject,
    mut v_x_3479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3480_: u8 = 0;
    let mut v_r_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3480_ =
        l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0(
            v_00_u03b2_3477_,
            v_x_3478_,
            v_x_3479_,
        );
    crate::leanh::lean_dec_ref(v_x_3479_);
    crate::leanh::lean_dec_ref(v_x_3478_);
    v_r_3481_ = crate::leanh::lean_box((v_res_3480_) as usize);
    return v_r_3481_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0(
    mut v_00_u03b2_3482_: *mut crate::leanh::LeanObject,
    mut v_x_3483_: *mut crate::leanh::LeanObject,
    mut v_x_3484_: usize,
    mut v_x_3485_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3486_: u8 = 0;
    v___x_3486_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___redArg(v_x_3483_, v_x_3484_, v_x_3485_);
    return v___x_3486_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0___boxed(
    mut v_00_u03b2_3487_: *mut crate::leanh::LeanObject,
    mut v_x_3488_: *mut crate::leanh::LeanObject,
    mut v_x_3489_: *mut crate::leanh::LeanObject,
    mut v_x_3490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_966__boxed_3491_: usize = 0;
    let mut v_res_3492_: u8 = 0;
    let mut v_r_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_966__boxed_3491_ = crate::leanh::lean_unbox_usize(v_x_3489_);
    crate::leanh::lean_dec(v_x_3489_);
    v_res_3492_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0(v_00_u03b2_3487_, v_x_3488_, v_x_966__boxed_3491_, v_x_3490_);
    crate::leanh::lean_dec_ref(v_x_3490_);
    crate::leanh::lean_dec_ref(v_x_3488_);
    v_r_3493_ = crate::leanh::lean_box((v_res_3492_) as usize);
    return v_r_3493_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3494_: *mut crate::leanh::LeanObject,
    mut v_keys_3495_: *mut crate::leanh::LeanObject,
    mut v_vals_3496_: *mut crate::leanh::LeanObject,
    mut v_heq_3497_: *mut crate::leanh::LeanObject,
    mut v_i_3498_: *mut crate::leanh::LeanObject,
    mut v_k_3499_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3500_: u8 = 0;
    v___x_3500_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___redArg(v_keys_3495_, v_i_3498_, v_k_3499_);
    return v___x_3500_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_3501_: *mut crate::leanh::LeanObject,
    mut v_keys_3502_: *mut crate::leanh::LeanObject,
    mut v_vals_3503_: *mut crate::leanh::LeanObject,
    mut v_heq_3504_: *mut crate::leanh::LeanObject,
    mut v_i_3505_: *mut crate::leanh::LeanObject,
    mut v_k_3506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3507_: u8 = 0;
    let mut v_r_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3507_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_Arith_Cutsat_hasVar_spec__0_spec__0_spec__1(v_00_u03b2_3501_, v_keys_3502_, v_vals_3503_, v_heq_3504_, v_i_3505_, v_k_3506_);
    crate::leanh::lean_dec_ref(v_k_3506_);
    crate::leanh::lean_dec_ref(v_vals_3503_);
    crate::leanh::lean_dec_ref(v_keys_3502_);
    v_r_3508_ = crate::leanh::lean_box((v_res_3507_) as usize);
    return v_r_3508_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg(
    mut v_e_3509_: *mut crate::leanh::LeanObject,
    mut v_a_3510_: *mut crate::leanh::LeanObject,
    mut v_a_3511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3513_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_3509_, v_a_3510_, v_a_3511_);
    return v___x_3513_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg___boxed(
    mut v_e_3514_: *mut crate::leanh::LeanObject,
    mut v_a_3515_: *mut crate::leanh::LeanObject,
    mut v_a_3516_: *mut crate::leanh::LeanObject,
    mut v_a_3517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3518_ =
        l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___redArg(v_e_3514_, v_a_3515_, v_a_3516_);
    crate::leanh::lean_dec_ref(v_a_3516_);
    crate::leanh::lean_dec(v_a_3515_);
    crate::leanh::lean_dec_ref(v_e_3514_);
    return v_res_3518_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm(
    mut v_e_3519_: *mut crate::leanh::LeanObject,
    mut v_a_3520_: *mut crate::leanh::LeanObject,
    mut v_a_3521_: *mut crate::leanh::LeanObject,
    mut v_a_3522_: *mut crate::leanh::LeanObject,
    mut v_a_3523_: *mut crate::leanh::LeanObject,
    mut v_a_3524_: *mut crate::leanh::LeanObject,
    mut v_a_3525_: *mut crate::leanh::LeanObject,
    mut v_a_3526_: *mut crate::leanh::LeanObject,
    mut v_a_3527_: *mut crate::leanh::LeanObject,
    mut v_a_3528_: *mut crate::leanh::LeanObject,
    mut v_a_3529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3531_ = l_Lean_Meta_Grind_Arith_Cutsat_hasVar___redArg(v_e_3519_, v_a_3520_, v_a_3528_);
    return v___x_3531_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm___boxed(
    mut v_e_3532_: *mut crate::leanh::LeanObject,
    mut v_a_3533_: *mut crate::leanh::LeanObject,
    mut v_a_3534_: *mut crate::leanh::LeanObject,
    mut v_a_3535_: *mut crate::leanh::LeanObject,
    mut v_a_3536_: *mut crate::leanh::LeanObject,
    mut v_a_3537_: *mut crate::leanh::LeanObject,
    mut v_a_3538_: *mut crate::leanh::LeanObject,
    mut v_a_3539_: *mut crate::leanh::LeanObject,
    mut v_a_3540_: *mut crate::leanh::LeanObject,
    mut v_a_3541_: *mut crate::leanh::LeanObject,
    mut v_a_3542_: *mut crate::leanh::LeanObject,
    mut v_a_3543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3544_ = l_Lean_Meta_Grind_Arith_Cutsat_isIntTerm(
        v_e_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_,
        v_a_3540_, v_a_3541_, v_a_3542_,
    );
    crate::leanh::lean_dec(v_a_3542_);
    crate::leanh::lean_dec_ref(v_a_3541_);
    crate::leanh::lean_dec(v_a_3540_);
    crate::leanh::lean_dec_ref(v_a_3539_);
    crate::leanh::lean_dec(v_a_3538_);
    crate::leanh::lean_dec_ref(v_a_3537_);
    crate::leanh::lean_dec(v_a_3536_);
    crate::leanh::lean_dec_ref(v_a_3535_);
    crate::leanh::lean_dec(v_a_3534_);
    crate::leanh::lean_dec(v_a_3533_);
    crate::leanh::lean_dec_ref(v_e_3532_);
    return v_res_3544_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(
    mut v_x_3545_: *mut crate::leanh::LeanObject,
    mut v_a_3546_: *mut crate::leanh::LeanObject,
    mut v_a_3547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3553_: u8 = 0;
    let mut v___y_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: u8 = 0;
    let mut v___x_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: u8 = 0;
    let mut v___x_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elimEqs_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: u8 = 0;
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3572_: u8 = 0;
    let mut v_a_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3576_: u8 = 0;
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3580_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3549_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_3546_, v_a_3547_);
                if crate::leanh::lean_obj_tag(v___x_3549_) == 0 {
                    v_a_3550_ = crate::leanh::lean_ctor_get(v___x_3549_, 0);
                    v_isSharedCheck_3572_ = (!crate::leanh::lean_is_exclusive(v___x_3549_)) as u8;
                    if v_isSharedCheck_3572_ == 0 {
                        v___x_3552_ = v___x_3549_;
                        v_isShared_3553_ = v_isSharedCheck_3572_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3550_);
                        crate::leanh::lean_dec(v___x_3549_);
                        v___x_3552_ = crate::leanh::lean_box(0);
                        v_isShared_3553_ = v_isSharedCheck_3572_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3573_ = crate::leanh::lean_ctor_get(v___x_3549_, 0);
                    v_isSharedCheck_3580_ = (!crate::leanh::lean_is_exclusive(v___x_3549_)) as u8;
                    if v_isSharedCheck_3580_ == 0 {
                        v___x_3575_ = v___x_3549_;
                        v_isShared_3576_ = v_isSharedCheck_3580_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3573_);
                        crate::leanh::lean_dec(v___x_3549_);
                        v___x_3575_ = crate::leanh::lean_box(0);
                        v_isShared_3576_ = v_isSharedCheck_3580_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_elimEqs_3566_ = crate::leanh::lean_ctor_get(v_a_3550_, 10);
                crate::leanh::lean_inc_ref(v_elimEqs_3566_);
                crate::leanh::lean_dec(v_a_3550_);
                v_size_3567_ = crate::leanh::lean_ctor_get(v_elimEqs_3566_, 2);
                v___x_3568_ = crate::leanh::lean_box(0);
                v___x_3569_ = lean_nat_dec_lt(v_x_3545_, v_size_3567_);
                if v___x_3569_ == 0 {
                    crate::leanh::lean_dec_ref(v_elimEqs_3566_);
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
                    crate::leanh::lean_dec_ref(v_elimEqs_3566_);
                    v___y_3555_ = v___x_3571_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_3555_) == 0 {
                    v___x_3556_ = 0;
                    v___x_3557_ = crate::leanh::lean_box((v___x_3556_) as usize);
                    if v_isShared_3553_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3552_, 0, v___x_3557_);
                        v___x_3559_ = v___x_3552_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3560_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3557_);
                        v___x_3559_ = v_reuseFailAlloc_3560_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___y_3555_, 1);
                    v___x_3561_ = 1;
                    v___x_3562_ = crate::leanh::lean_box((v___x_3561_) as usize);
                    if v_isShared_3553_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3552_, 0, v___x_3562_);
                        v___x_3564_ = v___x_3552_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3565_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___x_3562_);
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
                    v_reuseFailAlloc_3579_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_a_3573_);
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
    mut v_x_3581_: *mut crate::leanh::LeanObject,
    mut v_a_3582_: *mut crate::leanh::LeanObject,
    mut v_a_3583_: *mut crate::leanh::LeanObject,
    mut v_a_3584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3585_ =
        l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_x_3581_, v_a_3582_, v_a_3583_);
    crate::leanh::lean_dec_ref(v_a_3583_);
    crate::leanh::lean_dec(v_a_3582_);
    crate::leanh::lean_dec(v_x_3581_);
    return v_res_3585_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_eliminated(
    mut v_x_3586_: *mut crate::leanh::LeanObject,
    mut v_a_3587_: *mut crate::leanh::LeanObject,
    mut v_a_3588_: *mut crate::leanh::LeanObject,
    mut v_a_3589_: *mut crate::leanh::LeanObject,
    mut v_a_3590_: *mut crate::leanh::LeanObject,
    mut v_a_3591_: *mut crate::leanh::LeanObject,
    mut v_a_3592_: *mut crate::leanh::LeanObject,
    mut v_a_3593_: *mut crate::leanh::LeanObject,
    mut v_a_3594_: *mut crate::leanh::LeanObject,
    mut v_a_3595_: *mut crate::leanh::LeanObject,
    mut v_a_3596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3598_ =
        l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(v_x_3586_, v_a_3587_, v_a_3595_);
    return v___x_3598_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_eliminated___boxed(
    mut v_x_3599_: *mut crate::leanh::LeanObject,
    mut v_a_3600_: *mut crate::leanh::LeanObject,
    mut v_a_3601_: *mut crate::leanh::LeanObject,
    mut v_a_3602_: *mut crate::leanh::LeanObject,
    mut v_a_3603_: *mut crate::leanh::LeanObject,
    mut v_a_3604_: *mut crate::leanh::LeanObject,
    mut v_a_3605_: *mut crate::leanh::LeanObject,
    mut v_a_3606_: *mut crate::leanh::LeanObject,
    mut v_a_3607_: *mut crate::leanh::LeanObject,
    mut v_a_3608_: *mut crate::leanh::LeanObject,
    mut v_a_3609_: *mut crate::leanh::LeanObject,
    mut v_a_3610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3611_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated(
        v_x_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_,
        v_a_3607_, v_a_3608_, v_a_3609_,
    );
    crate::leanh::lean_dec(v_a_3609_);
    crate::leanh::lean_dec_ref(v_a_3608_);
    crate::leanh::lean_dec(v_a_3607_);
    crate::leanh::lean_dec_ref(v_a_3606_);
    crate::leanh::lean_dec(v_a_3605_);
    crate::leanh::lean_dec_ref(v_a_3604_);
    crate::leanh::lean_dec(v_a_3603_);
    crate::leanh::lean_dec_ref(v_a_3602_);
    crate::leanh::lean_dec(v_a_3601_);
    crate::leanh::lean_dec(v_a_3600_);
    crate::leanh::lean_dec(v_x_3599_);
    return v_res_3611_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_assert___boxed(
    mut v_c_3624_: *mut crate::leanh::LeanObject,
    mut v_a_3625_: *mut crate::leanh::LeanObject,
    mut v_a_3626_: *mut crate::leanh::LeanObject,
    mut v_a_3627_: *mut crate::leanh::LeanObject,
    mut v_a_3628_: *mut crate::leanh::LeanObject,
    mut v_a_3629_: *mut crate::leanh::LeanObject,
    mut v_a_3630_: *mut crate::leanh::LeanObject,
    mut v_a_3631_: *mut crate::leanh::LeanObject,
    mut v_a_3632_: *mut crate::leanh::LeanObject,
    mut v_a_3633_: *mut crate::leanh::LeanObject,
    mut v_a_3634_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_3635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3636_ = lean_grind_cutsat_assert_eq(
        v_c_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_,
        v_a_3632_, v_a_3633_, v_a_3634_,
    );
    return v_res_3636_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0(
    mut v_x_3637_: *mut crate::leanh::LeanObject,
    mut v_s_3638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vars_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_x27_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_x27_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natToIntMap_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natDef_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dvds_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lowers_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uppers_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elimEqs_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elimStack_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_occurs_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignment_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextCnstrId_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_caseSplits_3654_: u8 = 0;
    let mut v_conflict_x3f_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqSplits_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_divMod_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntIds_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntInfos_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntTermMap_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntVarMap_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedCommRing_3662_: u8 = 0;
    let mut v_nonlinearOccs_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3666_: u8 = 0;
    let mut v___x_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3671_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vars_3639_ = crate::leanh::lean_ctor_get(v_s_3638_, 0);
                v_varMap_3640_ = crate::leanh::lean_ctor_get(v_s_3638_, 1);
                v_vars_x27_3641_ = crate::leanh::lean_ctor_get(v_s_3638_, 2);
                v_varMap_x27_3642_ = crate::leanh::lean_ctor_get(v_s_3638_, 3);
                v_natToIntMap_3643_ = crate::leanh::lean_ctor_get(v_s_3638_, 4);
                v_natDef_3644_ = crate::leanh::lean_ctor_get(v_s_3638_, 5);
                v_dvds_3645_ = crate::leanh::lean_ctor_get(v_s_3638_, 6);
                v_lowers_3646_ = crate::leanh::lean_ctor_get(v_s_3638_, 7);
                v_uppers_3647_ = crate::leanh::lean_ctor_get(v_s_3638_, 8);
                v_diseqs_3648_ = crate::leanh::lean_ctor_get(v_s_3638_, 9);
                v_elimEqs_3649_ = crate::leanh::lean_ctor_get(v_s_3638_, 10);
                v_elimStack_3650_ = crate::leanh::lean_ctor_get(v_s_3638_, 11);
                v_occurs_3651_ = crate::leanh::lean_ctor_get(v_s_3638_, 12);
                v_assignment_3652_ = crate::leanh::lean_ctor_get(v_s_3638_, 13);
                v_nextCnstrId_3653_ = crate::leanh::lean_ctor_get(v_s_3638_, 14);
                v_caseSplits_3654_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_3638_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 23) as u32,
                );
                v_conflict_x3f_3655_ = crate::leanh::lean_ctor_get(v_s_3638_, 15);
                v_diseqSplits_3656_ = crate::leanh::lean_ctor_get(v_s_3638_, 16);
                v_divMod_3657_ = crate::leanh::lean_ctor_get(v_s_3638_, 17);
                v_toIntIds_3658_ = crate::leanh::lean_ctor_get(v_s_3638_, 18);
                v_toIntInfos_3659_ = crate::leanh::lean_ctor_get(v_s_3638_, 19);
                v_toIntTermMap_3660_ = crate::leanh::lean_ctor_get(v_s_3638_, 20);
                v_toIntVarMap_3661_ = crate::leanh::lean_ctor_get(v_s_3638_, 21);
                v_usedCommRing_3662_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_3638_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 23 + 1) as u32,
                );
                v_nonlinearOccs_3663_ = crate::leanh::lean_ctor_get(v_s_3638_, 22);
                v_isSharedCheck_3671_ = (!crate::leanh::lean_is_exclusive(v_s_3638_)) as u8;
                if v_isSharedCheck_3671_ == 0 {
                    v___x_3665_ = v_s_3638_;
                    v_isShared_3666_ = v_isSharedCheck_3671_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nonlinearOccs_3663_);
                    crate::leanh::lean_inc(v_toIntVarMap_3661_);
                    crate::leanh::lean_inc(v_toIntTermMap_3660_);
                    crate::leanh::lean_inc(v_toIntInfos_3659_);
                    crate::leanh::lean_inc(v_toIntIds_3658_);
                    crate::leanh::lean_inc(v_divMod_3657_);
                    crate::leanh::lean_inc(v_diseqSplits_3656_);
                    crate::leanh::lean_inc(v_conflict_x3f_3655_);
                    crate::leanh::lean_inc(v_nextCnstrId_3653_);
                    crate::leanh::lean_inc(v_assignment_3652_);
                    crate::leanh::lean_inc(v_occurs_3651_);
                    crate::leanh::lean_inc(v_elimStack_3650_);
                    crate::leanh::lean_inc(v_elimEqs_3649_);
                    crate::leanh::lean_inc(v_diseqs_3648_);
                    crate::leanh::lean_inc(v_uppers_3647_);
                    crate::leanh::lean_inc(v_lowers_3646_);
                    crate::leanh::lean_inc(v_dvds_3645_);
                    crate::leanh::lean_inc(v_natDef_3644_);
                    crate::leanh::lean_inc(v_natToIntMap_3643_);
                    crate::leanh::lean_inc(v_varMap_x27_3642_);
                    crate::leanh::lean_inc(v_vars_x27_3641_);
                    crate::leanh::lean_inc(v_varMap_3640_);
                    crate::leanh::lean_inc(v_vars_3639_);
                    crate::leanh::lean_dec(v_s_3638_);
                    v___x_3665_ = crate::leanh::lean_box(0);
                    v_isShared_3666_ = v_isSharedCheck_3671_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3667_ = l_Lean_Meta_Grind_Arith_shrink(v_assignment_3652_, v_x_3637_);
                if v_isShared_3666_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3665_, 13, v___x_3667_);
                    v___x_3669_ = v___x_3665_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3670_ = crate::leanh::lean_alloc_ctor(0, 23, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_vars_3639_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 1, v_varMap_3640_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 2, v_vars_x27_3641_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 3, v_varMap_x27_3642_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 4, v_natToIntMap_3643_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 5, v_natDef_3644_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 6, v_dvds_3645_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 7, v_lowers_3646_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 8, v_uppers_3647_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 9, v_diseqs_3648_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 10, v_elimEqs_3649_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 11, v_elimStack_3650_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 12, v_occurs_3651_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 13, v___x_3667_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 14, v_nextCnstrId_3653_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 15, v_conflict_x3f_3655_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 16, v_diseqSplits_3656_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 17, v_divMod_3657_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 18, v_toIntIds_3658_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 19, v_toIntInfos_3659_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 20, v_toIntTermMap_3660_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 21, v_toIntVarMap_3661_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 22, v_nonlinearOccs_3663_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3670_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 23) as u32,
                        v_caseSplits_3654_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3670_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 23 + 1) as u32,
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
    mut v_x_3672_: *mut crate::leanh::LeanObject,
    mut v_s_3673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3674_ =
        l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0(v_x_3672_, v_s_3673_);
    crate::leanh::lean_dec(v_x_3672_);
    return v_res_3674_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(
    mut v_x_3675_: *mut crate::leanh::LeanObject,
    mut v_a_3676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3678_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3678_, 0, v_x_3675_);
    v___x_3679_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
    v___x_3680_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3679_, v___f_3678_, v_a_3676_);
    return v___x_3680_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg___boxed(
    mut v_x_3681_: *mut crate::leanh::LeanObject,
    mut v_a_3682_: *mut crate::leanh::LeanObject,
    mut v_a_3683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3684_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_x_3681_, v_a_3682_);
    crate::leanh::lean_dec(v_a_3682_);
    return v_res_3684_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom(
    mut v_x_3685_: *mut crate::leanh::LeanObject,
    mut v_a_3686_: *mut crate::leanh::LeanObject,
    mut v_a_3687_: *mut crate::leanh::LeanObject,
    mut v_a_3688_: *mut crate::leanh::LeanObject,
    mut v_a_3689_: *mut crate::leanh::LeanObject,
    mut v_a_3690_: *mut crate::leanh::LeanObject,
    mut v_a_3691_: *mut crate::leanh::LeanObject,
    mut v_a_3692_: *mut crate::leanh::LeanObject,
    mut v_a_3693_: *mut crate::leanh::LeanObject,
    mut v_a_3694_: *mut crate::leanh::LeanObject,
    mut v_a_3695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3697_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_x_3685_, v_a_3686_);
    return v___x_3697_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___boxed(
    mut v_x_3698_: *mut crate::leanh::LeanObject,
    mut v_a_3699_: *mut crate::leanh::LeanObject,
    mut v_a_3700_: *mut crate::leanh::LeanObject,
    mut v_a_3701_: *mut crate::leanh::LeanObject,
    mut v_a_3702_: *mut crate::leanh::LeanObject,
    mut v_a_3703_: *mut crate::leanh::LeanObject,
    mut v_a_3704_: *mut crate::leanh::LeanObject,
    mut v_a_3705_: *mut crate::leanh::LeanObject,
    mut v_a_3706_: *mut crate::leanh::LeanObject,
    mut v_a_3707_: *mut crate::leanh::LeanObject,
    mut v_a_3708_: *mut crate::leanh::LeanObject,
    mut v_a_3709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3710_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom(
        v_x_3698_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_,
        v_a_3706_, v_a_3707_, v_a_3708_,
    );
    crate::leanh::lean_dec(v_a_3708_);
    crate::leanh::lean_dec_ref(v_a_3707_);
    crate::leanh::lean_dec(v_a_3706_);
    crate::leanh::lean_dec_ref(v_a_3705_);
    crate::leanh::lean_dec(v_a_3704_);
    crate::leanh::lean_dec_ref(v_a_3703_);
    crate::leanh::lean_dec(v_a_3702_);
    crate::leanh::lean_dec_ref(v_a_3701_);
    crate::leanh::lean_dec(v_a_3700_);
    crate::leanh::lean_dec(v_a_3699_);
    return v_res_3710_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3712_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__0;
    v___x_3713_ = l_Lean_stringToMessageData(v___x_3712_);
    return v___x_3713_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3714_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_3715_ = lean_nat_to_int(v___x_3714_);
    return v___x_3715_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3717_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__3;
    v___x_3718_ = l_Lean_stringToMessageData(v___x_3717_);
    return v___x_3718_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg(
    mut v_r_3719_: *mut crate::leanh::LeanObject,
    mut v_p_3720_: *mut crate::leanh::LeanObject,
    mut v_a_3721_: *mut crate::leanh::LeanObject,
    mut v_a_3722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3727_: u8 = 0;
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: u8 = 0;
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3742_: u8 = 0;
    let mut v_k_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: u8 = 0;
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3764_: u8 = 0;
    let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3768_: u8 = 0;
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3779_: u8 = 0;
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3783_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_3720_) == 0 {
                    v_k_3724_ = crate::leanh::lean_ctor_get(v_p_3720_, 0);
                    v_isSharedCheck_3742_ = (!crate::leanh::lean_is_exclusive(v_p_3720_)) as u8;
                    if v_isSharedCheck_3742_ == 0 {
                        v___x_3726_ = v_p_3720_;
                        v_isShared_3727_ = v_isSharedCheck_3742_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_3724_);
                        crate::leanh::lean_dec(v_p_3720_);
                        v___x_3726_ = crate::leanh::lean_box(0);
                        v_isShared_3727_ = v_isSharedCheck_3742_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_3743_ = crate::leanh::lean_ctor_get(v_p_3720_, 0);
                    crate::leanh::lean_inc(v_k_3743_);
                    v_v_3744_ = crate::leanh::lean_ctor_get(v_p_3720_, 1);
                    crate::leanh::lean_inc(v_v_3744_);
                    v_p_3745_ = crate::leanh::lean_ctor_get(v_p_3720_, 2);
                    crate::leanh::lean_inc_ref(v_p_3745_);
                    crate::leanh::lean_dec_ref_known(v_p_3720_, 3);
                    v___x_3746_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2);
                    v___x_3747_ = lean_int_dec_eq(v_k_3743_, v___x_3746_);
                    if v___x_3747_ == 0 {
                        v___x_3748_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(
                            v_v_3744_, v_a_3721_, v_a_3722_,
                        );
                        crate::leanh::lean_dec(v_v_3744_);
                        if crate::leanh::lean_obj_tag(v___x_3748_) == 0 {
                            v_a_3749_ = crate::leanh::lean_ctor_get(v___x_3748_, 0);
                            crate::leanh::lean_inc(v_a_3749_);
                            crate::leanh::lean_dec_ref_known(v___x_3748_, 1);
                            v___x_3750_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1);
                            v___x_3751_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3751_, 0, v_r_3719_);
                            crate::leanh::lean_ctor_set(v___x_3751_, 1, v___x_3750_);
                            v___x_3752_ = l_Int_repr(v_k_3743_);
                            crate::leanh::lean_dec(v_k_3743_);
                            v___x_3753_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3753_, 0, v___x_3752_);
                            v___x_3754_ = l_Lean_MessageData_ofFormat(v___x_3753_);
                            v___x_3755_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3755_, 0, v___x_3751_);
                            crate::leanh::lean_ctor_set(v___x_3755_, 1, v___x_3754_);
                            v___x_3756_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4);
                            v___x_3757_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3757_, 0, v___x_3755_);
                            crate::leanh::lean_ctor_set(v___x_3757_, 1, v___x_3756_);
                            v___x_3758_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_3749_);
                            v___x_3759_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3759_, 0, v___x_3757_);
                            crate::leanh::lean_ctor_set(v___x_3759_, 1, v___x_3758_);
                            v_r_3719_ = v___x_3759_;
                            v_p_3720_ = v_p_3745_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_p_3745_);
                            crate::leanh::lean_dec(v_k_3743_);
                            crate::leanh::lean_dec_ref(v_r_3719_);
                            v_a_3761_ = crate::leanh::lean_ctor_get(v___x_3748_, 0);
                            v_isSharedCheck_3768_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3748_)) as u8;
                            if v_isSharedCheck_3768_ == 0 {
                                v___x_3763_ = v___x_3748_;
                                v_isShared_3764_ = v_isSharedCheck_3768_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3761_);
                                crate::leanh::lean_dec(v___x_3748_);
                                v___x_3763_ = crate::leanh::lean_box(0);
                                v_isShared_3764_ = v_isSharedCheck_3768_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_k_3743_);
                        v___x_3769_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(
                            v_v_3744_, v_a_3721_, v_a_3722_,
                        );
                        crate::leanh::lean_dec(v_v_3744_);
                        if crate::leanh::lean_obj_tag(v___x_3769_) == 0 {
                            v_a_3770_ = crate::leanh::lean_ctor_get(v___x_3769_, 0);
                            crate::leanh::lean_inc(v_a_3770_);
                            crate::leanh::lean_dec_ref_known(v___x_3769_, 1);
                            v___x_3771_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1);
                            v___x_3772_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3772_, 0, v_r_3719_);
                            crate::leanh::lean_ctor_set(v___x_3772_, 1, v___x_3771_);
                            v___x_3773_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_3770_);
                            v___x_3774_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3774_, 0, v___x_3772_);
                            crate::leanh::lean_ctor_set(v___x_3774_, 1, v___x_3773_);
                            v_r_3719_ = v___x_3774_;
                            v_p_3720_ = v_p_3745_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_p_3745_);
                            crate::leanh::lean_dec_ref(v_r_3719_);
                            v_a_3776_ = crate::leanh::lean_ctor_get(v___x_3769_, 0);
                            v_isSharedCheck_3783_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3769_)) as u8;
                            if v_isSharedCheck_3783_ == 0 {
                                v___x_3778_ = v___x_3769_;
                                v_isShared_3779_ = v_isSharedCheck_3783_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3776_);
                                crate::leanh::lean_dec(v___x_3769_);
                                v___x_3778_ = crate::leanh::lean_box(0);
                                v_isShared_3779_ = v_isSharedCheck_3783_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3728_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Int_Linear_Poly_isZero___closed__0),
                    core::ptr::addr_of_mut!(l_Int_Linear_Poly_isZero___closed__0_once),
                    _init_l_Int_Linear_Poly_isZero___closed__0,
                );
                v___x_3729_ = lean_int_dec_eq(v_k_3724_, v___x_3728_);
                if v___x_3729_ == 0 {
                    v___x_3730_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__1);
                    v___x_3731_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3731_, 0, v_r_3719_);
                    crate::leanh::lean_ctor_set(v___x_3731_, 1, v___x_3730_);
                    v___x_3732_ = l_Int_repr(v_k_3724_);
                    crate::leanh::lean_dec(v_k_3724_);
                    if v_isShared_3727_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3726_, 3);
                        crate::leanh::lean_ctor_set(v___x_3726_, 0, v___x_3732_);
                        v___x_3734_ = v___x_3726_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3738_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 0, v___x_3732_);
                        v___x_3734_ = v_reuseFailAlloc_3738_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_3724_);
                    if v_isShared_3727_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3726_, 0, v_r_3719_);
                        v___x_3740_ = v___x_3726_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3741_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_r_3719_);
                        v___x_3740_ = v_reuseFailAlloc_3741_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3735_ = l_Lean_MessageData_ofFormat(v___x_3734_);
                v___x_3736_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3736_, 0, v___x_3731_);
                crate::leanh::lean_ctor_set(v___x_3736_, 1, v___x_3735_);
                v___x_3737_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3737_, 0, v___x_3736_);
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
                    v_reuseFailAlloc_3767_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_a_3761_);
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
                    v_reuseFailAlloc_3782_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_a_3776_);
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
    mut v_r_3784_: *mut crate::leanh::LeanObject,
    mut v_p_3785_: *mut crate::leanh::LeanObject,
    mut v_a_3786_: *mut crate::leanh::LeanObject,
    mut v_a_3787_: *mut crate::leanh::LeanObject,
    mut v_a_3788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3789_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg(
            v_r_3784_, v_p_3785_, v_a_3786_, v_a_3787_,
        );
    crate::leanh::lean_dec_ref(v_a_3787_);
    crate::leanh::lean_dec(v_a_3786_);
    return v_res_3789_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go(
    mut v_r_3790_: *mut crate::leanh::LeanObject,
    mut v_p_3791_: *mut crate::leanh::LeanObject,
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
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3803_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg(
            v_r_3790_, v_p_3791_, v_a_3792_, v_a_3800_,
        );
    return v___x_3803_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___boxed(
    mut v_r_3804_: *mut crate::leanh::LeanObject,
    mut v_p_3805_: *mut crate::leanh::LeanObject,
    mut v_a_3806_: *mut crate::leanh::LeanObject,
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
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3817_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go(
        v_r_3804_, v_p_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_,
        v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_,
    );
    crate::leanh::lean_dec(v_a_3815_);
    crate::leanh::lean_dec_ref(v_a_3814_);
    crate::leanh::lean_dec(v_a_3813_);
    crate::leanh::lean_dec_ref(v_a_3812_);
    crate::leanh::lean_dec(v_a_3811_);
    crate::leanh::lean_dec_ref(v_a_3810_);
    crate::leanh::lean_dec(v_a_3809_);
    crate::leanh::lean_dec_ref(v_a_3808_);
    crate::leanh::lean_dec(v_a_3807_);
    crate::leanh::lean_dec(v_a_3806_);
    return v_res_3817_;
}
pub unsafe fn l_Int_Linear_Poly_pp___redArg(
    mut v_p_3818_: *mut crate::leanh::LeanObject,
    mut v_a_3819_: *mut crate::leanh::LeanObject,
    mut v_a_3820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3825_: u8 = 0;
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3832_: u8 = 0;
    let mut v_k_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: u8 = 0;
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3851_: u8 = 0;
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3855_: u8 = 0;
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3863_: u8 = 0;
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3867_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_3818_) == 0 {
                    v_k_3822_ = crate::leanh::lean_ctor_get(v_p_3818_, 0);
                    v_isSharedCheck_3832_ = (!crate::leanh::lean_is_exclusive(v_p_3818_)) as u8;
                    if v_isSharedCheck_3832_ == 0 {
                        v___x_3824_ = v_p_3818_;
                        v_isShared_3825_ = v_isSharedCheck_3832_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_3822_);
                        crate::leanh::lean_dec(v_p_3818_);
                        v___x_3824_ = crate::leanh::lean_box(0);
                        v_isShared_3825_ = v_isSharedCheck_3832_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_3833_ = crate::leanh::lean_ctor_get(v_p_3818_, 0);
                    crate::leanh::lean_inc(v_k_3833_);
                    v_v_3834_ = crate::leanh::lean_ctor_get(v_p_3818_, 1);
                    crate::leanh::lean_inc(v_v_3834_);
                    v_p_3835_ = crate::leanh::lean_ctor_get(v_p_3818_, 2);
                    crate::leanh::lean_inc_ref(v_p_3835_);
                    crate::leanh::lean_dec_ref_known(v_p_3818_, 3);
                    v___x_3836_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2);
                    v___x_3837_ = lean_int_dec_eq(v_k_3833_, v___x_3836_);
                    if v___x_3837_ == 0 {
                        v___x_3838_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(
                            v_v_3834_, v_a_3819_, v_a_3820_,
                        );
                        crate::leanh::lean_dec(v_v_3834_);
                        if crate::leanh::lean_obj_tag(v___x_3838_) == 0 {
                            v_a_3839_ = crate::leanh::lean_ctor_get(v___x_3838_, 0);
                            crate::leanh::lean_inc(v_a_3839_);
                            crate::leanh::lean_dec_ref_known(v___x_3838_, 1);
                            v___x_3840_ = l_Int_repr(v_k_3833_);
                            crate::leanh::lean_dec(v_k_3833_);
                            v___x_3841_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3841_, 0, v___x_3840_);
                            v___x_3842_ = l_Lean_MessageData_ofFormat(v___x_3841_);
                            v___x_3843_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__4);
                            v___x_3844_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3844_, 0, v___x_3842_);
                            crate::leanh::lean_ctor_set(v___x_3844_, 1, v___x_3843_);
                            v___x_3845_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_3839_);
                            v___x_3846_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3846_, 0, v___x_3844_);
                            crate::leanh::lean_ctor_set(v___x_3846_, 1, v___x_3845_);
                            v___x_3847_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg(v___x_3846_, v_p_3835_, v_a_3819_, v_a_3820_);
                            return v___x_3847_;
                        } else {
                            crate::leanh::lean_dec_ref(v_p_3835_);
                            crate::leanh::lean_dec(v_k_3833_);
                            v_a_3848_ = crate::leanh::lean_ctor_get(v___x_3838_, 0);
                            v_isSharedCheck_3855_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3838_)) as u8;
                            if v_isSharedCheck_3855_ == 0 {
                                v___x_3850_ = v___x_3838_;
                                v_isShared_3851_ = v_isSharedCheck_3855_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3848_);
                                crate::leanh::lean_dec(v___x_3838_);
                                v___x_3850_ = crate::leanh::lean_box(0);
                                v_isShared_3851_ = v_isSharedCheck_3855_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_k_3833_);
                        v___x_3856_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(
                            v_v_3834_, v_a_3819_, v_a_3820_,
                        );
                        crate::leanh::lean_dec(v_v_3834_);
                        if crate::leanh::lean_obj_tag(v___x_3856_) == 0 {
                            v_a_3857_ = crate::leanh::lean_ctor_get(v___x_3856_, 0);
                            crate::leanh::lean_inc(v_a_3857_);
                            crate::leanh::lean_dec_ref_known(v___x_3856_, 1);
                            v___x_3858_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_a_3857_);
                            v___x_3859_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg(v___x_3858_, v_p_3835_, v_a_3819_, v_a_3820_);
                            return v___x_3859_;
                        } else {
                            crate::leanh::lean_dec_ref(v_p_3835_);
                            v_a_3860_ = crate::leanh::lean_ctor_get(v___x_3856_, 0);
                            v_isSharedCheck_3867_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3856_)) as u8;
                            if v_isSharedCheck_3867_ == 0 {
                                v___x_3862_ = v___x_3856_;
                                v_isShared_3863_ = v_isSharedCheck_3867_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3860_);
                                crate::leanh::lean_dec(v___x_3856_);
                                v___x_3862_ = crate::leanh::lean_box(0);
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
                crate::leanh::lean_dec(v_k_3822_);
                if v_isShared_3825_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3824_, 3);
                    crate::leanh::lean_ctor_set(v___x_3824_, 0, v___x_3826_);
                    v___x_3828_ = v___x_3824_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3831_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3826_);
                    v___x_3828_ = v_reuseFailAlloc_3831_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3829_ = l_Lean_MessageData_ofFormat(v___x_3828_);
                v___x_3830_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3830_, 0, v___x_3829_);
                return v___x_3830_;
            }
            3 => {
                if v_isShared_3851_ == 0 {
                    v___x_3853_ = v___x_3850_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3854_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_a_3848_);
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
                    v_reuseFailAlloc_3866_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
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
    mut v_p_3868_: *mut crate::leanh::LeanObject,
    mut v_a_3869_: *mut crate::leanh::LeanObject,
    mut v_a_3870_: *mut crate::leanh::LeanObject,
    mut v_a_3871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3872_ = l_Int_Linear_Poly_pp___redArg(v_p_3868_, v_a_3869_, v_a_3870_);
    crate::leanh::lean_dec_ref(v_a_3870_);
    crate::leanh::lean_dec(v_a_3869_);
    return v_res_3872_;
}
pub unsafe fn l_Int_Linear_Poly_pp(
    mut v_p_3873_: *mut crate::leanh::LeanObject,
    mut v_a_3874_: *mut crate::leanh::LeanObject,
    mut v_a_3875_: *mut crate::leanh::LeanObject,
    mut v_a_3876_: *mut crate::leanh::LeanObject,
    mut v_a_3877_: *mut crate::leanh::LeanObject,
    mut v_a_3878_: *mut crate::leanh::LeanObject,
    mut v_a_3879_: *mut crate::leanh::LeanObject,
    mut v_a_3880_: *mut crate::leanh::LeanObject,
    mut v_a_3881_: *mut crate::leanh::LeanObject,
    mut v_a_3882_: *mut crate::leanh::LeanObject,
    mut v_a_3883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3885_ = l_Int_Linear_Poly_pp___redArg(v_p_3873_, v_a_3874_, v_a_3882_);
    return v___x_3885_;
}
pub unsafe fn l_Int_Linear_Poly_pp___boxed(
    mut v_p_3886_: *mut crate::leanh::LeanObject,
    mut v_a_3887_: *mut crate::leanh::LeanObject,
    mut v_a_3888_: *mut crate::leanh::LeanObject,
    mut v_a_3889_: *mut crate::leanh::LeanObject,
    mut v_a_3890_: *mut crate::leanh::LeanObject,
    mut v_a_3891_: *mut crate::leanh::LeanObject,
    mut v_a_3892_: *mut crate::leanh::LeanObject,
    mut v_a_3893_: *mut crate::leanh::LeanObject,
    mut v_a_3894_: *mut crate::leanh::LeanObject,
    mut v_a_3895_: *mut crate::leanh::LeanObject,
    mut v_a_3896_: *mut crate::leanh::LeanObject,
    mut v_a_3897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3898_ = l_Int_Linear_Poly_pp(
        v_p_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_,
        v_a_3894_, v_a_3895_, v_a_3896_,
    );
    crate::leanh::lean_dec(v_a_3896_);
    crate::leanh::lean_dec_ref(v_a_3895_);
    crate::leanh::lean_dec(v_a_3894_);
    crate::leanh::lean_dec_ref(v_a_3893_);
    crate::leanh::lean_dec(v_a_3892_);
    crate::leanh::lean_dec_ref(v_a_3891_);
    crate::leanh::lean_dec(v_a_3890_);
    crate::leanh::lean_dec_ref(v_a_3889_);
    crate::leanh::lean_dec(v_a_3888_);
    crate::leanh::lean_dec(v_a_3887_);
    return v_res_3898_;
}
pub unsafe fn l_Int_Linear_Poly_denoteExpr_x27___redArg___lam__0(
    mut v_a_3899_: *mut crate::leanh::LeanObject,
    mut v___x_3900_: *mut crate::leanh::LeanObject,
    mut v_x_3901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: u8 = 0;
    v_size_3902_ = crate::leanh::lean_ctor_get(v_a_3899_, 2);
    v___x_3903_ = lean_nat_dec_lt(v_x_3901_, v_size_3902_);
    if v___x_3903_ == 0 {
        let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3904_ = l_outOfBounds___redArg(v___x_3900_);
        return v___x_3904_;
    } else {
        let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3905_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3900_, v_a_3899_, v_x_3901_);
        return v___x_3905_;
    }
}
pub unsafe fn l_Int_Linear_Poly_denoteExpr_x27___redArg___lam__0___boxed(
    mut v_a_3906_: *mut crate::leanh::LeanObject,
    mut v___x_3907_: *mut crate::leanh::LeanObject,
    mut v_x_3908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3909_ =
        l_Int_Linear_Poly_denoteExpr_x27___redArg___lam__0(v_a_3906_, v___x_3907_, v_x_3908_);
    crate::leanh::lean_dec(v_x_3908_);
    crate::leanh::lean_dec_ref(v___x_3907_);
    crate::leanh::lean_dec_ref(v_a_3906_);
    return v_res_3909_;
}
pub unsafe fn l_Int_Linear_Poly_denoteExpr_x27___redArg(
    mut v_p_3910_: *mut crate::leanh::LeanObject,
    mut v_a_3911_: *mut crate::leanh::LeanObject,
    mut v_a_3912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3922_: u8 = 0;
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3926_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3914_ = l_Lean_Meta_Grind_Arith_Cutsat_getVars___redArg(v_a_3911_, v_a_3912_);
                if crate::leanh::lean_obj_tag(v___x_3914_) == 0 {
                    v_a_3915_ = crate::leanh::lean_ctor_get(v___x_3914_, 0);
                    crate::leanh::lean_inc(v_a_3915_);
                    crate::leanh::lean_dec_ref_known(v___x_3914_, 1);
                    v___x_3916_ = l_Lean_instInhabitedExpr;
                    v___f_3917_ = crate::leanh::lean_alloc_closure(
                        l_Int_Linear_Poly_denoteExpr_x27___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_3917_, 0, v_a_3915_);
                    crate::leanh::lean_closure_set(v___f_3917_, 1, v___x_3916_);
                    v___x_3918_ = l_Int_Linear_Poly_denoteExpr___redArg(v___f_3917_, v_p_3910_);
                    return v___x_3918_;
                } else {
                    crate::leanh::lean_dec_ref(v_p_3910_);
                    v_a_3919_ = crate::leanh::lean_ctor_get(v___x_3914_, 0);
                    v_isSharedCheck_3926_ = (!crate::leanh::lean_is_exclusive(v___x_3914_)) as u8;
                    if v_isSharedCheck_3926_ == 0 {
                        v___x_3921_ = v___x_3914_;
                        v_isShared_3922_ = v_isSharedCheck_3926_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3919_);
                        crate::leanh::lean_dec(v___x_3914_);
                        v___x_3921_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_3925_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_a_3919_);
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
    mut v_p_3927_: *mut crate::leanh::LeanObject,
    mut v_a_3928_: *mut crate::leanh::LeanObject,
    mut v_a_3929_: *mut crate::leanh::LeanObject,
    mut v_a_3930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3931_ = l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_3927_, v_a_3928_, v_a_3929_);
    crate::leanh::lean_dec_ref(v_a_3929_);
    crate::leanh::lean_dec(v_a_3928_);
    return v_res_3931_;
}
pub unsafe fn l_Int_Linear_Poly_denoteExpr_x27(
    mut v_p_3932_: *mut crate::leanh::LeanObject,
    mut v_a_3933_: *mut crate::leanh::LeanObject,
    mut v_a_3934_: *mut crate::leanh::LeanObject,
    mut v_a_3935_: *mut crate::leanh::LeanObject,
    mut v_a_3936_: *mut crate::leanh::LeanObject,
    mut v_a_3937_: *mut crate::leanh::LeanObject,
    mut v_a_3938_: *mut crate::leanh::LeanObject,
    mut v_a_3939_: *mut crate::leanh::LeanObject,
    mut v_a_3940_: *mut crate::leanh::LeanObject,
    mut v_a_3941_: *mut crate::leanh::LeanObject,
    mut v_a_3942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3944_ = l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_3932_, v_a_3933_, v_a_3941_);
    return v___x_3944_;
}
pub unsafe fn l_Int_Linear_Poly_denoteExpr_x27___boxed(
    mut v_p_3945_: *mut crate::leanh::LeanObject,
    mut v_a_3946_: *mut crate::leanh::LeanObject,
    mut v_a_3947_: *mut crate::leanh::LeanObject,
    mut v_a_3948_: *mut crate::leanh::LeanObject,
    mut v_a_3949_: *mut crate::leanh::LeanObject,
    mut v_a_3950_: *mut crate::leanh::LeanObject,
    mut v_a_3951_: *mut crate::leanh::LeanObject,
    mut v_a_3952_: *mut crate::leanh::LeanObject,
    mut v_a_3953_: *mut crate::leanh::LeanObject,
    mut v_a_3954_: *mut crate::leanh::LeanObject,
    mut v_a_3955_: *mut crate::leanh::LeanObject,
    mut v_a_3956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3957_ = l_Int_Linear_Poly_denoteExpr_x27(
        v_p_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_,
        v_a_3953_, v_a_3954_, v_a_3955_,
    );
    crate::leanh::lean_dec(v_a_3955_);
    crate::leanh::lean_dec_ref(v_a_3954_);
    crate::leanh::lean_dec(v_a_3953_);
    crate::leanh::lean_dec_ref(v_a_3952_);
    crate::leanh::lean_dec(v_a_3951_);
    crate::leanh::lean_dec_ref(v_a_3950_);
    crate::leanh::lean_dec(v_a_3949_);
    crate::leanh::lean_dec_ref(v_a_3948_);
    crate::leanh::lean_dec(v_a_3947_);
    crate::leanh::lean_dec(v_a_3946_);
    return v_res_3957_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(
    mut v_c_3958_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_p_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_p_3959_ = crate::leanh::lean_ctor_get(v_c_3958_, 1);
    if crate::leanh::lean_obj_tag(v_p_3959_) == 0 {
        let mut v_d_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3964_: u8 = 0;
        v_d_3960_ = crate::leanh::lean_ctor_get(v_c_3958_, 0);
        v_k_3961_ = crate::leanh::lean_ctor_get(v_p_3959_, 0);
        v___x_3962_ = lean_int_emod(v_k_3961_, v_d_3960_);
        v___x_3963_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_Linear_Poly_isZero___closed__0),
            core::ptr::addr_of_mut!(l_Int_Linear_Poly_isZero___closed__0_once),
            _init_l_Int_Linear_Poly_isZero___closed__0,
        );
        v___x_3964_ = lean_int_dec_eq(v___x_3962_, v___x_3963_);
        crate::leanh::lean_dec(v___x_3962_);
        return v___x_3964_;
    } else {
        let mut v_d_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3967_: u8 = 0;
        v_d_3965_ = crate::leanh::lean_ctor_get(v_c_3958_, 0);
        v___x_3966_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_pp_go___redArg___closed__2);
        v___x_3967_ = lean_int_dec_eq(v_d_3965_, v___x_3966_);
        return v___x_3967_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial___boxed(
    mut v_c_3968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3969_: u8 = 0;
    let mut v_r_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3969_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v_c_3968_);
    crate::leanh::lean_dec_ref(v_c_3968_);
    v_r_3970_ = crate::leanh::lean_box((v_res_3969_) as usize);
    return v_r_3970_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3972_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__0;
    v___x_3973_ = l_Lean_stringToMessageData(v___x_3972_);
    return v___x_3973_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(
    mut v_c_3974_: *mut crate::leanh::LeanObject,
    mut v_a_3975_: *mut crate::leanh::LeanObject,
    mut v_a_3976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_d_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3984_: u8 = 0;
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3994_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_d_3978_ = crate::leanh::lean_ctor_get(v_c_3974_, 0);
                crate::leanh::lean_inc(v_d_3978_);
                v_p_3979_ = crate::leanh::lean_ctor_get(v_c_3974_, 1);
                crate::leanh::lean_inc_ref(v_p_3979_);
                crate::leanh::lean_dec_ref(v_c_3974_);
                v___x_3980_ = l_Int_Linear_Poly_pp___redArg(v_p_3979_, v_a_3975_, v_a_3976_);
                if crate::leanh::lean_obj_tag(v___x_3980_) == 0 {
                    v_a_3981_ = crate::leanh::lean_ctor_get(v___x_3980_, 0);
                    v_isSharedCheck_3994_ = (!crate::leanh::lean_is_exclusive(v___x_3980_)) as u8;
                    if v_isSharedCheck_3994_ == 0 {
                        v___x_3983_ = v___x_3980_;
                        v_isShared_3984_ = v_isSharedCheck_3994_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3981_);
                        crate::leanh::lean_dec(v___x_3980_);
                        v___x_3983_ = crate::leanh::lean_box(0);
                        v_isShared_3984_ = v_isSharedCheck_3994_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_d_3978_);
                    return v___x_3980_;
                }
            }
            1 => {
                v___x_3985_ = l_Int_repr(v_d_3978_);
                crate::leanh::lean_dec(v_d_3978_);
                v___x_3986_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3986_, 0, v___x_3985_);
                v___x_3987_ = l_Lean_MessageData_ofFormat(v___x_3986_);
                v___x_3988_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg___closed__1,
                );
                v___x_3989_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3989_, 0, v___x_3987_);
                crate::leanh::lean_ctor_set(v___x_3989_, 1, v___x_3988_);
                v___x_3990_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3990_, 0, v___x_3989_);
                crate::leanh::lean_ctor_set(v___x_3990_, 1, v_a_3981_);
                if v_isShared_3984_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3983_, 0, v___x_3990_);
                    v___x_3992_ = v___x_3983_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3993_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3993_, 0, v___x_3990_);
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
    mut v_c_3995_: *mut crate::leanh::LeanObject,
    mut v_a_3996_: *mut crate::leanh::LeanObject,
    mut v_a_3997_: *mut crate::leanh::LeanObject,
    mut v_a_3998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3999_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_3995_, v_a_3996_, v_a_3997_);
    crate::leanh::lean_dec_ref(v_a_3997_);
    crate::leanh::lean_dec(v_a_3996_);
    return v_res_3999_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(
    mut v_c_4000_: *mut crate::leanh::LeanObject,
    mut v_a_4001_: *mut crate::leanh::LeanObject,
    mut v_a_4002_: *mut crate::leanh::LeanObject,
    mut v_a_4003_: *mut crate::leanh::LeanObject,
    mut v_a_4004_: *mut crate::leanh::LeanObject,
    mut v_a_4005_: *mut crate::leanh::LeanObject,
    mut v_a_4006_: *mut crate::leanh::LeanObject,
    mut v_a_4007_: *mut crate::leanh::LeanObject,
    mut v_a_4008_: *mut crate::leanh::LeanObject,
    mut v_a_4009_: *mut crate::leanh::LeanObject,
    mut v_a_4010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4012_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_4000_, v_a_4001_, v_a_4009_);
    return v___x_4012_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___boxed(
    mut v_c_4013_: *mut crate::leanh::LeanObject,
    mut v_a_4014_: *mut crate::leanh::LeanObject,
    mut v_a_4015_: *mut crate::leanh::LeanObject,
    mut v_a_4016_: *mut crate::leanh::LeanObject,
    mut v_a_4017_: *mut crate::leanh::LeanObject,
    mut v_a_4018_: *mut crate::leanh::LeanObject,
    mut v_a_4019_: *mut crate::leanh::LeanObject,
    mut v_a_4020_: *mut crate::leanh::LeanObject,
    mut v_a_4021_: *mut crate::leanh::LeanObject,
    mut v_a_4022_: *mut crate::leanh::LeanObject,
    mut v_a_4023_: *mut crate::leanh::LeanObject,
    mut v_a_4024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4025_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp(
        v_c_4013_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_,
        v_a_4021_, v_a_4022_, v_a_4023_,
    );
    crate::leanh::lean_dec(v_a_4023_);
    crate::leanh::lean_dec_ref(v_a_4022_);
    crate::leanh::lean_dec(v_a_4021_);
    crate::leanh::lean_dec_ref(v_a_4020_);
    crate::leanh::lean_dec(v_a_4019_);
    crate::leanh::lean_dec_ref(v_a_4018_);
    crate::leanh::lean_dec(v_a_4017_);
    crate::leanh::lean_dec_ref(v_a_4016_);
    crate::leanh::lean_dec(v_a_4015_);
    crate::leanh::lean_dec(v_a_4014_);
    return v_res_4025_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4031_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4032_ = l_Lean_Level_ofNat(v___x_4031_);
    return v___x_4032_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4033_ = crate::leanh::lean_box(0);
    v___x_4034_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__3,
    );
    v___x_4035_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4035_, 0, v___x_4034_);
    crate::leanh::lean_ctor_set(v___x_4035_, 1, v___x_4033_);
    return v___x_4035_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4036_ = crate::leanh::lean_obj_once(
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4042_ = crate::leanh::lean_box(0);
    v___x_4043_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__7;
    v___x_4044_ = l_Lean_Expr_const___override(v___x_4043_, v___x_4042_);
    return v___x_4044_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4049_ = crate::leanh::lean_box(0);
    v___x_4050_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__10;
    v___x_4051_ = l_Lean_Expr_const___override(v___x_4050_, v___x_4049_);
    return v___x_4051_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(
    mut v_c_4052_: *mut crate::leanh::LeanObject,
    mut v_a_4053_: *mut crate::leanh::LeanObject,
    mut v_a_4054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_d_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4062_: u8 = 0;
    let mut v___y_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: u8 = 0;
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4080_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_d_4056_ = crate::leanh::lean_ctor_get(v_c_4052_, 0);
                crate::leanh::lean_inc(v_d_4056_);
                v_p_4057_ = crate::leanh::lean_ctor_get(v_c_4052_, 1);
                crate::leanh::lean_inc_ref(v_p_4057_);
                crate::leanh::lean_dec_ref(v_c_4052_);
                v___x_4058_ =
                    l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_4057_, v_a_4053_, v_a_4054_);
                if crate::leanh::lean_obj_tag(v___x_4058_) == 0 {
                    v_a_4059_ = crate::leanh::lean_ctor_get(v___x_4058_, 0);
                    v_isSharedCheck_4080_ = (!crate::leanh::lean_is_exclusive(v___x_4058_)) as u8;
                    if v_isSharedCheck_4080_ == 0 {
                        v___x_4061_ = v___x_4058_;
                        v_isShared_4062_ = v_isSharedCheck_4080_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4059_);
                        crate::leanh::lean_dec(v___x_4058_);
                        v___x_4061_ = crate::leanh::lean_box(0);
                        v_isShared_4062_ = v_isSharedCheck_4080_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_d_4056_);
                    return v___x_4058_;
                }
            }
            1 => {
                v___x_4069_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Int_Linear_Poly_isZero___closed__0),
                    core::ptr::addr_of_mut!(l_Int_Linear_Poly_isZero___closed__0_once),
                    _init_l_Int_Linear_Poly_isZero___closed__0,
                );
                v___x_4070_ = lean_int_dec_le(v___x_4069_, v_d_4056_);
                if v___x_4070_ == 0 {
                    v___x_4071_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__5);
                    v___x_4072_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__8);
                    v___x_4073_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg___closed__11);
                    v___x_4074_ = lean_int_neg(v_d_4056_);
                    crate::leanh::lean_dec(v_d_4056_);
                    v___x_4075_ = l_Int_toNat(v___x_4074_);
                    crate::leanh::lean_dec(v___x_4074_);
                    v___x_4076_ = l_Lean_instToExprInt_mkNat(v___x_4075_);
                    v___x_4077_ = l_Lean_mkApp3(v___x_4071_, v___x_4072_, v___x_4073_, v___x_4076_);
                    v___y_4064_ = v___x_4077_;
                    state = 2;
                    continue;
                } else {
                    v___x_4078_ = l_Int_toNat(v_d_4056_);
                    crate::leanh::lean_dec(v_d_4056_);
                    v___x_4079_ = l_Lean_instToExprInt_mkNat(v___x_4078_);
                    v___y_4064_ = v___x_4079_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4065_ = l_Lean_mkIntDvd(v___y_4064_, v_a_4059_);
                if v_isShared_4062_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4061_, 0, v___x_4065_);
                    v___x_4067_ = v___x_4061_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4068_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4068_, 0, v___x_4065_);
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
    mut v_c_4081_: *mut crate::leanh::LeanObject,
    mut v_a_4082_: *mut crate::leanh::LeanObject,
    mut v_a_4083_: *mut crate::leanh::LeanObject,
    mut v_a_4084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4085_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(
        v_c_4081_, v_a_4082_, v_a_4083_,
    );
    crate::leanh::lean_dec_ref(v_a_4083_);
    crate::leanh::lean_dec(v_a_4082_);
    return v_res_4085_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr(
    mut v_c_4086_: *mut crate::leanh::LeanObject,
    mut v_a_4087_: *mut crate::leanh::LeanObject,
    mut v_a_4088_: *mut crate::leanh::LeanObject,
    mut v_a_4089_: *mut crate::leanh::LeanObject,
    mut v_a_4090_: *mut crate::leanh::LeanObject,
    mut v_a_4091_: *mut crate::leanh::LeanObject,
    mut v_a_4092_: *mut crate::leanh::LeanObject,
    mut v_a_4093_: *mut crate::leanh::LeanObject,
    mut v_a_4094_: *mut crate::leanh::LeanObject,
    mut v_a_4095_: *mut crate::leanh::LeanObject,
    mut v_a_4096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4098_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___redArg(
        v_c_4086_, v_a_4087_, v_a_4095_,
    );
    return v___x_4098_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr___boxed(
    mut v_c_4099_: *mut crate::leanh::LeanObject,
    mut v_a_4100_: *mut crate::leanh::LeanObject,
    mut v_a_4101_: *mut crate::leanh::LeanObject,
    mut v_a_4102_: *mut crate::leanh::LeanObject,
    mut v_a_4103_: *mut crate::leanh::LeanObject,
    mut v_a_4104_: *mut crate::leanh::LeanObject,
    mut v_a_4105_: *mut crate::leanh::LeanObject,
    mut v_a_4106_: *mut crate::leanh::LeanObject,
    mut v_a_4107_: *mut crate::leanh::LeanObject,
    mut v_a_4108_: *mut crate::leanh::LeanObject,
    mut v_a_4109_: *mut crate::leanh::LeanObject,
    mut v_a_4110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4111_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_denoteExpr(
        v_c_4099_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_,
        v_a_4107_, v_a_4108_, v_a_4109_,
    );
    crate::leanh::lean_dec(v_a_4109_);
    crate::leanh::lean_dec_ref(v_a_4108_);
    crate::leanh::lean_dec(v_a_4107_);
    crate::leanh::lean_dec_ref(v_a_4106_);
    crate::leanh::lean_dec(v_a_4105_);
    crate::leanh::lean_dec_ref(v_a_4104_);
    crate::leanh::lean_dec(v_a_4103_);
    crate::leanh::lean_dec_ref(v_a_4102_);
    crate::leanh::lean_dec(v_a_4101_);
    crate::leanh::lean_dec(v_a_4100_);
    return v_res_4111_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(
    mut v_msgData_4112_: *mut crate::leanh::LeanObject,
    mut v___y_4113_: *mut crate::leanh::LeanObject,
    mut v___y_4114_: *mut crate::leanh::LeanObject,
    mut v___y_4115_: *mut crate::leanh::LeanObject,
    mut v___y_4116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4118_ = lean_st_ref_get(v___y_4116_);
    v_env_4119_ = crate::leanh::lean_ctor_get(v___x_4118_, 0);
    crate::leanh::lean_inc_ref(v_env_4119_);
    crate::leanh::lean_dec(v___x_4118_);
    v___x_4120_ = lean_st_ref_get(v___y_4114_);
    v_mctx_4121_ = crate::leanh::lean_ctor_get(v___x_4120_, 0);
    crate::leanh::lean_inc_ref(v_mctx_4121_);
    crate::leanh::lean_dec(v___x_4120_);
    v_lctx_4122_ = crate::leanh::lean_ctor_get(v___y_4113_, 2);
    v_options_4123_ = crate::leanh::lean_ctor_get(v___y_4115_, 2);
    crate::leanh::lean_inc_ref(v_options_4123_);
    crate::leanh::lean_inc_ref(v_lctx_4122_);
    v___x_4124_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4124_, 0, v_env_4119_);
    crate::leanh::lean_ctor_set(v___x_4124_, 1, v_mctx_4121_);
    crate::leanh::lean_ctor_set(v___x_4124_, 2, v_lctx_4122_);
    crate::leanh::lean_ctor_set(v___x_4124_, 3, v_options_4123_);
    v___x_4125_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4125_, 0, v___x_4124_);
    crate::leanh::lean_ctor_set(v___x_4125_, 1, v_msgData_4112_);
    v___x_4126_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4126_, 0, v___x_4125_);
    return v___x_4126_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0___boxed(
    mut v_msgData_4127_: *mut crate::leanh::LeanObject,
    mut v___y_4128_: *mut crate::leanh::LeanObject,
    mut v___y_4129_: *mut crate::leanh::LeanObject,
    mut v___y_4130_: *mut crate::leanh::LeanObject,
    mut v___y_4131_: *mut crate::leanh::LeanObject,
    mut v___y_4132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4133_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(v_msgData_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
    crate::leanh::lean_dec(v___y_4131_);
    crate::leanh::lean_dec_ref(v___y_4130_);
    crate::leanh::lean_dec(v___y_4129_);
    crate::leanh::lean_dec_ref(v___y_4128_);
    return v_res_4133_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(
    mut v_msg_4134_: *mut crate::leanh::LeanObject,
    mut v___y_4135_: *mut crate::leanh::LeanObject,
    mut v___y_4136_: *mut crate::leanh::LeanObject,
    mut v___y_4137_: *mut crate::leanh::LeanObject,
    mut v___y_4138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4145_: u8 = 0;
    let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4150_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4140_ = crate::leanh::lean_ctor_get(v___y_4137_, 5);
                v___x_4141_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0_spec__0(v_msg_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
                v_a_4142_ = crate::leanh::lean_ctor_get(v___x_4141_, 0);
                v_isSharedCheck_4150_ = (!crate::leanh::lean_is_exclusive(v___x_4141_)) as u8;
                if v_isSharedCheck_4150_ == 0 {
                    v___x_4144_ = v___x_4141_;
                    v_isShared_4145_ = v_isSharedCheck_4150_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4142_);
                    crate::leanh::lean_dec(v___x_4141_);
                    v___x_4144_ = crate::leanh::lean_box(0);
                    v_isShared_4145_ = v_isSharedCheck_4150_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_4140_);
                v___x_4146_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4146_, 0, v_ref_4140_);
                crate::leanh::lean_ctor_set(v___x_4146_, 1, v_a_4142_);
                if v_isShared_4145_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4144_, 1);
                    crate::leanh::lean_ctor_set(v___x_4144_, 0, v___x_4146_);
                    v___x_4148_ = v___x_4144_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4149_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4149_, 0, v___x_4146_);
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
    mut v_msg_4151_: *mut crate::leanh::LeanObject,
    mut v___y_4152_: *mut crate::leanh::LeanObject,
    mut v___y_4153_: *mut crate::leanh::LeanObject,
    mut v___y_4154_: *mut crate::leanh::LeanObject,
    mut v___y_4155_: *mut crate::leanh::LeanObject,
    mut v___y_4156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4157_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v_msg_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_);
    crate::leanh::lean_dec(v___y_4155_);
    crate::leanh::lean_dec_ref(v___y_4154_);
    crate::leanh::lean_dec(v___y_4153_);
    crate::leanh::lean_dec_ref(v___y_4152_);
    return v_res_4157_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4159_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__0;
    v___x_4160_ = l_Lean_stringToMessageData(v___x_4159_);
    return v___x_4160_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4162_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__2;
    v___x_4163_ = l_Lean_stringToMessageData(v___x_4162_);
    return v___x_4163_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(
    mut v_c_4164_: *mut crate::leanh::LeanObject,
    mut v_a_4165_: *mut crate::leanh::LeanObject,
    mut v_a_4166_: *mut crate::leanh::LeanObject,
    mut v_a_4167_: *mut crate::leanh::LeanObject,
    mut v_a_4168_: *mut crate::leanh::LeanObject,
    mut v_a_4169_: *mut crate::leanh::LeanObject,
    mut v_a_4170_: *mut crate::leanh::LeanObject,
    mut v_a_4171_: *mut crate::leanh::LeanObject,
    mut v_a_4172_: *mut crate::leanh::LeanObject,
    mut v_a_4173_: *mut crate::leanh::LeanObject,
    mut v_a_4174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4187_: u8 = 0;
    let mut v___x_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4191_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4176_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(
                    v_c_4164_, v_a_4165_, v_a_4173_,
                );
                if crate::leanh::lean_obj_tag(v___x_4176_) == 0 {
                    v_a_4177_ = crate::leanh::lean_ctor_get(v___x_4176_, 0);
                    crate::leanh::lean_inc(v_a_4177_);
                    crate::leanh::lean_dec_ref_known(v___x_4176_, 1);
                    v___x_4178_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
                    v___x_4179_ = l_Lean_indentD(v_a_4177_);
                    v___x_4180_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4180_, 0, v___x_4178_);
                    crate::leanh::lean_ctor_set(v___x_4180_, 1, v___x_4179_);
                    v___x_4181_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__3);
                    v___x_4182_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4182_, 0, v___x_4180_);
                    crate::leanh::lean_ctor_set(v___x_4182_, 1, v___x_4181_);
                    v___x_4183_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_4182_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_);
                    return v___x_4183_;
                } else {
                    v_a_4184_ = crate::leanh::lean_ctor_get(v___x_4176_, 0);
                    v_isSharedCheck_4191_ = (!crate::leanh::lean_is_exclusive(v___x_4176_)) as u8;
                    if v_isSharedCheck_4191_ == 0 {
                        v___x_4186_ = v___x_4176_;
                        v_isShared_4187_ = v_isSharedCheck_4191_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4184_);
                        crate::leanh::lean_dec(v___x_4176_);
                        v___x_4186_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4190_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4190_, 0, v_a_4184_);
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
    mut v_c_4192_: *mut crate::leanh::LeanObject,
    mut v_a_4193_: *mut crate::leanh::LeanObject,
    mut v_a_4194_: *mut crate::leanh::LeanObject,
    mut v_a_4195_: *mut crate::leanh::LeanObject,
    mut v_a_4196_: *mut crate::leanh::LeanObject,
    mut v_a_4197_: *mut crate::leanh::LeanObject,
    mut v_a_4198_: *mut crate::leanh::LeanObject,
    mut v_a_4199_: *mut crate::leanh::LeanObject,
    mut v_a_4200_: *mut crate::leanh::LeanObject,
    mut v_a_4201_: *mut crate::leanh::LeanObject,
    mut v_a_4202_: *mut crate::leanh::LeanObject,
    mut v_a_4203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4204_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(
        v_c_4192_, v_a_4193_, v_a_4194_, v_a_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_,
        v_a_4200_, v_a_4201_, v_a_4202_,
    );
    crate::leanh::lean_dec(v_a_4202_);
    crate::leanh::lean_dec_ref(v_a_4201_);
    crate::leanh::lean_dec(v_a_4200_);
    crate::leanh::lean_dec_ref(v_a_4199_);
    crate::leanh::lean_dec(v_a_4198_);
    crate::leanh::lean_dec_ref(v_a_4197_);
    crate::leanh::lean_dec(v_a_4196_);
    crate::leanh::lean_dec_ref(v_a_4195_);
    crate::leanh::lean_dec(v_a_4194_);
    crate::leanh::lean_dec(v_a_4193_);
    return v_res_4204_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(
    mut v_00_u03b1_4205_: *mut crate::leanh::LeanObject,
    mut v_c_4206_: *mut crate::leanh::LeanObject,
    mut v_a_4207_: *mut crate::leanh::LeanObject,
    mut v_a_4208_: *mut crate::leanh::LeanObject,
    mut v_a_4209_: *mut crate::leanh::LeanObject,
    mut v_a_4210_: *mut crate::leanh::LeanObject,
    mut v_a_4211_: *mut crate::leanh::LeanObject,
    mut v_a_4212_: *mut crate::leanh::LeanObject,
    mut v_a_4213_: *mut crate::leanh::LeanObject,
    mut v_a_4214_: *mut crate::leanh::LeanObject,
    mut v_a_4215_: *mut crate::leanh::LeanObject,
    mut v_a_4216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4218_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(
        v_c_4206_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_,
        v_a_4214_, v_a_4215_, v_a_4216_,
    );
    return v___x_4218_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___boxed(
    mut v_00_u03b1_4219_: *mut crate::leanh::LeanObject,
    mut v_c_4220_: *mut crate::leanh::LeanObject,
    mut v_a_4221_: *mut crate::leanh::LeanObject,
    mut v_a_4222_: *mut crate::leanh::LeanObject,
    mut v_a_4223_: *mut crate::leanh::LeanObject,
    mut v_a_4224_: *mut crate::leanh::LeanObject,
    mut v_a_4225_: *mut crate::leanh::LeanObject,
    mut v_a_4226_: *mut crate::leanh::LeanObject,
    mut v_a_4227_: *mut crate::leanh::LeanObject,
    mut v_a_4228_: *mut crate::leanh::LeanObject,
    mut v_a_4229_: *mut crate::leanh::LeanObject,
    mut v_a_4230_: *mut crate::leanh::LeanObject,
    mut v_a_4231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_4230_);
    crate::leanh::lean_dec_ref(v_a_4229_);
    crate::leanh::lean_dec(v_a_4228_);
    crate::leanh::lean_dec_ref(v_a_4227_);
    crate::leanh::lean_dec(v_a_4226_);
    crate::leanh::lean_dec_ref(v_a_4225_);
    crate::leanh::lean_dec(v_a_4224_);
    crate::leanh::lean_dec_ref(v_a_4223_);
    crate::leanh::lean_dec(v_a_4222_);
    crate::leanh::lean_dec(v_a_4221_);
    return v_res_4232_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0(
    mut v_00_u03b1_4233_: *mut crate::leanh::LeanObject,
    mut v_msg_4234_: *mut crate::leanh::LeanObject,
    mut v___y_4235_: *mut crate::leanh::LeanObject,
    mut v___y_4236_: *mut crate::leanh::LeanObject,
    mut v___y_4237_: *mut crate::leanh::LeanObject,
    mut v___y_4238_: *mut crate::leanh::LeanObject,
    mut v___y_4239_: *mut crate::leanh::LeanObject,
    mut v___y_4240_: *mut crate::leanh::LeanObject,
    mut v___y_4241_: *mut crate::leanh::LeanObject,
    mut v___y_4242_: *mut crate::leanh::LeanObject,
    mut v___y_4243_: *mut crate::leanh::LeanObject,
    mut v___y_4244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4246_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v_msg_4234_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_);
    return v___x_4246_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___boxed(
    mut v_00_u03b1_4247_: *mut crate::leanh::LeanObject,
    mut v_msg_4248_: *mut crate::leanh::LeanObject,
    mut v___y_4249_: *mut crate::leanh::LeanObject,
    mut v___y_4250_: *mut crate::leanh::LeanObject,
    mut v___y_4251_: *mut crate::leanh::LeanObject,
    mut v___y_4252_: *mut crate::leanh::LeanObject,
    mut v___y_4253_: *mut crate::leanh::LeanObject,
    mut v___y_4254_: *mut crate::leanh::LeanObject,
    mut v___y_4255_: *mut crate::leanh::LeanObject,
    mut v___y_4256_: *mut crate::leanh::LeanObject,
    mut v___y_4257_: *mut crate::leanh::LeanObject,
    mut v___y_4258_: *mut crate::leanh::LeanObject,
    mut v___y_4259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_4258_);
    crate::leanh::lean_dec_ref(v___y_4257_);
    crate::leanh::lean_dec(v___y_4256_);
    crate::leanh::lean_dec_ref(v___y_4255_);
    crate::leanh::lean_dec(v___y_4254_);
    crate::leanh::lean_dec_ref(v___y_4253_);
    crate::leanh::lean_dec(v___y_4252_);
    crate::leanh::lean_dec_ref(v___y_4251_);
    crate::leanh::lean_dec(v___y_4250_);
    crate::leanh::lean_dec(v___y_4249_);
    return v_res_4260_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial_spec__0(
    mut v_a_4261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4262_ = lean_nat_to_int(v_a_4261_);
    return v___x_4262_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial(
    mut v_c_4263_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_p_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_p_4264_ = crate::leanh::lean_ctor_get(v_c_4263_, 0);
    if crate::leanh::lean_obj_tag(v_p_4264_) == 0 {
        let mut v_k_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4267_: u8 = 0;
        v_k_4265_ = crate::leanh::lean_ctor_get(v_p_4264_, 0);
        v___x_4266_ = crate::leanh::lean_obj_once(
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
        let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4275_: u8 = 0;
        v___x_4270_ = l_Int_Linear_Poly_getConst(v_p_4264_);
        v___x_4271_ = l_Int_Linear_Poly_gcdCoeffs_x27(v_p_4264_);
        v___x_4272_ = lean_nat_to_int(v___x_4271_);
        v___x_4273_ = lean_int_emod(v___x_4270_, v___x_4272_);
        crate::leanh::lean_dec(v___x_4272_);
        crate::leanh::lean_dec(v___x_4270_);
        v___x_4274_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_Linear_Poly_isZero___closed__0),
            core::ptr::addr_of_mut!(l_Int_Linear_Poly_isZero___closed__0_once),
            _init_l_Int_Linear_Poly_isZero___closed__0,
        );
        v___x_4275_ = lean_int_dec_eq(v___x_4273_, v___x_4274_);
        crate::leanh::lean_dec(v___x_4273_);
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
    mut v_c_4278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4279_: u8 = 0;
    let mut v_r_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4279_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_isTrivial(v_c_4278_);
    crate::leanh::lean_dec_ref(v_c_4278_);
    v_r_4280_ = crate::leanh::lean_box((v_res_4279_) as usize);
    return v_r_4280_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4282_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__0;
    v___x_4283_ = l_Lean_stringToMessageData(v___x_4282_);
    return v___x_4283_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(
    mut v_c_4284_: *mut crate::leanh::LeanObject,
    mut v_a_4285_: *mut crate::leanh::LeanObject,
    mut v_a_4286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_p_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4291_: u8 = 0;
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4296_: u8 = 0;
    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4304_: u8 = 0;
    let mut v_isSharedCheck_4305_: u8 = 0;
    let mut v_unused_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_p_4288_ = crate::leanh::lean_ctor_get(v_c_4284_, 0);
                v_isSharedCheck_4305_ = (!crate::leanh::lean_is_exclusive(v_c_4284_)) as u8;
                if v_isSharedCheck_4305_ == 0 {
                    v_unused_4306_ = crate::leanh::lean_ctor_get(v_c_4284_, 1);
                    crate::leanh::lean_dec(v_unused_4306_);
                    v___x_4290_ = v_c_4284_;
                    v_isShared_4291_ = v_isSharedCheck_4305_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_p_4288_);
                    crate::leanh::lean_dec(v_c_4284_);
                    v___x_4290_ = crate::leanh::lean_box(0);
                    v_isShared_4291_ = v_isSharedCheck_4305_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4292_ = l_Int_Linear_Poly_pp___redArg(v_p_4288_, v_a_4285_, v_a_4286_);
                if crate::leanh::lean_obj_tag(v___x_4292_) == 0 {
                    v_a_4293_ = crate::leanh::lean_ctor_get(v___x_4292_, 0);
                    v_isSharedCheck_4304_ = (!crate::leanh::lean_is_exclusive(v___x_4292_)) as u8;
                    if v_isSharedCheck_4304_ == 0 {
                        v___x_4295_ = v___x_4292_;
                        v_isShared_4296_ = v_isSharedCheck_4304_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4293_);
                        crate::leanh::lean_dec(v___x_4292_);
                        v___x_4295_ = crate::leanh::lean_box(0);
                        v_isShared_4296_ = v_isSharedCheck_4304_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4290_);
                    return v___x_4292_;
                }
            }
            2 => {
                v___x_4297_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg___closed__1,
                );
                if v_isShared_4291_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4290_, 7);
                    crate::leanh::lean_ctor_set(v___x_4290_, 1, v___x_4297_);
                    crate::leanh::lean_ctor_set(v___x_4290_, 0, v_a_4293_);
                    v___x_4299_ = v___x_4290_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4303_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4303_, 0, v_a_4293_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4303_, 1, v___x_4297_);
                    v___x_4299_ = v_reuseFailAlloc_4303_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4296_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4295_, 0, v___x_4299_);
                    v___x_4301_ = v___x_4295_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4302_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4302_, 0, v___x_4299_);
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
    mut v_c_4307_: *mut crate::leanh::LeanObject,
    mut v_a_4308_: *mut crate::leanh::LeanObject,
    mut v_a_4309_: *mut crate::leanh::LeanObject,
    mut v_a_4310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4311_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_4307_, v_a_4308_, v_a_4309_);
    crate::leanh::lean_dec_ref(v_a_4309_);
    crate::leanh::lean_dec(v_a_4308_);
    return v_res_4311_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(
    mut v_c_4312_: *mut crate::leanh::LeanObject,
    mut v_a_4313_: *mut crate::leanh::LeanObject,
    mut v_a_4314_: *mut crate::leanh::LeanObject,
    mut v_a_4315_: *mut crate::leanh::LeanObject,
    mut v_a_4316_: *mut crate::leanh::LeanObject,
    mut v_a_4317_: *mut crate::leanh::LeanObject,
    mut v_a_4318_: *mut crate::leanh::LeanObject,
    mut v_a_4319_: *mut crate::leanh::LeanObject,
    mut v_a_4320_: *mut crate::leanh::LeanObject,
    mut v_a_4321_: *mut crate::leanh::LeanObject,
    mut v_a_4322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4324_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(v_c_4312_, v_a_4313_, v_a_4321_);
    return v___x_4324_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___boxed(
    mut v_c_4325_: *mut crate::leanh::LeanObject,
    mut v_a_4326_: *mut crate::leanh::LeanObject,
    mut v_a_4327_: *mut crate::leanh::LeanObject,
    mut v_a_4328_: *mut crate::leanh::LeanObject,
    mut v_a_4329_: *mut crate::leanh::LeanObject,
    mut v_a_4330_: *mut crate::leanh::LeanObject,
    mut v_a_4331_: *mut crate::leanh::LeanObject,
    mut v_a_4332_: *mut crate::leanh::LeanObject,
    mut v_a_4333_: *mut crate::leanh::LeanObject,
    mut v_a_4334_: *mut crate::leanh::LeanObject,
    mut v_a_4335_: *mut crate::leanh::LeanObject,
    mut v_a_4336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4337_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp(
        v_c_4325_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_, v_a_4331_, v_a_4332_,
        v_a_4333_, v_a_4334_, v_a_4335_,
    );
    crate::leanh::lean_dec(v_a_4335_);
    crate::leanh::lean_dec_ref(v_a_4334_);
    crate::leanh::lean_dec(v_a_4333_);
    crate::leanh::lean_dec_ref(v_a_4332_);
    crate::leanh::lean_dec(v_a_4331_);
    crate::leanh::lean_dec_ref(v_a_4330_);
    crate::leanh::lean_dec(v_a_4329_);
    crate::leanh::lean_dec_ref(v_a_4328_);
    crate::leanh::lean_dec(v_a_4327_);
    crate::leanh::lean_dec(v_a_4326_);
    return v_res_4337_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(
    mut v_c_4338_: *mut crate::leanh::LeanObject,
    mut v_a_4339_: *mut crate::leanh::LeanObject,
    mut v_a_4340_: *mut crate::leanh::LeanObject,
    mut v_a_4341_: *mut crate::leanh::LeanObject,
    mut v_a_4342_: *mut crate::leanh::LeanObject,
    mut v_a_4343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4354_: u8 = 0;
    let mut v___x_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4358_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4345_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(
                    v_c_4338_, v_a_4339_, v_a_4342_,
                );
                if crate::leanh::lean_obj_tag(v___x_4345_) == 0 {
                    v_a_4346_ = crate::leanh::lean_ctor_get(v___x_4345_, 0);
                    crate::leanh::lean_inc(v_a_4346_);
                    crate::leanh::lean_dec_ref_known(v___x_4345_, 1);
                    v___x_4347_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
                    v___x_4348_ = l_Lean_indentD(v_a_4346_);
                    v___x_4349_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4349_, 0, v___x_4347_);
                    crate::leanh::lean_ctor_set(v___x_4349_, 1, v___x_4348_);
                    v___x_4350_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_4349_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_);
                    return v___x_4350_;
                } else {
                    v_a_4351_ = crate::leanh::lean_ctor_get(v___x_4345_, 0);
                    v_isSharedCheck_4358_ = (!crate::leanh::lean_is_exclusive(v___x_4345_)) as u8;
                    if v_isSharedCheck_4358_ == 0 {
                        v___x_4353_ = v___x_4345_;
                        v_isShared_4354_ = v_isSharedCheck_4358_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4351_);
                        crate::leanh::lean_dec(v___x_4345_);
                        v___x_4353_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4357_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4357_, 0, v_a_4351_);
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
    mut v_c_4359_: *mut crate::leanh::LeanObject,
    mut v_a_4360_: *mut crate::leanh::LeanObject,
    mut v_a_4361_: *mut crate::leanh::LeanObject,
    mut v_a_4362_: *mut crate::leanh::LeanObject,
    mut v_a_4363_: *mut crate::leanh::LeanObject,
    mut v_a_4364_: *mut crate::leanh::LeanObject,
    mut v_a_4365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4366_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(
        v_c_4359_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_,
    );
    crate::leanh::lean_dec(v_a_4364_);
    crate::leanh::lean_dec_ref(v_a_4363_);
    crate::leanh::lean_dec(v_a_4362_);
    crate::leanh::lean_dec_ref(v_a_4361_);
    crate::leanh::lean_dec(v_a_4360_);
    return v_res_4366_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected(
    mut v_00_u03b1_4367_: *mut crate::leanh::LeanObject,
    mut v_c_4368_: *mut crate::leanh::LeanObject,
    mut v_a_4369_: *mut crate::leanh::LeanObject,
    mut v_a_4370_: *mut crate::leanh::LeanObject,
    mut v_a_4371_: *mut crate::leanh::LeanObject,
    mut v_a_4372_: *mut crate::leanh::LeanObject,
    mut v_a_4373_: *mut crate::leanh::LeanObject,
    mut v_a_4374_: *mut crate::leanh::LeanObject,
    mut v_a_4375_: *mut crate::leanh::LeanObject,
    mut v_a_4376_: *mut crate::leanh::LeanObject,
    mut v_a_4377_: *mut crate::leanh::LeanObject,
    mut v_a_4378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4380_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___redArg(
        v_c_4368_, v_a_4369_, v_a_4375_, v_a_4376_, v_a_4377_, v_a_4378_,
    );
    return v___x_4380_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_throwUnexpected___boxed(
    mut v_00_u03b1_4381_: *mut crate::leanh::LeanObject,
    mut v_c_4382_: *mut crate::leanh::LeanObject,
    mut v_a_4383_: *mut crate::leanh::LeanObject,
    mut v_a_4384_: *mut crate::leanh::LeanObject,
    mut v_a_4385_: *mut crate::leanh::LeanObject,
    mut v_a_4386_: *mut crate::leanh::LeanObject,
    mut v_a_4387_: *mut crate::leanh::LeanObject,
    mut v_a_4388_: *mut crate::leanh::LeanObject,
    mut v_a_4389_: *mut crate::leanh::LeanObject,
    mut v_a_4390_: *mut crate::leanh::LeanObject,
    mut v_a_4391_: *mut crate::leanh::LeanObject,
    mut v_a_4392_: *mut crate::leanh::LeanObject,
    mut v_a_4393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_4392_);
    crate::leanh::lean_dec_ref(v_a_4391_);
    crate::leanh::lean_dec(v_a_4390_);
    crate::leanh::lean_dec_ref(v_a_4389_);
    crate::leanh::lean_dec(v_a_4388_);
    crate::leanh::lean_dec_ref(v_a_4387_);
    crate::leanh::lean_dec(v_a_4386_);
    crate::leanh::lean_dec_ref(v_a_4385_);
    crate::leanh::lean_dec(v_a_4384_);
    crate::leanh::lean_dec(v_a_4383_);
    return v_res_4394_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4395_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_Linear_Poly_isZero___closed__0),
        core::ptr::addr_of_mut!(l_Int_Linear_Poly_isZero___closed__0_once),
        _init_l_Int_Linear_Poly_isZero___closed__0,
    );
    v___x_4396_ = l_Lean_mkIntLit(v___x_4395_);
    return v___x_4396_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(
    mut v_c_4397_: *mut crate::leanh::LeanObject,
    mut v_a_4398_: *mut crate::leanh::LeanObject,
    mut v_a_4399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_p_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4406_: u8 = 0;
    let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4413_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_p_4401_ = crate::leanh::lean_ctor_get(v_c_4397_, 0);
                crate::leanh::lean_inc_ref(v_p_4401_);
                crate::leanh::lean_dec_ref(v_c_4397_);
                v___x_4402_ =
                    l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_4401_, v_a_4398_, v_a_4399_);
                if crate::leanh::lean_obj_tag(v___x_4402_) == 0 {
                    v_a_4403_ = crate::leanh::lean_ctor_get(v___x_4402_, 0);
                    v_isSharedCheck_4413_ = (!crate::leanh::lean_is_exclusive(v___x_4402_)) as u8;
                    if v_isSharedCheck_4413_ == 0 {
                        v___x_4405_ = v___x_4402_;
                        v_isShared_4406_ = v_isSharedCheck_4413_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4403_);
                        crate::leanh::lean_dec(v___x_4402_);
                        v___x_4405_ = crate::leanh::lean_box(0);
                        v_isShared_4406_ = v_isSharedCheck_4413_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_4402_;
                }
            }
            1 => {
                v___x_4407_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
                v___x_4408_ = l_Lean_mkIntEq(v_a_4403_, v___x_4407_);
                v___x_4409_ = l_Lean_mkNot(v___x_4408_);
                if v_isShared_4406_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4405_, 0, v___x_4409_);
                    v___x_4411_ = v___x_4405_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4412_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4412_, 0, v___x_4409_);
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
    mut v_c_4414_: *mut crate::leanh::LeanObject,
    mut v_a_4415_: *mut crate::leanh::LeanObject,
    mut v_a_4416_: *mut crate::leanh::LeanObject,
    mut v_a_4417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4418_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(
        v_c_4414_, v_a_4415_, v_a_4416_,
    );
    crate::leanh::lean_dec_ref(v_a_4416_);
    crate::leanh::lean_dec(v_a_4415_);
    return v_res_4418_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(
    mut v_c_4419_: *mut crate::leanh::LeanObject,
    mut v_a_4420_: *mut crate::leanh::LeanObject,
    mut v_a_4421_: *mut crate::leanh::LeanObject,
    mut v_a_4422_: *mut crate::leanh::LeanObject,
    mut v_a_4423_: *mut crate::leanh::LeanObject,
    mut v_a_4424_: *mut crate::leanh::LeanObject,
    mut v_a_4425_: *mut crate::leanh::LeanObject,
    mut v_a_4426_: *mut crate::leanh::LeanObject,
    mut v_a_4427_: *mut crate::leanh::LeanObject,
    mut v_a_4428_: *mut crate::leanh::LeanObject,
    mut v_a_4429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4431_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg(
        v_c_4419_, v_a_4420_, v_a_4428_,
    );
    return v___x_4431_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___boxed(
    mut v_c_4432_: *mut crate::leanh::LeanObject,
    mut v_a_4433_: *mut crate::leanh::LeanObject,
    mut v_a_4434_: *mut crate::leanh::LeanObject,
    mut v_a_4435_: *mut crate::leanh::LeanObject,
    mut v_a_4436_: *mut crate::leanh::LeanObject,
    mut v_a_4437_: *mut crate::leanh::LeanObject,
    mut v_a_4438_: *mut crate::leanh::LeanObject,
    mut v_a_4439_: *mut crate::leanh::LeanObject,
    mut v_a_4440_: *mut crate::leanh::LeanObject,
    mut v_a_4441_: *mut crate::leanh::LeanObject,
    mut v_a_4442_: *mut crate::leanh::LeanObject,
    mut v_a_4443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4444_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr(
        v_c_4432_, v_a_4433_, v_a_4434_, v_a_4435_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_,
        v_a_4440_, v_a_4441_, v_a_4442_,
    );
    crate::leanh::lean_dec(v_a_4442_);
    crate::leanh::lean_dec_ref(v_a_4441_);
    crate::leanh::lean_dec(v_a_4440_);
    crate::leanh::lean_dec_ref(v_a_4439_);
    crate::leanh::lean_dec(v_a_4438_);
    crate::leanh::lean_dec_ref(v_a_4437_);
    crate::leanh::lean_dec(v_a_4436_);
    crate::leanh::lean_dec_ref(v_a_4435_);
    crate::leanh::lean_dec(v_a_4434_);
    crate::leanh::lean_dec(v_a_4433_);
    return v_res_4444_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assert___boxed(
    mut v_c_4457_: *mut crate::leanh::LeanObject,
    mut v_a_4458_: *mut crate::leanh::LeanObject,
    mut v_a_4459_: *mut crate::leanh::LeanObject,
    mut v_a_4460_: *mut crate::leanh::LeanObject,
    mut v_a_4461_: *mut crate::leanh::LeanObject,
    mut v_a_4462_: *mut crate::leanh::LeanObject,
    mut v_a_4463_: *mut crate::leanh::LeanObject,
    mut v_a_4464_: *mut crate::leanh::LeanObject,
    mut v_a_4465_: *mut crate::leanh::LeanObject,
    mut v_a_4466_: *mut crate::leanh::LeanObject,
    mut v_a_4467_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_4468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4469_ = lean_grind_cutsat_assert_le(
        v_c_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_, v_a_4463_, v_a_4464_,
        v_a_4465_, v_a_4466_, v_a_4467_,
    );
    return v_res_4469_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(
    mut v_c_4470_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_p_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_p_4471_ = crate::leanh::lean_ctor_get(v_c_4470_, 0);
    if crate::leanh::lean_obj_tag(v_p_4471_) == 0 {
        let mut v_k_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4474_: u8 = 0;
        v_k_4472_ = crate::leanh::lean_ctor_get(v_p_4471_, 0);
        v___x_4473_ = crate::leanh::lean_obj_once(
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
    mut v_c_4476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4477_: u8 = 0;
    let mut v_r_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4477_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(v_c_4476_);
    crate::leanh::lean_dec_ref(v_c_4476_);
    v_r_4478_ = crate::leanh::lean_box((v_res_4477_) as usize);
    return v_r_4478_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4480_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__0;
    v___x_4481_ = l_Lean_stringToMessageData(v___x_4480_);
    return v___x_4481_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(
    mut v_c_4482_: *mut crate::leanh::LeanObject,
    mut v_a_4483_: *mut crate::leanh::LeanObject,
    mut v_a_4484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_p_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4489_: u8 = 0;
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4494_: u8 = 0;
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4502_: u8 = 0;
    let mut v_isSharedCheck_4503_: u8 = 0;
    let mut v_unused_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_p_4486_ = crate::leanh::lean_ctor_get(v_c_4482_, 0);
                v_isSharedCheck_4503_ = (!crate::leanh::lean_is_exclusive(v_c_4482_)) as u8;
                if v_isSharedCheck_4503_ == 0 {
                    v_unused_4504_ = crate::leanh::lean_ctor_get(v_c_4482_, 1);
                    crate::leanh::lean_dec(v_unused_4504_);
                    v___x_4488_ = v_c_4482_;
                    v_isShared_4489_ = v_isSharedCheck_4503_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_p_4486_);
                    crate::leanh::lean_dec(v_c_4482_);
                    v___x_4488_ = crate::leanh::lean_box(0);
                    v_isShared_4489_ = v_isSharedCheck_4503_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4490_ = l_Int_Linear_Poly_pp___redArg(v_p_4486_, v_a_4483_, v_a_4484_);
                if crate::leanh::lean_obj_tag(v___x_4490_) == 0 {
                    v_a_4491_ = crate::leanh::lean_ctor_get(v___x_4490_, 0);
                    v_isSharedCheck_4502_ = (!crate::leanh::lean_is_exclusive(v___x_4490_)) as u8;
                    if v_isSharedCheck_4502_ == 0 {
                        v___x_4493_ = v___x_4490_;
                        v_isShared_4494_ = v_isSharedCheck_4502_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4491_);
                        crate::leanh::lean_dec(v___x_4490_);
                        v___x_4493_ = crate::leanh::lean_box(0);
                        v_isShared_4494_ = v_isSharedCheck_4502_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4488_);
                    return v___x_4490_;
                }
            }
            2 => {
                v___x_4495_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg___closed__1,
                );
                if v_isShared_4489_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4488_, 7);
                    crate::leanh::lean_ctor_set(v___x_4488_, 1, v___x_4495_);
                    crate::leanh::lean_ctor_set(v___x_4488_, 0, v_a_4491_);
                    v___x_4497_ = v___x_4488_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4501_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4501_, 0, v_a_4491_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4501_, 1, v___x_4495_);
                    v___x_4497_ = v_reuseFailAlloc_4501_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4494_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4493_, 0, v___x_4497_);
                    v___x_4499_ = v___x_4493_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4500_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4500_, 0, v___x_4497_);
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
    mut v_c_4505_: *mut crate::leanh::LeanObject,
    mut v_a_4506_: *mut crate::leanh::LeanObject,
    mut v_a_4507_: *mut crate::leanh::LeanObject,
    mut v_a_4508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4509_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_4505_, v_a_4506_, v_a_4507_);
    crate::leanh::lean_dec_ref(v_a_4507_);
    crate::leanh::lean_dec(v_a_4506_);
    return v_res_4509_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(
    mut v_c_4510_: *mut crate::leanh::LeanObject,
    mut v_a_4511_: *mut crate::leanh::LeanObject,
    mut v_a_4512_: *mut crate::leanh::LeanObject,
    mut v_a_4513_: *mut crate::leanh::LeanObject,
    mut v_a_4514_: *mut crate::leanh::LeanObject,
    mut v_a_4515_: *mut crate::leanh::LeanObject,
    mut v_a_4516_: *mut crate::leanh::LeanObject,
    mut v_a_4517_: *mut crate::leanh::LeanObject,
    mut v_a_4518_: *mut crate::leanh::LeanObject,
    mut v_a_4519_: *mut crate::leanh::LeanObject,
    mut v_a_4520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4522_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_4510_, v_a_4511_, v_a_4519_);
    return v___x_4522_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___boxed(
    mut v_c_4523_: *mut crate::leanh::LeanObject,
    mut v_a_4524_: *mut crate::leanh::LeanObject,
    mut v_a_4525_: *mut crate::leanh::LeanObject,
    mut v_a_4526_: *mut crate::leanh::LeanObject,
    mut v_a_4527_: *mut crate::leanh::LeanObject,
    mut v_a_4528_: *mut crate::leanh::LeanObject,
    mut v_a_4529_: *mut crate::leanh::LeanObject,
    mut v_a_4530_: *mut crate::leanh::LeanObject,
    mut v_a_4531_: *mut crate::leanh::LeanObject,
    mut v_a_4532_: *mut crate::leanh::LeanObject,
    mut v_a_4533_: *mut crate::leanh::LeanObject,
    mut v_a_4534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4535_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp(
        v_c_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_,
        v_a_4531_, v_a_4532_, v_a_4533_,
    );
    crate::leanh::lean_dec(v_a_4533_);
    crate::leanh::lean_dec_ref(v_a_4532_);
    crate::leanh::lean_dec(v_a_4531_);
    crate::leanh::lean_dec_ref(v_a_4530_);
    crate::leanh::lean_dec(v_a_4529_);
    crate::leanh::lean_dec_ref(v_a_4528_);
    crate::leanh::lean_dec(v_a_4527_);
    crate::leanh::lean_dec_ref(v_a_4526_);
    crate::leanh::lean_dec(v_a_4525_);
    crate::leanh::lean_dec(v_a_4524_);
    return v_res_4535_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(
    mut v_c_4536_: *mut crate::leanh::LeanObject,
    mut v_a_4537_: *mut crate::leanh::LeanObject,
    mut v_a_4538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_p_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4545_: u8 = 0;
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4551_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_p_4540_ = crate::leanh::lean_ctor_get(v_c_4536_, 0);
                crate::leanh::lean_inc_ref(v_p_4540_);
                crate::leanh::lean_dec_ref(v_c_4536_);
                v___x_4541_ =
                    l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_4540_, v_a_4537_, v_a_4538_);
                if crate::leanh::lean_obj_tag(v___x_4541_) == 0 {
                    v_a_4542_ = crate::leanh::lean_ctor_get(v___x_4541_, 0);
                    v_isSharedCheck_4551_ = (!crate::leanh::lean_is_exclusive(v___x_4541_)) as u8;
                    if v_isSharedCheck_4551_ == 0 {
                        v___x_4544_ = v___x_4541_;
                        v_isShared_4545_ = v_isSharedCheck_4551_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4542_);
                        crate::leanh::lean_dec(v___x_4541_);
                        v___x_4544_ = crate::leanh::lean_box(0);
                        v_isShared_4545_ = v_isSharedCheck_4551_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_4541_;
                }
            }
            1 => {
                v___x_4546_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
                v___x_4547_ = l_Lean_mkIntLE(v_a_4542_, v___x_4546_);
                if v_isShared_4545_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4544_, 0, v___x_4547_);
                    v___x_4549_ = v___x_4544_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4550_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4550_, 0, v___x_4547_);
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
    mut v_c_4552_: *mut crate::leanh::LeanObject,
    mut v_a_4553_: *mut crate::leanh::LeanObject,
    mut v_a_4554_: *mut crate::leanh::LeanObject,
    mut v_a_4555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4556_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(v_c_4552_, v_a_4553_, v_a_4554_);
    crate::leanh::lean_dec_ref(v_a_4554_);
    crate::leanh::lean_dec(v_a_4553_);
    return v_res_4556_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(
    mut v_c_4557_: *mut crate::leanh::LeanObject,
    mut v_a_4558_: *mut crate::leanh::LeanObject,
    mut v_a_4559_: *mut crate::leanh::LeanObject,
    mut v_a_4560_: *mut crate::leanh::LeanObject,
    mut v_a_4561_: *mut crate::leanh::LeanObject,
    mut v_a_4562_: *mut crate::leanh::LeanObject,
    mut v_a_4563_: *mut crate::leanh::LeanObject,
    mut v_a_4564_: *mut crate::leanh::LeanObject,
    mut v_a_4565_: *mut crate::leanh::LeanObject,
    mut v_a_4566_: *mut crate::leanh::LeanObject,
    mut v_a_4567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4569_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___redArg(v_c_4557_, v_a_4558_, v_a_4566_);
    return v___x_4569_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr___boxed(
    mut v_c_4570_: *mut crate::leanh::LeanObject,
    mut v_a_4571_: *mut crate::leanh::LeanObject,
    mut v_a_4572_: *mut crate::leanh::LeanObject,
    mut v_a_4573_: *mut crate::leanh::LeanObject,
    mut v_a_4574_: *mut crate::leanh::LeanObject,
    mut v_a_4575_: *mut crate::leanh::LeanObject,
    mut v_a_4576_: *mut crate::leanh::LeanObject,
    mut v_a_4577_: *mut crate::leanh::LeanObject,
    mut v_a_4578_: *mut crate::leanh::LeanObject,
    mut v_a_4579_: *mut crate::leanh::LeanObject,
    mut v_a_4580_: *mut crate::leanh::LeanObject,
    mut v_a_4581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4582_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_denoteExpr(
        v_c_4570_, v_a_4571_, v_a_4572_, v_a_4573_, v_a_4574_, v_a_4575_, v_a_4576_, v_a_4577_,
        v_a_4578_, v_a_4579_, v_a_4580_,
    );
    crate::leanh::lean_dec(v_a_4580_);
    crate::leanh::lean_dec_ref(v_a_4579_);
    crate::leanh::lean_dec(v_a_4578_);
    crate::leanh::lean_dec_ref(v_a_4577_);
    crate::leanh::lean_dec(v_a_4576_);
    crate::leanh::lean_dec_ref(v_a_4575_);
    crate::leanh::lean_dec(v_a_4574_);
    crate::leanh::lean_dec_ref(v_a_4573_);
    crate::leanh::lean_dec(v_a_4572_);
    crate::leanh::lean_dec(v_a_4571_);
    return v_res_4582_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(
    mut v_c_4583_: *mut crate::leanh::LeanObject,
    mut v_a_4584_: *mut crate::leanh::LeanObject,
    mut v_a_4585_: *mut crate::leanh::LeanObject,
    mut v_a_4586_: *mut crate::leanh::LeanObject,
    mut v_a_4587_: *mut crate::leanh::LeanObject,
    mut v_a_4588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4599_: u8 = 0;
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4603_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4590_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(
                    v_c_4583_, v_a_4584_, v_a_4587_,
                );
                if crate::leanh::lean_obj_tag(v___x_4590_) == 0 {
                    v_a_4591_ = crate::leanh::lean_ctor_get(v___x_4590_, 0);
                    crate::leanh::lean_inc(v_a_4591_);
                    crate::leanh::lean_dec_ref_known(v___x_4590_, 1);
                    v___x_4592_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
                    v___x_4593_ = l_Lean_indentD(v_a_4591_);
                    v___x_4594_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4594_, 0, v___x_4592_);
                    crate::leanh::lean_ctor_set(v___x_4594_, 1, v___x_4593_);
                    v___x_4595_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_4594_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_);
                    return v___x_4595_;
                } else {
                    v_a_4596_ = crate::leanh::lean_ctor_get(v___x_4590_, 0);
                    v_isSharedCheck_4603_ = (!crate::leanh::lean_is_exclusive(v___x_4590_)) as u8;
                    if v_isSharedCheck_4603_ == 0 {
                        v___x_4598_ = v___x_4590_;
                        v_isShared_4599_ = v_isSharedCheck_4603_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4596_);
                        crate::leanh::lean_dec(v___x_4590_);
                        v___x_4598_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4602_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4602_, 0, v_a_4596_);
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
    mut v_c_4604_: *mut crate::leanh::LeanObject,
    mut v_a_4605_: *mut crate::leanh::LeanObject,
    mut v_a_4606_: *mut crate::leanh::LeanObject,
    mut v_a_4607_: *mut crate::leanh::LeanObject,
    mut v_a_4608_: *mut crate::leanh::LeanObject,
    mut v_a_4609_: *mut crate::leanh::LeanObject,
    mut v_a_4610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4611_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(
        v_c_4604_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_,
    );
    crate::leanh::lean_dec(v_a_4609_);
    crate::leanh::lean_dec_ref(v_a_4608_);
    crate::leanh::lean_dec(v_a_4607_);
    crate::leanh::lean_dec_ref(v_a_4606_);
    crate::leanh::lean_dec(v_a_4605_);
    return v_res_4611_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected(
    mut v_00_u03b1_4612_: *mut crate::leanh::LeanObject,
    mut v_c_4613_: *mut crate::leanh::LeanObject,
    mut v_a_4614_: *mut crate::leanh::LeanObject,
    mut v_a_4615_: *mut crate::leanh::LeanObject,
    mut v_a_4616_: *mut crate::leanh::LeanObject,
    mut v_a_4617_: *mut crate::leanh::LeanObject,
    mut v_a_4618_: *mut crate::leanh::LeanObject,
    mut v_a_4619_: *mut crate::leanh::LeanObject,
    mut v_a_4620_: *mut crate::leanh::LeanObject,
    mut v_a_4621_: *mut crate::leanh::LeanObject,
    mut v_a_4622_: *mut crate::leanh::LeanObject,
    mut v_a_4623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4625_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(
        v_c_4613_, v_a_4614_, v_a_4620_, v_a_4621_, v_a_4622_, v_a_4623_,
    );
    return v___x_4625_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___boxed(
    mut v_00_u03b1_4626_: *mut crate::leanh::LeanObject,
    mut v_c_4627_: *mut crate::leanh::LeanObject,
    mut v_a_4628_: *mut crate::leanh::LeanObject,
    mut v_a_4629_: *mut crate::leanh::LeanObject,
    mut v_a_4630_: *mut crate::leanh::LeanObject,
    mut v_a_4631_: *mut crate::leanh::LeanObject,
    mut v_a_4632_: *mut crate::leanh::LeanObject,
    mut v_a_4633_: *mut crate::leanh::LeanObject,
    mut v_a_4634_: *mut crate::leanh::LeanObject,
    mut v_a_4635_: *mut crate::leanh::LeanObject,
    mut v_a_4636_: *mut crate::leanh::LeanObject,
    mut v_a_4637_: *mut crate::leanh::LeanObject,
    mut v_a_4638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_4637_);
    crate::leanh::lean_dec_ref(v_a_4636_);
    crate::leanh::lean_dec(v_a_4635_);
    crate::leanh::lean_dec_ref(v_a_4634_);
    crate::leanh::lean_dec(v_a_4633_);
    crate::leanh::lean_dec_ref(v_a_4632_);
    crate::leanh::lean_dec(v_a_4631_);
    crate::leanh::lean_dec_ref(v_a_4630_);
    crate::leanh::lean_dec(v_a_4629_);
    crate::leanh::lean_dec(v_a_4628_);
    return v_res_4639_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(
    mut v_c_4640_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_p_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_p_4641_ = crate::leanh::lean_ctor_get(v_c_4640_, 0);
    if crate::leanh::lean_obj_tag(v_p_4641_) == 0 {
        let mut v_k_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4644_: u8 = 0;
        v_k_4642_ = crate::leanh::lean_ctor_get(v_p_4641_, 0);
        v___x_4643_ = crate::leanh::lean_obj_once(
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
    mut v_c_4646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4647_: u8 = 0;
    let mut v_r_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4647_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_isTrivial(v_c_4646_);
    crate::leanh::lean_dec_ref(v_c_4646_);
    v_r_4648_ = crate::leanh::lean_box((v_res_4647_) as usize);
    return v_r_4648_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4650_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__0;
    v___x_4651_ = l_Lean_stringToMessageData(v___x_4650_);
    return v___x_4651_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(
    mut v_c_4652_: *mut crate::leanh::LeanObject,
    mut v_a_4653_: *mut crate::leanh::LeanObject,
    mut v_a_4654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_p_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4659_: u8 = 0;
    let mut v___x_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4664_: u8 = 0;
    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4672_: u8 = 0;
    let mut v_isSharedCheck_4673_: u8 = 0;
    let mut v_unused_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_p_4656_ = crate::leanh::lean_ctor_get(v_c_4652_, 0);
                v_isSharedCheck_4673_ = (!crate::leanh::lean_is_exclusive(v_c_4652_)) as u8;
                if v_isSharedCheck_4673_ == 0 {
                    v_unused_4674_ = crate::leanh::lean_ctor_get(v_c_4652_, 1);
                    crate::leanh::lean_dec(v_unused_4674_);
                    v___x_4658_ = v_c_4652_;
                    v_isShared_4659_ = v_isSharedCheck_4673_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_p_4656_);
                    crate::leanh::lean_dec(v_c_4652_);
                    v___x_4658_ = crate::leanh::lean_box(0);
                    v_isShared_4659_ = v_isSharedCheck_4673_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4660_ = l_Int_Linear_Poly_pp___redArg(v_p_4656_, v_a_4653_, v_a_4654_);
                if crate::leanh::lean_obj_tag(v___x_4660_) == 0 {
                    v_a_4661_ = crate::leanh::lean_ctor_get(v___x_4660_, 0);
                    v_isSharedCheck_4672_ = (!crate::leanh::lean_is_exclusive(v___x_4660_)) as u8;
                    if v_isSharedCheck_4672_ == 0 {
                        v___x_4663_ = v___x_4660_;
                        v_isShared_4664_ = v_isSharedCheck_4672_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4661_);
                        crate::leanh::lean_dec(v___x_4660_);
                        v___x_4663_ = crate::leanh::lean_box(0);
                        v_isShared_4664_ = v_isSharedCheck_4672_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4658_);
                    return v___x_4660_;
                }
            }
            2 => {
                v___x_4665_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg___closed__1,
                );
                if v_isShared_4659_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4658_, 7);
                    crate::leanh::lean_ctor_set(v___x_4658_, 1, v___x_4665_);
                    crate::leanh::lean_ctor_set(v___x_4658_, 0, v_a_4661_);
                    v___x_4667_ = v___x_4658_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4671_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4671_, 0, v_a_4661_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4671_, 1, v___x_4665_);
                    v___x_4667_ = v_reuseFailAlloc_4671_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4664_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4663_, 0, v___x_4667_);
                    v___x_4669_ = v___x_4663_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4670_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4670_, 0, v___x_4667_);
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
    mut v_c_4675_: *mut crate::leanh::LeanObject,
    mut v_a_4676_: *mut crate::leanh::LeanObject,
    mut v_a_4677_: *mut crate::leanh::LeanObject,
    mut v_a_4678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4679_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_4675_, v_a_4676_, v_a_4677_);
    crate::leanh::lean_dec_ref(v_a_4677_);
    crate::leanh::lean_dec(v_a_4676_);
    return v_res_4679_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(
    mut v_c_4680_: *mut crate::leanh::LeanObject,
    mut v_a_4681_: *mut crate::leanh::LeanObject,
    mut v_a_4682_: *mut crate::leanh::LeanObject,
    mut v_a_4683_: *mut crate::leanh::LeanObject,
    mut v_a_4684_: *mut crate::leanh::LeanObject,
    mut v_a_4685_: *mut crate::leanh::LeanObject,
    mut v_a_4686_: *mut crate::leanh::LeanObject,
    mut v_a_4687_: *mut crate::leanh::LeanObject,
    mut v_a_4688_: *mut crate::leanh::LeanObject,
    mut v_a_4689_: *mut crate::leanh::LeanObject,
    mut v_a_4690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4692_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_4680_, v_a_4681_, v_a_4689_);
    return v___x_4692_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___boxed(
    mut v_c_4693_: *mut crate::leanh::LeanObject,
    mut v_a_4694_: *mut crate::leanh::LeanObject,
    mut v_a_4695_: *mut crate::leanh::LeanObject,
    mut v_a_4696_: *mut crate::leanh::LeanObject,
    mut v_a_4697_: *mut crate::leanh::LeanObject,
    mut v_a_4698_: *mut crate::leanh::LeanObject,
    mut v_a_4699_: *mut crate::leanh::LeanObject,
    mut v_a_4700_: *mut crate::leanh::LeanObject,
    mut v_a_4701_: *mut crate::leanh::LeanObject,
    mut v_a_4702_: *mut crate::leanh::LeanObject,
    mut v_a_4703_: *mut crate::leanh::LeanObject,
    mut v_a_4704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4705_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp(
        v_c_4693_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_, v_a_4700_,
        v_a_4701_, v_a_4702_, v_a_4703_,
    );
    crate::leanh::lean_dec(v_a_4703_);
    crate::leanh::lean_dec_ref(v_a_4702_);
    crate::leanh::lean_dec(v_a_4701_);
    crate::leanh::lean_dec_ref(v_a_4700_);
    crate::leanh::lean_dec(v_a_4699_);
    crate::leanh::lean_dec_ref(v_a_4698_);
    crate::leanh::lean_dec(v_a_4697_);
    crate::leanh::lean_dec_ref(v_a_4696_);
    crate::leanh::lean_dec(v_a_4695_);
    crate::leanh::lean_dec(v_a_4694_);
    return v_res_4705_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(
    mut v_c_4706_: *mut crate::leanh::LeanObject,
    mut v_a_4707_: *mut crate::leanh::LeanObject,
    mut v_a_4708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_p_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4715_: u8 = 0;
    let mut v___x_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4721_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_p_4710_ = crate::leanh::lean_ctor_get(v_c_4706_, 0);
                crate::leanh::lean_inc_ref(v_p_4710_);
                crate::leanh::lean_dec_ref(v_c_4706_);
                v___x_4711_ =
                    l_Int_Linear_Poly_denoteExpr_x27___redArg(v_p_4710_, v_a_4707_, v_a_4708_);
                if crate::leanh::lean_obj_tag(v___x_4711_) == 0 {
                    v_a_4712_ = crate::leanh::lean_ctor_get(v___x_4711_, 0);
                    v_isSharedCheck_4721_ = (!crate::leanh::lean_is_exclusive(v___x_4711_)) as u8;
                    if v_isSharedCheck_4721_ == 0 {
                        v___x_4714_ = v___x_4711_;
                        v_isShared_4715_ = v_isSharedCheck_4721_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4712_);
                        crate::leanh::lean_dec(v___x_4711_);
                        v___x_4714_ = crate::leanh::lean_box(0);
                        v_isShared_4715_ = v_isSharedCheck_4721_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_4711_;
                }
            }
            1 => {
                v___x_4716_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_denoteExpr___redArg___closed__0);
                v___x_4717_ = l_Lean_mkIntEq(v_a_4712_, v___x_4716_);
                if v_isShared_4715_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4714_, 0, v___x_4717_);
                    v___x_4719_ = v___x_4714_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4720_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4720_, 0, v___x_4717_);
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
    mut v_c_4722_: *mut crate::leanh::LeanObject,
    mut v_a_4723_: *mut crate::leanh::LeanObject,
    mut v_a_4724_: *mut crate::leanh::LeanObject,
    mut v_a_4725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4726_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(v_c_4722_, v_a_4723_, v_a_4724_);
    crate::leanh::lean_dec_ref(v_a_4724_);
    crate::leanh::lean_dec(v_a_4723_);
    return v_res_4726_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(
    mut v_c_4727_: *mut crate::leanh::LeanObject,
    mut v_a_4728_: *mut crate::leanh::LeanObject,
    mut v_a_4729_: *mut crate::leanh::LeanObject,
    mut v_a_4730_: *mut crate::leanh::LeanObject,
    mut v_a_4731_: *mut crate::leanh::LeanObject,
    mut v_a_4732_: *mut crate::leanh::LeanObject,
    mut v_a_4733_: *mut crate::leanh::LeanObject,
    mut v_a_4734_: *mut crate::leanh::LeanObject,
    mut v_a_4735_: *mut crate::leanh::LeanObject,
    mut v_a_4736_: *mut crate::leanh::LeanObject,
    mut v_a_4737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4739_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___redArg(v_c_4727_, v_a_4728_, v_a_4736_);
    return v___x_4739_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr___boxed(
    mut v_c_4740_: *mut crate::leanh::LeanObject,
    mut v_a_4741_: *mut crate::leanh::LeanObject,
    mut v_a_4742_: *mut crate::leanh::LeanObject,
    mut v_a_4743_: *mut crate::leanh::LeanObject,
    mut v_a_4744_: *mut crate::leanh::LeanObject,
    mut v_a_4745_: *mut crate::leanh::LeanObject,
    mut v_a_4746_: *mut crate::leanh::LeanObject,
    mut v_a_4747_: *mut crate::leanh::LeanObject,
    mut v_a_4748_: *mut crate::leanh::LeanObject,
    mut v_a_4749_: *mut crate::leanh::LeanObject,
    mut v_a_4750_: *mut crate::leanh::LeanObject,
    mut v_a_4751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4752_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_denoteExpr(
        v_c_4740_, v_a_4741_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_,
        v_a_4748_, v_a_4749_, v_a_4750_,
    );
    crate::leanh::lean_dec(v_a_4750_);
    crate::leanh::lean_dec_ref(v_a_4749_);
    crate::leanh::lean_dec(v_a_4748_);
    crate::leanh::lean_dec_ref(v_a_4747_);
    crate::leanh::lean_dec(v_a_4746_);
    crate::leanh::lean_dec_ref(v_a_4745_);
    crate::leanh::lean_dec(v_a_4744_);
    crate::leanh::lean_dec_ref(v_a_4743_);
    crate::leanh::lean_dec(v_a_4742_);
    crate::leanh::lean_dec(v_a_4741_);
    return v_res_4752_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(
    mut v_c_4753_: *mut crate::leanh::LeanObject,
    mut v_a_4754_: *mut crate::leanh::LeanObject,
    mut v_a_4755_: *mut crate::leanh::LeanObject,
    mut v_a_4756_: *mut crate::leanh::LeanObject,
    mut v_a_4757_: *mut crate::leanh::LeanObject,
    mut v_a_4758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4769_: u8 = 0;
    let mut v___x_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4773_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4760_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(
                    v_c_4753_, v_a_4754_, v_a_4757_,
                );
                if crate::leanh::lean_obj_tag(v___x_4760_) == 0 {
                    v_a_4761_ = crate::leanh::lean_ctor_get(v___x_4760_, 0);
                    crate::leanh::lean_inc(v_a_4761_);
                    crate::leanh::lean_dec_ref_known(v___x_4760_, 1);
                    v___x_4762_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg___closed__1);
                    v___x_4763_ = l_Lean_indentD(v_a_4761_);
                    v___x_4764_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4764_, 0, v___x_4762_);
                    crate::leanh::lean_ctor_set(v___x_4764_, 1, v___x_4763_);
                    v___x_4765_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_4764_, v_a_4755_, v_a_4756_, v_a_4757_, v_a_4758_);
                    return v___x_4765_;
                } else {
                    v_a_4766_ = crate::leanh::lean_ctor_get(v___x_4760_, 0);
                    v_isSharedCheck_4773_ = (!crate::leanh::lean_is_exclusive(v___x_4760_)) as u8;
                    if v_isSharedCheck_4773_ == 0 {
                        v___x_4768_ = v___x_4760_;
                        v_isShared_4769_ = v_isSharedCheck_4773_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4766_);
                        crate::leanh::lean_dec(v___x_4760_);
                        v___x_4768_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4772_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4772_, 0, v_a_4766_);
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
    mut v_c_4774_: *mut crate::leanh::LeanObject,
    mut v_a_4775_: *mut crate::leanh::LeanObject,
    mut v_a_4776_: *mut crate::leanh::LeanObject,
    mut v_a_4777_: *mut crate::leanh::LeanObject,
    mut v_a_4778_: *mut crate::leanh::LeanObject,
    mut v_a_4779_: *mut crate::leanh::LeanObject,
    mut v_a_4780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4781_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(
        v_c_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_,
    );
    crate::leanh::lean_dec(v_a_4779_);
    crate::leanh::lean_dec_ref(v_a_4778_);
    crate::leanh::lean_dec(v_a_4777_);
    crate::leanh::lean_dec_ref(v_a_4776_);
    crate::leanh::lean_dec(v_a_4775_);
    return v_res_4781_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected(
    mut v_00_u03b1_4782_: *mut crate::leanh::LeanObject,
    mut v_c_4783_: *mut crate::leanh::LeanObject,
    mut v_a_4784_: *mut crate::leanh::LeanObject,
    mut v_a_4785_: *mut crate::leanh::LeanObject,
    mut v_a_4786_: *mut crate::leanh::LeanObject,
    mut v_a_4787_: *mut crate::leanh::LeanObject,
    mut v_a_4788_: *mut crate::leanh::LeanObject,
    mut v_a_4789_: *mut crate::leanh::LeanObject,
    mut v_a_4790_: *mut crate::leanh::LeanObject,
    mut v_a_4791_: *mut crate::leanh::LeanObject,
    mut v_a_4792_: *mut crate::leanh::LeanObject,
    mut v_a_4793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4795_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___redArg(
        v_c_4783_, v_a_4784_, v_a_4790_, v_a_4791_, v_a_4792_, v_a_4793_,
    );
    return v___x_4795_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_throwUnexpected___boxed(
    mut v_00_u03b1_4796_: *mut crate::leanh::LeanObject,
    mut v_c_4797_: *mut crate::leanh::LeanObject,
    mut v_a_4798_: *mut crate::leanh::LeanObject,
    mut v_a_4799_: *mut crate::leanh::LeanObject,
    mut v_a_4800_: *mut crate::leanh::LeanObject,
    mut v_a_4801_: *mut crate::leanh::LeanObject,
    mut v_a_4802_: *mut crate::leanh::LeanObject,
    mut v_a_4803_: *mut crate::leanh::LeanObject,
    mut v_a_4804_: *mut crate::leanh::LeanObject,
    mut v_a_4805_: *mut crate::leanh::LeanObject,
    mut v_a_4806_: *mut crate::leanh::LeanObject,
    mut v_a_4807_: *mut crate::leanh::LeanObject,
    mut v_a_4808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_4807_);
    crate::leanh::lean_dec_ref(v_a_4806_);
    crate::leanh::lean_dec(v_a_4805_);
    crate::leanh::lean_dec_ref(v_a_4804_);
    crate::leanh::lean_dec(v_a_4803_);
    crate::leanh::lean_dec_ref(v_a_4802_);
    crate::leanh::lean_dec(v_a_4801_);
    crate::leanh::lean_dec_ref(v_a_4800_);
    crate::leanh::lean_dec(v_a_4799_);
    crate::leanh::lean_dec(v_a_4798_);
    return v_res_4809_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(
    mut v_x_4810_: *mut crate::leanh::LeanObject,
    mut v_a_4811_: *mut crate::leanh::LeanObject,
    mut v_a_4812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4818_: u8 = 0;
    let mut v_occurs_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: u8 = 0;
    let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4831_: u8 = 0;
    let mut v_a_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4835_: u8 = 0;
    let mut v___x_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4839_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4814_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_4811_, v_a_4812_);
                if crate::leanh::lean_obj_tag(v___x_4814_) == 0 {
                    v_a_4815_ = crate::leanh::lean_ctor_get(v___x_4814_, 0);
                    v_isSharedCheck_4831_ = (!crate::leanh::lean_is_exclusive(v___x_4814_)) as u8;
                    if v_isSharedCheck_4831_ == 0 {
                        v___x_4817_ = v___x_4814_;
                        v_isShared_4818_ = v_isSharedCheck_4831_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4815_);
                        crate::leanh::lean_dec(v___x_4814_);
                        v___x_4817_ = crate::leanh::lean_box(0);
                        v_isShared_4818_ = v_isSharedCheck_4831_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4832_ = crate::leanh::lean_ctor_get(v___x_4814_, 0);
                    v_isSharedCheck_4839_ = (!crate::leanh::lean_is_exclusive(v___x_4814_)) as u8;
                    if v_isSharedCheck_4839_ == 0 {
                        v___x_4834_ = v___x_4814_;
                        v_isShared_4835_ = v_isSharedCheck_4839_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4832_);
                        crate::leanh::lean_dec(v___x_4814_);
                        v___x_4834_ = crate::leanh::lean_box(0);
                        v_isShared_4835_ = v_isSharedCheck_4839_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_occurs_4819_ = crate::leanh::lean_ctor_get(v_a_4815_, 12);
                crate::leanh::lean_inc_ref(v_occurs_4819_);
                crate::leanh::lean_dec(v_a_4815_);
                v_size_4820_ = crate::leanh::lean_ctor_get(v_occurs_4819_, 2);
                v___x_4821_ = crate::leanh::lean_box(1);
                v___x_4822_ = lean_nat_dec_lt(v_x_4810_, v_size_4820_);
                if v___x_4822_ == 0 {
                    crate::leanh::lean_dec_ref(v_occurs_4819_);
                    v___x_4823_ = l_outOfBounds___redArg(v___x_4821_);
                    if v_isShared_4818_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4817_, 0, v___x_4823_);
                        v___x_4825_ = v___x_4817_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4826_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4826_, 0, v___x_4823_);
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
                    crate::leanh::lean_dec_ref(v_occurs_4819_);
                    if v_isShared_4818_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4817_, 0, v___x_4827_);
                        v___x_4829_ = v___x_4817_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4830_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4830_, 0, v___x_4827_);
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
                    v_reuseFailAlloc_4838_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4838_, 0, v_a_4832_);
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
    mut v_x_4840_: *mut crate::leanh::LeanObject,
    mut v_a_4841_: *mut crate::leanh::LeanObject,
    mut v_a_4842_: *mut crate::leanh::LeanObject,
    mut v_a_4843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4844_ =
        l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_4840_, v_a_4841_, v_a_4842_);
    crate::leanh::lean_dec_ref(v_a_4842_);
    crate::leanh::lean_dec(v_a_4841_);
    crate::leanh::lean_dec(v_x_4840_);
    return v_res_4844_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(
    mut v_x_4845_: *mut crate::leanh::LeanObject,
    mut v_a_4846_: *mut crate::leanh::LeanObject,
    mut v_a_4847_: *mut crate::leanh::LeanObject,
    mut v_a_4848_: *mut crate::leanh::LeanObject,
    mut v_a_4849_: *mut crate::leanh::LeanObject,
    mut v_a_4850_: *mut crate::leanh::LeanObject,
    mut v_a_4851_: *mut crate::leanh::LeanObject,
    mut v_a_4852_: *mut crate::leanh::LeanObject,
    mut v_a_4853_: *mut crate::leanh::LeanObject,
    mut v_a_4854_: *mut crate::leanh::LeanObject,
    mut v_a_4855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4857_ =
        l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(v_x_4845_, v_a_4846_, v_a_4854_);
    return v___x_4857_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___boxed(
    mut v_x_4858_: *mut crate::leanh::LeanObject,
    mut v_a_4859_: *mut crate::leanh::LeanObject,
    mut v_a_4860_: *mut crate::leanh::LeanObject,
    mut v_a_4861_: *mut crate::leanh::LeanObject,
    mut v_a_4862_: *mut crate::leanh::LeanObject,
    mut v_a_4863_: *mut crate::leanh::LeanObject,
    mut v_a_4864_: *mut crate::leanh::LeanObject,
    mut v_a_4865_: *mut crate::leanh::LeanObject,
    mut v_a_4866_: *mut crate::leanh::LeanObject,
    mut v_a_4867_: *mut crate::leanh::LeanObject,
    mut v_a_4868_: *mut crate::leanh::LeanObject,
    mut v_a_4869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4870_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf(
        v_x_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_,
        v_a_4866_, v_a_4867_, v_a_4868_,
    );
    crate::leanh::lean_dec(v_a_4868_);
    crate::leanh::lean_dec_ref(v_a_4867_);
    crate::leanh::lean_dec(v_a_4866_);
    crate::leanh::lean_dec_ref(v_a_4865_);
    crate::leanh::lean_dec(v_a_4864_);
    crate::leanh::lean_dec_ref(v_a_4863_);
    crate::leanh::lean_dec(v_a_4862_);
    crate::leanh::lean_dec_ref(v_a_4861_);
    crate::leanh::lean_dec(v_a_4860_);
    crate::leanh::lean_dec(v_a_4859_);
    crate::leanh::lean_dec(v_x_4858_);
    return v_res_4870_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(
    mut v_k_4871_: *mut crate::leanh::LeanObject,
    mut v_v_4872_: *mut crate::leanh::LeanObject,
    mut v_t_4873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4881_: u8 = 0;
    let mut v___x_4882_: u8 = 0;
    let mut v___x_4883_: u8 = 0;
    let mut v_impl_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: u8 = 0;
    let mut v___x_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4902_: u8 = 0;
    let mut v_size_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: u8 = 0;
    let mut v___x_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4914_: u8 = 0;
    let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4939_: u8 = 0;
    let mut v_unused_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4952_: u8 = 0;
    let mut v___x_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4956_: u8 = 0;
    let mut v_unused_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4963_: u8 = 0;
    let mut v_unused_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4975_: u8 = 0;
    let mut v_k_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4980_: u8 = 0;
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4991_: u8 = 0;
    let mut v_unused_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4995_: u8 = 0;
    let mut v_unused_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5003_: u8 = 0;
    let mut v___x_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5011_: u8 = 0;
    let mut v_unused_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: u8 = 0;
    let mut v___x_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5040_: u8 = 0;
    let mut v_size_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: u8 = 0;
    let mut v___x_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5052_: u8 = 0;
    let mut v___x_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5078_: u8 = 0;
    let mut v_unused_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5092_: u8 = 0;
    let mut v___x_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5096_: u8 = 0;
    let mut v_unused_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5103_: u8 = 0;
    let mut v_unused_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5115_: u8 = 0;
    let mut v___x_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5123_: u8 = 0;
    let mut v_unused_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5131_: u8 = 0;
    let mut v_k_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5136_: u8 = 0;
    let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5147_: u8 = 0;
    let mut v_unused_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5151_: u8 = 0;
    let mut v_unused_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5159_: u8 = 0;
    let mut v___x_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_4873_) == 0 {
                    v_size_4874_ = crate::leanh::lean_ctor_get(v_t_4873_, 0);
                    v_k_4875_ = crate::leanh::lean_ctor_get(v_t_4873_, 1);
                    v_v_4876_ = crate::leanh::lean_ctor_get(v_t_4873_, 2);
                    v_l_4877_ = crate::leanh::lean_ctor_get(v_t_4873_, 3);
                    v_r_4878_ = crate::leanh::lean_ctor_get(v_t_4873_, 4);
                    v_isSharedCheck_5159_ = (!crate::leanh::lean_is_exclusive(v_t_4873_)) as u8;
                    if v_isSharedCheck_5159_ == 0 {
                        v___x_4880_ = v_t_4873_;
                        v_isShared_4881_ = v_isSharedCheck_5159_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_4878_);
                        crate::leanh::lean_inc(v_l_4877_);
                        crate::leanh::lean_inc(v_v_4876_);
                        crate::leanh::lean_inc(v_k_4875_);
                        crate::leanh::lean_inc(v_size_4874_);
                        crate::leanh::lean_dec(v_t_4873_);
                        v___x_4880_ = crate::leanh::lean_box(0);
                        v_isShared_4881_ = v_isSharedCheck_5159_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_5160_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5161_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5161_, 0, v___x_5160_);
                    crate::leanh::lean_ctor_set(v___x_5161_, 1, v_k_4871_);
                    crate::leanh::lean_ctor_set(v___x_5161_, 2, v_v_4872_);
                    crate::leanh::lean_ctor_set(v___x_5161_, 3, v_t_4873_);
                    crate::leanh::lean_ctor_set(v___x_5161_, 4, v_t_4873_);
                    return v___x_5161_;
                }
            }
            1 => {
                v___x_4882_ = lean_nat_dec_lt(v_k_4871_, v_k_4875_);
                if v___x_4882_ == 0 {
                    v___x_4883_ = lean_nat_dec_eq(v_k_4871_, v_k_4875_);
                    if v___x_4883_ == 0 {
                        crate::leanh::lean_dec(v_size_4874_);
                        v_impl_4884_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_4871_, v_v_4872_, v_r_4878_);
                        v___x_4885_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_l_4877_) == 0 {
                            v_size_4886_ = crate::leanh::lean_ctor_get(v_l_4877_, 0);
                            v_size_4887_ = crate::leanh::lean_ctor_get(v_impl_4884_, 0);
                            crate::leanh::lean_inc(v_size_4887_);
                            v_k_4888_ = crate::leanh::lean_ctor_get(v_impl_4884_, 1);
                            crate::leanh::lean_inc(v_k_4888_);
                            v_v_4889_ = crate::leanh::lean_ctor_get(v_impl_4884_, 2);
                            crate::leanh::lean_inc(v_v_4889_);
                            v_l_4890_ = crate::leanh::lean_ctor_get(v_impl_4884_, 3);
                            crate::leanh::lean_inc(v_l_4890_);
                            v_r_4891_ = crate::leanh::lean_ctor_get(v_impl_4884_, 4);
                            crate::leanh::lean_inc(v_r_4891_);
                            v___x_4892_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_4893_ = lean_nat_mul(v___x_4892_, v_size_4886_);
                            v___x_4894_ = lean_nat_dec_lt(v___x_4893_, v_size_4887_);
                            crate::leanh::lean_dec(v___x_4893_);
                            if v___x_4894_ == 0 {
                                crate::leanh::lean_dec(v_r_4891_);
                                crate::leanh::lean_dec(v_l_4890_);
                                crate::leanh::lean_dec(v_v_4889_);
                                crate::leanh::lean_dec(v_k_4888_);
                                v___x_4895_ = lean_nat_add(v___x_4885_, v_size_4886_);
                                v___x_4896_ = lean_nat_add(v___x_4895_, v_size_4887_);
                                crate::leanh::lean_dec(v_size_4887_);
                                crate::leanh::lean_dec(v___x_4895_);
                                if v_isShared_4881_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_4880_, 4, v_impl_4884_);
                                    crate::leanh::lean_ctor_set(v___x_4880_, 0, v___x_4896_);
                                    v___x_4898_ = v___x_4880_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4899_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4899_,
                                        0,
                                        v___x_4896_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4899_,
                                        1,
                                        v_k_4875_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4899_,
                                        2,
                                        v_v_4876_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4899_,
                                        3,
                                        v_l_4877_,
                                    );
                                    crate::leanh::lean_ctor_set(
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
                                    (!crate::leanh::lean_is_exclusive(v_impl_4884_)) as u8;
                                if v_isSharedCheck_4963_ == 0 {
                                    v_unused_4964_ = crate::leanh::lean_ctor_get(v_impl_4884_, 4);
                                    crate::leanh::lean_dec(v_unused_4964_);
                                    v_unused_4965_ = crate::leanh::lean_ctor_get(v_impl_4884_, 3);
                                    crate::leanh::lean_dec(v_unused_4965_);
                                    v_unused_4966_ = crate::leanh::lean_ctor_get(v_impl_4884_, 2);
                                    crate::leanh::lean_dec(v_unused_4966_);
                                    v_unused_4967_ = crate::leanh::lean_ctor_get(v_impl_4884_, 1);
                                    crate::leanh::lean_dec(v_unused_4967_);
                                    v_unused_4968_ = crate::leanh::lean_ctor_get(v_impl_4884_, 0);
                                    crate::leanh::lean_dec(v_unused_4968_);
                                    v___x_4901_ = v_impl_4884_;
                                    v_isShared_4902_ = v_isSharedCheck_4963_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_4884_);
                                    v___x_4901_ = crate::leanh::lean_box(0);
                                    v_isShared_4902_ = v_isSharedCheck_4963_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_4969_ = crate::leanh::lean_ctor_get(v_impl_4884_, 3);
                            crate::leanh::lean_inc(v_l_4969_);
                            if crate::leanh::lean_obj_tag(v_l_4969_) == 0 {
                                v_r_4970_ = crate::leanh::lean_ctor_get(v_impl_4884_, 4);
                                v_k_4971_ = crate::leanh::lean_ctor_get(v_impl_4884_, 1);
                                v_v_4972_ = crate::leanh::lean_ctor_get(v_impl_4884_, 2);
                                v_isSharedCheck_4995_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_4884_)) as u8;
                                if v_isSharedCheck_4995_ == 0 {
                                    v_unused_4996_ = crate::leanh::lean_ctor_get(v_impl_4884_, 3);
                                    crate::leanh::lean_dec(v_unused_4996_);
                                    v_unused_4997_ = crate::leanh::lean_ctor_get(v_impl_4884_, 0);
                                    crate::leanh::lean_dec(v_unused_4997_);
                                    v___x_4974_ = v_impl_4884_;
                                    v_isShared_4975_ = v_isSharedCheck_4995_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_4970_);
                                    crate::leanh::lean_inc(v_v_4972_);
                                    crate::leanh::lean_inc(v_k_4971_);
                                    crate::leanh::lean_dec(v_impl_4884_);
                                    v___x_4974_ = crate::leanh::lean_box(0);
                                    v_isShared_4975_ = v_isSharedCheck_4995_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_4998_ = crate::leanh::lean_ctor_get(v_impl_4884_, 4);
                                crate::leanh::lean_inc(v_r_4998_);
                                if crate::leanh::lean_obj_tag(v_r_4998_) == 0 {
                                    v_k_4999_ = crate::leanh::lean_ctor_get(v_impl_4884_, 1);
                                    v_v_5000_ = crate::leanh::lean_ctor_get(v_impl_4884_, 2);
                                    v_isSharedCheck_5011_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_4884_)) as u8;
                                    if v_isSharedCheck_5011_ == 0 {
                                        v_unused_5012_ =
                                            crate::leanh::lean_ctor_get(v_impl_4884_, 4);
                                        crate::leanh::lean_dec(v_unused_5012_);
                                        v_unused_5013_ =
                                            crate::leanh::lean_ctor_get(v_impl_4884_, 3);
                                        crate::leanh::lean_dec(v_unused_5013_);
                                        v_unused_5014_ =
                                            crate::leanh::lean_ctor_get(v_impl_4884_, 0);
                                        crate::leanh::lean_dec(v_unused_5014_);
                                        v___x_5002_ = v_impl_4884_;
                                        v_isShared_5003_ = v_isSharedCheck_5011_;
                                        state = 18;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_5000_);
                                        crate::leanh::lean_inc(v_k_4999_);
                                        crate::leanh::lean_dec(v_impl_4884_);
                                        v___x_5002_ = crate::leanh::lean_box(0);
                                        v_isShared_5003_ = v_isSharedCheck_5011_;
                                        state = 18;
                                        continue;
                                    }
                                } else {
                                    v___x_5015_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_4881_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_4880_, 4, v_impl_4884_);
                                        crate::leanh::lean_ctor_set(v___x_4880_, 3, v_r_4998_);
                                        crate::leanh::lean_ctor_set(v___x_4880_, 0, v___x_5015_);
                                        v___x_5017_ = v___x_4880_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_5018_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5018_,
                                            0,
                                            v___x_5015_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5018_,
                                            1,
                                            v_k_4875_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5018_,
                                            2,
                                            v_v_4876_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5018_,
                                            3,
                                            v_r_4998_,
                                        );
                                        crate::leanh::lean_ctor_set(
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
                        crate::leanh::lean_dec(v_v_4876_);
                        crate::leanh::lean_dec(v_k_4875_);
                        if v_isShared_4881_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4880_, 2, v_v_4872_);
                            crate::leanh::lean_ctor_set(v___x_4880_, 1, v_k_4871_);
                            v___x_5020_ = v___x_4880_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_5021_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5021_, 0, v_size_4874_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5021_, 1, v_k_4871_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5021_, 2, v_v_4872_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5021_, 3, v_l_4877_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5021_, 4, v_r_4878_);
                            v___x_5020_ = v_reuseFailAlloc_5021_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_size_4874_);
                    v_impl_5022_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_4871_, v_v_4872_, v_l_4877_);
                    v___x_5023_ = crate::leanh::lean_unsigned_to_nat(1);
                    if crate::leanh::lean_obj_tag(v_r_4878_) == 0 {
                        v_size_5024_ = crate::leanh::lean_ctor_get(v_r_4878_, 0);
                        v_size_5025_ = crate::leanh::lean_ctor_get(v_impl_5022_, 0);
                        crate::leanh::lean_inc(v_size_5025_);
                        v_k_5026_ = crate::leanh::lean_ctor_get(v_impl_5022_, 1);
                        crate::leanh::lean_inc(v_k_5026_);
                        v_v_5027_ = crate::leanh::lean_ctor_get(v_impl_5022_, 2);
                        crate::leanh::lean_inc(v_v_5027_);
                        v_l_5028_ = crate::leanh::lean_ctor_get(v_impl_5022_, 3);
                        crate::leanh::lean_inc(v_l_5028_);
                        v_r_5029_ = crate::leanh::lean_ctor_get(v_impl_5022_, 4);
                        crate::leanh::lean_inc(v_r_5029_);
                        v___x_5030_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_5031_ = lean_nat_mul(v___x_5030_, v_size_5024_);
                        v___x_5032_ = lean_nat_dec_lt(v___x_5031_, v_size_5025_);
                        crate::leanh::lean_dec(v___x_5031_);
                        if v___x_5032_ == 0 {
                            crate::leanh::lean_dec(v_r_5029_);
                            crate::leanh::lean_dec(v_l_5028_);
                            crate::leanh::lean_dec(v_v_5027_);
                            crate::leanh::lean_dec(v_k_5026_);
                            v___x_5033_ = lean_nat_add(v___x_5023_, v_size_5025_);
                            crate::leanh::lean_dec(v_size_5025_);
                            v___x_5034_ = lean_nat_add(v___x_5033_, v_size_5024_);
                            crate::leanh::lean_dec(v___x_5033_);
                            if v_isShared_4881_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4880_, 3, v_impl_5022_);
                                crate::leanh::lean_ctor_set(v___x_4880_, 0, v___x_5034_);
                                v___x_5036_ = v___x_4880_;
                                state = 23;
                                continue;
                            } else {
                                v_reuseFailAlloc_5037_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5037_, 0, v___x_5034_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5037_, 1, v_k_4875_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5037_, 2, v_v_4876_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_5037_,
                                    3,
                                    v_impl_5022_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5037_, 4, v_r_4878_);
                                v___x_5036_ = v_reuseFailAlloc_5037_;
                                state = 23;
                                continue;
                            }
                        } else {
                            v_isSharedCheck_5103_ =
                                (!crate::leanh::lean_is_exclusive(v_impl_5022_)) as u8;
                            if v_isSharedCheck_5103_ == 0 {
                                v_unused_5104_ = crate::leanh::lean_ctor_get(v_impl_5022_, 4);
                                crate::leanh::lean_dec(v_unused_5104_);
                                v_unused_5105_ = crate::leanh::lean_ctor_get(v_impl_5022_, 3);
                                crate::leanh::lean_dec(v_unused_5105_);
                                v_unused_5106_ = crate::leanh::lean_ctor_get(v_impl_5022_, 2);
                                crate::leanh::lean_dec(v_unused_5106_);
                                v_unused_5107_ = crate::leanh::lean_ctor_get(v_impl_5022_, 1);
                                crate::leanh::lean_dec(v_unused_5107_);
                                v_unused_5108_ = crate::leanh::lean_ctor_get(v_impl_5022_, 0);
                                crate::leanh::lean_dec(v_unused_5108_);
                                v___x_5039_ = v_impl_5022_;
                                v_isShared_5040_ = v_isSharedCheck_5103_;
                                state = 24;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_impl_5022_);
                                v___x_5039_ = crate::leanh::lean_box(0);
                                v_isShared_5040_ = v_isSharedCheck_5103_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        v_l_5109_ = crate::leanh::lean_ctor_get(v_impl_5022_, 3);
                        crate::leanh::lean_inc(v_l_5109_);
                        if crate::leanh::lean_obj_tag(v_l_5109_) == 0 {
                            v_r_5110_ = crate::leanh::lean_ctor_get(v_impl_5022_, 4);
                            v_k_5111_ = crate::leanh::lean_ctor_get(v_impl_5022_, 1);
                            v_v_5112_ = crate::leanh::lean_ctor_get(v_impl_5022_, 2);
                            v_isSharedCheck_5123_ =
                                (!crate::leanh::lean_is_exclusive(v_impl_5022_)) as u8;
                            if v_isSharedCheck_5123_ == 0 {
                                v_unused_5124_ = crate::leanh::lean_ctor_get(v_impl_5022_, 3);
                                crate::leanh::lean_dec(v_unused_5124_);
                                v_unused_5125_ = crate::leanh::lean_ctor_get(v_impl_5022_, 0);
                                crate::leanh::lean_dec(v_unused_5125_);
                                v___x_5114_ = v_impl_5022_;
                                v_isShared_5115_ = v_isSharedCheck_5123_;
                                state = 34;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_r_5110_);
                                crate::leanh::lean_inc(v_v_5112_);
                                crate::leanh::lean_inc(v_k_5111_);
                                crate::leanh::lean_dec(v_impl_5022_);
                                v___x_5114_ = crate::leanh::lean_box(0);
                                v_isShared_5115_ = v_isSharedCheck_5123_;
                                state = 34;
                                continue;
                            }
                        } else {
                            v_r_5126_ = crate::leanh::lean_ctor_get(v_impl_5022_, 4);
                            crate::leanh::lean_inc(v_r_5126_);
                            if crate::leanh::lean_obj_tag(v_r_5126_) == 0 {
                                v_k_5127_ = crate::leanh::lean_ctor_get(v_impl_5022_, 1);
                                v_v_5128_ = crate::leanh::lean_ctor_get(v_impl_5022_, 2);
                                v_isSharedCheck_5151_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_5022_)) as u8;
                                if v_isSharedCheck_5151_ == 0 {
                                    v_unused_5152_ = crate::leanh::lean_ctor_get(v_impl_5022_, 4);
                                    crate::leanh::lean_dec(v_unused_5152_);
                                    v_unused_5153_ = crate::leanh::lean_ctor_get(v_impl_5022_, 3);
                                    crate::leanh::lean_dec(v_unused_5153_);
                                    v_unused_5154_ = crate::leanh::lean_ctor_get(v_impl_5022_, 0);
                                    crate::leanh::lean_dec(v_unused_5154_);
                                    v___x_5130_ = v_impl_5022_;
                                    v_isShared_5131_ = v_isSharedCheck_5151_;
                                    state = 37;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_v_5128_);
                                    crate::leanh::lean_inc(v_k_5127_);
                                    crate::leanh::lean_dec(v_impl_5022_);
                                    v___x_5130_ = crate::leanh::lean_box(0);
                                    v_isShared_5131_ = v_isSharedCheck_5151_;
                                    state = 37;
                                    continue;
                                }
                            } else {
                                v___x_5155_ = crate::leanh::lean_unsigned_to_nat(2);
                                if v_isShared_4881_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_4880_, 4, v_r_5126_);
                                    crate::leanh::lean_ctor_set(v___x_4880_, 3, v_impl_5022_);
                                    crate::leanh::lean_ctor_set(v___x_4880_, 0, v___x_5155_);
                                    v___x_5157_ = v___x_4880_;
                                    state = 42;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_5158_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5158_,
                                        0,
                                        v___x_5155_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5158_,
                                        1,
                                        v_k_4875_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5158_,
                                        2,
                                        v_v_4876_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5158_,
                                        3,
                                        v_impl_5022_,
                                    );
                                    crate::leanh::lean_ctor_set(
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
                v_size_4903_ = crate::leanh::lean_ctor_get(v_l_4890_, 0);
                v_k_4904_ = crate::leanh::lean_ctor_get(v_l_4890_, 1);
                v_v_4905_ = crate::leanh::lean_ctor_get(v_l_4890_, 2);
                v_l_4906_ = crate::leanh::lean_ctor_get(v_l_4890_, 3);
                v_r_4907_ = crate::leanh::lean_ctor_get(v_l_4890_, 4);
                v_size_4908_ = crate::leanh::lean_ctor_get(v_r_4891_, 0);
                v___x_4909_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_4910_ = lean_nat_mul(v___x_4909_, v_size_4908_);
                v___x_4911_ = lean_nat_dec_lt(v_size_4903_, v___x_4910_);
                crate::leanh::lean_dec(v___x_4910_);
                if v___x_4911_ == 0 {
                    crate::leanh::lean_inc(v_r_4907_);
                    crate::leanh::lean_inc(v_l_4906_);
                    crate::leanh::lean_inc(v_v_4905_);
                    crate::leanh::lean_inc(v_k_4904_);
                    v_isSharedCheck_4939_ = (!crate::leanh::lean_is_exclusive(v_l_4890_)) as u8;
                    if v_isSharedCheck_4939_ == 0 {
                        v_unused_4940_ = crate::leanh::lean_ctor_get(v_l_4890_, 4);
                        crate::leanh::lean_dec(v_unused_4940_);
                        v_unused_4941_ = crate::leanh::lean_ctor_get(v_l_4890_, 3);
                        crate::leanh::lean_dec(v_unused_4941_);
                        v_unused_4942_ = crate::leanh::lean_ctor_get(v_l_4890_, 2);
                        crate::leanh::lean_dec(v_unused_4942_);
                        v_unused_4943_ = crate::leanh::lean_ctor_get(v_l_4890_, 1);
                        crate::leanh::lean_dec(v_unused_4943_);
                        v_unused_4944_ = crate::leanh::lean_ctor_get(v_l_4890_, 0);
                        crate::leanh::lean_dec(v_unused_4944_);
                        v___x_4913_ = v_l_4890_;
                        v_isShared_4914_ = v_isSharedCheck_4939_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_4890_);
                        v___x_4913_ = crate::leanh::lean_box(0);
                        v_isShared_4914_ = v_isSharedCheck_4939_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4880_);
                    v___x_4945_ = lean_nat_add(v___x_4885_, v_size_4886_);
                    v___x_4946_ = lean_nat_add(v___x_4945_, v_size_4887_);
                    crate::leanh::lean_dec(v_size_4887_);
                    v___x_4947_ = lean_nat_add(v___x_4945_, v_size_4903_);
                    crate::leanh::lean_dec(v___x_4945_);
                    crate::leanh::lean_inc_ref(v_l_4877_);
                    if v_isShared_4902_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4901_, 4, v_l_4890_);
                        crate::leanh::lean_ctor_set(v___x_4901_, 3, v_l_4877_);
                        crate::leanh::lean_ctor_set(v___x_4901_, 2, v_v_4876_);
                        crate::leanh::lean_ctor_set(v___x_4901_, 1, v_k_4875_);
                        crate::leanh::lean_ctor_set(v___x_4901_, 0, v___x_4947_);
                        v___x_4949_ = v___x_4901_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4962_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4962_, 0, v___x_4947_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4962_, 1, v_k_4875_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4962_, 2, v_v_4876_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4962_, 3, v_l_4877_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4962_, 4, v_l_4890_);
                        v___x_4949_ = v_reuseFailAlloc_4962_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_4915_ = lean_nat_add(v___x_4885_, v_size_4886_);
                v___x_4916_ = lean_nat_add(v___x_4915_, v_size_4887_);
                crate::leanh::lean_dec(v_size_4887_);
                if crate::leanh::lean_obj_tag(v_l_4906_) == 0 {
                    v_size_4937_ = crate::leanh::lean_ctor_get(v_l_4906_, 0);
                    crate::leanh::lean_inc(v_size_4937_);
                    v___y_4929_ = v_size_4937_;
                    state = 8;
                    continue;
                } else {
                    v___x_4938_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4929_ = v___x_4938_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_4921_ = lean_nat_add(v___y_4918_, v___y_4920_);
                crate::leanh::lean_dec(v___y_4920_);
                crate::leanh::lean_dec(v___y_4918_);
                if v_isShared_4914_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4913_, 4, v_r_4891_);
                    crate::leanh::lean_ctor_set(v___x_4913_, 3, v_r_4907_);
                    crate::leanh::lean_ctor_set(v___x_4913_, 2, v_v_4889_);
                    crate::leanh::lean_ctor_set(v___x_4913_, 1, v_k_4888_);
                    crate::leanh::lean_ctor_set(v___x_4913_, 0, v___x_4921_);
                    v___x_4923_ = v___x_4913_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4927_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4927_, 0, v___x_4921_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4927_, 1, v_k_4888_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4927_, 2, v_v_4889_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4927_, 3, v_r_4907_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4927_, 4, v_r_4891_);
                    v___x_4923_ = v_reuseFailAlloc_4927_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4902_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4901_, 4, v___x_4923_);
                    crate::leanh::lean_ctor_set(v___x_4901_, 3, v___y_4919_);
                    crate::leanh::lean_ctor_set(v___x_4901_, 2, v_v_4905_);
                    crate::leanh::lean_ctor_set(v___x_4901_, 1, v_k_4904_);
                    crate::leanh::lean_ctor_set(v___x_4901_, 0, v___x_4916_);
                    v___x_4925_ = v___x_4901_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4926_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4926_, 0, v___x_4916_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4926_, 1, v_k_4904_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4926_, 2, v_v_4905_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4926_, 3, v___y_4919_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4926_, 4, v___x_4923_);
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
                crate::leanh::lean_dec(v___y_4929_);
                crate::leanh::lean_dec(v___x_4915_);
                if v_isShared_4881_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4880_, 4, v_l_4906_);
                    crate::leanh::lean_ctor_set(v___x_4880_, 0, v___x_4930_);
                    v___x_4932_ = v___x_4880_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4936_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4936_, 0, v___x_4930_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4936_, 1, v_k_4875_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4936_, 2, v_v_4876_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4936_, 3, v_l_4877_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4936_, 4, v_l_4906_);
                    v___x_4932_ = v_reuseFailAlloc_4936_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_4933_ = lean_nat_add(v___x_4885_, v_size_4908_);
                if crate::leanh::lean_obj_tag(v_r_4907_) == 0 {
                    v_size_4934_ = crate::leanh::lean_ctor_get(v_r_4907_, 0);
                    crate::leanh::lean_inc(v_size_4934_);
                    v___y_4918_ = v___x_4933_;
                    v___y_4919_ = v___x_4932_;
                    v___y_4920_ = v_size_4934_;
                    state = 5;
                    continue;
                } else {
                    v___x_4935_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4918_ = v___x_4933_;
                    v___y_4919_ = v___x_4932_;
                    v___y_4920_ = v___x_4935_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_4956_ = (!crate::leanh::lean_is_exclusive(v_l_4877_)) as u8;
                if v_isSharedCheck_4956_ == 0 {
                    v_unused_4957_ = crate::leanh::lean_ctor_get(v_l_4877_, 4);
                    crate::leanh::lean_dec(v_unused_4957_);
                    v_unused_4958_ = crate::leanh::lean_ctor_get(v_l_4877_, 3);
                    crate::leanh::lean_dec(v_unused_4958_);
                    v_unused_4959_ = crate::leanh::lean_ctor_get(v_l_4877_, 2);
                    crate::leanh::lean_dec(v_unused_4959_);
                    v_unused_4960_ = crate::leanh::lean_ctor_get(v_l_4877_, 1);
                    crate::leanh::lean_dec(v_unused_4960_);
                    v_unused_4961_ = crate::leanh::lean_ctor_get(v_l_4877_, 0);
                    crate::leanh::lean_dec(v_unused_4961_);
                    v___x_4951_ = v_l_4877_;
                    v_isShared_4952_ = v_isSharedCheck_4956_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_4877_);
                    v___x_4951_ = crate::leanh::lean_box(0);
                    v_isShared_4952_ = v_isSharedCheck_4956_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_4952_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4951_, 4, v_r_4891_);
                    crate::leanh::lean_ctor_set(v___x_4951_, 3, v___x_4949_);
                    crate::leanh::lean_ctor_set(v___x_4951_, 2, v_v_4889_);
                    crate::leanh::lean_ctor_set(v___x_4951_, 1, v_k_4888_);
                    crate::leanh::lean_ctor_set(v___x_4951_, 0, v___x_4946_);
                    v___x_4954_ = v___x_4951_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4955_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4955_, 0, v___x_4946_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4955_, 1, v_k_4888_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4955_, 2, v_v_4889_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4955_, 3, v___x_4949_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4955_, 4, v_r_4891_);
                    v___x_4954_ = v_reuseFailAlloc_4955_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4954_;
            }
            13 => {
                v_k_4976_ = crate::leanh::lean_ctor_get(v_l_4969_, 1);
                v_v_4977_ = crate::leanh::lean_ctor_get(v_l_4969_, 2);
                v_isSharedCheck_4991_ = (!crate::leanh::lean_is_exclusive(v_l_4969_)) as u8;
                if v_isSharedCheck_4991_ == 0 {
                    v_unused_4992_ = crate::leanh::lean_ctor_get(v_l_4969_, 4);
                    crate::leanh::lean_dec(v_unused_4992_);
                    v_unused_4993_ = crate::leanh::lean_ctor_get(v_l_4969_, 3);
                    crate::leanh::lean_dec(v_unused_4993_);
                    v_unused_4994_ = crate::leanh::lean_ctor_get(v_l_4969_, 0);
                    crate::leanh::lean_dec(v_unused_4994_);
                    v___x_4979_ = v_l_4969_;
                    v_isShared_4980_ = v_isSharedCheck_4991_;
                    state = 14;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_4977_);
                    crate::leanh::lean_inc(v_k_4976_);
                    crate::leanh::lean_dec(v_l_4969_);
                    v___x_4979_ = crate::leanh::lean_box(0);
                    v_isShared_4980_ = v_isSharedCheck_4991_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_4981_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc_n(v_r_4970_, 2);
                if v_isShared_4980_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4979_, 4, v_r_4970_);
                    crate::leanh::lean_ctor_set(v___x_4979_, 3, v_r_4970_);
                    crate::leanh::lean_ctor_set(v___x_4979_, 2, v_v_4876_);
                    crate::leanh::lean_ctor_set(v___x_4979_, 1, v_k_4875_);
                    crate::leanh::lean_ctor_set(v___x_4979_, 0, v___x_4885_);
                    v___x_4983_ = v___x_4979_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4990_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4990_, 0, v___x_4885_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4990_, 1, v_k_4875_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4990_, 2, v_v_4876_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4990_, 3, v_r_4970_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4990_, 4, v_r_4970_);
                    v___x_4983_ = v_reuseFailAlloc_4990_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                crate::leanh::lean_inc(v_r_4970_);
                if v_isShared_4975_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4974_, 3, v_r_4970_);
                    crate::leanh::lean_ctor_set(v___x_4974_, 0, v___x_4885_);
                    v___x_4985_ = v___x_4974_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4989_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4989_, 0, v___x_4885_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4989_, 1, v_k_4971_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4989_, 2, v_v_4972_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4989_, 3, v_r_4970_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4989_, 4, v_r_4970_);
                    v___x_4985_ = v_reuseFailAlloc_4989_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_4881_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4880_, 4, v___x_4985_);
                    crate::leanh::lean_ctor_set(v___x_4880_, 3, v___x_4983_);
                    crate::leanh::lean_ctor_set(v___x_4880_, 2, v_v_4977_);
                    crate::leanh::lean_ctor_set(v___x_4880_, 1, v_k_4976_);
                    crate::leanh::lean_ctor_set(v___x_4880_, 0, v___x_4981_);
                    v___x_4987_ = v___x_4880_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4988_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4988_, 0, v___x_4981_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4988_, 1, v_k_4976_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4988_, 2, v_v_4977_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4988_, 3, v___x_4983_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4988_, 4, v___x_4985_);
                    v___x_4987_ = v_reuseFailAlloc_4988_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4987_;
            }
            18 => {
                v___x_5004_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_5003_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5002_, 4, v_l_4969_);
                    crate::leanh::lean_ctor_set(v___x_5002_, 2, v_v_4876_);
                    crate::leanh::lean_ctor_set(v___x_5002_, 1, v_k_4875_);
                    crate::leanh::lean_ctor_set(v___x_5002_, 0, v___x_4885_);
                    v___x_5006_ = v___x_5002_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5010_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5010_, 0, v___x_4885_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5010_, 1, v_k_4875_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5010_, 2, v_v_4876_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5010_, 3, v_l_4969_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5010_, 4, v_l_4969_);
                    v___x_5006_ = v_reuseFailAlloc_5010_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_4881_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4880_, 4, v_r_4998_);
                    crate::leanh::lean_ctor_set(v___x_4880_, 3, v___x_5006_);
                    crate::leanh::lean_ctor_set(v___x_4880_, 2, v_v_5000_);
                    crate::leanh::lean_ctor_set(v___x_4880_, 1, v_k_4999_);
                    crate::leanh::lean_ctor_set(v___x_4880_, 0, v___x_5004_);
                    v___x_5008_ = v___x_4880_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5009_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5009_, 0, v___x_5004_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5009_, 1, v_k_4999_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5009_, 2, v_v_5000_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5009_, 3, v___x_5006_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5009_, 4, v_r_4998_);
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
                v_size_5041_ = crate::leanh::lean_ctor_get(v_l_5028_, 0);
                v_size_5042_ = crate::leanh::lean_ctor_get(v_r_5029_, 0);
                v_k_5043_ = crate::leanh::lean_ctor_get(v_r_5029_, 1);
                v_v_5044_ = crate::leanh::lean_ctor_get(v_r_5029_, 2);
                v_l_5045_ = crate::leanh::lean_ctor_get(v_r_5029_, 3);
                v_r_5046_ = crate::leanh::lean_ctor_get(v_r_5029_, 4);
                v___x_5047_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_5048_ = lean_nat_mul(v___x_5047_, v_size_5041_);
                v___x_5049_ = lean_nat_dec_lt(v_size_5042_, v___x_5048_);
                crate::leanh::lean_dec(v___x_5048_);
                if v___x_5049_ == 0 {
                    crate::leanh::lean_inc(v_r_5046_);
                    crate::leanh::lean_inc(v_l_5045_);
                    crate::leanh::lean_inc(v_v_5044_);
                    crate::leanh::lean_inc(v_k_5043_);
                    v_isSharedCheck_5078_ = (!crate::leanh::lean_is_exclusive(v_r_5029_)) as u8;
                    if v_isSharedCheck_5078_ == 0 {
                        v_unused_5079_ = crate::leanh::lean_ctor_get(v_r_5029_, 4);
                        crate::leanh::lean_dec(v_unused_5079_);
                        v_unused_5080_ = crate::leanh::lean_ctor_get(v_r_5029_, 3);
                        crate::leanh::lean_dec(v_unused_5080_);
                        v_unused_5081_ = crate::leanh::lean_ctor_get(v_r_5029_, 2);
                        crate::leanh::lean_dec(v_unused_5081_);
                        v_unused_5082_ = crate::leanh::lean_ctor_get(v_r_5029_, 1);
                        crate::leanh::lean_dec(v_unused_5082_);
                        v_unused_5083_ = crate::leanh::lean_ctor_get(v_r_5029_, 0);
                        crate::leanh::lean_dec(v_unused_5083_);
                        v___x_5051_ = v_r_5029_;
                        v_isShared_5052_ = v_isSharedCheck_5078_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_5029_);
                        v___x_5051_ = crate::leanh::lean_box(0);
                        v_isShared_5052_ = v_isSharedCheck_5078_;
                        state = 25;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4880_);
                    v___x_5084_ = lean_nat_add(v___x_5023_, v_size_5025_);
                    crate::leanh::lean_dec(v_size_5025_);
                    v___x_5085_ = lean_nat_add(v___x_5084_, v_size_5024_);
                    crate::leanh::lean_dec(v___x_5084_);
                    v___x_5086_ = lean_nat_add(v___x_5023_, v_size_5024_);
                    v___x_5087_ = lean_nat_add(v___x_5086_, v_size_5042_);
                    crate::leanh::lean_dec(v___x_5086_);
                    crate::leanh::lean_inc_ref(v_r_4878_);
                    if v_isShared_5040_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5039_, 4, v_r_4878_);
                        crate::leanh::lean_ctor_set(v___x_5039_, 3, v_r_5029_);
                        crate::leanh::lean_ctor_set(v___x_5039_, 2, v_v_4876_);
                        crate::leanh::lean_ctor_set(v___x_5039_, 1, v_k_4875_);
                        crate::leanh::lean_ctor_set(v___x_5039_, 0, v___x_5087_);
                        v___x_5089_ = v___x_5039_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_5102_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5102_, 0, v___x_5087_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5102_, 1, v_k_4875_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5102_, 2, v_v_4876_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5102_, 3, v_r_5029_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5102_, 4, v_r_4878_);
                        v___x_5089_ = v_reuseFailAlloc_5102_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_5053_ = lean_nat_add(v___x_5023_, v_size_5025_);
                crate::leanh::lean_dec(v_size_5025_);
                v___x_5054_ = lean_nat_add(v___x_5053_, v_size_5024_);
                crate::leanh::lean_dec(v___x_5053_);
                v___x_5066_ = lean_nat_add(v___x_5023_, v_size_5041_);
                if crate::leanh::lean_obj_tag(v_l_5045_) == 0 {
                    v_size_5076_ = crate::leanh::lean_ctor_get(v_l_5045_, 0);
                    crate::leanh::lean_inc(v_size_5076_);
                    v___y_5068_ = v_size_5076_;
                    state = 29;
                    continue;
                } else {
                    v___x_5077_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_5068_ = v___x_5077_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_5059_ = lean_nat_add(v___y_5057_, v___y_5058_);
                crate::leanh::lean_dec(v___y_5058_);
                crate::leanh::lean_dec(v___y_5057_);
                if v_isShared_5052_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5051_, 4, v_r_4878_);
                    crate::leanh::lean_ctor_set(v___x_5051_, 3, v_r_5046_);
                    crate::leanh::lean_ctor_set(v___x_5051_, 2, v_v_4876_);
                    crate::leanh::lean_ctor_set(v___x_5051_, 1, v_k_4875_);
                    crate::leanh::lean_ctor_set(v___x_5051_, 0, v___x_5059_);
                    v___x_5061_ = v___x_5051_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_5065_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5065_, 0, v___x_5059_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5065_, 1, v_k_4875_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5065_, 2, v_v_4876_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5065_, 3, v_r_5046_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5065_, 4, v_r_4878_);
                    v___x_5061_ = v_reuseFailAlloc_5065_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_5040_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5039_, 4, v___x_5061_);
                    crate::leanh::lean_ctor_set(v___x_5039_, 3, v___y_5056_);
                    crate::leanh::lean_ctor_set(v___x_5039_, 2, v_v_5044_);
                    crate::leanh::lean_ctor_set(v___x_5039_, 1, v_k_5043_);
                    crate::leanh::lean_ctor_set(v___x_5039_, 0, v___x_5054_);
                    v___x_5063_ = v___x_5039_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5064_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5064_, 0, v___x_5054_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5064_, 1, v_k_5043_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5064_, 2, v_v_5044_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5064_, 3, v___y_5056_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5064_, 4, v___x_5061_);
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
                crate::leanh::lean_dec(v___y_5068_);
                crate::leanh::lean_dec(v___x_5066_);
                if v_isShared_4881_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4880_, 4, v_l_5045_);
                    crate::leanh::lean_ctor_set(v___x_4880_, 3, v_l_5028_);
                    crate::leanh::lean_ctor_set(v___x_4880_, 2, v_v_5027_);
                    crate::leanh::lean_ctor_set(v___x_4880_, 1, v_k_5026_);
                    crate::leanh::lean_ctor_set(v___x_4880_, 0, v___x_5069_);
                    v___x_5071_ = v___x_4880_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_5075_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 0, v___x_5069_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 1, v_k_5026_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 2, v_v_5027_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 3, v_l_5028_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5075_, 4, v_l_5045_);
                    v___x_5071_ = v_reuseFailAlloc_5075_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_5072_ = lean_nat_add(v___x_5023_, v_size_5024_);
                if crate::leanh::lean_obj_tag(v_r_5046_) == 0 {
                    v_size_5073_ = crate::leanh::lean_ctor_get(v_r_5046_, 0);
                    crate::leanh::lean_inc(v_size_5073_);
                    v___y_5056_ = v___x_5071_;
                    v___y_5057_ = v___x_5072_;
                    v___y_5058_ = v_size_5073_;
                    state = 26;
                    continue;
                } else {
                    v___x_5074_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_5056_ = v___x_5071_;
                    v___y_5057_ = v___x_5072_;
                    v___y_5058_ = v___x_5074_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_5096_ = (!crate::leanh::lean_is_exclusive(v_r_4878_)) as u8;
                if v_isSharedCheck_5096_ == 0 {
                    v_unused_5097_ = crate::leanh::lean_ctor_get(v_r_4878_, 4);
                    crate::leanh::lean_dec(v_unused_5097_);
                    v_unused_5098_ = crate::leanh::lean_ctor_get(v_r_4878_, 3);
                    crate::leanh::lean_dec(v_unused_5098_);
                    v_unused_5099_ = crate::leanh::lean_ctor_get(v_r_4878_, 2);
                    crate::leanh::lean_dec(v_unused_5099_);
                    v_unused_5100_ = crate::leanh::lean_ctor_get(v_r_4878_, 1);
                    crate::leanh::lean_dec(v_unused_5100_);
                    v_unused_5101_ = crate::leanh::lean_ctor_get(v_r_4878_, 0);
                    crate::leanh::lean_dec(v_unused_5101_);
                    v___x_5091_ = v_r_4878_;
                    v_isShared_5092_ = v_isSharedCheck_5096_;
                    state = 32;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_4878_);
                    v___x_5091_ = crate::leanh::lean_box(0);
                    v_isShared_5092_ = v_isSharedCheck_5096_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_5092_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5091_, 4, v___x_5089_);
                    crate::leanh::lean_ctor_set(v___x_5091_, 3, v_l_5028_);
                    crate::leanh::lean_ctor_set(v___x_5091_, 2, v_v_5027_);
                    crate::leanh::lean_ctor_set(v___x_5091_, 1, v_k_5026_);
                    crate::leanh::lean_ctor_set(v___x_5091_, 0, v___x_5085_);
                    v___x_5094_ = v___x_5091_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_5095_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5095_, 0, v___x_5085_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5095_, 1, v_k_5026_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5095_, 2, v_v_5027_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5095_, 3, v_l_5028_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5095_, 4, v___x_5089_);
                    v___x_5094_ = v_reuseFailAlloc_5095_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_5094_;
            }
            34 => {
                v___x_5116_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc(v_r_5110_);
                if v_isShared_5115_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5114_, 3, v_r_5110_);
                    crate::leanh::lean_ctor_set(v___x_5114_, 2, v_v_4876_);
                    crate::leanh::lean_ctor_set(v___x_5114_, 1, v_k_4875_);
                    crate::leanh::lean_ctor_set(v___x_5114_, 0, v___x_5023_);
                    v___x_5118_ = v___x_5114_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_5122_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5122_, 0, v___x_5023_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5122_, 1, v_k_4875_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5122_, 2, v_v_4876_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5122_, 3, v_r_5110_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5122_, 4, v_r_5110_);
                    v___x_5118_ = v_reuseFailAlloc_5122_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_4881_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4880_, 4, v___x_5118_);
                    crate::leanh::lean_ctor_set(v___x_4880_, 3, v_l_5109_);
                    crate::leanh::lean_ctor_set(v___x_4880_, 2, v_v_5112_);
                    crate::leanh::lean_ctor_set(v___x_4880_, 1, v_k_5111_);
                    crate::leanh::lean_ctor_set(v___x_4880_, 0, v___x_5116_);
                    v___x_5120_ = v___x_4880_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_5121_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5121_, 0, v___x_5116_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5121_, 1, v_k_5111_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5121_, 2, v_v_5112_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5121_, 3, v_l_5109_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5121_, 4, v___x_5118_);
                    v___x_5120_ = v_reuseFailAlloc_5121_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_5120_;
            }
            37 => {
                v_k_5132_ = crate::leanh::lean_ctor_get(v_r_5126_, 1);
                v_v_5133_ = crate::leanh::lean_ctor_get(v_r_5126_, 2);
                v_isSharedCheck_5147_ = (!crate::leanh::lean_is_exclusive(v_r_5126_)) as u8;
                if v_isSharedCheck_5147_ == 0 {
                    v_unused_5148_ = crate::leanh::lean_ctor_get(v_r_5126_, 4);
                    crate::leanh::lean_dec(v_unused_5148_);
                    v_unused_5149_ = crate::leanh::lean_ctor_get(v_r_5126_, 3);
                    crate::leanh::lean_dec(v_unused_5149_);
                    v_unused_5150_ = crate::leanh::lean_ctor_get(v_r_5126_, 0);
                    crate::leanh::lean_dec(v_unused_5150_);
                    v___x_5135_ = v_r_5126_;
                    v_isShared_5136_ = v_isSharedCheck_5147_;
                    state = 38;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_5133_);
                    crate::leanh::lean_inc(v_k_5132_);
                    crate::leanh::lean_dec(v_r_5126_);
                    v___x_5135_ = crate::leanh::lean_box(0);
                    v_isShared_5136_ = v_isSharedCheck_5147_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_5137_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_5136_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5135_, 4, v_l_5109_);
                    crate::leanh::lean_ctor_set(v___x_5135_, 3, v_l_5109_);
                    crate::leanh::lean_ctor_set(v___x_5135_, 2, v_v_5128_);
                    crate::leanh::lean_ctor_set(v___x_5135_, 1, v_k_5127_);
                    crate::leanh::lean_ctor_set(v___x_5135_, 0, v___x_5023_);
                    v___x_5139_ = v___x_5135_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_5146_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 0, v___x_5023_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 1, v_k_5127_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 2, v_v_5128_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 3, v_l_5109_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 4, v_l_5109_);
                    v___x_5139_ = v_reuseFailAlloc_5146_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                if v_isShared_5131_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5130_, 4, v_l_5109_);
                    crate::leanh::lean_ctor_set(v___x_5130_, 2, v_v_4876_);
                    crate::leanh::lean_ctor_set(v___x_5130_, 1, v_k_4875_);
                    crate::leanh::lean_ctor_set(v___x_5130_, 0, v___x_5023_);
                    v___x_5141_ = v___x_5130_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_5145_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5145_, 0, v___x_5023_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5145_, 1, v_k_4875_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5145_, 2, v_v_4876_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5145_, 3, v_l_5109_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5145_, 4, v_l_5109_);
                    v___x_5141_ = v_reuseFailAlloc_5145_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_4881_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4880_, 4, v___x_5141_);
                    crate::leanh::lean_ctor_set(v___x_4880_, 3, v___x_5139_);
                    crate::leanh::lean_ctor_set(v___x_4880_, 2, v_v_5133_);
                    crate::leanh::lean_ctor_set(v___x_4880_, 1, v_k_5132_);
                    crate::leanh::lean_ctor_set(v___x_4880_, 0, v___x_5137_);
                    v___x_5143_ = v___x_4880_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_5144_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5144_, 0, v___x_5137_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5144_, 1, v_k_5132_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5144_, 2, v_v_5133_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5144_, 3, v___x_5139_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5144_, 4, v___x_5141_);
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
    mut v_k_5162_: *mut crate::leanh::LeanObject,
    mut v_t_5163_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: u8 = 0;
    let mut v___x_5168_: u8 = 0;
    let mut v___x_5171_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_5163_) == 0 {
                    v_k_5164_ = crate::leanh::lean_ctor_get(v_t_5163_, 1);
                    v_l_5165_ = crate::leanh::lean_ctor_get(v_t_5163_, 3);
                    v_r_5166_ = crate::leanh::lean_ctor_get(v_t_5163_, 4);
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
    mut v_k_5172_: *mut crate::leanh::LeanObject,
    mut v_t_5173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5174_: u8 = 0;
    let mut v_r_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5174_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_k_5172_, v_t_5173_);
    crate::leanh::lean_dec(v_t_5173_);
    crate::leanh::lean_dec(v_k_5172_);
    v_r_5175_ = crate::leanh::lean_box((v_res_5174_) as usize);
    return v_r_5175_;
}
pub unsafe fn l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(
    mut v_y_5176_: *mut crate::leanh::LeanObject,
    mut v_x_5177_: *mut crate::leanh::LeanObject,
    mut v_x_5178_: usize,
    mut v_x_5179_: usize,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_5181_: usize = 0;
    let mut v___x_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: u8 = 0;
    let mut v___x_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5187_: u8 = 0;
    let mut v___x_5188_: usize = 0;
    let mut v___x_5189_: usize = 0;
    let mut v___x_5190_: usize = 0;
    let mut v_i_5191_: usize = 0;
    let mut v___x_5192_: usize = 0;
    let mut v_shift_5193_: usize = 0;
    let mut v_v_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5202_: u8 = 0;
    let mut v_unused_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: u8 = 0;
    let mut v___x_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5210_: u8 = 0;
    let mut v_v_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: u8 = 0;
    let mut v___x_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5222_: u8 = 0;
    let mut v_unused_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5177_) == 0 {
                    v_cs_5180_ = crate::leanh::lean_ctor_get(v_x_5177_, 0);
                    v_j_5181_ = lean_usize_shift_right(v_x_5178_, v_x_5179_);
                    v___x_5182_ = lean_usize_to_nat(v_j_5181_);
                    v___x_5183_ = lean_array_get_size(v_cs_5180_);
                    v___x_5184_ = lean_nat_dec_lt(v___x_5182_, v___x_5183_);
                    if v___x_5184_ == 0 {
                        crate::leanh::lean_dec(v___x_5182_);
                        crate::leanh::lean_dec(v_y_5176_);
                        return v_x_5177_;
                    } else {
                        crate::leanh::lean_inc_ref(v_cs_5180_);
                        v_isSharedCheck_5202_ = (!crate::leanh::lean_is_exclusive(v_x_5177_)) as u8;
                        if v_isSharedCheck_5202_ == 0 {
                            v_unused_5203_ = crate::leanh::lean_ctor_get(v_x_5177_, 0);
                            crate::leanh::lean_dec(v_unused_5203_);
                            v___x_5186_ = v_x_5177_;
                            v_isShared_5187_ = v_isSharedCheck_5202_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_5177_);
                            v___x_5186_ = crate::leanh::lean_box(0);
                            v_isShared_5187_ = v_isSharedCheck_5202_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_vs_5204_ = crate::leanh::lean_ctor_get(v_x_5177_, 0);
                    v___x_5205_ = lean_usize_to_nat(v_x_5178_);
                    v___x_5206_ = lean_array_get_size(v_vs_5204_);
                    v___x_5207_ = lean_nat_dec_lt(v___x_5205_, v___x_5206_);
                    if v___x_5207_ == 0 {
                        crate::leanh::lean_dec(v___x_5205_);
                        crate::leanh::lean_dec(v_y_5176_);
                        return v_x_5177_;
                    } else {
                        crate::leanh::lean_inc_ref(v_vs_5204_);
                        v_isSharedCheck_5222_ = (!crate::leanh::lean_is_exclusive(v_x_5177_)) as u8;
                        if v_isSharedCheck_5222_ == 0 {
                            v_unused_5223_ = crate::leanh::lean_ctor_get(v_x_5177_, 0);
                            crate::leanh::lean_dec(v_unused_5223_);
                            v___x_5209_ = v_x_5177_;
                            v_isShared_5210_ = v_isSharedCheck_5222_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_5177_);
                            v___x_5209_ = crate::leanh::lean_box(0);
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
                v___x_5195_ = crate::leanh::lean_box(0);
                v_xs_x27_5196_ = lean_array_fset(v_cs_5180_, v___x_5182_, v___x_5195_);
                v___x_5197_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_5176_, v_v_5194_, v_i_5191_, v_shift_5193_);
                v___x_5198_ = lean_array_fset(v_xs_x27_5196_, v___x_5182_, v___x_5197_);
                crate::leanh::lean_dec(v___x_5182_);
                if v_isShared_5187_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5186_, 0, v___x_5198_);
                    v___x_5200_ = v___x_5186_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5201_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5201_, 0, v___x_5198_);
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
                v___x_5212_ = crate::leanh::lean_box(0);
                v_xs_x27_5213_ = lean_array_fset(v_vs_5204_, v___x_5205_, v___x_5212_);
                v___x_5220_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_5176_, v_v_5211_);
                if v___x_5220_ == 0 {
                    v___x_5221_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_y_5176_, v___x_5212_, v_v_5211_);
                    v___y_5215_ = v___x_5221_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_y_5176_);
                    v___y_5215_ = v_v_5211_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5216_ = lean_array_fset(v_xs_x27_5213_, v___x_5205_, v___y_5215_);
                crate::leanh::lean_dec(v___x_5205_);
                if v_isShared_5210_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5209_, 0, v___x_5216_);
                    v___x_5218_ = v___x_5209_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5219_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5219_, 0, v___x_5216_);
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
    mut v_y_5224_: *mut crate::leanh::LeanObject,
    mut v_x_5225_: *mut crate::leanh::LeanObject,
    mut v_x_5226_: *mut crate::leanh::LeanObject,
    mut v_x_5227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4518__boxed_5228_: usize = 0;
    let mut v_x_4519__boxed_5229_: usize = 0;
    let mut v_res_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4518__boxed_5228_ = crate::leanh::lean_unbox_usize(v_x_5226_);
    crate::leanh::lean_dec(v_x_5226_);
    v_x_4519__boxed_5229_ = crate::leanh::lean_unbox_usize(v_x_5227_);
    crate::leanh::lean_dec(v_x_5227_);
    v_res_5230_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2_spec__2(v_y_5224_, v_x_5225_, v_x_4518__boxed_5228_, v_x_4519__boxed_5229_);
    return v_res_5230_;
}
pub unsafe fn l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(
    mut v_y_5231_: *mut crate::leanh::LeanObject,
    mut v_t_5232_: *mut crate::leanh::LeanObject,
    mut v_i_5233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_shift_5237_: usize = 0;
    let mut v_tailOff_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5241_: u8 = 0;
    let mut v___x_5242_: u8 = 0;
    let mut v___x_5243_: usize = 0;
    let mut v___x_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: u8 = 0;
    let mut v___x_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: u8 = 0;
    let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5265_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_5234_ = crate::leanh::lean_ctor_get(v_t_5232_, 0);
                v_tail_5235_ = crate::leanh::lean_ctor_get(v_t_5232_, 1);
                v_size_5236_ = crate::leanh::lean_ctor_get(v_t_5232_, 2);
                v_shift_5237_ = crate::leanh::lean_ctor_get_usize(v_t_5232_, 4);
                v_tailOff_5238_ = crate::leanh::lean_ctor_get(v_t_5232_, 3);
                v_isSharedCheck_5265_ = (!crate::leanh::lean_is_exclusive(v_t_5232_)) as u8;
                if v_isSharedCheck_5265_ == 0 {
                    v___x_5240_ = v_t_5232_;
                    v_isShared_5241_ = v_isSharedCheck_5265_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_tailOff_5238_);
                    crate::leanh::lean_inc(v_size_5236_);
                    crate::leanh::lean_inc(v_tail_5235_);
                    crate::leanh::lean_inc(v_root_5234_);
                    crate::leanh::lean_dec(v_t_5232_);
                    v___x_5240_ = crate::leanh::lean_box(0);
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
                        crate::leanh::lean_ctor_set(v___x_5240_, 0, v___x_5244_);
                        v___x_5246_ = v___x_5240_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5247_ = crate::leanh::lean_alloc_ctor(
                            0,
                            4,
                            (core::mem::size_of::<usize>() * 1) as u32,
                        );
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5247_, 0, v___x_5244_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5247_, 1, v_tail_5235_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5247_, 2, v_size_5236_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5247_, 3, v_tailOff_5238_);
                        crate::leanh::lean_ctor_set_usize(v_reuseFailAlloc_5247_, 4, v_shift_5237_);
                        v___x_5246_ = v_reuseFailAlloc_5247_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5248_ = lean_nat_sub(v_i_5233_, v_tailOff_5238_);
                    v___x_5249_ = lean_array_get_size(v_tail_5235_);
                    v___x_5250_ = lean_nat_dec_lt(v___x_5248_, v___x_5249_);
                    if v___x_5250_ == 0 {
                        crate::leanh::lean_dec(v___x_5248_);
                        crate::leanh::lean_dec(v_y_5231_);
                        if v_isShared_5241_ == 0 {
                            v___x_5252_ = v___x_5240_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5253_ = crate::leanh::lean_alloc_ctor(
                                0,
                                4,
                                (core::mem::size_of::<usize>() * 1) as u32,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5253_, 0, v_root_5234_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5253_, 1, v_tail_5235_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5253_, 2, v_size_5236_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5253_, 3, v_tailOff_5238_);
                            crate::leanh::lean_ctor_set_usize(
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
                        v___x_5255_ = crate::leanh::lean_box(0);
                        v_xs_x27_5256_ = lean_array_fset(v_tail_5235_, v___x_5248_, v___x_5255_);
                        v___x_5263_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_5231_, v_v_5254_);
                        if v___x_5263_ == 0 {
                            v___x_5264_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_y_5231_, v___x_5255_, v_v_5254_);
                            v___y_5258_ = v___x_5264_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_y_5231_);
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
                crate::leanh::lean_dec(v___x_5248_);
                if v_isShared_5241_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5240_, 1, v___x_5259_);
                    v___x_5261_ = v___x_5240_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5262_ = crate::leanh::lean_alloc_ctor(
                        0,
                        4,
                        (core::mem::size_of::<usize>() * 1) as u32,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5262_, 0, v_root_5234_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5262_, 1, v___x_5259_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5262_, 2, v_size_5236_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5262_, 3, v_tailOff_5238_);
                    crate::leanh::lean_ctor_set_usize(v_reuseFailAlloc_5262_, 4, v_shift_5237_);
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
    mut v_y_5266_: *mut crate::leanh::LeanObject,
    mut v_t_5267_: *mut crate::leanh::LeanObject,
    mut v_i_5268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5269_ =
        l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(
            v_y_5266_, v_t_5267_, v_i_5268_,
        );
    crate::leanh::lean_dec(v_i_5268_);
    return v_res_5269_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0(
    mut v_y_5270_: *mut crate::leanh::LeanObject,
    mut v_x_5271_: *mut crate::leanh::LeanObject,
    mut v_s_5272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vars_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_x27_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_x27_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natToIntMap_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natDef_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dvds_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lowers_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uppers_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elimEqs_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elimStack_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_occurs_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignment_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextCnstrId_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_caseSplits_5288_: u8 = 0;
    let mut v_conflict_x3f_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqSplits_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_divMod_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntIds_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntInfos_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntTermMap_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntVarMap_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedCommRing_5296_: u8 = 0;
    let mut v_nonlinearOccs_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5300_: u8 = 0;
    let mut v___x_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5305_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vars_5273_ = crate::leanh::lean_ctor_get(v_s_5272_, 0);
                v_varMap_5274_ = crate::leanh::lean_ctor_get(v_s_5272_, 1);
                v_vars_x27_5275_ = crate::leanh::lean_ctor_get(v_s_5272_, 2);
                v_varMap_x27_5276_ = crate::leanh::lean_ctor_get(v_s_5272_, 3);
                v_natToIntMap_5277_ = crate::leanh::lean_ctor_get(v_s_5272_, 4);
                v_natDef_5278_ = crate::leanh::lean_ctor_get(v_s_5272_, 5);
                v_dvds_5279_ = crate::leanh::lean_ctor_get(v_s_5272_, 6);
                v_lowers_5280_ = crate::leanh::lean_ctor_get(v_s_5272_, 7);
                v_uppers_5281_ = crate::leanh::lean_ctor_get(v_s_5272_, 8);
                v_diseqs_5282_ = crate::leanh::lean_ctor_get(v_s_5272_, 9);
                v_elimEqs_5283_ = crate::leanh::lean_ctor_get(v_s_5272_, 10);
                v_elimStack_5284_ = crate::leanh::lean_ctor_get(v_s_5272_, 11);
                v_occurs_5285_ = crate::leanh::lean_ctor_get(v_s_5272_, 12);
                v_assignment_5286_ = crate::leanh::lean_ctor_get(v_s_5272_, 13);
                v_nextCnstrId_5287_ = crate::leanh::lean_ctor_get(v_s_5272_, 14);
                v_caseSplits_5288_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_5272_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 23) as u32,
                );
                v_conflict_x3f_5289_ = crate::leanh::lean_ctor_get(v_s_5272_, 15);
                v_diseqSplits_5290_ = crate::leanh::lean_ctor_get(v_s_5272_, 16);
                v_divMod_5291_ = crate::leanh::lean_ctor_get(v_s_5272_, 17);
                v_toIntIds_5292_ = crate::leanh::lean_ctor_get(v_s_5272_, 18);
                v_toIntInfos_5293_ = crate::leanh::lean_ctor_get(v_s_5272_, 19);
                v_toIntTermMap_5294_ = crate::leanh::lean_ctor_get(v_s_5272_, 20);
                v_toIntVarMap_5295_ = crate::leanh::lean_ctor_get(v_s_5272_, 21);
                v_usedCommRing_5296_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_5272_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 23 + 1) as u32,
                );
                v_nonlinearOccs_5297_ = crate::leanh::lean_ctor_get(v_s_5272_, 22);
                v_isSharedCheck_5305_ = (!crate::leanh::lean_is_exclusive(v_s_5272_)) as u8;
                if v_isSharedCheck_5305_ == 0 {
                    v___x_5299_ = v_s_5272_;
                    v_isShared_5300_ = v_isSharedCheck_5305_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nonlinearOccs_5297_);
                    crate::leanh::lean_inc(v_toIntVarMap_5295_);
                    crate::leanh::lean_inc(v_toIntTermMap_5294_);
                    crate::leanh::lean_inc(v_toIntInfos_5293_);
                    crate::leanh::lean_inc(v_toIntIds_5292_);
                    crate::leanh::lean_inc(v_divMod_5291_);
                    crate::leanh::lean_inc(v_diseqSplits_5290_);
                    crate::leanh::lean_inc(v_conflict_x3f_5289_);
                    crate::leanh::lean_inc(v_nextCnstrId_5287_);
                    crate::leanh::lean_inc(v_assignment_5286_);
                    crate::leanh::lean_inc(v_occurs_5285_);
                    crate::leanh::lean_inc(v_elimStack_5284_);
                    crate::leanh::lean_inc(v_elimEqs_5283_);
                    crate::leanh::lean_inc(v_diseqs_5282_);
                    crate::leanh::lean_inc(v_uppers_5281_);
                    crate::leanh::lean_inc(v_lowers_5280_);
                    crate::leanh::lean_inc(v_dvds_5279_);
                    crate::leanh::lean_inc(v_natDef_5278_);
                    crate::leanh::lean_inc(v_natToIntMap_5277_);
                    crate::leanh::lean_inc(v_varMap_x27_5276_);
                    crate::leanh::lean_inc(v_vars_x27_5275_);
                    crate::leanh::lean_inc(v_varMap_5274_);
                    crate::leanh::lean_inc(v_vars_5273_);
                    crate::leanh::lean_dec(v_s_5272_);
                    v___x_5299_ = crate::leanh::lean_box(0);
                    v_isShared_5300_ = v_isSharedCheck_5305_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5301_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__2(v_y_5270_, v_occurs_5285_, v_x_5271_);
                if v_isShared_5300_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5299_, 12, v___x_5301_);
                    v___x_5303_ = v___x_5299_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5304_ = crate::leanh::lean_alloc_ctor(0, 23, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 0, v_vars_5273_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 1, v_varMap_5274_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 2, v_vars_x27_5275_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 3, v_varMap_x27_5276_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 4, v_natToIntMap_5277_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 5, v_natDef_5278_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 6, v_dvds_5279_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 7, v_lowers_5280_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 8, v_uppers_5281_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 9, v_diseqs_5282_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 10, v_elimEqs_5283_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 11, v_elimStack_5284_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 12, v___x_5301_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 13, v_assignment_5286_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 14, v_nextCnstrId_5287_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 15, v_conflict_x3f_5289_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 16, v_diseqSplits_5290_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 17, v_divMod_5291_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 18, v_toIntIds_5292_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 19, v_toIntInfos_5293_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 20, v_toIntTermMap_5294_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 21, v_toIntVarMap_5295_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 22, v_nonlinearOccs_5297_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5304_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 23) as u32,
                        v_caseSplits_5288_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5304_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 23 + 1) as u32,
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
    mut v_y_5306_: *mut crate::leanh::LeanObject,
    mut v_x_5307_: *mut crate::leanh::LeanObject,
    mut v_s_5308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5309_ =
        l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0(v_y_5306_, v_x_5307_, v_s_5308_);
    crate::leanh::lean_dec(v_x_5307_);
    return v_res_5309_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(
    mut v_x_5310_: *mut crate::leanh::LeanObject,
    mut v_y_5311_: *mut crate::leanh::LeanObject,
    mut v_a_5312_: *mut crate::leanh::LeanObject,
    mut v_a_5313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5319_: u8 = 0;
    let mut v___x_5320_: u8 = 0;
    let mut v___f_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5328_: u8 = 0;
    let mut v_a_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5332_: u8 = 0;
    let mut v___x_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5336_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5315_ = l_Lean_Meta_Grind_Arith_Cutsat_getOccursOf___redArg(
                    v_x_5310_, v_a_5312_, v_a_5313_,
                );
                if crate::leanh::lean_obj_tag(v___x_5315_) == 0 {
                    v_a_5316_ = crate::leanh::lean_ctor_get(v___x_5315_, 0);
                    v_isSharedCheck_5328_ = (!crate::leanh::lean_is_exclusive(v___x_5315_)) as u8;
                    if v_isSharedCheck_5328_ == 0 {
                        v___x_5318_ = v___x_5315_;
                        v_isShared_5319_ = v_isSharedCheck_5328_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5316_);
                        crate::leanh::lean_dec(v___x_5315_);
                        v___x_5318_ = crate::leanh::lean_box(0);
                        v_isShared_5319_ = v_isSharedCheck_5328_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_y_5311_);
                    crate::leanh::lean_dec(v_x_5310_);
                    v_a_5329_ = crate::leanh::lean_ctor_get(v___x_5315_, 0);
                    v_isSharedCheck_5336_ = (!crate::leanh::lean_is_exclusive(v___x_5315_)) as u8;
                    if v_isSharedCheck_5336_ == 0 {
                        v___x_5331_ = v___x_5315_;
                        v_isShared_5332_ = v_isSharedCheck_5336_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5329_);
                        crate::leanh::lean_dec(v___x_5315_);
                        v___x_5331_ = crate::leanh::lean_box(0);
                        v_isShared_5332_ = v_isSharedCheck_5336_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5320_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_y_5311_, v_a_5316_);
                crate::leanh::lean_dec(v_a_5316_);
                if v___x_5320_ == 0 {
                    crate::leanh::lean_del_object(v___x_5318_);
                    v___f_5321_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_5321_, 0, v_y_5311_);
                    crate::leanh::lean_closure_set(v___f_5321_, 1, v_x_5310_);
                    v___x_5322_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
                    v___x_5323_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_5322_, v___f_5321_, v_a_5312_);
                    return v___x_5323_;
                } else {
                    crate::leanh::lean_dec(v_y_5311_);
                    crate::leanh::lean_dec(v_x_5310_);
                    v___x_5324_ = crate::leanh::lean_box(0);
                    if v_isShared_5319_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5318_, 0, v___x_5324_);
                        v___x_5326_ = v___x_5318_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5327_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5327_, 0, v___x_5324_);
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
                    v_reuseFailAlloc_5335_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5335_, 0, v_a_5329_);
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
    mut v_x_5337_: *mut crate::leanh::LeanObject,
    mut v_y_5338_: *mut crate::leanh::LeanObject,
    mut v_a_5339_: *mut crate::leanh::LeanObject,
    mut v_a_5340_: *mut crate::leanh::LeanObject,
    mut v_a_5341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5342_ =
        l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_x_5337_, v_y_5338_, v_a_5339_, v_a_5340_);
    crate::leanh::lean_dec_ref(v_a_5340_);
    crate::leanh::lean_dec(v_a_5339_);
    return v_res_5342_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_addOcc(
    mut v_x_5343_: *mut crate::leanh::LeanObject,
    mut v_y_5344_: *mut crate::leanh::LeanObject,
    mut v_a_5345_: *mut crate::leanh::LeanObject,
    mut v_a_5346_: *mut crate::leanh::LeanObject,
    mut v_a_5347_: *mut crate::leanh::LeanObject,
    mut v_a_5348_: *mut crate::leanh::LeanObject,
    mut v_a_5349_: *mut crate::leanh::LeanObject,
    mut v_a_5350_: *mut crate::leanh::LeanObject,
    mut v_a_5351_: *mut crate::leanh::LeanObject,
    mut v_a_5352_: *mut crate::leanh::LeanObject,
    mut v_a_5353_: *mut crate::leanh::LeanObject,
    mut v_a_5354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5356_ =
        l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(v_x_5343_, v_y_5344_, v_a_5345_, v_a_5353_);
    return v___x_5356_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_addOcc___boxed(
    mut v_x_5357_: *mut crate::leanh::LeanObject,
    mut v_y_5358_: *mut crate::leanh::LeanObject,
    mut v_a_5359_: *mut crate::leanh::LeanObject,
    mut v_a_5360_: *mut crate::leanh::LeanObject,
    mut v_a_5361_: *mut crate::leanh::LeanObject,
    mut v_a_5362_: *mut crate::leanh::LeanObject,
    mut v_a_5363_: *mut crate::leanh::LeanObject,
    mut v_a_5364_: *mut crate::leanh::LeanObject,
    mut v_a_5365_: *mut crate::leanh::LeanObject,
    mut v_a_5366_: *mut crate::leanh::LeanObject,
    mut v_a_5367_: *mut crate::leanh::LeanObject,
    mut v_a_5368_: *mut crate::leanh::LeanObject,
    mut v_a_5369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5370_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc(
        v_x_5357_, v_y_5358_, v_a_5359_, v_a_5360_, v_a_5361_, v_a_5362_, v_a_5363_, v_a_5364_,
        v_a_5365_, v_a_5366_, v_a_5367_, v_a_5368_,
    );
    crate::leanh::lean_dec(v_a_5368_);
    crate::leanh::lean_dec_ref(v_a_5367_);
    crate::leanh::lean_dec(v_a_5366_);
    crate::leanh::lean_dec_ref(v_a_5365_);
    crate::leanh::lean_dec(v_a_5364_);
    crate::leanh::lean_dec_ref(v_a_5363_);
    crate::leanh::lean_dec(v_a_5362_);
    crate::leanh::lean_dec_ref(v_a_5361_);
    crate::leanh::lean_dec(v_a_5360_);
    crate::leanh::lean_dec(v_a_5359_);
    return v_res_5370_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0(
    mut v_00_u03b2_5371_: *mut crate::leanh::LeanObject,
    mut v_k_5372_: *mut crate::leanh::LeanObject,
    mut v_t_5373_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5374_: u8 = 0;
    v___x_5374_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___redArg(v_k_5372_, v_t_5373_);
    return v___x_5374_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0___boxed(
    mut v_00_u03b2_5375_: *mut crate::leanh::LeanObject,
    mut v_k_5376_: *mut crate::leanh::LeanObject,
    mut v_t_5377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5378_: u8 = 0;
    let mut v_r_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5378_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__0(
            v_00_u03b2_5375_,
            v_k_5376_,
            v_t_5377_,
        );
    crate::leanh::lean_dec(v_t_5377_);
    crate::leanh::lean_dec(v_k_5376_);
    v_r_5379_ = crate::leanh::lean_box((v_res_5378_) as usize);
    return v_r_5379_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1(
    mut v_00_u03b2_5380_: *mut crate::leanh::LeanObject,
    mut v_k_5381_: *mut crate::leanh::LeanObject,
    mut v_v_5382_: *mut crate::leanh::LeanObject,
    mut v_t_5383_: *mut crate::leanh::LeanObject,
    mut v_hl_5384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5385_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Cutsat_addOcc_spec__1___redArg(v_k_5381_, v_v_5382_, v_t_5383_);
    return v___x_5385_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___redArg(
    mut v_y_5386_: *mut crate::leanh::LeanObject,
    mut v_p_5387_: *mut crate::leanh::LeanObject,
    mut v_a_5388_: *mut crate::leanh::LeanObject,
    mut v_a_5389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_v_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_5387_) == 1 {
                    v_v_5391_ = crate::leanh::lean_ctor_get(v_p_5387_, 1);
                    crate::leanh::lean_inc(v_v_5391_);
                    v_p_5392_ = crate::leanh::lean_ctor_get(v_p_5387_, 2);
                    crate::leanh::lean_inc_ref(v_p_5392_);
                    crate::leanh::lean_dec_ref_known(v_p_5387_, 3);
                    crate::leanh::lean_inc(v_y_5386_);
                    v___x_5393_ = l_Lean_Meta_Grind_Arith_Cutsat_addOcc___redArg(
                        v_v_5391_, v_y_5386_, v_a_5388_, v_a_5389_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5393_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5393_, 1);
                        v_p_5387_ = v_p_5392_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_p_5392_);
                        crate::leanh::lean_dec(v_y_5386_);
                        return v___x_5393_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_p_5387_);
                    crate::leanh::lean_dec(v_y_5386_);
                    v___x_5395_ = crate::leanh::lean_box(0);
                    v___x_5396_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5396_, 0, v___x_5395_);
                    return v___x_5396_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___redArg___boxed(
    mut v_y_5397_: *mut crate::leanh::LeanObject,
    mut v_p_5398_: *mut crate::leanh::LeanObject,
    mut v_a_5399_: *mut crate::leanh::LeanObject,
    mut v_a_5400_: *mut crate::leanh::LeanObject,
    mut v_a_5401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5402_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___redArg(v_y_5397_, v_p_5398_, v_a_5399_, v_a_5400_);
    crate::leanh::lean_dec_ref(v_a_5400_);
    crate::leanh::lean_dec(v_a_5399_);
    return v_res_5402_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go(
    mut v_y_5403_: *mut crate::leanh::LeanObject,
    mut v_p_5404_: *mut crate::leanh::LeanObject,
    mut v_a_5405_: *mut crate::leanh::LeanObject,
    mut v_a_5406_: *mut crate::leanh::LeanObject,
    mut v_a_5407_: *mut crate::leanh::LeanObject,
    mut v_a_5408_: *mut crate::leanh::LeanObject,
    mut v_a_5409_: *mut crate::leanh::LeanObject,
    mut v_a_5410_: *mut crate::leanh::LeanObject,
    mut v_a_5411_: *mut crate::leanh::LeanObject,
    mut v_a_5412_: *mut crate::leanh::LeanObject,
    mut v_a_5413_: *mut crate::leanh::LeanObject,
    mut v_a_5414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5416_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___redArg(v_y_5403_, v_p_5404_, v_a_5405_, v_a_5413_);
    return v___x_5416_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___boxed(
    mut v_y_5417_: *mut crate::leanh::LeanObject,
    mut v_p_5418_: *mut crate::leanh::LeanObject,
    mut v_a_5419_: *mut crate::leanh::LeanObject,
    mut v_a_5420_: *mut crate::leanh::LeanObject,
    mut v_a_5421_: *mut crate::leanh::LeanObject,
    mut v_a_5422_: *mut crate::leanh::LeanObject,
    mut v_a_5423_: *mut crate::leanh::LeanObject,
    mut v_a_5424_: *mut crate::leanh::LeanObject,
    mut v_a_5425_: *mut crate::leanh::LeanObject,
    mut v_a_5426_: *mut crate::leanh::LeanObject,
    mut v_a_5427_: *mut crate::leanh::LeanObject,
    mut v_a_5428_: *mut crate::leanh::LeanObject,
    mut v_a_5429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5430_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go(
            v_y_5417_, v_p_5418_, v_a_5419_, v_a_5420_, v_a_5421_, v_a_5422_, v_a_5423_, v_a_5424_,
            v_a_5425_, v_a_5426_, v_a_5427_, v_a_5428_,
        );
    crate::leanh::lean_dec(v_a_5428_);
    crate::leanh::lean_dec_ref(v_a_5427_);
    crate::leanh::lean_dec(v_a_5426_);
    crate::leanh::lean_dec_ref(v_a_5425_);
    crate::leanh::lean_dec(v_a_5424_);
    crate::leanh::lean_dec_ref(v_a_5423_);
    crate::leanh::lean_dec(v_a_5422_);
    crate::leanh::lean_dec_ref(v_a_5421_);
    crate::leanh::lean_dec(v_a_5420_);
    crate::leanh::lean_dec(v_a_5419_);
    return v_res_5430_;
}
pub unsafe fn _init_l_Int_Linear_Poly_updateOccs___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5432_ = l_Int_Linear_Poly_updateOccs___redArg___closed__0;
    v___x_5433_ = l_Lean_stringToMessageData(v___x_5432_);
    return v___x_5433_;
}
pub unsafe fn l_Int_Linear_Poly_updateOccs___redArg(
    mut v_p_5434_: *mut crate::leanh::LeanObject,
    mut v_a_5435_: *mut crate::leanh::LeanObject,
    mut v_a_5436_: *mut crate::leanh::LeanObject,
    mut v_a_5437_: *mut crate::leanh::LeanObject,
    mut v_a_5438_: *mut crate::leanh::LeanObject,
    mut v_a_5439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_5434_) == 1 {
        let mut v_v_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_v_5441_ = crate::leanh::lean_ctor_get(v_p_5434_, 1);
        crate::leanh::lean_inc(v_v_5441_);
        v_p_5442_ = crate::leanh::lean_ctor_get(v_p_5434_, 2);
        crate::leanh::lean_inc_ref(v_p_5442_);
        crate::leanh::lean_dec_ref_known(v_p_5434_, 3);
        v___x_5443_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_updateOccs_go___redArg(v_v_5441_, v_p_5442_, v_a_5435_, v_a_5438_);
        return v___x_5443_;
    } else {
        let mut v___x_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_p_5434_);
        v___x_5444_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_Linear_Poly_updateOccs___redArg___closed__1),
            core::ptr::addr_of_mut!(l_Int_Linear_Poly_updateOccs___redArg___closed__1_once),
            _init_l_Int_Linear_Poly_updateOccs___redArg___closed__1,
        );
        v___x_5445_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected_spec__0___redArg(v___x_5444_, v_a_5436_, v_a_5437_, v_a_5438_, v_a_5439_);
        return v___x_5445_;
    }
}
pub unsafe fn l_Int_Linear_Poly_updateOccs___redArg___boxed(
    mut v_p_5446_: *mut crate::leanh::LeanObject,
    mut v_a_5447_: *mut crate::leanh::LeanObject,
    mut v_a_5448_: *mut crate::leanh::LeanObject,
    mut v_a_5449_: *mut crate::leanh::LeanObject,
    mut v_a_5450_: *mut crate::leanh::LeanObject,
    mut v_a_5451_: *mut crate::leanh::LeanObject,
    mut v_a_5452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5453_ = l_Int_Linear_Poly_updateOccs___redArg(
        v_p_5446_, v_a_5447_, v_a_5448_, v_a_5449_, v_a_5450_, v_a_5451_,
    );
    crate::leanh::lean_dec(v_a_5451_);
    crate::leanh::lean_dec_ref(v_a_5450_);
    crate::leanh::lean_dec(v_a_5449_);
    crate::leanh::lean_dec_ref(v_a_5448_);
    crate::leanh::lean_dec(v_a_5447_);
    return v_res_5453_;
}
pub unsafe fn l_Int_Linear_Poly_updateOccs(
    mut v_p_5454_: *mut crate::leanh::LeanObject,
    mut v_a_5455_: *mut crate::leanh::LeanObject,
    mut v_a_5456_: *mut crate::leanh::LeanObject,
    mut v_a_5457_: *mut crate::leanh::LeanObject,
    mut v_a_5458_: *mut crate::leanh::LeanObject,
    mut v_a_5459_: *mut crate::leanh::LeanObject,
    mut v_a_5460_: *mut crate::leanh::LeanObject,
    mut v_a_5461_: *mut crate::leanh::LeanObject,
    mut v_a_5462_: *mut crate::leanh::LeanObject,
    mut v_a_5463_: *mut crate::leanh::LeanObject,
    mut v_a_5464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5466_ = l_Int_Linear_Poly_updateOccs___redArg(
        v_p_5454_, v_a_5455_, v_a_5461_, v_a_5462_, v_a_5463_, v_a_5464_,
    );
    return v___x_5466_;
}
pub unsafe fn l_Int_Linear_Poly_updateOccs___boxed(
    mut v_p_5467_: *mut crate::leanh::LeanObject,
    mut v_a_5468_: *mut crate::leanh::LeanObject,
    mut v_a_5469_: *mut crate::leanh::LeanObject,
    mut v_a_5470_: *mut crate::leanh::LeanObject,
    mut v_a_5471_: *mut crate::leanh::LeanObject,
    mut v_a_5472_: *mut crate::leanh::LeanObject,
    mut v_a_5473_: *mut crate::leanh::LeanObject,
    mut v_a_5474_: *mut crate::leanh::LeanObject,
    mut v_a_5475_: *mut crate::leanh::LeanObject,
    mut v_a_5476_: *mut crate::leanh::LeanObject,
    mut v_a_5477_: *mut crate::leanh::LeanObject,
    mut v_a_5478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5479_ = l_Int_Linear_Poly_updateOccs(
        v_p_5467_, v_a_5468_, v_a_5469_, v_a_5470_, v_a_5471_, v_a_5472_, v_a_5473_, v_a_5474_,
        v_a_5475_, v_a_5476_, v_a_5477_,
    );
    crate::leanh::lean_dec(v_a_5477_);
    crate::leanh::lean_dec_ref(v_a_5476_);
    crate::leanh::lean_dec(v_a_5475_);
    crate::leanh::lean_dec_ref(v_a_5474_);
    crate::leanh::lean_dec(v_a_5473_);
    crate::leanh::lean_dec_ref(v_a_5472_);
    crate::leanh::lean_dec(v_a_5471_);
    crate::leanh::lean_dec_ref(v_a_5470_);
    crate::leanh::lean_dec(v_a_5469_);
    crate::leanh::lean_dec(v_a_5468_);
    return v_res_5479_;
}
pub unsafe fn l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_eval_x3f_go_spec__0(
    mut v_a_5480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5481_ = l_Rat_ofInt(v_a_5480_);
    return v___x_5481_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_eval_x3f_go(
    mut v_a_5482_: *mut crate::leanh::LeanObject,
    mut v_v_5483_: *mut crate::leanh::LeanObject,
    mut v_a_5484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5488_: u8 = 0;
    let mut v___x_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5494_: u8 = 0;
    let mut v_k_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: u8 = 0;
    let mut v___x_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_5484_) == 0 {
                    v_k_5485_ = crate::leanh::lean_ctor_get(v_a_5484_, 0);
                    v_isSharedCheck_5494_ = (!crate::leanh::lean_is_exclusive(v_a_5484_)) as u8;
                    if v_isSharedCheck_5494_ == 0 {
                        v___x_5487_ = v_a_5484_;
                        v_isShared_5488_ = v_isSharedCheck_5494_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_5485_);
                        crate::leanh::lean_dec(v_a_5484_);
                        v___x_5487_ = crate::leanh::lean_box(0);
                        v_isShared_5488_ = v_isSharedCheck_5494_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_5495_ = crate::leanh::lean_ctor_get(v_a_5484_, 0);
                    crate::leanh::lean_inc(v_k_5495_);
                    v_v_5496_ = crate::leanh::lean_ctor_get(v_a_5484_, 1);
                    crate::leanh::lean_inc(v_v_5496_);
                    v_p_5497_ = crate::leanh::lean_ctor_get(v_a_5484_, 2);
                    crate::leanh::lean_inc_ref(v_p_5497_);
                    crate::leanh::lean_dec_ref_known(v_a_5484_, 3);
                    v_size_5498_ = crate::leanh::lean_ctor_get(v_a_5482_, 2);
                    v___x_5499_ = lean_nat_dec_lt(v_v_5496_, v_size_5498_);
                    if v___x_5499_ == 0 {
                        crate::leanh::lean_dec_ref(v_p_5497_);
                        crate::leanh::lean_dec(v_v_5496_);
                        crate::leanh::lean_dec(v_k_5495_);
                        crate::leanh::lean_dec_ref(v_v_5483_);
                        v___x_5500_ = crate::leanh::lean_box(0);
                        return v___x_5500_;
                    } else {
                        v___x_5501_ = l_Rat_ofInt(v_k_5495_);
                        v___x_5502_ = l_instInhabitedRat;
                        v___x_5503_ = l_Lean_PersistentArray_get_x21___redArg(
                            v___x_5502_,
                            v_a_5482_,
                            v_v_5496_,
                        );
                        crate::leanh::lean_dec(v_v_5496_);
                        v___x_5504_ = l_Rat_mul(v___x_5501_, v___x_5503_);
                        crate::leanh::lean_dec_ref(v___x_5501_);
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
                    crate::leanh::lean_ctor_set_tag(v___x_5487_, 1);
                    crate::leanh::lean_ctor_set(v___x_5487_, 0, v___x_5490_);
                    v___x_5492_ = v___x_5487_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5493_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5493_, 0, v___x_5490_);
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
    mut v_a_5507_: *mut crate::leanh::LeanObject,
    mut v_v_5508_: *mut crate::leanh::LeanObject,
    mut v_a_5509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5510_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_eval_x3f_go(
            v_a_5507_, v_v_5508_, v_a_5509_,
        );
    crate::leanh::lean_dec_ref(v_a_5507_);
    return v_res_5510_;
}
pub unsafe fn l_Nat_cast___at___00Int_Linear_Poly_eval_x3f_spec__0(
    mut v_a_5511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5512_ = lean_nat_to_int(v_a_5511_);
    v___x_5513_ = l_Rat_ofInt(v___x_5512_);
    return v___x_5513_;
}
pub unsafe fn _init_l_Int_Linear_Poly_eval_x3f___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5514_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5515_ = l_Nat_cast___at___00Int_Linear_Poly_eval_x3f_spec__0(v___x_5514_);
    return v___x_5515_;
}
pub unsafe fn l_Int_Linear_Poly_eval_x3f___redArg(
    mut v_p_5516_: *mut crate::leanh::LeanObject,
    mut v_a_5517_: *mut crate::leanh::LeanObject,
    mut v_a_5518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5524_: u8 = 0;
    let mut v_assignment_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5531_: u8 = 0;
    let mut v_a_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5535_: u8 = 0;
    let mut v___x_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5539_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5520_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_5517_, v_a_5518_);
                if crate::leanh::lean_obj_tag(v___x_5520_) == 0 {
                    v_a_5521_ = crate::leanh::lean_ctor_get(v___x_5520_, 0);
                    v_isSharedCheck_5531_ = (!crate::leanh::lean_is_exclusive(v___x_5520_)) as u8;
                    if v_isSharedCheck_5531_ == 0 {
                        v___x_5523_ = v___x_5520_;
                        v_isShared_5524_ = v_isSharedCheck_5531_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5521_);
                        crate::leanh::lean_dec(v___x_5520_);
                        v___x_5523_ = crate::leanh::lean_box(0);
                        v_isShared_5524_ = v_isSharedCheck_5531_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_p_5516_);
                    v_a_5532_ = crate::leanh::lean_ctor_get(v___x_5520_, 0);
                    v_isSharedCheck_5539_ = (!crate::leanh::lean_is_exclusive(v___x_5520_)) as u8;
                    if v_isSharedCheck_5539_ == 0 {
                        v___x_5534_ = v___x_5520_;
                        v_isShared_5535_ = v_isSharedCheck_5539_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5532_);
                        crate::leanh::lean_dec(v___x_5520_);
                        v___x_5534_ = crate::leanh::lean_box(0);
                        v_isShared_5535_ = v_isSharedCheck_5539_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_assignment_5525_ = crate::leanh::lean_ctor_get(v_a_5521_, 13);
                crate::leanh::lean_inc_ref(v_assignment_5525_);
                crate::leanh::lean_dec(v_a_5521_);
                v___x_5526_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Int_Linear_Poly_eval_x3f___redArg___closed__0),
                    core::ptr::addr_of_mut!(l_Int_Linear_Poly_eval_x3f___redArg___closed__0_once),
                    _init_l_Int_Linear_Poly_eval_x3f___redArg___closed__0,
                );
                v___x_5527_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util_0__Int_Linear_Poly_eval_x3f_go(v_assignment_5525_, v___x_5526_, v_p_5516_);
                crate::leanh::lean_dec_ref(v_assignment_5525_);
                if v_isShared_5524_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5523_, 0, v___x_5527_);
                    v___x_5529_ = v___x_5523_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5530_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5530_, 0, v___x_5527_);
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
                    v_reuseFailAlloc_5538_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5538_, 0, v_a_5532_);
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
    mut v_p_5540_: *mut crate::leanh::LeanObject,
    mut v_a_5541_: *mut crate::leanh::LeanObject,
    mut v_a_5542_: *mut crate::leanh::LeanObject,
    mut v_a_5543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5544_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_5540_, v_a_5541_, v_a_5542_);
    crate::leanh::lean_dec_ref(v_a_5542_);
    crate::leanh::lean_dec(v_a_5541_);
    return v_res_5544_;
}
pub unsafe fn l_Int_Linear_Poly_eval_x3f(
    mut v_p_5545_: *mut crate::leanh::LeanObject,
    mut v_a_5546_: *mut crate::leanh::LeanObject,
    mut v_a_5547_: *mut crate::leanh::LeanObject,
    mut v_a_5548_: *mut crate::leanh::LeanObject,
    mut v_a_5549_: *mut crate::leanh::LeanObject,
    mut v_a_5550_: *mut crate::leanh::LeanObject,
    mut v_a_5551_: *mut crate::leanh::LeanObject,
    mut v_a_5552_: *mut crate::leanh::LeanObject,
    mut v_a_5553_: *mut crate::leanh::LeanObject,
    mut v_a_5554_: *mut crate::leanh::LeanObject,
    mut v_a_5555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5557_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_5545_, v_a_5546_, v_a_5554_);
    return v___x_5557_;
}
pub unsafe fn l_Int_Linear_Poly_eval_x3f___boxed(
    mut v_p_5558_: *mut crate::leanh::LeanObject,
    mut v_a_5559_: *mut crate::leanh::LeanObject,
    mut v_a_5560_: *mut crate::leanh::LeanObject,
    mut v_a_5561_: *mut crate::leanh::LeanObject,
    mut v_a_5562_: *mut crate::leanh::LeanObject,
    mut v_a_5563_: *mut crate::leanh::LeanObject,
    mut v_a_5564_: *mut crate::leanh::LeanObject,
    mut v_a_5565_: *mut crate::leanh::LeanObject,
    mut v_a_5566_: *mut crate::leanh::LeanObject,
    mut v_a_5567_: *mut crate::leanh::LeanObject,
    mut v_a_5568_: *mut crate::leanh::LeanObject,
    mut v_a_5569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5570_ = l_Int_Linear_Poly_eval_x3f(
        v_p_5558_, v_a_5559_, v_a_5560_, v_a_5561_, v_a_5562_, v_a_5563_, v_a_5564_, v_a_5565_,
        v_a_5566_, v_a_5567_, v_a_5568_,
    );
    crate::leanh::lean_dec(v_a_5568_);
    crate::leanh::lean_dec_ref(v_a_5567_);
    crate::leanh::lean_dec(v_a_5566_);
    crate::leanh::lean_dec_ref(v_a_5565_);
    crate::leanh::lean_dec(v_a_5564_);
    crate::leanh::lean_dec_ref(v_a_5563_);
    crate::leanh::lean_dec(v_a_5562_);
    crate::leanh::lean_dec_ref(v_a_5561_);
    crate::leanh::lean_dec(v_a_5560_);
    crate::leanh::lean_dec(v_a_5559_);
    return v_res_5570_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(
    mut v_c_5571_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_p_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: u8 = 0;
    v_p_5572_ = crate::leanh::lean_ctor_get(v_c_5571_, 0);
    v___x_5573_ = l_Int_Linear_Poly_isUnsatLe(v_p_5572_);
    return v___x_5573_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat___boxed(
    mut v_c_5574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5575_: u8 = 0;
    let mut v_r_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5575_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isUnsat(v_c_5574_);
    crate::leanh::lean_dec_ref(v_c_5574_);
    v_r_5576_ = crate::leanh::lean_box((v_res_5575_) as usize);
    return v_r_5576_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(
    mut v_c_5577_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_d_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5580_: u8 = 0;
    v_d_5578_ = crate::leanh::lean_ctor_get(v_c_5577_, 0);
    crate::leanh::lean_inc(v_d_5578_);
    v_p_5579_ = crate::leanh::lean_ctor_get(v_c_5577_, 1);
    crate::leanh::lean_inc_ref(v_p_5579_);
    crate::leanh::lean_dec_ref(v_c_5577_);
    v___x_5580_ = l_Int_Linear_Poly_isUnsatDvd(v_d_5578_, v_p_5579_);
    crate::leanh::lean_dec_ref(v_p_5579_);
    return v___x_5580_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat___boxed(
    mut v_c_5581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5582_: u8 = 0;
    let mut v_r_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5582_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isUnsat(v_c_5581_);
    v_r_5583_ = crate::leanh::lean_box((v_res_5582_) as usize);
    return v_r_5583_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(
    mut v_c_5584_: *mut crate::leanh::LeanObject,
    mut v_a_5585_: *mut crate::leanh::LeanObject,
    mut v_a_5586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_d_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5594_: u8 = 0;
    let mut v_val_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_num_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_den_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: u8 = 0;
    let mut v___x_5600_: u8 = 0;
    let mut v___x_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: u8 = 0;
    let mut v___x_5606_: u8 = 0;
    let mut v___x_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: u8 = 0;
    let mut v___x_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5616_: u8 = 0;
    let mut v_a_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5620_: u8 = 0;
    let mut v___x_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5624_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_d_5588_ = crate::leanh::lean_ctor_get(v_c_5584_, 0);
                crate::leanh::lean_inc(v_d_5588_);
                v_p_5589_ = crate::leanh::lean_ctor_get(v_c_5584_, 1);
                crate::leanh::lean_inc_ref(v_p_5589_);
                crate::leanh::lean_dec_ref(v_c_5584_);
                v___x_5590_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_5589_, v_a_5585_, v_a_5586_);
                if crate::leanh::lean_obj_tag(v___x_5590_) == 0 {
                    v_a_5591_ = crate::leanh::lean_ctor_get(v___x_5590_, 0);
                    v_isSharedCheck_5616_ = (!crate::leanh::lean_is_exclusive(v___x_5590_)) as u8;
                    if v_isSharedCheck_5616_ == 0 {
                        v___x_5593_ = v___x_5590_;
                        v_isShared_5594_ = v_isSharedCheck_5616_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5591_);
                        crate::leanh::lean_dec(v___x_5590_);
                        v___x_5593_ = crate::leanh::lean_box(0);
                        v_isShared_5594_ = v_isSharedCheck_5616_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_d_5588_);
                    v_a_5617_ = crate::leanh::lean_ctor_get(v___x_5590_, 0);
                    v_isSharedCheck_5624_ = (!crate::leanh::lean_is_exclusive(v___x_5590_)) as u8;
                    if v_isSharedCheck_5624_ == 0 {
                        v___x_5619_ = v___x_5590_;
                        v_isShared_5620_ = v_isSharedCheck_5624_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5617_);
                        crate::leanh::lean_dec(v___x_5590_);
                        v___x_5619_ = crate::leanh::lean_box(0);
                        v_isShared_5620_ = v_isSharedCheck_5624_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5591_) == 1 {
                    v_val_5595_ = crate::leanh::lean_ctor_get(v_a_5591_, 0);
                    crate::leanh::lean_inc(v_val_5595_);
                    crate::leanh::lean_dec_ref_known(v_a_5591_, 1);
                    v_num_5596_ = crate::leanh::lean_ctor_get(v_val_5595_, 0);
                    crate::leanh::lean_inc(v_num_5596_);
                    v_den_5597_ = crate::leanh::lean_ctor_get(v_val_5595_, 1);
                    crate::leanh::lean_inc(v_den_5597_);
                    crate::leanh::lean_dec(v_val_5595_);
                    v___x_5598_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5599_ = lean_nat_dec_eq(v_den_5597_, v___x_5598_);
                    crate::leanh::lean_dec(v_den_5597_);
                    if v___x_5599_ == 0 {
                        crate::leanh::lean_dec(v_num_5596_);
                        crate::leanh::lean_dec(v_d_5588_);
                        v___x_5600_ = 0;
                        v___x_5601_ = crate::leanh::lean_box((v___x_5600_) as usize);
                        if v_isShared_5594_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5593_, 0, v___x_5601_);
                            v___x_5603_ = v___x_5593_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_5604_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5604_, 0, v___x_5601_);
                            v___x_5603_ = v_reuseFailAlloc_5604_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_5605_ = l_Int_decidableDvd(v_d_5588_, v_num_5596_);
                        crate::leanh::lean_dec(v_num_5596_);
                        crate::leanh::lean_dec(v_d_5588_);
                        v___x_5606_ = l_Bool_toLBool(v___x_5605_);
                        v___x_5607_ = crate::leanh::lean_box((v___x_5606_) as usize);
                        if v_isShared_5594_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5593_, 0, v___x_5607_);
                            v___x_5609_ = v___x_5593_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5610_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5610_, 0, v___x_5607_);
                            v___x_5609_ = v_reuseFailAlloc_5610_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5591_);
                    crate::leanh::lean_dec(v_d_5588_);
                    v___x_5611_ = 2;
                    v___x_5612_ = crate::leanh::lean_box((v___x_5611_) as usize);
                    if v_isShared_5594_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5593_, 0, v___x_5612_);
                        v___x_5614_ = v___x_5593_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5615_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5615_, 0, v___x_5612_);
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
                    v_reuseFailAlloc_5623_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5623_, 0, v_a_5617_);
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
    mut v_c_5625_: *mut crate::leanh::LeanObject,
    mut v_a_5626_: *mut crate::leanh::LeanObject,
    mut v_a_5627_: *mut crate::leanh::LeanObject,
    mut v_a_5628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5629_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_c_5625_, v_a_5626_, v_a_5627_);
    crate::leanh::lean_dec_ref(v_a_5627_);
    crate::leanh::lean_dec(v_a_5626_);
    return v_res_5629_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(
    mut v_c_5630_: *mut crate::leanh::LeanObject,
    mut v_a_5631_: *mut crate::leanh::LeanObject,
    mut v_a_5632_: *mut crate::leanh::LeanObject,
    mut v_a_5633_: *mut crate::leanh::LeanObject,
    mut v_a_5634_: *mut crate::leanh::LeanObject,
    mut v_a_5635_: *mut crate::leanh::LeanObject,
    mut v_a_5636_: *mut crate::leanh::LeanObject,
    mut v_a_5637_: *mut crate::leanh::LeanObject,
    mut v_a_5638_: *mut crate::leanh::LeanObject,
    mut v_a_5639_: *mut crate::leanh::LeanObject,
    mut v_a_5640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5642_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_c_5630_, v_a_5631_, v_a_5639_);
    return v___x_5642_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___boxed(
    mut v_c_5643_: *mut crate::leanh::LeanObject,
    mut v_a_5644_: *mut crate::leanh::LeanObject,
    mut v_a_5645_: *mut crate::leanh::LeanObject,
    mut v_a_5646_: *mut crate::leanh::LeanObject,
    mut v_a_5647_: *mut crate::leanh::LeanObject,
    mut v_a_5648_: *mut crate::leanh::LeanObject,
    mut v_a_5649_: *mut crate::leanh::LeanObject,
    mut v_a_5650_: *mut crate::leanh::LeanObject,
    mut v_a_5651_: *mut crate::leanh::LeanObject,
    mut v_a_5652_: *mut crate::leanh::LeanObject,
    mut v_a_5653_: *mut crate::leanh::LeanObject,
    mut v_a_5654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5655_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied(
        v_c_5643_, v_a_5644_, v_a_5645_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_,
        v_a_5651_, v_a_5652_, v_a_5653_,
    );
    crate::leanh::lean_dec(v_a_5653_);
    crate::leanh::lean_dec_ref(v_a_5652_);
    crate::leanh::lean_dec(v_a_5651_);
    crate::leanh::lean_dec_ref(v_a_5650_);
    crate::leanh::lean_dec(v_a_5649_);
    crate::leanh::lean_dec_ref(v_a_5648_);
    crate::leanh::lean_dec(v_a_5647_);
    crate::leanh::lean_dec_ref(v_a_5646_);
    crate::leanh::lean_dec(v_a_5645_);
    crate::leanh::lean_dec(v_a_5644_);
    return v_res_5655_;
}
pub unsafe fn l_Int_Linear_Poly_satisfiedLe___redArg(
    mut v_p_5656_: *mut crate::leanh::LeanObject,
    mut v_a_5657_: *mut crate::leanh::LeanObject,
    mut v_a_5658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5664_: u8 = 0;
    let mut v_val_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: u8 = 0;
    let mut v___x_5668_: u8 = 0;
    let mut v___x_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: u8 = 0;
    let mut v___x_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5678_: u8 = 0;
    let mut v_a_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5682_: u8 = 0;
    let mut v___x_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5686_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5660_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_5656_, v_a_5657_, v_a_5658_);
                if crate::leanh::lean_obj_tag(v___x_5660_) == 0 {
                    v_a_5661_ = crate::leanh::lean_ctor_get(v___x_5660_, 0);
                    v_isSharedCheck_5678_ = (!crate::leanh::lean_is_exclusive(v___x_5660_)) as u8;
                    if v_isSharedCheck_5678_ == 0 {
                        v___x_5663_ = v___x_5660_;
                        v_isShared_5664_ = v_isSharedCheck_5678_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5661_);
                        crate::leanh::lean_dec(v___x_5660_);
                        v___x_5663_ = crate::leanh::lean_box(0);
                        v_isShared_5664_ = v_isSharedCheck_5678_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5679_ = crate::leanh::lean_ctor_get(v___x_5660_, 0);
                    v_isSharedCheck_5686_ = (!crate::leanh::lean_is_exclusive(v___x_5660_)) as u8;
                    if v_isSharedCheck_5686_ == 0 {
                        v___x_5681_ = v___x_5660_;
                        v_isShared_5682_ = v_isSharedCheck_5686_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5679_);
                        crate::leanh::lean_dec(v___x_5660_);
                        v___x_5681_ = crate::leanh::lean_box(0);
                        v_isShared_5682_ = v_isSharedCheck_5686_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5661_) == 1 {
                    v_val_5665_ = crate::leanh::lean_ctor_get(v_a_5661_, 0);
                    crate::leanh::lean_inc(v_val_5665_);
                    crate::leanh::lean_dec_ref_known(v_a_5661_, 1);
                    v___x_5666_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Int_Linear_Poly_eval_x3f___redArg___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Int_Linear_Poly_eval_x3f___redArg___closed__0_once
                        ),
                        _init_l_Int_Linear_Poly_eval_x3f___redArg___closed__0,
                    );
                    v___x_5667_ = l_Rat_instDecidableLe(v_val_5665_, v___x_5666_);
                    v___x_5668_ = l_Bool_toLBool(v___x_5667_);
                    v___x_5669_ = crate::leanh::lean_box((v___x_5668_) as usize);
                    if v_isShared_5664_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5663_, 0, v___x_5669_);
                        v___x_5671_ = v___x_5663_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5672_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5672_, 0, v___x_5669_);
                        v___x_5671_ = v_reuseFailAlloc_5672_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5661_);
                    v___x_5673_ = 2;
                    v___x_5674_ = crate::leanh::lean_box((v___x_5673_) as usize);
                    if v_isShared_5664_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5663_, 0, v___x_5674_);
                        v___x_5676_ = v___x_5663_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5677_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5677_, 0, v___x_5674_);
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
                    v_reuseFailAlloc_5685_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5685_, 0, v_a_5679_);
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
    mut v_p_5687_: *mut crate::leanh::LeanObject,
    mut v_a_5688_: *mut crate::leanh::LeanObject,
    mut v_a_5689_: *mut crate::leanh::LeanObject,
    mut v_a_5690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5691_ = l_Int_Linear_Poly_satisfiedLe___redArg(v_p_5687_, v_a_5688_, v_a_5689_);
    crate::leanh::lean_dec_ref(v_a_5689_);
    crate::leanh::lean_dec(v_a_5688_);
    return v_res_5691_;
}
pub unsafe fn l_Int_Linear_Poly_satisfiedLe(
    mut v_p_5692_: *mut crate::leanh::LeanObject,
    mut v_a_5693_: *mut crate::leanh::LeanObject,
    mut v_a_5694_: *mut crate::leanh::LeanObject,
    mut v_a_5695_: *mut crate::leanh::LeanObject,
    mut v_a_5696_: *mut crate::leanh::LeanObject,
    mut v_a_5697_: *mut crate::leanh::LeanObject,
    mut v_a_5698_: *mut crate::leanh::LeanObject,
    mut v_a_5699_: *mut crate::leanh::LeanObject,
    mut v_a_5700_: *mut crate::leanh::LeanObject,
    mut v_a_5701_: *mut crate::leanh::LeanObject,
    mut v_a_5702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5704_ = l_Int_Linear_Poly_satisfiedLe___redArg(v_p_5692_, v_a_5693_, v_a_5701_);
    return v___x_5704_;
}
pub unsafe fn l_Int_Linear_Poly_satisfiedLe___boxed(
    mut v_p_5705_: *mut crate::leanh::LeanObject,
    mut v_a_5706_: *mut crate::leanh::LeanObject,
    mut v_a_5707_: *mut crate::leanh::LeanObject,
    mut v_a_5708_: *mut crate::leanh::LeanObject,
    mut v_a_5709_: *mut crate::leanh::LeanObject,
    mut v_a_5710_: *mut crate::leanh::LeanObject,
    mut v_a_5711_: *mut crate::leanh::LeanObject,
    mut v_a_5712_: *mut crate::leanh::LeanObject,
    mut v_a_5713_: *mut crate::leanh::LeanObject,
    mut v_a_5714_: *mut crate::leanh::LeanObject,
    mut v_a_5715_: *mut crate::leanh::LeanObject,
    mut v_a_5716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5717_ = l_Int_Linear_Poly_satisfiedLe(
        v_p_5705_, v_a_5706_, v_a_5707_, v_a_5708_, v_a_5709_, v_a_5710_, v_a_5711_, v_a_5712_,
        v_a_5713_, v_a_5714_, v_a_5715_,
    );
    crate::leanh::lean_dec(v_a_5715_);
    crate::leanh::lean_dec_ref(v_a_5714_);
    crate::leanh::lean_dec(v_a_5713_);
    crate::leanh::lean_dec_ref(v_a_5712_);
    crate::leanh::lean_dec(v_a_5711_);
    crate::leanh::lean_dec_ref(v_a_5710_);
    crate::leanh::lean_dec(v_a_5709_);
    crate::leanh::lean_dec_ref(v_a_5708_);
    crate::leanh::lean_dec(v_a_5707_);
    crate::leanh::lean_dec(v_a_5706_);
    return v_res_5717_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(
    mut v_c_5718_: *mut crate::leanh::LeanObject,
    mut v_a_5719_: *mut crate::leanh::LeanObject,
    mut v_a_5720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_p_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_p_5722_ = crate::leanh::lean_ctor_get(v_c_5718_, 0);
    crate::leanh::lean_inc_ref(v_p_5722_);
    crate::leanh::lean_dec_ref(v_c_5718_);
    v___x_5723_ = l_Int_Linear_Poly_satisfiedLe___redArg(v_p_5722_, v_a_5719_, v_a_5720_);
    return v___x_5723_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg___boxed(
    mut v_c_5724_: *mut crate::leanh::LeanObject,
    mut v_a_5725_: *mut crate::leanh::LeanObject,
    mut v_a_5726_: *mut crate::leanh::LeanObject,
    mut v_a_5727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5728_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v_c_5724_, v_a_5725_, v_a_5726_);
    crate::leanh::lean_dec_ref(v_a_5726_);
    crate::leanh::lean_dec(v_a_5725_);
    return v_res_5728_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(
    mut v_c_5729_: *mut crate::leanh::LeanObject,
    mut v_a_5730_: *mut crate::leanh::LeanObject,
    mut v_a_5731_: *mut crate::leanh::LeanObject,
    mut v_a_5732_: *mut crate::leanh::LeanObject,
    mut v_a_5733_: *mut crate::leanh::LeanObject,
    mut v_a_5734_: *mut crate::leanh::LeanObject,
    mut v_a_5735_: *mut crate::leanh::LeanObject,
    mut v_a_5736_: *mut crate::leanh::LeanObject,
    mut v_a_5737_: *mut crate::leanh::LeanObject,
    mut v_a_5738_: *mut crate::leanh::LeanObject,
    mut v_a_5739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5741_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v_c_5729_, v_a_5730_, v_a_5738_);
    return v___x_5741_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___boxed(
    mut v_c_5742_: *mut crate::leanh::LeanObject,
    mut v_a_5743_: *mut crate::leanh::LeanObject,
    mut v_a_5744_: *mut crate::leanh::LeanObject,
    mut v_a_5745_: *mut crate::leanh::LeanObject,
    mut v_a_5746_: *mut crate::leanh::LeanObject,
    mut v_a_5747_: *mut crate::leanh::LeanObject,
    mut v_a_5748_: *mut crate::leanh::LeanObject,
    mut v_a_5749_: *mut crate::leanh::LeanObject,
    mut v_a_5750_: *mut crate::leanh::LeanObject,
    mut v_a_5751_: *mut crate::leanh::LeanObject,
    mut v_a_5752_: *mut crate::leanh::LeanObject,
    mut v_a_5753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5754_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied(
        v_c_5742_, v_a_5743_, v_a_5744_, v_a_5745_, v_a_5746_, v_a_5747_, v_a_5748_, v_a_5749_,
        v_a_5750_, v_a_5751_, v_a_5752_,
    );
    crate::leanh::lean_dec(v_a_5752_);
    crate::leanh::lean_dec_ref(v_a_5751_);
    crate::leanh::lean_dec(v_a_5750_);
    crate::leanh::lean_dec_ref(v_a_5749_);
    crate::leanh::lean_dec(v_a_5748_);
    crate::leanh::lean_dec_ref(v_a_5747_);
    crate::leanh::lean_dec(v_a_5746_);
    crate::leanh::lean_dec_ref(v_a_5745_);
    crate::leanh::lean_dec(v_a_5744_);
    crate::leanh::lean_dec(v_a_5743_);
    return v_res_5754_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(
    mut v_c_5755_: *mut crate::leanh::LeanObject,
    mut v_a_5756_: *mut crate::leanh::LeanObject,
    mut v_a_5757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_p_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5764_: u8 = 0;
    let mut v___y_5766_: u8 = 0;
    let mut v___x_5767_: u8 = 0;
    let mut v___x_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: u8 = 0;
    let mut v___x_5775_: u8 = 0;
    let mut v___x_5776_: u8 = 0;
    let mut v___x_5777_: u8 = 0;
    let mut v___x_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5780_: u8 = 0;
    let mut v_a_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5784_: u8 = 0;
    let mut v___x_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5788_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_p_5759_ = crate::leanh::lean_ctor_get(v_c_5755_, 0);
                crate::leanh::lean_inc_ref(v_p_5759_);
                crate::leanh::lean_dec_ref(v_c_5755_);
                v___x_5760_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_5759_, v_a_5756_, v_a_5757_);
                if crate::leanh::lean_obj_tag(v___x_5760_) == 0 {
                    v_a_5761_ = crate::leanh::lean_ctor_get(v___x_5760_, 0);
                    v_isSharedCheck_5780_ = (!crate::leanh::lean_is_exclusive(v___x_5760_)) as u8;
                    if v_isSharedCheck_5780_ == 0 {
                        v___x_5763_ = v___x_5760_;
                        v_isShared_5764_ = v_isSharedCheck_5780_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5761_);
                        crate::leanh::lean_dec(v___x_5760_);
                        v___x_5763_ = crate::leanh::lean_box(0);
                        v_isShared_5764_ = v_isSharedCheck_5780_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5781_ = crate::leanh::lean_ctor_get(v___x_5760_, 0);
                    v_isSharedCheck_5788_ = (!crate::leanh::lean_is_exclusive(v___x_5760_)) as u8;
                    if v_isSharedCheck_5788_ == 0 {
                        v___x_5783_ = v___x_5760_;
                        v_isShared_5784_ = v_isSharedCheck_5788_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5781_);
                        crate::leanh::lean_dec(v___x_5760_);
                        v___x_5783_ = crate::leanh::lean_box(0);
                        v_isShared_5784_ = v_isSharedCheck_5788_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5761_) == 1 {
                    v_val_5772_ = crate::leanh::lean_ctor_get(v_a_5761_, 0);
                    crate::leanh::lean_inc(v_val_5772_);
                    crate::leanh::lean_dec_ref_known(v_a_5761_, 1);
                    v___x_5773_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Int_Linear_Poly_eval_x3f___redArg___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Int_Linear_Poly_eval_x3f___redArg___closed__0_once
                        ),
                        _init_l_Int_Linear_Poly_eval_x3f___redArg___closed__0,
                    );
                    v___x_5774_ = l_instDecidableEqRat_decEq(v_val_5772_, v___x_5773_);
                    crate::leanh::lean_dec(v_val_5772_);
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
                    crate::leanh::lean_del_object(v___x_5763_);
                    crate::leanh::lean_dec(v_a_5761_);
                    v___x_5777_ = 2;
                    v___x_5778_ = crate::leanh::lean_box((v___x_5777_) as usize);
                    v___x_5779_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5779_, 0, v___x_5778_);
                    return v___x_5779_;
                }
            }
            2 => {
                v___x_5767_ = l_Bool_toLBool(v___y_5766_);
                v___x_5768_ = crate::leanh::lean_box((v___x_5767_) as usize);
                if v_isShared_5764_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5763_, 0, v___x_5768_);
                    v___x_5770_ = v___x_5763_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5771_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5771_, 0, v___x_5768_);
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
                    v_reuseFailAlloc_5787_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5787_, 0, v_a_5781_);
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
    mut v_c_5789_: *mut crate::leanh::LeanObject,
    mut v_a_5790_: *mut crate::leanh::LeanObject,
    mut v_a_5791_: *mut crate::leanh::LeanObject,
    mut v_a_5792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5793_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(
        v_c_5789_, v_a_5790_, v_a_5791_,
    );
    crate::leanh::lean_dec_ref(v_a_5791_);
    crate::leanh::lean_dec(v_a_5790_);
    return v_res_5793_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(
    mut v_c_5794_: *mut crate::leanh::LeanObject,
    mut v_a_5795_: *mut crate::leanh::LeanObject,
    mut v_a_5796_: *mut crate::leanh::LeanObject,
    mut v_a_5797_: *mut crate::leanh::LeanObject,
    mut v_a_5798_: *mut crate::leanh::LeanObject,
    mut v_a_5799_: *mut crate::leanh::LeanObject,
    mut v_a_5800_: *mut crate::leanh::LeanObject,
    mut v_a_5801_: *mut crate::leanh::LeanObject,
    mut v_a_5802_: *mut crate::leanh::LeanObject,
    mut v_a_5803_: *mut crate::leanh::LeanObject,
    mut v_a_5804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5806_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___redArg(
        v_c_5794_, v_a_5795_, v_a_5803_,
    );
    return v___x_5806_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied___boxed(
    mut v_c_5807_: *mut crate::leanh::LeanObject,
    mut v_a_5808_: *mut crate::leanh::LeanObject,
    mut v_a_5809_: *mut crate::leanh::LeanObject,
    mut v_a_5810_: *mut crate::leanh::LeanObject,
    mut v_a_5811_: *mut crate::leanh::LeanObject,
    mut v_a_5812_: *mut crate::leanh::LeanObject,
    mut v_a_5813_: *mut crate::leanh::LeanObject,
    mut v_a_5814_: *mut crate::leanh::LeanObject,
    mut v_a_5815_: *mut crate::leanh::LeanObject,
    mut v_a_5816_: *mut crate::leanh::LeanObject,
    mut v_a_5817_: *mut crate::leanh::LeanObject,
    mut v_a_5818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5819_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_satisfied(
        v_c_5807_, v_a_5808_, v_a_5809_, v_a_5810_, v_a_5811_, v_a_5812_, v_a_5813_, v_a_5814_,
        v_a_5815_, v_a_5816_, v_a_5817_,
    );
    crate::leanh::lean_dec(v_a_5817_);
    crate::leanh::lean_dec_ref(v_a_5816_);
    crate::leanh::lean_dec(v_a_5815_);
    crate::leanh::lean_dec_ref(v_a_5814_);
    crate::leanh::lean_dec(v_a_5813_);
    crate::leanh::lean_dec_ref(v_a_5812_);
    crate::leanh::lean_dec(v_a_5811_);
    crate::leanh::lean_dec_ref(v_a_5810_);
    crate::leanh::lean_dec(v_a_5809_);
    crate::leanh::lean_dec(v_a_5808_);
    return v_res_5819_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(
    mut v_c_5820_: *mut crate::leanh::LeanObject,
    mut v_a_5821_: *mut crate::leanh::LeanObject,
    mut v_a_5822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_p_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5829_: u8 = 0;
    let mut v_val_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: u8 = 0;
    let mut v___x_5833_: u8 = 0;
    let mut v___x_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5838_: u8 = 0;
    let mut v___x_5839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5843_: u8 = 0;
    let mut v_a_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5847_: u8 = 0;
    let mut v___x_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5851_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_p_5824_ = crate::leanh::lean_ctor_get(v_c_5820_, 0);
                crate::leanh::lean_inc_ref(v_p_5824_);
                crate::leanh::lean_dec_ref(v_c_5820_);
                v___x_5825_ = l_Int_Linear_Poly_eval_x3f___redArg(v_p_5824_, v_a_5821_, v_a_5822_);
                if crate::leanh::lean_obj_tag(v___x_5825_) == 0 {
                    v_a_5826_ = crate::leanh::lean_ctor_get(v___x_5825_, 0);
                    v_isSharedCheck_5843_ = (!crate::leanh::lean_is_exclusive(v___x_5825_)) as u8;
                    if v_isSharedCheck_5843_ == 0 {
                        v___x_5828_ = v___x_5825_;
                        v_isShared_5829_ = v_isSharedCheck_5843_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5826_);
                        crate::leanh::lean_dec(v___x_5825_);
                        v___x_5828_ = crate::leanh::lean_box(0);
                        v_isShared_5829_ = v_isSharedCheck_5843_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5844_ = crate::leanh::lean_ctor_get(v___x_5825_, 0);
                    v_isSharedCheck_5851_ = (!crate::leanh::lean_is_exclusive(v___x_5825_)) as u8;
                    if v_isSharedCheck_5851_ == 0 {
                        v___x_5846_ = v___x_5825_;
                        v_isShared_5847_ = v_isSharedCheck_5851_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5844_);
                        crate::leanh::lean_dec(v___x_5825_);
                        v___x_5846_ = crate::leanh::lean_box(0);
                        v_isShared_5847_ = v_isSharedCheck_5851_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5826_) == 1 {
                    v_val_5830_ = crate::leanh::lean_ctor_get(v_a_5826_, 0);
                    crate::leanh::lean_inc(v_val_5830_);
                    crate::leanh::lean_dec_ref_known(v_a_5826_, 1);
                    v___x_5831_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Int_Linear_Poly_eval_x3f___redArg___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Int_Linear_Poly_eval_x3f___redArg___closed__0_once
                        ),
                        _init_l_Int_Linear_Poly_eval_x3f___redArg___closed__0,
                    );
                    v___x_5832_ = l_instDecidableEqRat_decEq(v_val_5830_, v___x_5831_);
                    crate::leanh::lean_dec(v_val_5830_);
                    v___x_5833_ = l_Bool_toLBool(v___x_5832_);
                    v___x_5834_ = crate::leanh::lean_box((v___x_5833_) as usize);
                    if v_isShared_5829_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5828_, 0, v___x_5834_);
                        v___x_5836_ = v___x_5828_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5837_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5837_, 0, v___x_5834_);
                        v___x_5836_ = v_reuseFailAlloc_5837_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5826_);
                    v___x_5838_ = 2;
                    v___x_5839_ = crate::leanh::lean_box((v___x_5838_) as usize);
                    if v_isShared_5829_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5828_, 0, v___x_5839_);
                        v___x_5841_ = v___x_5828_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5842_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5842_, 0, v___x_5839_);
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
                    v_reuseFailAlloc_5850_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5850_, 0, v_a_5844_);
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
    mut v_c_5852_: *mut crate::leanh::LeanObject,
    mut v_a_5853_: *mut crate::leanh::LeanObject,
    mut v_a_5854_: *mut crate::leanh::LeanObject,
    mut v_a_5855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5856_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(v_c_5852_, v_a_5853_, v_a_5854_);
    crate::leanh::lean_dec_ref(v_a_5854_);
    crate::leanh::lean_dec(v_a_5853_);
    return v_res_5856_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(
    mut v_c_5857_: *mut crate::leanh::LeanObject,
    mut v_a_5858_: *mut crate::leanh::LeanObject,
    mut v_a_5859_: *mut crate::leanh::LeanObject,
    mut v_a_5860_: *mut crate::leanh::LeanObject,
    mut v_a_5861_: *mut crate::leanh::LeanObject,
    mut v_a_5862_: *mut crate::leanh::LeanObject,
    mut v_a_5863_: *mut crate::leanh::LeanObject,
    mut v_a_5864_: *mut crate::leanh::LeanObject,
    mut v_a_5865_: *mut crate::leanh::LeanObject,
    mut v_a_5866_: *mut crate::leanh::LeanObject,
    mut v_a_5867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5869_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___redArg(v_c_5857_, v_a_5858_, v_a_5866_);
    return v___x_5869_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied___boxed(
    mut v_c_5870_: *mut crate::leanh::LeanObject,
    mut v_a_5871_: *mut crate::leanh::LeanObject,
    mut v_a_5872_: *mut crate::leanh::LeanObject,
    mut v_a_5873_: *mut crate::leanh::LeanObject,
    mut v_a_5874_: *mut crate::leanh::LeanObject,
    mut v_a_5875_: *mut crate::leanh::LeanObject,
    mut v_a_5876_: *mut crate::leanh::LeanObject,
    mut v_a_5877_: *mut crate::leanh::LeanObject,
    mut v_a_5878_: *mut crate::leanh::LeanObject,
    mut v_a_5879_: *mut crate::leanh::LeanObject,
    mut v_a_5880_: *mut crate::leanh::LeanObject,
    mut v_a_5881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5882_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_satisfied(
        v_c_5870_, v_a_5871_, v_a_5872_, v_a_5873_, v_a_5874_, v_a_5875_, v_a_5876_, v_a_5877_,
        v_a_5878_, v_a_5879_, v_a_5880_,
    );
    crate::leanh::lean_dec(v_a_5880_);
    crate::leanh::lean_dec_ref(v_a_5879_);
    crate::leanh::lean_dec(v_a_5878_);
    crate::leanh::lean_dec_ref(v_a_5877_);
    crate::leanh::lean_dec(v_a_5876_);
    crate::leanh::lean_dec_ref(v_a_5875_);
    crate::leanh::lean_dec(v_a_5874_);
    crate::leanh::lean_dec_ref(v_a_5873_);
    crate::leanh::lean_dec(v_a_5872_);
    crate::leanh::lean_dec(v_a_5871_);
    return v_res_5882_;
}
pub unsafe fn l_Int_Linear_Poly_findVarToSubst___redArg(
    mut v_p_5883_: *mut crate::leanh::LeanObject,
    mut v_a_5884_: *mut crate::leanh::LeanObject,
    mut v_a_5885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5889_: u8 = 0;
    let mut v___x_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5894_: u8 = 0;
    let mut v_unused_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5903_: u8 = 0;
    let mut v___y_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5909_: u8 = 0;
    let mut v___x_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5918_: u8 = 0;
    let mut v_elimEqs_5920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5923_: u8 = 0;
    let mut v___x_5924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5926_: u8 = 0;
    let mut v_a_5927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5930_: u8 = 0;
    let mut v___x_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5934_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_5883_) == 0 {
                    v_isSharedCheck_5894_ = (!crate::leanh::lean_is_exclusive(v_p_5883_)) as u8;
                    if v_isSharedCheck_5894_ == 0 {
                        v_unused_5895_ = crate::leanh::lean_ctor_get(v_p_5883_, 0);
                        crate::leanh::lean_dec(v_unused_5895_);
                        v___x_5888_ = v_p_5883_;
                        v_isShared_5889_ = v_isSharedCheck_5894_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_p_5883_);
                        v___x_5888_ = crate::leanh::lean_box(0);
                        v_isShared_5889_ = v_isSharedCheck_5894_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_5896_ = crate::leanh::lean_ctor_get(v_p_5883_, 0);
                    crate::leanh::lean_inc(v_k_5896_);
                    v_v_5897_ = crate::leanh::lean_ctor_get(v_p_5883_, 1);
                    crate::leanh::lean_inc(v_v_5897_);
                    v_p_5898_ = crate::leanh::lean_ctor_get(v_p_5883_, 2);
                    crate::leanh::lean_inc_ref(v_p_5898_);
                    crate::leanh::lean_dec_ref_known(v_p_5883_, 3);
                    v___x_5899_ =
                        l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_5884_, v_a_5885_);
                    if crate::leanh::lean_obj_tag(v___x_5899_) == 0 {
                        v_a_5900_ = crate::leanh::lean_ctor_get(v___x_5899_, 0);
                        v_isSharedCheck_5926_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5899_)) as u8;
                        if v_isSharedCheck_5926_ == 0 {
                            v___x_5902_ = v___x_5899_;
                            v_isShared_5903_ = v_isSharedCheck_5926_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5900_);
                            crate::leanh::lean_dec(v___x_5899_);
                            v___x_5902_ = crate::leanh::lean_box(0);
                            v_isShared_5903_ = v_isSharedCheck_5926_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_p_5898_);
                        crate::leanh::lean_dec(v_v_5897_);
                        crate::leanh::lean_dec(v_k_5896_);
                        v_a_5927_ = crate::leanh::lean_ctor_get(v___x_5899_, 0);
                        v_isSharedCheck_5934_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5899_)) as u8;
                        if v_isSharedCheck_5934_ == 0 {
                            v___x_5929_ = v___x_5899_;
                            v_isShared_5930_ = v_isSharedCheck_5934_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5927_);
                            crate::leanh::lean_dec(v___x_5899_);
                            v___x_5929_ = crate::leanh::lean_box(0);
                            v_isShared_5930_ = v_isSharedCheck_5934_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5890_ = crate::leanh::lean_box(0);
                if v_isShared_5889_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5888_, 0, v___x_5890_);
                    v___x_5892_ = v___x_5888_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5893_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5893_, 0, v___x_5890_);
                    v___x_5892_ = v_reuseFailAlloc_5893_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5892_;
            }
            3 => {
                v_elimEqs_5920_ = crate::leanh::lean_ctor_get(v_a_5900_, 10);
                crate::leanh::lean_inc_ref(v_elimEqs_5920_);
                crate::leanh::lean_dec(v_a_5900_);
                v_size_5921_ = crate::leanh::lean_ctor_get(v_elimEqs_5920_, 2);
                v___x_5922_ = crate::leanh::lean_box(0);
                v___x_5923_ = lean_nat_dec_lt(v_v_5897_, v_size_5921_);
                if v___x_5923_ == 0 {
                    crate::leanh::lean_dec_ref(v_elimEqs_5920_);
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
                    crate::leanh::lean_dec_ref(v_elimEqs_5920_);
                    v___y_5905_ = v___x_5925_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if crate::leanh::lean_obj_tag(v___y_5905_) == 1 {
                    crate::leanh::lean_dec_ref(v_p_5898_);
                    v_val_5906_ = crate::leanh::lean_ctor_get(v___y_5905_, 0);
                    v_isSharedCheck_5918_ = (!crate::leanh::lean_is_exclusive(v___y_5905_)) as u8;
                    if v_isSharedCheck_5918_ == 0 {
                        v___x_5908_ = v___y_5905_;
                        v_isShared_5909_ = v_isSharedCheck_5918_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5906_);
                        crate::leanh::lean_dec(v___y_5905_);
                        v___x_5908_ = crate::leanh::lean_box(0);
                        v_isShared_5909_ = v_isSharedCheck_5918_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_5905_);
                    crate::leanh::lean_del_object(v___x_5902_);
                    crate::leanh::lean_dec(v_v_5897_);
                    crate::leanh::lean_dec(v_k_5896_);
                    v_p_5883_ = v_p_5898_;
                    state = 0;
                    continue;
                }
            }
            5 => {
                v___x_5910_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5910_, 0, v_v_5897_);
                crate::leanh::lean_ctor_set(v___x_5910_, 1, v_val_5906_);
                v___x_5911_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5911_, 0, v_k_5896_);
                crate::leanh::lean_ctor_set(v___x_5911_, 1, v___x_5910_);
                if v_isShared_5909_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5908_, 0, v___x_5911_);
                    v___x_5913_ = v___x_5908_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5917_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5917_, 0, v___x_5911_);
                    v___x_5913_ = v_reuseFailAlloc_5917_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_5903_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5902_, 0, v___x_5913_);
                    v___x_5915_ = v___x_5902_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5916_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5916_, 0, v___x_5913_);
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
                    v_reuseFailAlloc_5933_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5933_, 0, v_a_5927_);
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
    mut v_p_5935_: *mut crate::leanh::LeanObject,
    mut v_a_5936_: *mut crate::leanh::LeanObject,
    mut v_a_5937_: *mut crate::leanh::LeanObject,
    mut v_a_5938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5939_ = l_Int_Linear_Poly_findVarToSubst___redArg(v_p_5935_, v_a_5936_, v_a_5937_);
    crate::leanh::lean_dec_ref(v_a_5937_);
    crate::leanh::lean_dec(v_a_5936_);
    return v_res_5939_;
}
pub unsafe fn l_Int_Linear_Poly_findVarToSubst(
    mut v_p_5940_: *mut crate::leanh::LeanObject,
    mut v_a_5941_: *mut crate::leanh::LeanObject,
    mut v_a_5942_: *mut crate::leanh::LeanObject,
    mut v_a_5943_: *mut crate::leanh::LeanObject,
    mut v_a_5944_: *mut crate::leanh::LeanObject,
    mut v_a_5945_: *mut crate::leanh::LeanObject,
    mut v_a_5946_: *mut crate::leanh::LeanObject,
    mut v_a_5947_: *mut crate::leanh::LeanObject,
    mut v_a_5948_: *mut crate::leanh::LeanObject,
    mut v_a_5949_: *mut crate::leanh::LeanObject,
    mut v_a_5950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5952_ = l_Int_Linear_Poly_findVarToSubst___redArg(v_p_5940_, v_a_5941_, v_a_5949_);
    return v___x_5952_;
}
pub unsafe fn l_Int_Linear_Poly_findVarToSubst___boxed(
    mut v_p_5953_: *mut crate::leanh::LeanObject,
    mut v_a_5954_: *mut crate::leanh::LeanObject,
    mut v_a_5955_: *mut crate::leanh::LeanObject,
    mut v_a_5956_: *mut crate::leanh::LeanObject,
    mut v_a_5957_: *mut crate::leanh::LeanObject,
    mut v_a_5958_: *mut crate::leanh::LeanObject,
    mut v_a_5959_: *mut crate::leanh::LeanObject,
    mut v_a_5960_: *mut crate::leanh::LeanObject,
    mut v_a_5961_: *mut crate::leanh::LeanObject,
    mut v_a_5962_: *mut crate::leanh::LeanObject,
    mut v_a_5963_: *mut crate::leanh::LeanObject,
    mut v_a_5964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5965_ = l_Int_Linear_Poly_findVarToSubst(
        v_p_5953_, v_a_5954_, v_a_5955_, v_a_5956_, v_a_5957_, v_a_5958_, v_a_5959_, v_a_5960_,
        v_a_5961_, v_a_5962_, v_a_5963_,
    );
    crate::leanh::lean_dec(v_a_5963_);
    crate::leanh::lean_dec_ref(v_a_5962_);
    crate::leanh::lean_dec(v_a_5961_);
    crate::leanh::lean_dec_ref(v_a_5960_);
    crate::leanh::lean_dec(v_a_5959_);
    crate::leanh::lean_dec_ref(v_a_5958_);
    crate::leanh::lean_dec(v_a_5957_);
    crate::leanh::lean_dec_ref(v_a_5956_);
    crate::leanh::lean_dec(v_a_5955_);
    crate::leanh::lean_dec(v_a_5954_);
    return v_res_5965_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(
    mut v_pred_5966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_u2081_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_u2082_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_left_5969_: u8 = 0;
    let mut v_c_u2083_x3f_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_u2081_5967_ = crate::leanh::lean_ctor_get(v_pred_5966_, 0);
    v_c_u2082_5968_ = crate::leanh::lean_ctor_get(v_pred_5966_, 1);
    v_left_5969_ = crate::leanh::lean_ctor_get_uint8(
        v_pred_5966_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    v_c_u2083_x3f_5970_ = crate::leanh::lean_ctor_get(v_pred_5966_, 2);
    v_p_5971_ = crate::leanh::lean_ctor_get(v_c_u2081_5967_, 0);
    v_p_5972_ = crate::leanh::lean_ctor_get(v_c_u2082_5968_, 0);
    v_a_5973_ = l_Int_Linear_Poly_leadCoeff(v_p_5971_);
    v_b_5974_ = l_Int_Linear_Poly_leadCoeff(v_p_5972_);
    if crate::leanh::lean_obj_tag(v_c_u2083_x3f_5970_) == 0 {
        if v_left_5969_ == 0 {
            let mut v___x_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_a_5973_);
            v___x_5975_ = lean_nat_abs(v_b_5974_);
            crate::leanh::lean_dec(v_b_5974_);
            return v___x_5975_;
        } else {
            let mut v___x_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_b_5974_);
            v___x_5976_ = lean_nat_abs(v_a_5973_);
            crate::leanh::lean_dec(v_a_5973_);
            return v___x_5976_;
        }
    } else {
        let mut v_val_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_d_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_5979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_c_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5977_ = crate::leanh::lean_ctor_get(v_c_u2083_x3f_5970_, 0);
        v_d_5978_ = crate::leanh::lean_ctor_get(v_val_5977_, 0);
        v_p_5979_ = crate::leanh::lean_ctor_get(v_val_5977_, 1);
        v_c_5980_ = l_Int_Linear_Poly_leadCoeff(v_p_5979_);
        if v_left_5969_ == 0 {
            let mut v___x_5981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_a_5973_);
            v___x_5981_ = lean_int_mul(v_b_5974_, v_d_5978_);
            v___x_5982_ = l_Int_gcd(v___x_5981_, v_c_5980_);
            crate::leanh::lean_dec(v_c_5980_);
            v___x_5983_ = lean_nat_to_int(v___x_5982_);
            v___x_5984_ = lean_int_ediv(v___x_5981_, v___x_5983_);
            crate::leanh::lean_dec(v___x_5983_);
            crate::leanh::lean_dec(v___x_5981_);
            v___x_5985_ = l_Int_lcm(v_b_5974_, v___x_5984_);
            crate::leanh::lean_dec(v___x_5984_);
            crate::leanh::lean_dec(v_b_5974_);
            return v___x_5985_;
        } else {
            let mut v___x_5986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_b_5974_);
            v___x_5986_ = lean_int_mul(v_a_5973_, v_d_5978_);
            v___x_5987_ = l_Int_gcd(v___x_5986_, v_c_5980_);
            crate::leanh::lean_dec(v_c_5980_);
            v___x_5988_ = lean_nat_to_int(v___x_5987_);
            v___x_5989_ = lean_int_ediv(v___x_5986_, v___x_5988_);
            crate::leanh::lean_dec(v___x_5988_);
            crate::leanh::lean_dec(v___x_5986_);
            v___x_5990_ = l_Int_lcm(v_a_5973_, v___x_5989_);
            crate::leanh::lean_dec(v___x_5989_);
            crate::leanh::lean_dec(v_a_5973_);
            return v___x_5990_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases___boxed(
    mut v_pred_5991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5992_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_numCases(v_pred_5991_);
    crate::leanh::lean_dec_ref(v_pred_5991_);
    return v_res_5992_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5994_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__0;
    v___x_5995_ = l_Lean_stringToMessageData(v___x_5994_);
    return v___x_5995_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5999_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__3;
    v___x_6000_ = l_Lean_MessageData_ofFormat(v___x_5999_);
    return v___x_6000_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(
    mut v_pred_6001_: *mut crate::leanh::LeanObject,
    mut v_a_6002_: *mut crate::leanh::LeanObject,
    mut v_a_6003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_u2081_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_u2082_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_u2083_x3f_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6014_: u8 = 0;
    let mut v_a_6016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6029_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_c_u2081_6005_ = crate::leanh::lean_ctor_get(v_pred_6001_, 0);
                crate::leanh::lean_inc_ref(v_c_u2081_6005_);
                v_c_u2082_6006_ = crate::leanh::lean_ctor_get(v_pred_6001_, 1);
                crate::leanh::lean_inc_ref(v_c_u2082_6006_);
                v_c_u2083_x3f_6007_ = crate::leanh::lean_ctor_get(v_pred_6001_, 2);
                crate::leanh::lean_inc(v_c_u2083_x3f_6007_);
                crate::leanh::lean_dec_ref(v_pred_6001_);
                v___x_6008_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(
                    v_c_u2081_6005_,
                    v_a_6002_,
                    v_a_6003_,
                );
                if crate::leanh::lean_obj_tag(v___x_6008_) == 0 {
                    v_a_6009_ = crate::leanh::lean_ctor_get(v___x_6008_, 0);
                    crate::leanh::lean_inc(v_a_6009_);
                    crate::leanh::lean_dec_ref_known(v___x_6008_, 1);
                    v___x_6010_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(
                        v_c_u2082_6006_,
                        v_a_6002_,
                        v_a_6003_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6010_) == 0 {
                        v_a_6011_ = crate::leanh::lean_ctor_get(v___x_6010_, 0);
                        v_isSharedCheck_6029_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6010_)) as u8;
                        if v_isSharedCheck_6029_ == 0 {
                            v___x_6013_ = v___x_6010_;
                            v_isShared_6014_ = v_isSharedCheck_6029_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6011_);
                            crate::leanh::lean_dec(v___x_6010_);
                            v___x_6013_ = crate::leanh::lean_box(0);
                            v_isShared_6014_ = v_isSharedCheck_6029_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6009_);
                        crate::leanh::lean_dec(v_c_u2083_x3f_6007_);
                        return v___x_6010_;
                    }
                } else {
                    crate::leanh::lean_dec(v_c_u2083_x3f_6007_);
                    crate::leanh::lean_dec_ref(v_c_u2082_6006_);
                    return v___x_6008_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_c_u2083_x3f_6007_) == 1 {
                    v_val_6025_ = crate::leanh::lean_ctor_get(v_c_u2083_x3f_6007_, 0);
                    crate::leanh::lean_inc(v_val_6025_);
                    crate::leanh::lean_dec_ref_known(v_c_u2083_x3f_6007_, 1);
                    v___x_6026_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(
                        v_val_6025_,
                        v_a_6002_,
                        v_a_6003_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6026_) == 0 {
                        v_a_6027_ = crate::leanh::lean_ctor_get(v___x_6026_, 0);
                        crate::leanh::lean_inc(v_a_6027_);
                        crate::leanh::lean_dec_ref_known(v___x_6026_, 1);
                        v_a_6016_ = v_a_6027_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_6013_);
                        crate::leanh::lean_dec(v_a_6011_);
                        crate::leanh::lean_dec(v_a_6009_);
                        return v___x_6026_;
                    }
                } else {
                    crate::leanh::lean_dec(v_c_u2083_x3f_6007_);
                    v___x_6028_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__4);
                    v_a_6016_ = v___x_6028_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6017_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1,
                );
                v___x_6018_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6018_, 0, v_a_6009_);
                crate::leanh::lean_ctor_set(v___x_6018_, 1, v___x_6017_);
                v___x_6019_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6019_, 0, v___x_6018_);
                crate::leanh::lean_ctor_set(v___x_6019_, 1, v_a_6011_);
                v___x_6020_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6020_, 0, v___x_6019_);
                crate::leanh::lean_ctor_set(v___x_6020_, 1, v___x_6017_);
                v___x_6021_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6021_, 0, v___x_6020_);
                crate::leanh::lean_ctor_set(v___x_6021_, 1, v_a_6016_);
                if v_isShared_6014_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6013_, 0, v___x_6021_);
                    v___x_6023_ = v___x_6013_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6024_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6024_, 0, v___x_6021_);
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
    mut v_pred_6030_: *mut crate::leanh::LeanObject,
    mut v_a_6031_: *mut crate::leanh::LeanObject,
    mut v_a_6032_: *mut crate::leanh::LeanObject,
    mut v_a_6033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6034_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(
        v_pred_6030_,
        v_a_6031_,
        v_a_6032_,
    );
    crate::leanh::lean_dec_ref(v_a_6032_);
    crate::leanh::lean_dec(v_a_6031_);
    return v_res_6034_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp(
    mut v_pred_6035_: *mut crate::leanh::LeanObject,
    mut v_a_6036_: *mut crate::leanh::LeanObject,
    mut v_a_6037_: *mut crate::leanh::LeanObject,
    mut v_a_6038_: *mut crate::leanh::LeanObject,
    mut v_a_6039_: *mut crate::leanh::LeanObject,
    mut v_a_6040_: *mut crate::leanh::LeanObject,
    mut v_a_6041_: *mut crate::leanh::LeanObject,
    mut v_a_6042_: *mut crate::leanh::LeanObject,
    mut v_a_6043_: *mut crate::leanh::LeanObject,
    mut v_a_6044_: *mut crate::leanh::LeanObject,
    mut v_a_6045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6047_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg(
        v_pred_6035_,
        v_a_6036_,
        v_a_6044_,
    );
    return v___x_6047_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___boxed(
    mut v_pred_6048_: *mut crate::leanh::LeanObject,
    mut v_a_6049_: *mut crate::leanh::LeanObject,
    mut v_a_6050_: *mut crate::leanh::LeanObject,
    mut v_a_6051_: *mut crate::leanh::LeanObject,
    mut v_a_6052_: *mut crate::leanh::LeanObject,
    mut v_a_6053_: *mut crate::leanh::LeanObject,
    mut v_a_6054_: *mut crate::leanh::LeanObject,
    mut v_a_6055_: *mut crate::leanh::LeanObject,
    mut v_a_6056_: *mut crate::leanh::LeanObject,
    mut v_a_6057_: *mut crate::leanh::LeanObject,
    mut v_a_6058_: *mut crate::leanh::LeanObject,
    mut v_a_6059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_6058_);
    crate::leanh::lean_dec_ref(v_a_6057_);
    crate::leanh::lean_dec(v_a_6056_);
    crate::leanh::lean_dec_ref(v_a_6055_);
    crate::leanh::lean_dec(v_a_6054_);
    crate::leanh::lean_dec_ref(v_a_6053_);
    crate::leanh::lean_dec(v_a_6052_);
    crate::leanh::lean_dec_ref(v_a_6051_);
    crate::leanh::lean_dec(v_a_6050_);
    crate::leanh::lean_dec(v_a_6049_);
    return v_res_6060_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(
    mut v_h_6061_: *mut crate::leanh::LeanObject,
    mut v_a_6062_: *mut crate::leanh::LeanObject,
    mut v_a_6063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_6067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_6069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_u2081_6073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_u2082_6074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_u2083_6075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6084_: u8 = 0;
    let mut v___x_6085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6093_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_h_6061_) {
                0 => {
                    v_c_6065_ = crate::leanh::lean_ctor_get(v_h_6061_, 0);
                    crate::leanh::lean_inc_ref(v_c_6065_);
                    crate::leanh::lean_dec_ref_known(v_h_6061_, 1);
                    v___x_6066_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(
                        v_c_6065_, v_a_6062_, v_a_6063_,
                    );
                    return v___x_6066_;
                }
                1 => {
                    v_c_6067_ = crate::leanh::lean_ctor_get(v_h_6061_, 0);
                    crate::leanh::lean_inc_ref(v_c_6067_);
                    crate::leanh::lean_dec_ref_known(v_h_6061_, 1);
                    v___x_6068_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(
                        v_c_6067_, v_a_6062_, v_a_6063_,
                    );
                    return v___x_6068_;
                }
                2 => {
                    v_c_6069_ = crate::leanh::lean_ctor_get(v_h_6061_, 0);
                    crate::leanh::lean_inc_ref(v_c_6069_);
                    crate::leanh::lean_dec_ref_known(v_h_6061_, 1);
                    v___x_6070_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(
                        v_c_6069_, v_a_6062_, v_a_6063_,
                    );
                    return v___x_6070_;
                }
                3 => {
                    v_c_6071_ = crate::leanh::lean_ctor_get(v_h_6061_, 0);
                    crate::leanh::lean_inc_ref(v_c_6071_);
                    crate::leanh::lean_dec_ref_known(v_h_6061_, 1);
                    v___x_6072_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_pp___redArg(
                        v_c_6071_, v_a_6062_, v_a_6063_,
                    );
                    return v___x_6072_;
                }
                _ => {
                    v_c_u2081_6073_ = crate::leanh::lean_ctor_get(v_h_6061_, 0);
                    crate::leanh::lean_inc_ref(v_c_u2081_6073_);
                    v_c_u2082_6074_ = crate::leanh::lean_ctor_get(v_h_6061_, 1);
                    crate::leanh::lean_inc_ref(v_c_u2082_6074_);
                    v_c_u2083_6075_ = crate::leanh::lean_ctor_get(v_h_6061_, 2);
                    crate::leanh::lean_inc_ref(v_c_u2083_6075_);
                    crate::leanh::lean_dec_ref_known(v_h_6061_, 3);
                    v___x_6076_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(
                        v_c_u2081_6073_,
                        v_a_6062_,
                        v_a_6063_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6076_) == 0 {
                        v_a_6077_ = crate::leanh::lean_ctor_get(v___x_6076_, 0);
                        crate::leanh::lean_inc(v_a_6077_);
                        crate::leanh::lean_dec_ref_known(v___x_6076_, 1);
                        v___x_6078_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(
                            v_c_u2082_6074_,
                            v_a_6062_,
                            v_a_6063_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6078_) == 0 {
                            v_a_6079_ = crate::leanh::lean_ctor_get(v___x_6078_, 0);
                            crate::leanh::lean_inc(v_a_6079_);
                            crate::leanh::lean_dec_ref_known(v___x_6078_, 1);
                            v___x_6080_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(
                                v_c_u2083_6075_,
                                v_a_6062_,
                                v_a_6063_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_6080_) == 0 {
                                v_a_6081_ = crate::leanh::lean_ctor_get(v___x_6080_, 0);
                                v_isSharedCheck_6093_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6080_)) as u8;
                                if v_isSharedCheck_6093_ == 0 {
                                    v___x_6083_ = v___x_6080_;
                                    v_isShared_6084_ = v_isSharedCheck_6093_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6081_);
                                    crate::leanh::lean_dec(v___x_6080_);
                                    v___x_6083_ = crate::leanh::lean_box(0);
                                    v_isShared_6084_ = v_isSharedCheck_6093_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_6079_);
                                crate::leanh::lean_dec(v_a_6077_);
                                return v___x_6080_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_6077_);
                            crate::leanh::lean_dec_ref(v_c_u2083_6075_);
                            return v___x_6078_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_c_u2083_6075_);
                        crate::leanh::lean_dec_ref(v_c_u2082_6074_);
                        return v___x_6076_;
                    }
                }
            },
            1 => {
                v___x_6085_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitPred_pp___redArg___closed__1,
                );
                v___x_6086_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6086_, 0, v_a_6077_);
                crate::leanh::lean_ctor_set(v___x_6086_, 1, v___x_6085_);
                v___x_6087_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6087_, 0, v___x_6086_);
                crate::leanh::lean_ctor_set(v___x_6087_, 1, v_a_6079_);
                v___x_6088_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6088_, 0, v___x_6087_);
                crate::leanh::lean_ctor_set(v___x_6088_, 1, v___x_6085_);
                v___x_6089_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6089_, 0, v___x_6088_);
                crate::leanh::lean_ctor_set(v___x_6089_, 1, v_a_6081_);
                if v_isShared_6084_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6083_, 0, v___x_6089_);
                    v___x_6091_ = v___x_6083_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6092_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6092_, 0, v___x_6089_);
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
    mut v_h_6094_: *mut crate::leanh::LeanObject,
    mut v_a_6095_: *mut crate::leanh::LeanObject,
    mut v_a_6096_: *mut crate::leanh::LeanObject,
    mut v_a_6097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6098_ =
        l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(v_h_6094_, v_a_6095_, v_a_6096_);
    crate::leanh::lean_dec_ref(v_a_6096_);
    crate::leanh::lean_dec(v_a_6095_);
    return v_res_6098_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(
    mut v_h_6099_: *mut crate::leanh::LeanObject,
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
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6111_ =
        l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___redArg(v_h_6099_, v_a_6100_, v_a_6108_);
    return v___x_6111_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp___boxed(
    mut v_h_6112_: *mut crate::leanh::LeanObject,
    mut v_a_6113_: *mut crate::leanh::LeanObject,
    mut v_a_6114_: *mut crate::leanh::LeanObject,
    mut v_a_6115_: *mut crate::leanh::LeanObject,
    mut v_a_6116_: *mut crate::leanh::LeanObject,
    mut v_a_6117_: *mut crate::leanh::LeanObject,
    mut v_a_6118_: *mut crate::leanh::LeanObject,
    mut v_a_6119_: *mut crate::leanh::LeanObject,
    mut v_a_6120_: *mut crate::leanh::LeanObject,
    mut v_a_6121_: *mut crate::leanh::LeanObject,
    mut v_a_6122_: *mut crate::leanh::LeanObject,
    mut v_a_6123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6124_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_pp(
        v_h_6112_, v_a_6113_, v_a_6114_, v_a_6115_, v_a_6116_, v_a_6117_, v_a_6118_, v_a_6119_,
        v_a_6120_, v_a_6121_, v_a_6122_,
    );
    crate::leanh::lean_dec(v_a_6122_);
    crate::leanh::lean_dec_ref(v_a_6121_);
    crate::leanh::lean_dec(v_a_6120_);
    crate::leanh::lean_dec_ref(v_a_6119_);
    crate::leanh::lean_dec(v_a_6118_);
    crate::leanh::lean_dec_ref(v_a_6117_);
    crate::leanh::lean_dec(v_a_6116_);
    crate::leanh::lean_dec_ref(v_a_6115_);
    crate::leanh::lean_dec(v_a_6114_);
    crate::leanh::lean_dec(v_a_6113_);
    return v_res_6124_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
}
