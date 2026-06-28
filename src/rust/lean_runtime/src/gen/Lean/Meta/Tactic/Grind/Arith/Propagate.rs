// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Propagate
// Imports: Init.Grind Lean.Meta.Tactic.Grind.Arith.CommRing.RingId Lean.Meta.Tactic.Grind.Arith.CommRing.NonCommRingM Lean.Meta.Tactic.Grind.Arith.CommRing.NonCommSemiringM Lean.Meta.Tactic.Grind.PropagatorAttr
use crate::r#gen::Init::Data::Nat::Bitwise::Basic::{
    l_Nat_land___boxed, l_Nat_lor___boxed, l_Nat_shiftLeft___boxed, l_Nat_shiftRight___boxed,
    l_Nat_xor___boxed,
};
use crate::r#gen::Init::Grind::{initialize_Init_Grind, runtime_initialize_Init_Grind};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_constLevels_x21,
    l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_getRevArg_x21, l_Lean_Expr_isApp,
    l_Lean_Expr_isAppOfArity, l_Lean_Expr_isConstOf, l_Lean_eagerReflBoolTrue, l_Lean_mkApp5,
    l_Lean_mkApp8, l_Lean_mkConst, l_Lean_mkNatLit,
};
use crate::r#gen::Lean::Meta::LitValues::l_Lean_Meta_getNatValue_x3f;
use crate::r#gen::Lean::Meta::Sym::ExprPtr::l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1;
use crate::r#gen::Lean::Meta::Sym::SymM::l_Lean_Meta_Sym_shareCommon___redArg;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::NonCommRingM::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM,
    l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::NonCommSemiringM::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM,
    l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::RingId::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId,
    l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f,
    l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f,
    l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f,
    l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::SemiringM::l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring;
use crate::r#gen::Lean::Meta::Tactic::Grind::PropagatorAttr::{
    initialize_Lean_Meta_Tactic_Grind_PropagatorAttr,
    l_Lean_Meta_Grind_registerBuiltinUpwardPropagator,
    runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l_Lean_Meta_Grind_Goal_getRoot, l_Lean_Meta_Grind_pushEqCore___redArg,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_of_nat, lean_usize_sub};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_uint64_of_nat,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Meta::Tactic::Grind::Types::{
    lean_grind_internalize, lean_grind_mk_eq_proof,
};
pub static l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0_value:
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
    m_data: [78, 97, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11442535297760353691 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__0_value:
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
    m_fun: l_Nat_land___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__1_value:
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
    m_data: [72, 65, 110, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__2_value:
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
    m_data: [104, 65, 110, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__1_value)
            as *mut crate::leanh::LeanObject,
        12657514296478584286 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__2_value)
            as *mut crate::leanh::LeanObject,
        14441402839729941302 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value:
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
static mut l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value:
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
static mut l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__6_value:
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
    m_data: [97, 110, 100, 95, 99, 111, 110, 103, 114, 0],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0_value)
            as *mut crate::leanh::LeanObject,
        8407093297865582880 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__6_value)
            as *mut crate::leanh::LeanObject,
        11118137186597392547 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatOr___closed__0_value:
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
    m_fun: l_Nat_lor___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatOr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatOr___closed__1_value:
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
    m_data: [72, 79, 114, 0],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatOr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatOr___closed__2_value:
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
    m_data: [104, 79, 114, 0],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatOr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__1_value)
            as *mut crate::leanh::LeanObject,
        10041220898573864337 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__2_value)
            as *mut crate::leanh::LeanObject,
        9518792213721863725 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatOr___closed__4_value:
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
    m_data: [111, 114, 95, 99, 111, 110, 103, 114, 0],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatOr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0_value)
            as *mut crate::leanh::LeanObject,
        8407093297865582880 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__4_value)
            as *mut crate::leanh::LeanObject,
        937577760758191742 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__0_value:
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
    m_fun: l_Nat_xor___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__1_value:
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
    m_data: [72, 88, 111, 114, 0],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__2_value:
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
    m_data: [104, 88, 111, 114, 0],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__1_value)
            as *mut crate::leanh::LeanObject,
        5661876967030703708 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__2_value)
            as *mut crate::leanh::LeanObject,
        11995384298059439981 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__4_value:
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
    m_data: [120, 111, 114, 95, 99, 111, 110, 103, 114, 0],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0_value)
            as *mut crate::leanh::LeanObject,
        8407093297865582880 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__4_value)
            as *mut crate::leanh::LeanObject,
        5602409458539743654 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__0_value:
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
    m_fun: l_Nat_shiftLeft___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__1_value:
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
    m_data: [72, 83, 104, 105, 102, 116, 76, 101, 102, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__2_value:
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
    m_data: [104, 83, 104, 105, 102, 116, 76, 101, 102, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__1_value)
            as *mut crate::leanh::LeanObject,
        12221703946232912343 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__2_value)
            as *mut crate::leanh::LeanObject,
        4302041416438838709 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__4_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        115, 104, 105, 102, 116, 76, 101, 102, 116, 95, 99, 111, 110, 103, 114, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0_value)
            as *mut crate::leanh::LeanObject,
        8407093297865582880 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__4_value)
            as *mut crate::leanh::LeanObject,
        418335497322784062 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__0_value:
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
    m_fun: l_Nat_shiftRight___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__1_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [72, 83, 104, 105, 102, 116, 82, 105, 103, 104, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__2_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [104, 83, 104, 105, 102, 116, 82, 105, 103, 104, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__1_value)
            as *mut crate::leanh::LeanObject,
        5422698995969631099 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__2_value)
            as *mut crate::leanh::LeanObject,
        11315714300293431604 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__4_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        115, 104, 105, 102, 116, 82, 105, 103, 104, 116, 95, 99, 111, 110, 103, 114, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0_value)
            as *mut crate::leanh::LeanObject,
        8407093297865582880 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__4_value)
            as *mut crate::leanh::LeanObject,
        9012786009031937223 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0: u64 = 0;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [73, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__2_value) as *mut crate::leanh::LeanObject,7009148538150066493 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__4_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__4_value) as *mut crate::leanh::LeanObject,3708748166848919527 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__6_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [66, 105, 116, 86, 101, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__6_value) as *mut crate::leanh::LeanObject,5394957827732845164 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__8_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [85, 73, 110, 116, 56, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__8_value) as *mut crate::leanh::LeanObject,15764114953608429200 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__10_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [85, 73, 110, 116, 49, 54, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__10_value) as *mut crate::leanh::LeanObject,9755723410228041222 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__12_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [85, 73, 110, 116, 51, 50, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__12_value) as *mut crate::leanh::LeanObject,13474504806189678690 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__14_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [73, 110, 116, 54, 52, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__14_value) as *mut crate::leanh::LeanObject,6508593840631735363 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__16_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [73, 110, 116, 56, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__16_value) as *mut crate::leanh::LeanObject,4828225126264449809 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__18_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [73, 110, 116, 49, 54, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__19_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__18_value) as *mut crate::leanh::LeanObject,1593258566177356093 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__20_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [73, 110, 116, 51, 50, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__21_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__20_value) as *mut crate::leanh::LeanObject,17423969607579146442 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__22_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__15_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__23_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__21_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__22_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__24_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__19_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__23_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__24_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__25_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__17_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__24_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__26_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__15_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__25_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__26_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__27_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__13_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__26_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__27_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__28_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__11_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__27_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__28_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__29_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__9_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__28_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__29_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__30_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__29_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__30_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__31_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__5_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__30_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__31: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__31_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__32_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__3_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__31_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__32: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__32_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__33_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__1_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__32_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__33: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__33_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__34_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__34: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__0_value) as *mut crate::leanh::LeanObject,17636616155771105671 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__1_value) as *mut crate::leanh::LeanObject,15578568367168711682 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateMul___closed__0_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Meta_Grind_Arith_propagateMul___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateMul___closed__1_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Meta_Grind_Arith_propagateMul___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_propagateMul___closed__2_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__0_value)
            as *mut crate::leanh::LeanObject,
        2929883540436775422 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_propagateMul___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__1_value)
                as *mut crate::leanh::LeanObject,
            1611444129324655608 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_propagateMul___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateMul___closed__3_value: crate::leanh::LeanStringObject<
    9,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Meta_Grind_Arith_propagateMul___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateMul___closed__4_value: crate::leanh::LeanStringObject<
    14,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        111, 110, 101, 95, 109, 117, 108, 95, 99, 111, 110, 103, 114, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_propagateMul___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_propagateMul___closed__5_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_propagateMul___closed__5_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_propagateMul___closed__5_value_aux_2: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__5_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__3_value)
            as *mut crate::leanh::LeanObject,
        12050285396929189622 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_propagateMul___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__5_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__4_value)
                as *mut crate::leanh::LeanObject,
            4558874899281809587 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_propagateMul___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateMul___closed__6_value: crate::leanh::LeanStringObject<
    15,
> = crate::leanh::LeanStringObject {
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
        122, 101, 114, 111, 95, 109, 117, 108, 95, 99, 111, 110, 103, 114, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_propagateMul___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_propagateMul___closed__7_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_propagateMul___closed__7_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_propagateMul___closed__7_value_aux_2: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__7_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__3_value)
            as *mut crate::leanh::LeanObject,
        12050285396929189622 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_propagateMul___closed__7_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__7_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__6_value)
                as *mut crate::leanh::LeanObject,
            2337859110404477674 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_propagateMul___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateMul___closed__8_value: crate::leanh::LeanStringObject<
    14,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        109, 117, 108, 95, 111, 110, 101, 95, 99, 111, 110, 103, 114, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_propagateMul___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_propagateMul___closed__9_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_propagateMul___closed__9_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__9_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_propagateMul___closed__9_value_aux_2: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__9_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__3_value)
            as *mut crate::leanh::LeanObject,
        12050285396929189622 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_propagateMul___closed__9_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__9_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__8_value)
                as *mut crate::leanh::LeanObject,
            2596960839554822006 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_propagateMul___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_propagateMul___closed__10_value: crate::leanh::LeanStringObject<
    15,
> = crate::leanh::LeanStringObject {
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
        109, 117, 108, 95, 122, 101, 114, 111, 95, 99, 111, 110, 103, 114, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_propagateMul___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_propagateMul___closed__11_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_propagateMul___closed__11_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__11_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_propagateMul___closed__11_value_aux_2: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__11_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__3_value)
            as *mut crate::leanh::LeanObject,
        12050285396929189622 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_propagateMul___closed__11_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__11_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__10_value)
            as *mut crate::leanh::LeanObject,
        5789827322931640234 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_propagateMul___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_propagateMul___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateNatBinOp(
    mut v_declName_1121_: *mut crate::leanh::LeanObject,
    mut v_congrThmName_1122_: *mut crate::leanh::LeanObject,
    mut v_op_1123_: *mut crate::leanh::LeanObject,
    mut v_e_1124_: *mut crate::leanh::LeanObject,
    mut v_a_1125_: *mut crate::leanh::LeanObject,
    mut v_a_1126_: *mut crate::leanh::LeanObject,
    mut v_a_1127_: *mut crate::leanh::LeanObject,
    mut v_a_1128_: *mut crate::leanh::LeanObject,
    mut v_a_1129_: *mut crate::leanh::LeanObject,
    mut v_a_1130_: *mut crate::leanh::LeanObject,
    mut v_a_1131_: *mut crate::leanh::LeanObject,
    mut v_a_1132_: *mut crate::leanh::LeanObject,
    mut v_a_1133_: *mut crate::leanh::LeanObject,
    mut v_a_1134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_arity_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: u8 = 0;
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: u8 = 0;
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: u8 = 0;
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1161_: u8 = 0;
    let mut v_val_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1172_: u8 = 0;
    let mut v_val_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: u8 = 0;
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1193_: u8 = 0;
    let mut v___x_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1197_: u8 = 0;
    let mut v_a_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1201_: u8 = 0;
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1205_: u8 = 0;
    let mut v_a_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1209_: u8 = 0;
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1213_: u8 = 0;
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1218_: u8 = 0;
    let mut v_a_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1222_: u8 = 0;
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1226_: u8 = 0;
    let mut v_a_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1230_: u8 = 0;
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1234_: u8 = 0;
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1239_: u8 = 0;
    let mut v_a_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1243_: u8 = 0;
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1247_: u8 = 0;
    let mut v_a_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1251_: u8 = 0;
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1255_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_arity_1136_ = crate::leanh::lean_unsigned_to_nat(6);
                v___x_1137_ = l_Lean_Expr_isAppOfArity(v_e_1124_, v_declName_1121_, v_arity_1136_);
                if v___x_1137_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_1124_);
                    crate::leanh::lean_dec_ref(v_op_1123_);
                    crate::leanh::lean_dec(v_congrThmName_1122_);
                    v___x_1138_ = crate::leanh::lean_box(0);
                    v___x_1139_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1139_, 0, v___x_1138_);
                    return v___x_1139_;
                } else {
                    v___x_1140_ = l_Lean_Expr_getAppNumArgs(v_e_1124_);
                    v___x_1141_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1142_ = lean_nat_sub(v___x_1140_, v___x_1141_);
                    crate::leanh::lean_dec(v___x_1140_);
                    crate::leanh::lean_inc(v___x_1142_);
                    v___x_1143_ = l_Lean_Expr_getRevArg_x21(v_e_1124_, v___x_1142_);
                    v___x_1144_ = l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__1;
                    v___x_1145_ = l_Lean_Expr_isConstOf(v___x_1143_, v___x_1144_);
                    crate::leanh::lean_dec_ref(v___x_1143_);
                    if v___x_1145_ == 0 {
                        crate::leanh::lean_dec(v___x_1142_);
                        crate::leanh::lean_dec_ref(v_e_1124_);
                        crate::leanh::lean_dec_ref(v_op_1123_);
                        crate::leanh::lean_dec(v_congrThmName_1122_);
                        v___x_1146_ = crate::leanh::lean_box(0);
                        v___x_1147_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1147_, 0, v___x_1146_);
                        return v___x_1147_;
                    } else {
                        v___x_1148_ = lean_nat_sub(v___x_1142_, v___x_1141_);
                        crate::leanh::lean_dec(v___x_1142_);
                        v___x_1149_ = l_Lean_Expr_getRevArg_x21(v_e_1124_, v___x_1148_);
                        v___x_1150_ = l_Lean_Expr_isConstOf(v___x_1149_, v___x_1144_);
                        crate::leanh::lean_dec_ref(v___x_1149_);
                        if v___x_1150_ == 0 {
                            crate::leanh::lean_dec_ref(v_e_1124_);
                            crate::leanh::lean_dec_ref(v_op_1123_);
                            crate::leanh::lean_dec(v_congrThmName_1122_);
                            v___x_1151_ = crate::leanh::lean_box(0);
                            v___x_1152_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1152_, 0, v___x_1151_);
                            return v___x_1152_;
                        } else {
                            v___x_1153_ = lean_st_ref_get(v_a_1125_);
                            v_a_1154_ = l_Lean_Expr_getRevArg_x21(v_e_1124_, v___x_1141_);
                            crate::leanh::lean_inc_ref(v_a_1154_);
                            v___x_1155_ = l_Lean_Meta_Grind_Goal_getRoot(
                                v___x_1153_,
                                v_a_1154_,
                                v_a_1131_,
                                v_a_1132_,
                                v_a_1133_,
                                v_a_1134_,
                            );
                            crate::leanh::lean_dec(v___x_1153_);
                            if crate::leanh::lean_obj_tag(v___x_1155_) == 0 {
                                v_a_1156_ = crate::leanh::lean_ctor_get(v___x_1155_, 0);
                                crate::leanh::lean_inc(v_a_1156_);
                                crate::leanh::lean_dec_ref_known(v___x_1155_, 1);
                                v___x_1157_ = l_Lean_Meta_getNatValue_x3f(
                                    v_a_1156_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1157_) == 0 {
                                    v_a_1158_ = crate::leanh::lean_ctor_get(v___x_1157_, 0);
                                    v_isSharedCheck_1239_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1157_)) as u8;
                                    if v_isSharedCheck_1239_ == 0 {
                                        v___x_1160_ = v___x_1157_;
                                        v_isShared_1161_ = v_isSharedCheck_1239_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1158_);
                                        crate::leanh::lean_dec(v___x_1157_);
                                        v___x_1160_ = crate::leanh::lean_box(0);
                                        v_isShared_1161_ = v_isSharedCheck_1239_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_1156_);
                                    crate::leanh::lean_dec_ref(v_a_1154_);
                                    crate::leanh::lean_dec_ref(v_e_1124_);
                                    crate::leanh::lean_dec_ref(v_op_1123_);
                                    crate::leanh::lean_dec(v_congrThmName_1122_);
                                    v_a_1240_ = crate::leanh::lean_ctor_get(v___x_1157_, 0);
                                    v_isSharedCheck_1247_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1157_)) as u8;
                                    if v_isSharedCheck_1247_ == 0 {
                                        v___x_1242_ = v___x_1157_;
                                        v_isShared_1243_ = v_isSharedCheck_1247_;
                                        state = 15;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1240_);
                                        crate::leanh::lean_dec(v___x_1157_);
                                        v___x_1242_ = crate::leanh::lean_box(0);
                                        v_isShared_1243_ = v_isSharedCheck_1247_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_a_1154_);
                                crate::leanh::lean_dec_ref(v_e_1124_);
                                crate::leanh::lean_dec_ref(v_op_1123_);
                                crate::leanh::lean_dec(v_congrThmName_1122_);
                                v_a_1248_ = crate::leanh::lean_ctor_get(v___x_1155_, 0);
                                v_isSharedCheck_1255_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1155_)) as u8;
                                if v_isSharedCheck_1255_ == 0 {
                                    v___x_1250_ = v___x_1155_;
                                    v_isShared_1251_ = v_isSharedCheck_1255_;
                                    state = 17;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1248_);
                                    crate::leanh::lean_dec(v___x_1155_);
                                    v___x_1250_ = crate::leanh::lean_box(0);
                                    v_isShared_1251_ = v_isSharedCheck_1255_;
                                    state = 17;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1158_) == 1 {
                    crate::leanh::lean_del_object(v___x_1160_);
                    v_val_1162_ = crate::leanh::lean_ctor_get(v_a_1158_, 0);
                    crate::leanh::lean_inc(v_val_1162_);
                    crate::leanh::lean_dec_ref_known(v_a_1158_, 1);
                    v___x_1163_ = lean_st_ref_get(v_a_1125_);
                    v___x_1164_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1165_ = l_Lean_Expr_getRevArg_x21(v_e_1124_, v___x_1164_);
                    crate::leanh::lean_inc_ref(v___x_1165_);
                    v___x_1166_ = l_Lean_Meta_Grind_Goal_getRoot(
                        v___x_1163_,
                        v___x_1165_,
                        v_a_1131_,
                        v_a_1132_,
                        v_a_1133_,
                        v_a_1134_,
                    );
                    crate::leanh::lean_dec(v___x_1163_);
                    if crate::leanh::lean_obj_tag(v___x_1166_) == 0 {
                        v_a_1167_ = crate::leanh::lean_ctor_get(v___x_1166_, 0);
                        crate::leanh::lean_inc(v_a_1167_);
                        crate::leanh::lean_dec_ref_known(v___x_1166_, 1);
                        v___x_1168_ = l_Lean_Meta_getNatValue_x3f(
                            v_a_1167_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1168_) == 0 {
                            v_a_1169_ = crate::leanh::lean_ctor_get(v___x_1168_, 0);
                            v_isSharedCheck_1218_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1168_)) as u8;
                            if v_isSharedCheck_1218_ == 0 {
                                v___x_1171_ = v___x_1168_;
                                v_isShared_1172_ = v_isSharedCheck_1218_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1169_);
                                crate::leanh::lean_dec(v___x_1168_);
                                v___x_1171_ = crate::leanh::lean_box(0);
                                v_isShared_1172_ = v_isSharedCheck_1218_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1167_);
                            crate::leanh::lean_dec_ref(v___x_1165_);
                            crate::leanh::lean_dec(v_val_1162_);
                            crate::leanh::lean_dec(v_a_1156_);
                            crate::leanh::lean_dec_ref(v_a_1154_);
                            crate::leanh::lean_dec_ref(v_e_1124_);
                            crate::leanh::lean_dec_ref(v_op_1123_);
                            crate::leanh::lean_dec(v_congrThmName_1122_);
                            v_a_1219_ = crate::leanh::lean_ctor_get(v___x_1168_, 0);
                            v_isSharedCheck_1226_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1168_)) as u8;
                            if v_isSharedCheck_1226_ == 0 {
                                v___x_1221_ = v___x_1168_;
                                v_isShared_1222_ = v_isSharedCheck_1226_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1219_);
                                crate::leanh::lean_dec(v___x_1168_);
                                v___x_1221_ = crate::leanh::lean_box(0);
                                v_isShared_1222_ = v_isSharedCheck_1226_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1165_);
                        crate::leanh::lean_dec(v_val_1162_);
                        crate::leanh::lean_dec(v_a_1156_);
                        crate::leanh::lean_dec_ref(v_a_1154_);
                        crate::leanh::lean_dec_ref(v_e_1124_);
                        crate::leanh::lean_dec_ref(v_op_1123_);
                        crate::leanh::lean_dec(v_congrThmName_1122_);
                        v_a_1227_ = crate::leanh::lean_ctor_get(v___x_1166_, 0);
                        v_isSharedCheck_1234_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1166_)) as u8;
                        if v_isSharedCheck_1234_ == 0 {
                            v___x_1229_ = v___x_1166_;
                            v_isShared_1230_ = v_isSharedCheck_1234_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1227_);
                            crate::leanh::lean_dec(v___x_1166_);
                            v___x_1229_ = crate::leanh::lean_box(0);
                            v_isShared_1230_ = v_isSharedCheck_1234_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1158_);
                    crate::leanh::lean_dec(v_a_1156_);
                    crate::leanh::lean_dec_ref(v_a_1154_);
                    crate::leanh::lean_dec_ref(v_e_1124_);
                    crate::leanh::lean_dec_ref(v_op_1123_);
                    crate::leanh::lean_dec(v_congrThmName_1122_);
                    v___x_1235_ = crate::leanh::lean_box(0);
                    if v_isShared_1161_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1160_, 0, v___x_1235_);
                        v___x_1237_ = v___x_1160_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_1238_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1235_);
                        v___x_1237_ = v_reuseFailAlloc_1238_;
                        state = 14;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_1169_) == 1 {
                    crate::leanh::lean_del_object(v___x_1171_);
                    v_val_1173_ = crate::leanh::lean_ctor_get(v_a_1169_, 0);
                    crate::leanh::lean_inc(v_val_1173_);
                    crate::leanh::lean_dec_ref_known(v_a_1169_, 1);
                    v___x_1174_ = crate::leanh::lean_apply_2(v_op_1123_, v_val_1162_, v_val_1173_);
                    v___x_1175_ = l_Lean_mkNatLit(v___x_1174_);
                    v___x_1176_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_1175_, v_a_1130_);
                    if crate::leanh::lean_obj_tag(v___x_1176_) == 0 {
                        v_a_1177_ = crate::leanh::lean_ctor_get(v___x_1176_, 0);
                        crate::leanh::lean_inc_n(v_a_1177_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_1176_, 1);
                        v___x_1178_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc(v_a_1134_);
                        crate::leanh::lean_inc_ref(v_a_1133_);
                        crate::leanh::lean_inc(v_a_1132_);
                        crate::leanh::lean_inc_ref(v_a_1131_);
                        crate::leanh::lean_inc(v_a_1130_);
                        crate::leanh::lean_inc_ref(v_a_1129_);
                        crate::leanh::lean_inc(v_a_1128_);
                        crate::leanh::lean_inc_ref(v_a_1127_);
                        crate::leanh::lean_inc(v_a_1126_);
                        crate::leanh::lean_inc(v_a_1125_);
                        v___x_1179_ = lean_grind_internalize(
                            v_a_1177_,
                            v___x_1164_,
                            v___x_1178_,
                            v_a_1125_,
                            v_a_1126_,
                            v_a_1127_,
                            v_a_1128_,
                            v_a_1129_,
                            v_a_1130_,
                            v_a_1131_,
                            v_a_1132_,
                            v_a_1133_,
                            v_a_1134_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1179_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_1179_, 1);
                            crate::leanh::lean_inc(v_a_1134_);
                            crate::leanh::lean_inc_ref(v_a_1133_);
                            crate::leanh::lean_inc(v_a_1132_);
                            crate::leanh::lean_inc_ref(v_a_1131_);
                            crate::leanh::lean_inc(v_a_1130_);
                            crate::leanh::lean_inc_ref(v_a_1129_);
                            crate::leanh::lean_inc(v_a_1128_);
                            crate::leanh::lean_inc_ref(v_a_1127_);
                            crate::leanh::lean_inc(v_a_1126_);
                            crate::leanh::lean_inc(v_a_1125_);
                            crate::leanh::lean_inc(v_a_1156_);
                            crate::leanh::lean_inc_ref(v_a_1154_);
                            v___x_1180_ = lean_grind_mk_eq_proof(
                                v_a_1154_, v_a_1156_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_,
                                v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1180_) == 0 {
                                v_a_1181_ = crate::leanh::lean_ctor_get(v___x_1180_, 0);
                                crate::leanh::lean_inc(v_a_1181_);
                                crate::leanh::lean_dec_ref_known(v___x_1180_, 1);
                                crate::leanh::lean_inc(v_a_1134_);
                                crate::leanh::lean_inc_ref(v_a_1133_);
                                crate::leanh::lean_inc(v_a_1132_);
                                crate::leanh::lean_inc_ref(v_a_1131_);
                                crate::leanh::lean_inc(v_a_1130_);
                                crate::leanh::lean_inc_ref(v_a_1129_);
                                crate::leanh::lean_inc(v_a_1128_);
                                crate::leanh::lean_inc_ref(v_a_1127_);
                                crate::leanh::lean_inc(v_a_1126_);
                                crate::leanh::lean_inc(v_a_1125_);
                                crate::leanh::lean_inc(v_a_1167_);
                                crate::leanh::lean_inc_ref(v___x_1165_);
                                v___x_1182_ = lean_grind_mk_eq_proof(
                                    v___x_1165_,
                                    v_a_1167_,
                                    v_a_1125_,
                                    v_a_1126_,
                                    v_a_1127_,
                                    v_a_1128_,
                                    v_a_1129_,
                                    v_a_1130_,
                                    v_a_1131_,
                                    v_a_1132_,
                                    v_a_1133_,
                                    v_a_1134_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1182_) == 0 {
                                    v_a_1183_ = crate::leanh::lean_ctor_get(v___x_1182_, 0);
                                    crate::leanh::lean_inc(v_a_1183_);
                                    crate::leanh::lean_dec_ref_known(v___x_1182_, 1);
                                    v___x_1184_ = crate::leanh::lean_box(0);
                                    v___x_1185_ = l_Lean_mkConst(v_congrThmName_1122_, v___x_1184_);
                                    v___x_1186_ = l_Lean_eagerReflBoolTrue;
                                    crate::leanh::lean_inc(v_a_1177_);
                                    v___x_1187_ = l_Lean_mkApp8(
                                        v___x_1185_,
                                        v_a_1154_,
                                        v___x_1165_,
                                        v_a_1156_,
                                        v_a_1167_,
                                        v_a_1177_,
                                        v_a_1181_,
                                        v_a_1183_,
                                        v___x_1186_,
                                    );
                                    v___x_1188_ = 0;
                                    v___x_1189_ = l_Lean_Meta_Grind_pushEqCore___redArg(
                                        v_e_1124_,
                                        v_a_1177_,
                                        v___x_1187_,
                                        v___x_1188_,
                                        v_a_1125_,
                                        v_a_1127_,
                                        v_a_1131_,
                                        v_a_1132_,
                                        v_a_1133_,
                                        v_a_1134_,
                                    );
                                    return v___x_1189_;
                                } else {
                                    crate::leanh::lean_dec(v_a_1181_);
                                    crate::leanh::lean_dec(v_a_1177_);
                                    crate::leanh::lean_dec(v_a_1167_);
                                    crate::leanh::lean_dec_ref(v___x_1165_);
                                    crate::leanh::lean_dec(v_a_1156_);
                                    crate::leanh::lean_dec_ref(v_a_1154_);
                                    crate::leanh::lean_dec_ref(v_e_1124_);
                                    crate::leanh::lean_dec(v_congrThmName_1122_);
                                    v_a_1190_ = crate::leanh::lean_ctor_get(v___x_1182_, 0);
                                    v_isSharedCheck_1197_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1182_)) as u8;
                                    if v_isSharedCheck_1197_ == 0 {
                                        v___x_1192_ = v___x_1182_;
                                        v_isShared_1193_ = v_isSharedCheck_1197_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1190_);
                                        crate::leanh::lean_dec(v___x_1182_);
                                        v___x_1192_ = crate::leanh::lean_box(0);
                                        v_isShared_1193_ = v_isSharedCheck_1197_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_1177_);
                                crate::leanh::lean_dec(v_a_1167_);
                                crate::leanh::lean_dec_ref(v___x_1165_);
                                crate::leanh::lean_dec(v_a_1156_);
                                crate::leanh::lean_dec_ref(v_a_1154_);
                                crate::leanh::lean_dec_ref(v_e_1124_);
                                crate::leanh::lean_dec(v_congrThmName_1122_);
                                v_a_1198_ = crate::leanh::lean_ctor_get(v___x_1180_, 0);
                                v_isSharedCheck_1205_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1180_)) as u8;
                                if v_isSharedCheck_1205_ == 0 {
                                    v___x_1200_ = v___x_1180_;
                                    v_isShared_1201_ = v_isSharedCheck_1205_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1198_);
                                    crate::leanh::lean_dec(v___x_1180_);
                                    v___x_1200_ = crate::leanh::lean_box(0);
                                    v_isShared_1201_ = v_isSharedCheck_1205_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1177_);
                            crate::leanh::lean_dec(v_a_1167_);
                            crate::leanh::lean_dec_ref(v___x_1165_);
                            crate::leanh::lean_dec(v_a_1156_);
                            crate::leanh::lean_dec_ref(v_a_1154_);
                            crate::leanh::lean_dec_ref(v_e_1124_);
                            crate::leanh::lean_dec(v_congrThmName_1122_);
                            return v___x_1179_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1167_);
                        crate::leanh::lean_dec_ref(v___x_1165_);
                        crate::leanh::lean_dec(v_a_1156_);
                        crate::leanh::lean_dec_ref(v_a_1154_);
                        crate::leanh::lean_dec_ref(v_e_1124_);
                        crate::leanh::lean_dec(v_congrThmName_1122_);
                        v_a_1206_ = crate::leanh::lean_ctor_get(v___x_1176_, 0);
                        v_isSharedCheck_1213_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1176_)) as u8;
                        if v_isSharedCheck_1213_ == 0 {
                            v___x_1208_ = v___x_1176_;
                            v_isShared_1209_ = v_isSharedCheck_1213_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1206_);
                            crate::leanh::lean_dec(v___x_1176_);
                            v___x_1208_ = crate::leanh::lean_box(0);
                            v_isShared_1209_ = v_isSharedCheck_1213_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1169_);
                    crate::leanh::lean_dec(v_a_1167_);
                    crate::leanh::lean_dec_ref(v___x_1165_);
                    crate::leanh::lean_dec(v_val_1162_);
                    crate::leanh::lean_dec(v_a_1156_);
                    crate::leanh::lean_dec_ref(v_a_1154_);
                    crate::leanh::lean_dec_ref(v_e_1124_);
                    crate::leanh::lean_dec_ref(v_op_1123_);
                    crate::leanh::lean_dec(v_congrThmName_1122_);
                    v___x_1214_ = crate::leanh::lean_box(0);
                    if v_isShared_1172_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1171_, 0, v___x_1214_);
                        v___x_1216_ = v___x_1171_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1217_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1214_);
                        v___x_1216_ = v_reuseFailAlloc_1217_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1193_ == 0 {
                    v___x_1195_ = v___x_1192_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1196_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1190_);
                    v___x_1195_ = v_reuseFailAlloc_1196_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1195_;
            }
            5 => {
                if v_isShared_1201_ == 0 {
                    v___x_1203_ = v___x_1200_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1204_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
                    v___x_1203_ = v_reuseFailAlloc_1204_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1203_;
            }
            7 => {
                if v_isShared_1209_ == 0 {
                    v___x_1211_ = v___x_1208_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1212_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
                    v___x_1211_ = v_reuseFailAlloc_1212_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1211_;
            }
            9 => {
                return v___x_1216_;
            }
            10 => {
                if v_isShared_1222_ == 0 {
                    v___x_1224_ = v___x_1221_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1225_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1219_);
                    v___x_1224_ = v_reuseFailAlloc_1225_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1224_;
            }
            12 => {
                if v_isShared_1230_ == 0 {
                    v___x_1232_ = v___x_1229_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1233_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
                    v___x_1232_ = v_reuseFailAlloc_1233_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1232_;
            }
            14 => {
                return v___x_1237_;
            }
            15 => {
                if v_isShared_1243_ == 0 {
                    v___x_1245_ = v___x_1242_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1246_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
                    v___x_1245_ = v_reuseFailAlloc_1246_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1245_;
            }
            17 => {
                if v_isShared_1251_ == 0 {
                    v___x_1253_ = v___x_1250_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1254_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
                    v___x_1253_ = v_reuseFailAlloc_1254_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1253_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateNatBinOp___boxed(
    mut v_declName_1256_: *mut crate::leanh::LeanObject,
    mut v_congrThmName_1257_: *mut crate::leanh::LeanObject,
    mut v_op_1258_: *mut crate::leanh::LeanObject,
    mut v_e_1259_: *mut crate::leanh::LeanObject,
    mut v_a_1260_: *mut crate::leanh::LeanObject,
    mut v_a_1261_: *mut crate::leanh::LeanObject,
    mut v_a_1262_: *mut crate::leanh::LeanObject,
    mut v_a_1263_: *mut crate::leanh::LeanObject,
    mut v_a_1264_: *mut crate::leanh::LeanObject,
    mut v_a_1265_: *mut crate::leanh::LeanObject,
    mut v_a_1266_: *mut crate::leanh::LeanObject,
    mut v_a_1267_: *mut crate::leanh::LeanObject,
    mut v_a_1268_: *mut crate::leanh::LeanObject,
    mut v_a_1269_: *mut crate::leanh::LeanObject,
    mut v_a_1270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1271_ = l_Lean_Meta_Grind_Arith_propagateNatBinOp(
        v_declName_1256_,
        v_congrThmName_1257_,
        v_op_1258_,
        v_e_1259_,
        v_a_1260_,
        v_a_1261_,
        v_a_1262_,
        v_a_1263_,
        v_a_1264_,
        v_a_1265_,
        v_a_1266_,
        v_a_1267_,
        v_a_1268_,
        v_a_1269_,
    );
    crate::leanh::lean_dec(v_a_1269_);
    crate::leanh::lean_dec_ref(v_a_1268_);
    crate::leanh::lean_dec(v_a_1267_);
    crate::leanh::lean_dec_ref(v_a_1266_);
    crate::leanh::lean_dec(v_a_1265_);
    crate::leanh::lean_dec_ref(v_a_1264_);
    crate::leanh::lean_dec(v_a_1263_);
    crate::leanh::lean_dec_ref(v_a_1262_);
    crate::leanh::lean_dec(v_a_1261_);
    crate::leanh::lean_dec(v_a_1260_);
    crate::leanh::lean_dec(v_declName_1256_);
    return v_res_1271_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateNatAnd(
    mut v_e_1286_: *mut crate::leanh::LeanObject,
    mut v_a_1287_: *mut crate::leanh::LeanObject,
    mut v_a_1288_: *mut crate::leanh::LeanObject,
    mut v_a_1289_: *mut crate::leanh::LeanObject,
    mut v_a_1290_: *mut crate::leanh::LeanObject,
    mut v_a_1291_: *mut crate::leanh::LeanObject,
    mut v_a_1292_: *mut crate::leanh::LeanObject,
    mut v_a_1293_: *mut crate::leanh::LeanObject,
    mut v_a_1294_: *mut crate::leanh::LeanObject,
    mut v_a_1295_: *mut crate::leanh::LeanObject,
    mut v_a_1296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1298_ = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__0;
    v___x_1299_ = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3;
    v___x_1300_ = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7;
    v___x_1301_ = l_Lean_Meta_Grind_Arith_propagateNatBinOp(
        v___x_1299_,
        v___x_1300_,
        v___f_1298_,
        v_e_1286_,
        v_a_1287_,
        v_a_1288_,
        v_a_1289_,
        v_a_1290_,
        v_a_1291_,
        v_a_1292_,
        v_a_1293_,
        v_a_1294_,
        v_a_1295_,
        v_a_1296_,
    );
    return v___x_1301_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateNatAnd___boxed(
    mut v_e_1302_: *mut crate::leanh::LeanObject,
    mut v_a_1303_: *mut crate::leanh::LeanObject,
    mut v_a_1304_: *mut crate::leanh::LeanObject,
    mut v_a_1305_: *mut crate::leanh::LeanObject,
    mut v_a_1306_: *mut crate::leanh::LeanObject,
    mut v_a_1307_: *mut crate::leanh::LeanObject,
    mut v_a_1308_: *mut crate::leanh::LeanObject,
    mut v_a_1309_: *mut crate::leanh::LeanObject,
    mut v_a_1310_: *mut crate::leanh::LeanObject,
    mut v_a_1311_: *mut crate::leanh::LeanObject,
    mut v_a_1312_: *mut crate::leanh::LeanObject,
    mut v_a_1313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1314_ = l_Lean_Meta_Grind_Arith_propagateNatAnd(
        v_e_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_,
        v_a_1310_, v_a_1311_, v_a_1312_,
    );
    crate::leanh::lean_dec(v_a_1312_);
    crate::leanh::lean_dec_ref(v_a_1311_);
    crate::leanh::lean_dec(v_a_1310_);
    crate::leanh::lean_dec_ref(v_a_1309_);
    crate::leanh::lean_dec(v_a_1308_);
    crate::leanh::lean_dec_ref(v_a_1307_);
    crate::leanh::lean_dec(v_a_1306_);
    crate::leanh::lean_dec_ref(v_a_1305_);
    crate::leanh::lean_dec(v_a_1304_);
    crate::leanh::lean_dec(v_a_1303_);
    return v_res_1314_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_8_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1316_ = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3;
    v___x_1317_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_propagateNatAnd___boxed as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_1318_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1316_, v___x_1317_);
    return v___x_1318_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_8____boxed(
    mut v_a_1319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1320_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_8_();
    return v_res_1320_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateNatOr(
    mut v_e_1333_: *mut crate::leanh::LeanObject,
    mut v_a_1334_: *mut crate::leanh::LeanObject,
    mut v_a_1335_: *mut crate::leanh::LeanObject,
    mut v_a_1336_: *mut crate::leanh::LeanObject,
    mut v_a_1337_: *mut crate::leanh::LeanObject,
    mut v_a_1338_: *mut crate::leanh::LeanObject,
    mut v_a_1339_: *mut crate::leanh::LeanObject,
    mut v_a_1340_: *mut crate::leanh::LeanObject,
    mut v_a_1341_: *mut crate::leanh::LeanObject,
    mut v_a_1342_: *mut crate::leanh::LeanObject,
    mut v_a_1343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1345_ = l_Lean_Meta_Grind_Arith_propagateNatOr___closed__0;
    v___x_1346_ = l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3;
    v___x_1347_ = l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5;
    v___x_1348_ = l_Lean_Meta_Grind_Arith_propagateNatBinOp(
        v___x_1346_,
        v___x_1347_,
        v___f_1345_,
        v_e_1333_,
        v_a_1334_,
        v_a_1335_,
        v_a_1336_,
        v_a_1337_,
        v_a_1338_,
        v_a_1339_,
        v_a_1340_,
        v_a_1341_,
        v_a_1342_,
        v_a_1343_,
    );
    return v___x_1348_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateNatOr___boxed(
    mut v_e_1349_: *mut crate::leanh::LeanObject,
    mut v_a_1350_: *mut crate::leanh::LeanObject,
    mut v_a_1351_: *mut crate::leanh::LeanObject,
    mut v_a_1352_: *mut crate::leanh::LeanObject,
    mut v_a_1353_: *mut crate::leanh::LeanObject,
    mut v_a_1354_: *mut crate::leanh::LeanObject,
    mut v_a_1355_: *mut crate::leanh::LeanObject,
    mut v_a_1356_: *mut crate::leanh::LeanObject,
    mut v_a_1357_: *mut crate::leanh::LeanObject,
    mut v_a_1358_: *mut crate::leanh::LeanObject,
    mut v_a_1359_: *mut crate::leanh::LeanObject,
    mut v_a_1360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1361_ = l_Lean_Meta_Grind_Arith_propagateNatOr(
        v_e_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_,
        v_a_1357_, v_a_1358_, v_a_1359_,
    );
    crate::leanh::lean_dec(v_a_1359_);
    crate::leanh::lean_dec_ref(v_a_1358_);
    crate::leanh::lean_dec(v_a_1357_);
    crate::leanh::lean_dec_ref(v_a_1356_);
    crate::leanh::lean_dec(v_a_1355_);
    crate::leanh::lean_dec_ref(v_a_1354_);
    crate::leanh::lean_dec(v_a_1353_);
    crate::leanh::lean_dec_ref(v_a_1352_);
    crate::leanh::lean_dec(v_a_1351_);
    crate::leanh::lean_dec(v_a_1350_);
    return v_res_1361_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_8_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1363_ = l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3;
    v___x_1364_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_propagateNatOr___boxed as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_1365_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1363_, v___x_1364_);
    return v___x_1365_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_8____boxed(
    mut v_a_1366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1367_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_8_();
    return v_res_1367_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateNatXOr(
    mut v_e_1380_: *mut crate::leanh::LeanObject,
    mut v_a_1381_: *mut crate::leanh::LeanObject,
    mut v_a_1382_: *mut crate::leanh::LeanObject,
    mut v_a_1383_: *mut crate::leanh::LeanObject,
    mut v_a_1384_: *mut crate::leanh::LeanObject,
    mut v_a_1385_: *mut crate::leanh::LeanObject,
    mut v_a_1386_: *mut crate::leanh::LeanObject,
    mut v_a_1387_: *mut crate::leanh::LeanObject,
    mut v_a_1388_: *mut crate::leanh::LeanObject,
    mut v_a_1389_: *mut crate::leanh::LeanObject,
    mut v_a_1390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1392_ = l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__0;
    v___x_1393_ = l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3;
    v___x_1394_ = l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5;
    v___x_1395_ = l_Lean_Meta_Grind_Arith_propagateNatBinOp(
        v___x_1393_,
        v___x_1394_,
        v___f_1392_,
        v_e_1380_,
        v_a_1381_,
        v_a_1382_,
        v_a_1383_,
        v_a_1384_,
        v_a_1385_,
        v_a_1386_,
        v_a_1387_,
        v_a_1388_,
        v_a_1389_,
        v_a_1390_,
    );
    return v___x_1395_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateNatXOr___boxed(
    mut v_e_1396_: *mut crate::leanh::LeanObject,
    mut v_a_1397_: *mut crate::leanh::LeanObject,
    mut v_a_1398_: *mut crate::leanh::LeanObject,
    mut v_a_1399_: *mut crate::leanh::LeanObject,
    mut v_a_1400_: *mut crate::leanh::LeanObject,
    mut v_a_1401_: *mut crate::leanh::LeanObject,
    mut v_a_1402_: *mut crate::leanh::LeanObject,
    mut v_a_1403_: *mut crate::leanh::LeanObject,
    mut v_a_1404_: *mut crate::leanh::LeanObject,
    mut v_a_1405_: *mut crate::leanh::LeanObject,
    mut v_a_1406_: *mut crate::leanh::LeanObject,
    mut v_a_1407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1408_ = l_Lean_Meta_Grind_Arith_propagateNatXOr(
        v_e_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_,
        v_a_1404_, v_a_1405_, v_a_1406_,
    );
    crate::leanh::lean_dec(v_a_1406_);
    crate::leanh::lean_dec_ref(v_a_1405_);
    crate::leanh::lean_dec(v_a_1404_);
    crate::leanh::lean_dec_ref(v_a_1403_);
    crate::leanh::lean_dec(v_a_1402_);
    crate::leanh::lean_dec_ref(v_a_1401_);
    crate::leanh::lean_dec(v_a_1400_);
    crate::leanh::lean_dec_ref(v_a_1399_);
    crate::leanh::lean_dec(v_a_1398_);
    crate::leanh::lean_dec(v_a_1397_);
    return v_res_1408_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_8_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1410_ = l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3;
    v___x_1411_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_propagateNatXOr___boxed as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_1412_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1410_, v___x_1411_);
    return v___x_1412_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_8____boxed(
    mut v_a_1413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1414_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_8_();
    return v_res_1414_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateNatShiftLeft(
    mut v_e_1427_: *mut crate::leanh::LeanObject,
    mut v_a_1428_: *mut crate::leanh::LeanObject,
    mut v_a_1429_: *mut crate::leanh::LeanObject,
    mut v_a_1430_: *mut crate::leanh::LeanObject,
    mut v_a_1431_: *mut crate::leanh::LeanObject,
    mut v_a_1432_: *mut crate::leanh::LeanObject,
    mut v_a_1433_: *mut crate::leanh::LeanObject,
    mut v_a_1434_: *mut crate::leanh::LeanObject,
    mut v_a_1435_: *mut crate::leanh::LeanObject,
    mut v_a_1436_: *mut crate::leanh::LeanObject,
    mut v_a_1437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1439_ = l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__0;
    v___x_1440_ = l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3;
    v___x_1441_ = l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5;
    v___x_1442_ = l_Lean_Meta_Grind_Arith_propagateNatBinOp(
        v___x_1440_,
        v___x_1441_,
        v___f_1439_,
        v_e_1427_,
        v_a_1428_,
        v_a_1429_,
        v_a_1430_,
        v_a_1431_,
        v_a_1432_,
        v_a_1433_,
        v_a_1434_,
        v_a_1435_,
        v_a_1436_,
        v_a_1437_,
    );
    return v___x_1442_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___boxed(
    mut v_e_1443_: *mut crate::leanh::LeanObject,
    mut v_a_1444_: *mut crate::leanh::LeanObject,
    mut v_a_1445_: *mut crate::leanh::LeanObject,
    mut v_a_1446_: *mut crate::leanh::LeanObject,
    mut v_a_1447_: *mut crate::leanh::LeanObject,
    mut v_a_1448_: *mut crate::leanh::LeanObject,
    mut v_a_1449_: *mut crate::leanh::LeanObject,
    mut v_a_1450_: *mut crate::leanh::LeanObject,
    mut v_a_1451_: *mut crate::leanh::LeanObject,
    mut v_a_1452_: *mut crate::leanh::LeanObject,
    mut v_a_1453_: *mut crate::leanh::LeanObject,
    mut v_a_1454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1455_ = l_Lean_Meta_Grind_Arith_propagateNatShiftLeft(
        v_e_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_,
        v_a_1451_, v_a_1452_, v_a_1453_,
    );
    crate::leanh::lean_dec(v_a_1453_);
    crate::leanh::lean_dec_ref(v_a_1452_);
    crate::leanh::lean_dec(v_a_1451_);
    crate::leanh::lean_dec_ref(v_a_1450_);
    crate::leanh::lean_dec(v_a_1449_);
    crate::leanh::lean_dec_ref(v_a_1448_);
    crate::leanh::lean_dec(v_a_1447_);
    crate::leanh::lean_dec_ref(v_a_1446_);
    crate::leanh::lean_dec(v_a_1445_);
    crate::leanh::lean_dec(v_a_1444_);
    return v_res_1455_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_8_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1457_ = l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3;
    v___x_1458_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___boxed as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_1459_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1457_, v___x_1458_);
    return v___x_1459_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_8____boxed(
    mut v_a_1460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1461_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_8_();
    return v_res_1461_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateNatShiftRight(
    mut v_e_1474_: *mut crate::leanh::LeanObject,
    mut v_a_1475_: *mut crate::leanh::LeanObject,
    mut v_a_1476_: *mut crate::leanh::LeanObject,
    mut v_a_1477_: *mut crate::leanh::LeanObject,
    mut v_a_1478_: *mut crate::leanh::LeanObject,
    mut v_a_1479_: *mut crate::leanh::LeanObject,
    mut v_a_1480_: *mut crate::leanh::LeanObject,
    mut v_a_1481_: *mut crate::leanh::LeanObject,
    mut v_a_1482_: *mut crate::leanh::LeanObject,
    mut v_a_1483_: *mut crate::leanh::LeanObject,
    mut v_a_1484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1486_ = l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__0;
    v___x_1487_ = l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3;
    v___x_1488_ = l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5;
    v___x_1489_ = l_Lean_Meta_Grind_Arith_propagateNatBinOp(
        v___x_1487_,
        v___x_1488_,
        v___f_1486_,
        v_e_1474_,
        v_a_1475_,
        v_a_1476_,
        v_a_1477_,
        v_a_1478_,
        v_a_1479_,
        v_a_1480_,
        v_a_1481_,
        v_a_1482_,
        v_a_1483_,
        v_a_1484_,
    );
    return v___x_1489_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateNatShiftRight___boxed(
    mut v_e_1490_: *mut crate::leanh::LeanObject,
    mut v_a_1491_: *mut crate::leanh::LeanObject,
    mut v_a_1492_: *mut crate::leanh::LeanObject,
    mut v_a_1493_: *mut crate::leanh::LeanObject,
    mut v_a_1494_: *mut crate::leanh::LeanObject,
    mut v_a_1495_: *mut crate::leanh::LeanObject,
    mut v_a_1496_: *mut crate::leanh::LeanObject,
    mut v_a_1497_: *mut crate::leanh::LeanObject,
    mut v_a_1498_: *mut crate::leanh::LeanObject,
    mut v_a_1499_: *mut crate::leanh::LeanObject,
    mut v_a_1500_: *mut crate::leanh::LeanObject,
    mut v_a_1501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1502_ = l_Lean_Meta_Grind_Arith_propagateNatShiftRight(
        v_e_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_,
        v_a_1498_, v_a_1499_, v_a_1500_,
    );
    crate::leanh::lean_dec(v_a_1500_);
    crate::leanh::lean_dec_ref(v_a_1499_);
    crate::leanh::lean_dec(v_a_1498_);
    crate::leanh::lean_dec_ref(v_a_1497_);
    crate::leanh::lean_dec(v_a_1496_);
    crate::leanh::lean_dec_ref(v_a_1495_);
    crate::leanh::lean_dec(v_a_1494_);
    crate::leanh::lean_dec_ref(v_a_1493_);
    crate::leanh::lean_dec(v_a_1492_);
    crate::leanh::lean_dec(v_a_1491_);
    return v_res_1502_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_8_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1504_ = l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3;
    v___x_1505_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_propagateNatShiftRight___boxed as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_1506_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1504_, v___x_1505_);
    return v___x_1506_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_8____boxed(
    mut v_a_1507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1508_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_8_();
    return v_res_1508_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0()
-> u64 {
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: u64 = 0;
    v___x_1509_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_1510_ = lean_uint64_of_nat(v___x_1509_);
    return v___x_1510_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_x_1511_: *mut crate::leanh::LeanObject,
    mut v_x_1512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1518_: u8 = 0;
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1521_: u64 = 0;
    let mut v___x_1522_: u64 = 0;
    let mut v___x_1523_: u64 = 0;
    let mut v_fold_1524_: u64 = 0;
    let mut v___x_1525_: u64 = 0;
    let mut v___x_1526_: u64 = 0;
    let mut v___x_1527_: u64 = 0;
    let mut v___x_1528_: usize = 0;
    let mut v___x_1529_: usize = 0;
    let mut v___x_1530_: usize = 0;
    let mut v___x_1531_: usize = 0;
    let mut v___x_1532_: usize = 0;
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: u64 = 0;
    let mut v_hash_1540_: u64 = 0;
    let mut v_isSharedCheck_1541_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1512_) == 0 {
                    return v_x_1511_;
                } else {
                    v_key_1513_ = crate::leanh::lean_ctor_get(v_x_1512_, 0);
                    v_value_1514_ = crate::leanh::lean_ctor_get(v_x_1512_, 1);
                    v_tail_1515_ = crate::leanh::lean_ctor_get(v_x_1512_, 2);
                    v_isSharedCheck_1541_ = (!crate::leanh::lean_is_exclusive(v_x_1512_)) as u8;
                    if v_isSharedCheck_1541_ == 0 {
                        v___x_1517_ = v_x_1512_;
                        v_isShared_1518_ = v_isSharedCheck_1541_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1515_);
                        crate::leanh::lean_inc(v_value_1514_);
                        crate::leanh::lean_inc(v_key_1513_);
                        crate::leanh::lean_dec(v_x_1512_);
                        v___x_1517_ = crate::leanh::lean_box(0);
                        v_isShared_1518_ = v_isSharedCheck_1541_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1519_ = lean_array_get_size(v_x_1511_);
                if crate::leanh::lean_obj_tag(v_key_1513_) == 0 {
                    v___x_1539_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0);
                    v___y_1521_ = v___x_1539_;
                    state = 2;
                    continue;
                } else {
                    v_hash_1540_ = crate::leanh::lean_ctor_get_uint64(
                        v_key_1513_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_1521_ = v_hash_1540_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1522_ = 32u64;
                v___x_1523_ = lean_uint64_shift_right(v___y_1521_, v___x_1522_);
                v_fold_1524_ = lean_uint64_xor(v___y_1521_, v___x_1523_);
                v___x_1525_ = 16u64;
                v___x_1526_ = lean_uint64_shift_right(v_fold_1524_, v___x_1525_);
                v___x_1527_ = lean_uint64_xor(v_fold_1524_, v___x_1526_);
                v___x_1528_ = lean_uint64_to_usize(v___x_1527_);
                v___x_1529_ = lean_usize_of_nat(v___x_1519_);
                v___x_1530_ = 1usize;
                v___x_1531_ = lean_usize_sub(v___x_1529_, v___x_1530_);
                v___x_1532_ = lean_usize_land(v___x_1528_, v___x_1531_);
                v___x_1533_ = lean_array_uget_borrowed(v_x_1511_, v___x_1532_);
                crate::leanh::lean_inc(v___x_1533_);
                if v_isShared_1518_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1517_, 2, v___x_1533_);
                    v___x_1535_ = v___x_1517_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1538_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_key_1513_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_value_1514_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1538_, 2, v___x_1533_);
                    v___x_1535_ = v_reuseFailAlloc_1538_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1536_ = lean_array_uset(v_x_1511_, v___x_1532_, v___x_1535_);
                v_x_1511_ = v___x_1536_;
                v_x_1512_ = v_tail_1515_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2___redArg(
    mut v_i_1542_: *mut crate::leanh::LeanObject,
    mut v_source_1543_: *mut crate::leanh::LeanObject,
    mut v_target_1544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: u8 = 0;
    let mut v_es_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1545_ = lean_array_get_size(v_source_1543_);
                v___x_1546_ = lean_nat_dec_lt(v_i_1542_, v___x_1545_);
                if v___x_1546_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_1543_);
                    crate::leanh::lean_dec(v_i_1542_);
                    return v_target_1544_;
                } else {
                    v_es_1547_ = lean_array_fget(v_source_1543_, v_i_1542_);
                    v___x_1548_ = crate::leanh::lean_box(0);
                    v_source_1549_ = lean_array_fset(v_source_1543_, v_i_1542_, v___x_1548_);
                    v_target_1550_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg(v_target_1544_, v_es_1547_);
                    v___x_1551_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1552_ = lean_nat_add(v_i_1542_, v___x_1551_);
                    crate::leanh::lean_dec(v_i_1542_);
                    v_i_1542_ = v___x_1552_;
                    v_source_1543_ = v_source_1549_;
                    v_target_1544_ = v_target_1550_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1___redArg(
    mut v_data_1554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1555_ = lean_array_get_size(v_data_1554_);
    v___x_1556_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1557_ = lean_nat_mul(v___x_1555_, v___x_1556_);
    v___x_1558_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1559_ = crate::leanh::lean_box(0);
    v___x_1560_ = lean_mk_array(v_nbuckets_1557_, v___x_1559_);
    v___x_1561_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2___redArg(v___x_1558_, v_data_1554_, v___x_1560_);
    return v___x_1561_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(
    mut v_a_1562_: *mut crate::leanh::LeanObject,
    mut v_x_1563_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1564_: u8 = 0;
    let mut v_key_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1563_) == 0 {
                    v___x_1564_ = 0;
                    return v___x_1564_;
                } else {
                    v_key_1565_ = crate::leanh::lean_ctor_get(v_x_1563_, 0);
                    v_tail_1566_ = crate::leanh::lean_ctor_get(v_x_1563_, 2);
                    v___x_1567_ = lean_name_eq(v_key_1565_, v_a_1562_);
                    if v___x_1567_ == 0 {
                        v_x_1563_ = v_tail_1566_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1567_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg___boxed(
    mut v_a_1569_: *mut crate::leanh::LeanObject,
    mut v_x_1570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1571_: u8 = 0;
    let mut v_r_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1571_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(v_a_1569_, v_x_1570_);
    crate::leanh::lean_dec(v_x_1570_);
    crate::leanh::lean_dec(v_a_1569_);
    v_r_1572_ = crate::leanh::lean_box((v_res_1571_) as usize);
    return v_r_1572_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___redArg(
    mut v_m_1573_: *mut crate::leanh::LeanObject,
    mut v_a_1574_: *mut crate::leanh::LeanObject,
    mut v_b_1575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1580_: u64 = 0;
    let mut v___x_1581_: u64 = 0;
    let mut v___x_1582_: u64 = 0;
    let mut v_fold_1583_: u64 = 0;
    let mut v___x_1584_: u64 = 0;
    let mut v___x_1585_: u64 = 0;
    let mut v___x_1586_: u64 = 0;
    let mut v___x_1587_: usize = 0;
    let mut v___x_1588_: usize = 0;
    let mut v___x_1589_: usize = 0;
    let mut v___x_1590_: usize = 0;
    let mut v___x_1591_: usize = 0;
    let mut v_bkt_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: u8 = 0;
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1596_: u8 = 0;
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: u8 = 0;
    let mut v_val_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1614_: u8 = 0;
    let mut v_unused_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: u64 = 0;
    let mut v_hash_1618_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1576_ = crate::leanh::lean_ctor_get(v_m_1573_, 0);
                v_buckets_1577_ = crate::leanh::lean_ctor_get(v_m_1573_, 1);
                v___x_1578_ = lean_array_get_size(v_buckets_1577_);
                if crate::leanh::lean_obj_tag(v_a_1574_) == 0 {
                    v___x_1617_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0);
                    v___y_1580_ = v___x_1617_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1618_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_1574_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_1580_ = v_hash_1618_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1581_ = 32u64;
                v___x_1582_ = lean_uint64_shift_right(v___y_1580_, v___x_1581_);
                v_fold_1583_ = lean_uint64_xor(v___y_1580_, v___x_1582_);
                v___x_1584_ = 16u64;
                v___x_1585_ = lean_uint64_shift_right(v_fold_1583_, v___x_1584_);
                v___x_1586_ = lean_uint64_xor(v_fold_1583_, v___x_1585_);
                v___x_1587_ = lean_uint64_to_usize(v___x_1586_);
                v___x_1588_ = lean_usize_of_nat(v___x_1578_);
                v___x_1589_ = 1usize;
                v___x_1590_ = lean_usize_sub(v___x_1588_, v___x_1589_);
                v___x_1591_ = lean_usize_land(v___x_1587_, v___x_1590_);
                v_bkt_1592_ = lean_array_uget_borrowed(v_buckets_1577_, v___x_1591_);
                v___x_1593_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(v_a_1574_, v_bkt_1592_);
                if v___x_1593_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_1577_);
                    crate::leanh::lean_inc(v_size_1576_);
                    v_isSharedCheck_1614_ = (!crate::leanh::lean_is_exclusive(v_m_1573_)) as u8;
                    if v_isSharedCheck_1614_ == 0 {
                        v_unused_1615_ = crate::leanh::lean_ctor_get(v_m_1573_, 1);
                        crate::leanh::lean_dec(v_unused_1615_);
                        v_unused_1616_ = crate::leanh::lean_ctor_get(v_m_1573_, 0);
                        crate::leanh::lean_dec(v_unused_1616_);
                        v___x_1595_ = v_m_1573_;
                        v_isShared_1596_ = v_isSharedCheck_1614_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_1573_);
                        v___x_1595_ = crate::leanh::lean_box(0);
                        v_isShared_1596_ = v_isSharedCheck_1614_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_1575_);
                    crate::leanh::lean_dec(v_a_1574_);
                    return v_m_1573_;
                }
            }
            2 => {
                v___x_1597_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_1598_ = lean_nat_add(v_size_1576_, v___x_1597_);
                crate::leanh::lean_dec(v_size_1576_);
                crate::leanh::lean_inc(v_bkt_1592_);
                v___x_1599_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1599_, 0, v_a_1574_);
                crate::leanh::lean_ctor_set(v___x_1599_, 1, v_b_1575_);
                crate::leanh::lean_ctor_set(v___x_1599_, 2, v_bkt_1592_);
                v_buckets_x27_1600_ = lean_array_uset(v_buckets_1577_, v___x_1591_, v___x_1599_);
                v___x_1601_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_1602_ = lean_nat_mul(v_size_x27_1598_, v___x_1601_);
                v___x_1603_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1604_ = lean_nat_div(v___x_1602_, v___x_1603_);
                crate::leanh::lean_dec(v___x_1602_);
                v___x_1605_ = lean_array_get_size(v_buckets_x27_1600_);
                v___x_1606_ = lean_nat_dec_le(v___x_1604_, v___x_1605_);
                crate::leanh::lean_dec(v___x_1604_);
                if v___x_1606_ == 0 {
                    v_val_1607_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1___redArg(v_buckets_x27_1600_);
                    if v_isShared_1596_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1595_, 1, v_val_1607_);
                        crate::leanh::lean_ctor_set(v___x_1595_, 0, v_size_x27_1598_);
                        v___x_1609_ = v___x_1595_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1610_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_size_x27_1598_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_val_1607_);
                        v___x_1609_ = v_reuseFailAlloc_1610_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_1596_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1595_, 1, v_buckets_x27_1600_);
                        crate::leanh::lean_ctor_set(v___x_1595_, 0, v_size_x27_1598_);
                        v___x_1612_ = v___x_1595_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1613_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_size_x27_1598_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_buckets_x27_1600_);
                        v___x_1612_ = v_reuseFailAlloc_1613_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1609_;
            }
            4 => {
                return v___x_1612_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1(
    mut v_x_1619_: *mut crate::leanh::LeanObject,
    mut v_x_1620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1620_) == 0 {
                    return v_x_1619_;
                } else {
                    v_head_1621_ = crate::leanh::lean_ctor_get(v_x_1620_, 0);
                    crate::leanh::lean_inc(v_head_1621_);
                    v_tail_1622_ = crate::leanh::lean_ctor_get(v_x_1620_, 1);
                    crate::leanh::lean_inc(v_tail_1622_);
                    crate::leanh::lean_dec_ref_known(v_x_1620_, 2);
                    v___x_1623_ = crate::leanh::lean_box(0);
                    v___x_1624_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___redArg(v_x_1619_, v_head_1621_, v___x_1623_);
                    v_x_1619_ = v___x_1624_;
                    v_x_1620_ = v_tail_1622_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1626_ = crate::leanh::lean_box(0);
    v___x_1627_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1628_ = lean_mk_array(v___x_1627_, v___x_1626_);
    return v___x_1628_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1629_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0);
    v___x_1630_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1631_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1631_, 0, v___x_1630_);
    crate::leanh::lean_ctor_set(v___x_1631_, 1, v___x_1629_);
    return v___x_1631_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__34()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1698_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__33;
    v___x_1699_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1);
    v___x_1700_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1(v___x_1699_, v___x_1698_);
    return v___x_1700_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1701_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__34), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__34_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__34);
    return v___x_1701_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0(
    mut v_00_u03b2_1702_: *mut crate::leanh::LeanObject,
    mut v_m_1703_: *mut crate::leanh::LeanObject,
    mut v_a_1704_: *mut crate::leanh::LeanObject,
    mut v_b_1705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1706_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___redArg(v_m_1703_, v_a_1704_, v_b_1705_);
    return v___x_1706_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0(
    mut v_00_u03b2_1707_: *mut crate::leanh::LeanObject,
    mut v_a_1708_: *mut crate::leanh::LeanObject,
    mut v_x_1709_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1710_: u8 = 0;
    v___x_1710_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(v_a_1708_, v_x_1709_);
    return v___x_1710_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___boxed(
    mut v_00_u03b2_1711_: *mut crate::leanh::LeanObject,
    mut v_a_1712_: *mut crate::leanh::LeanObject,
    mut v_x_1713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1714_: u8 = 0;
    let mut v_r_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1714_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0(v_00_u03b2_1711_, v_a_1712_, v_x_1713_);
    crate::leanh::lean_dec(v_x_1713_);
    crate::leanh::lean_dec(v_a_1712_);
    v_r_1715_ = crate::leanh::lean_box((v_res_1714_) as usize);
    return v_r_1715_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1(
    mut v_00_u03b2_1716_: *mut crate::leanh::LeanObject,
    mut v_data_1717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1718_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1___redArg(v_data_1717_);
    return v___x_1718_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2(
    mut v_00_u03b2_1719_: *mut crate::leanh::LeanObject,
    mut v_i_1720_: *mut crate::leanh::LeanObject,
    mut v_source_1721_: *mut crate::leanh::LeanObject,
    mut v_target_1722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1723_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2___redArg(v_i_1720_, v_source_1721_, v_target_1722_);
    return v___x_1723_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b2_1724_: *mut crate::leanh::LeanObject,
    mut v_x_1725_: *mut crate::leanh::LeanObject,
    mut v_x_1726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1727_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg(v_x_1725_, v_x_1726_);
    return v___x_1727_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg(
    mut v_m_1728_: *mut crate::leanh::LeanObject,
    mut v_a_1729_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1733_: u64 = 0;
    let mut v___x_1734_: u64 = 0;
    let mut v___x_1735_: u64 = 0;
    let mut v_fold_1736_: u64 = 0;
    let mut v___x_1737_: u64 = 0;
    let mut v___x_1738_: u64 = 0;
    let mut v___x_1739_: u64 = 0;
    let mut v___x_1740_: usize = 0;
    let mut v___x_1741_: usize = 0;
    let mut v___x_1742_: usize = 0;
    let mut v___x_1743_: usize = 0;
    let mut v___x_1744_: usize = 0;
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: u8 = 0;
    let mut v___x_1747_: u64 = 0;
    let mut v_hash_1748_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_1730_ = crate::leanh::lean_ctor_get(v_m_1728_, 1);
                v___x_1731_ = lean_array_get_size(v_buckets_1730_);
                if crate::leanh::lean_obj_tag(v_a_1729_) == 0 {
                    v___x_1747_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0);
                    v___y_1733_ = v___x_1747_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1748_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_1729_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_1733_ = v_hash_1748_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1734_ = 32u64;
                v___x_1735_ = lean_uint64_shift_right(v___y_1733_, v___x_1734_);
                v_fold_1736_ = lean_uint64_xor(v___y_1733_, v___x_1735_);
                v___x_1737_ = 16u64;
                v___x_1738_ = lean_uint64_shift_right(v_fold_1736_, v___x_1737_);
                v___x_1739_ = lean_uint64_xor(v_fold_1736_, v___x_1738_);
                v___x_1740_ = lean_uint64_to_usize(v___x_1739_);
                v___x_1741_ = lean_usize_of_nat(v___x_1731_);
                v___x_1742_ = 1usize;
                v___x_1743_ = lean_usize_sub(v___x_1741_, v___x_1742_);
                v___x_1744_ = lean_usize_land(v___x_1740_, v___x_1743_);
                v___x_1745_ = lean_array_uget_borrowed(v_buckets_1730_, v___x_1744_);
                v___x_1746_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(v_a_1729_, v___x_1745_);
                return v___x_1746_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg___boxed(
    mut v_m_1749_: *mut crate::leanh::LeanObject,
    mut v_a_1750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1751_: u8 = 0;
    let mut v_r_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1751_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg(v_m_1749_, v_a_1750_);
    crate::leanh::lean_dec(v_a_1750_);
    crate::leanh::lean_dec_ref(v_m_1749_);
    v_r_1752_ = crate::leanh::lean_box((v_res_1751_) as usize);
    return v_r_1752_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick(
    mut v_type_1753_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1754_ = l_Lean_Expr_getAppFn(v_type_1753_);
    if crate::leanh::lean_obj_tag(v___x_1754_) == 4 {
        let mut v_declName_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1757_: u8 = 0;
        v_declName_1755_ = crate::leanh::lean_ctor_get(v___x_1754_, 0);
        crate::leanh::lean_inc(v_declName_1755_);
        crate::leanh::lean_dec_ref_known(v___x_1754_, 2);
        v___x_1756_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring;
        v___x_1757_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg(v___x_1756_, v_declName_1755_);
        crate::leanh::lean_dec(v_declName_1755_);
        return v___x_1757_;
    } else {
        let mut v___x_1758_: u8 = 0;
        crate::leanh::lean_dec_ref(v___x_1754_);
        v___x_1758_ = 0;
        return v___x_1758_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick___boxed(
    mut v_type_1759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1760_: u8 = 0;
    let mut v_r_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1760_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick(v_type_1759_);
    crate::leanh::lean_dec_ref(v_type_1759_);
    v_r_1761_ = crate::leanh::lean_box((v_res_1760_) as usize);
    return v_r_1761_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0(
    mut v_00_u03b2_1762_: *mut crate::leanh::LeanObject,
    mut v_m_1763_: *mut crate::leanh::LeanObject,
    mut v_a_1764_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1765_: u8 = 0;
    v___x_1765_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg(v_m_1763_, v_a_1764_);
    return v___x_1765_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___boxed(
    mut v_00_u03b2_1766_: *mut crate::leanh::LeanObject,
    mut v_m_1767_: *mut crate::leanh::LeanObject,
    mut v_a_1768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1769_: u8 = 0;
    let mut v_r_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1769_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0(v_00_u03b2_1766_, v_m_1767_, v_a_1768_);
    crate::leanh::lean_dec(v_a_1768_);
    crate::leanh::lean_dec_ref(v_m_1767_);
    v_r_1770_ = crate::leanh::lean_box((v_res_1769_) as usize);
    return v_r_1770_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f(
    mut v_type_1771_: *mut crate::leanh::LeanObject,
    mut v_a_1772_: *mut crate::leanh::LeanObject,
    mut v_a_1773_: *mut crate::leanh::LeanObject,
    mut v_a_1774_: *mut crate::leanh::LeanObject,
    mut v_a_1775_: *mut crate::leanh::LeanObject,
    mut v_a_1776_: *mut crate::leanh::LeanObject,
    mut v_a_1777_: *mut crate::leanh::LeanObject,
    mut v_a_1778_: *mut crate::leanh::LeanObject,
    mut v_a_1779_: *mut crate::leanh::LeanObject,
    mut v_a_1780_: *mut crate::leanh::LeanObject,
    mut v_a_1781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1783_: u8 = 0;
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1788_: u8 = 0;
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1799_: u8 = 0;
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1804_: u8 = 0;
    let mut v_toSemiring_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1813_: u8 = 0;
    let mut v_a_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1817_: u8 = 0;
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1821_: u8 = 0;
    let mut v_isSharedCheck_1822_: u8 = 0;
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1828_: u8 = 0;
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1833_: u8 = 0;
    let mut v_semiringInst_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1841_: u8 = 0;
    let mut v_a_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1845_: u8 = 0;
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1849_: u8 = 0;
    let mut v_isSharedCheck_1850_: u8 = 0;
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1855_: u8 = 0;
    let mut v_val_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1859_: u8 = 0;
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1864_: u8 = 0;
    let mut v_semiringInst_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1872_: u8 = 0;
    let mut v_a_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1876_: u8 = 0;
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1880_: u8 = 0;
    let mut v_isSharedCheck_1881_: u8 = 0;
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1886_: u8 = 0;
    let mut v_a_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1890_: u8 = 0;
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1894_: u8 = 0;
    let mut v_a_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1898_: u8 = 0;
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1902_: u8 = 0;
    let mut v_a_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1906_: u8 = 0;
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1910_: u8 = 0;
    let mut v_isSharedCheck_1911_: u8 = 0;
    let mut v_a_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1915_: u8 = 0;
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1919_: u8 = 0;
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1783_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick(v_type_1771_);
                if v___x_1783_ == 0 {
                    crate::leanh::lean_inc_ref(v_type_1771_);
                    v___x_1784_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(
                        v_type_1771_,
                        v_a_1772_,
                        v_a_1773_,
                        v_a_1774_,
                        v_a_1775_,
                        v_a_1776_,
                        v_a_1777_,
                        v_a_1778_,
                        v_a_1779_,
                        v_a_1780_,
                        v_a_1781_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1784_) == 0 {
                        v_a_1785_ = crate::leanh::lean_ctor_get(v___x_1784_, 0);
                        v_isSharedCheck_1911_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1784_)) as u8;
                        if v_isSharedCheck_1911_ == 0 {
                            v___x_1787_ = v___x_1784_;
                            v_isShared_1788_ = v_isSharedCheck_1911_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1785_);
                            crate::leanh::lean_dec(v___x_1784_);
                            v___x_1787_ = crate::leanh::lean_box(0);
                            v_isShared_1788_ = v_isSharedCheck_1911_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_type_1771_);
                        v_a_1912_ = crate::leanh::lean_ctor_get(v___x_1784_, 0);
                        v_isSharedCheck_1919_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1784_)) as u8;
                        if v_isSharedCheck_1919_ == 0 {
                            v___x_1914_ = v___x_1784_;
                            v_isShared_1915_ = v_isSharedCheck_1919_;
                            state = 30;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1912_);
                            crate::leanh::lean_dec(v___x_1784_);
                            v___x_1914_ = crate::leanh::lean_box(0);
                            v_isShared_1915_ = v_isSharedCheck_1919_;
                            state = 30;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_1771_);
                    v___x_1920_ = crate::leanh::lean_box(0);
                    v___x_1921_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1921_, 0, v___x_1920_);
                    return v___x_1921_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1785_) == 0 {
                    if v___x_1783_ == 0 {
                        crate::leanh::lean_del_object(v___x_1787_);
                        crate::leanh::lean_inc_ref(v_type_1771_);
                        v___x_1794_ = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(
                            v_type_1771_,
                            v_a_1772_,
                            v_a_1773_,
                            v_a_1774_,
                            v_a_1775_,
                            v_a_1776_,
                            v_a_1777_,
                            v_a_1778_,
                            v_a_1779_,
                            v_a_1780_,
                            v_a_1781_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1794_) == 0 {
                            v_a_1795_ = crate::leanh::lean_ctor_get(v___x_1794_, 0);
                            crate::leanh::lean_inc(v_a_1795_);
                            crate::leanh::lean_dec_ref_known(v___x_1794_, 1);
                            if crate::leanh::lean_obj_tag(v_a_1795_) == 1 {
                                crate::leanh::lean_dec_ref(v_type_1771_);
                                v_val_1796_ = crate::leanh::lean_ctor_get(v_a_1795_, 0);
                                v_isSharedCheck_1822_ =
                                    (!crate::leanh::lean_is_exclusive(v_a_1795_)) as u8;
                                if v_isSharedCheck_1822_ == 0 {
                                    v___x_1798_ = v_a_1795_;
                                    v_isShared_1799_ = v_isSharedCheck_1822_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_1796_);
                                    crate::leanh::lean_dec(v_a_1795_);
                                    v___x_1798_ = crate::leanh::lean_box(0);
                                    v_isShared_1799_ = v_isSharedCheck_1822_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_1795_);
                                crate::leanh::lean_inc_ref(v_type_1771_);
                                v___x_1823_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(
                                    v_type_1771_,
                                    v_a_1772_,
                                    v_a_1773_,
                                    v_a_1774_,
                                    v_a_1775_,
                                    v_a_1776_,
                                    v_a_1777_,
                                    v_a_1778_,
                                    v_a_1779_,
                                    v_a_1780_,
                                    v_a_1781_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1823_) == 0 {
                                    v_a_1824_ = crate::leanh::lean_ctor_get(v___x_1823_, 0);
                                    crate::leanh::lean_inc(v_a_1824_);
                                    crate::leanh::lean_dec_ref_known(v___x_1823_, 1);
                                    if crate::leanh::lean_obj_tag(v_a_1824_) == 1 {
                                        crate::leanh::lean_dec_ref(v_type_1771_);
                                        v_val_1825_ = crate::leanh::lean_ctor_get(v_a_1824_, 0);
                                        v_isSharedCheck_1850_ =
                                            (!crate::leanh::lean_is_exclusive(v_a_1824_)) as u8;
                                        if v_isSharedCheck_1850_ == 0 {
                                            v___x_1827_ = v_a_1824_;
                                            v_isShared_1828_ = v_isSharedCheck_1850_;
                                            state = 10;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_val_1825_);
                                            crate::leanh::lean_dec(v_a_1824_);
                                            v___x_1827_ = crate::leanh::lean_box(0);
                                            v_isShared_1828_ = v_isSharedCheck_1850_;
                                            state = 10;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_1824_);
                                        v___x_1851_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(v_type_1771_, v_a_1772_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_);
                                        if crate::leanh::lean_obj_tag(v___x_1851_) == 0 {
                                            v_a_1852_ = crate::leanh::lean_ctor_get(v___x_1851_, 0);
                                            v_isSharedCheck_1886_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_1851_))
                                                    as u8;
                                            if v_isSharedCheck_1886_ == 0 {
                                                v___x_1854_ = v___x_1851_;
                                                v_isShared_1855_ = v_isSharedCheck_1886_;
                                                state = 16;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_1852_);
                                                crate::leanh::lean_dec(v___x_1851_);
                                                v___x_1854_ = crate::leanh::lean_box(0);
                                                v_isShared_1855_ = v_isSharedCheck_1886_;
                                                state = 16;
                                                continue;
                                            }
                                        } else {
                                            v_a_1887_ = crate::leanh::lean_ctor_get(v___x_1851_, 0);
                                            v_isSharedCheck_1894_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_1851_))
                                                    as u8;
                                            if v_isSharedCheck_1894_ == 0 {
                                                v___x_1889_ = v___x_1851_;
                                                v_isShared_1890_ = v_isSharedCheck_1894_;
                                                state = 24;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_1887_);
                                                crate::leanh::lean_dec(v___x_1851_);
                                                v___x_1889_ = crate::leanh::lean_box(0);
                                                v_isShared_1890_ = v_isSharedCheck_1894_;
                                                state = 24;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_type_1771_);
                                    v_a_1895_ = crate::leanh::lean_ctor_get(v___x_1823_, 0);
                                    v_isSharedCheck_1902_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1823_)) as u8;
                                    if v_isSharedCheck_1902_ == 0 {
                                        v___x_1897_ = v___x_1823_;
                                        v_isShared_1898_ = v_isSharedCheck_1902_;
                                        state = 26;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1895_);
                                        crate::leanh::lean_dec(v___x_1823_);
                                        v___x_1897_ = crate::leanh::lean_box(0);
                                        v_isShared_1898_ = v_isSharedCheck_1902_;
                                        state = 26;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_type_1771_);
                            v_a_1903_ = crate::leanh::lean_ctor_get(v___x_1794_, 0);
                            v_isSharedCheck_1910_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1794_)) as u8;
                            if v_isSharedCheck_1910_ == 0 {
                                v___x_1905_ = v___x_1794_;
                                v_isShared_1906_ = v_isSharedCheck_1910_;
                                state = 28;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1903_);
                                crate::leanh::lean_dec(v___x_1794_);
                                v___x_1905_ = crate::leanh::lean_box(0);
                                v_isShared_1906_ = v_isSharedCheck_1910_;
                                state = 28;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_type_1771_);
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_1785_, 1);
                    crate::leanh::lean_dec_ref(v_type_1771_);
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1790_ = crate::leanh::lean_box(0);
                if v_isShared_1788_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1787_, 0, v___x_1790_);
                    v___x_1792_ = v___x_1787_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1793_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1790_);
                    v___x_1792_ = v_reuseFailAlloc_1793_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1792_;
            }
            4 => {
                v___x_1800_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(
                    v_val_1796_,
                    v_a_1772_,
                    v_a_1773_,
                    v_a_1774_,
                    v_a_1775_,
                    v_a_1776_,
                    v_a_1777_,
                    v_a_1778_,
                    v_a_1779_,
                    v_a_1780_,
                    v_a_1781_,
                );
                crate::leanh::lean_dec(v_val_1796_);
                if crate::leanh::lean_obj_tag(v___x_1800_) == 0 {
                    v_a_1801_ = crate::leanh::lean_ctor_get(v___x_1800_, 0);
                    v_isSharedCheck_1813_ = (!crate::leanh::lean_is_exclusive(v___x_1800_)) as u8;
                    if v_isSharedCheck_1813_ == 0 {
                        v___x_1803_ = v___x_1800_;
                        v_isShared_1804_ = v_isSharedCheck_1813_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1801_);
                        crate::leanh::lean_dec(v___x_1800_);
                        v___x_1803_ = crate::leanh::lean_box(0);
                        v_isShared_1804_ = v_isSharedCheck_1813_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1798_);
                    v_a_1814_ = crate::leanh::lean_ctor_get(v___x_1800_, 0);
                    v_isSharedCheck_1821_ = (!crate::leanh::lean_is_exclusive(v___x_1800_)) as u8;
                    if v_isSharedCheck_1821_ == 0 {
                        v___x_1816_ = v___x_1800_;
                        v_isShared_1817_ = v_isSharedCheck_1821_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1814_);
                        crate::leanh::lean_dec(v___x_1800_);
                        v___x_1816_ = crate::leanh::lean_box(0);
                        v_isShared_1817_ = v_isSharedCheck_1821_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                v_toSemiring_1805_ = crate::leanh::lean_ctor_get(v_a_1801_, 0);
                crate::leanh::lean_inc_ref(v_toSemiring_1805_);
                crate::leanh::lean_dec(v_a_1801_);
                v_semiringInst_1806_ = crate::leanh::lean_ctor_get(v_toSemiring_1805_, 3);
                crate::leanh::lean_inc_ref(v_semiringInst_1806_);
                crate::leanh::lean_dec_ref(v_toSemiring_1805_);
                if v_isShared_1799_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1798_, 0, v_semiringInst_1806_);
                    v___x_1808_ = v___x_1798_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1812_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_semiringInst_1806_);
                    v___x_1808_ = v_reuseFailAlloc_1812_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1804_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1803_, 0, v___x_1808_);
                    v___x_1810_ = v___x_1803_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1811_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1808_);
                    v___x_1810_ = v_reuseFailAlloc_1811_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1810_;
            }
            8 => {
                if v_isShared_1817_ == 0 {
                    v___x_1819_ = v___x_1816_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1820_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1814_);
                    v___x_1819_ = v_reuseFailAlloc_1820_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1819_;
            }
            10 => {
                v___x_1829_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(
                    v_val_1825_,
                    v_a_1772_,
                    v_a_1773_,
                    v_a_1774_,
                    v_a_1775_,
                    v_a_1776_,
                    v_a_1777_,
                    v_a_1778_,
                    v_a_1779_,
                    v_a_1780_,
                    v_a_1781_,
                );
                crate::leanh::lean_dec(v_val_1825_);
                if crate::leanh::lean_obj_tag(v___x_1829_) == 0 {
                    v_a_1830_ = crate::leanh::lean_ctor_get(v___x_1829_, 0);
                    v_isSharedCheck_1841_ = (!crate::leanh::lean_is_exclusive(v___x_1829_)) as u8;
                    if v_isSharedCheck_1841_ == 0 {
                        v___x_1832_ = v___x_1829_;
                        v_isShared_1833_ = v_isSharedCheck_1841_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1830_);
                        crate::leanh::lean_dec(v___x_1829_);
                        v___x_1832_ = crate::leanh::lean_box(0);
                        v_isShared_1833_ = v_isSharedCheck_1841_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1827_);
                    v_a_1842_ = crate::leanh::lean_ctor_get(v___x_1829_, 0);
                    v_isSharedCheck_1849_ = (!crate::leanh::lean_is_exclusive(v___x_1829_)) as u8;
                    if v_isSharedCheck_1849_ == 0 {
                        v___x_1844_ = v___x_1829_;
                        v_isShared_1845_ = v_isSharedCheck_1849_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1842_);
                        crate::leanh::lean_dec(v___x_1829_);
                        v___x_1844_ = crate::leanh::lean_box(0);
                        v_isShared_1845_ = v_isSharedCheck_1849_;
                        state = 14;
                        continue;
                    }
                }
            }
            11 => {
                v_semiringInst_1834_ = crate::leanh::lean_ctor_get(v_a_1830_, 4);
                crate::leanh::lean_inc_ref(v_semiringInst_1834_);
                crate::leanh::lean_dec(v_a_1830_);
                if v_isShared_1828_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1827_, 0, v_semiringInst_1834_);
                    v___x_1836_ = v___x_1827_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1840_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_semiringInst_1834_);
                    v___x_1836_ = v_reuseFailAlloc_1840_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_1833_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1832_, 0, v___x_1836_);
                    v___x_1838_ = v___x_1832_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1839_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
                    v___x_1838_ = v_reuseFailAlloc_1839_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1838_;
            }
            14 => {
                if v_isShared_1845_ == 0 {
                    v___x_1847_ = v___x_1844_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1848_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
                    v___x_1847_ = v_reuseFailAlloc_1848_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1847_;
            }
            16 => {
                if crate::leanh::lean_obj_tag(v_a_1852_) == 1 {
                    crate::leanh::lean_del_object(v___x_1854_);
                    v_val_1856_ = crate::leanh::lean_ctor_get(v_a_1852_, 0);
                    v_isSharedCheck_1881_ = (!crate::leanh::lean_is_exclusive(v_a_1852_)) as u8;
                    if v_isSharedCheck_1881_ == 0 {
                        v___x_1858_ = v_a_1852_;
                        v_isShared_1859_ = v_isSharedCheck_1881_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1856_);
                        crate::leanh::lean_dec(v_a_1852_);
                        v___x_1858_ = crate::leanh::lean_box(0);
                        v_isShared_1859_ = v_isSharedCheck_1881_;
                        state = 17;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1852_);
                    v___x_1882_ = crate::leanh::lean_box(0);
                    if v_isShared_1855_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1854_, 0, v___x_1882_);
                        v___x_1884_ = v___x_1854_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_1885_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1882_);
                        v___x_1884_ = v_reuseFailAlloc_1885_;
                        state = 23;
                        continue;
                    }
                }
            }
            17 => {
                v___x_1860_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring(
                    v_val_1856_,
                    v_a_1772_,
                    v_a_1773_,
                    v_a_1774_,
                    v_a_1775_,
                    v_a_1776_,
                    v_a_1777_,
                    v_a_1778_,
                    v_a_1779_,
                    v_a_1780_,
                    v_a_1781_,
                );
                crate::leanh::lean_dec(v_val_1856_);
                if crate::leanh::lean_obj_tag(v___x_1860_) == 0 {
                    v_a_1861_ = crate::leanh::lean_ctor_get(v___x_1860_, 0);
                    v_isSharedCheck_1872_ = (!crate::leanh::lean_is_exclusive(v___x_1860_)) as u8;
                    if v_isSharedCheck_1872_ == 0 {
                        v___x_1863_ = v___x_1860_;
                        v_isShared_1864_ = v_isSharedCheck_1872_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1861_);
                        crate::leanh::lean_dec(v___x_1860_);
                        v___x_1863_ = crate::leanh::lean_box(0);
                        v_isShared_1864_ = v_isSharedCheck_1872_;
                        state = 18;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1858_);
                    v_a_1873_ = crate::leanh::lean_ctor_get(v___x_1860_, 0);
                    v_isSharedCheck_1880_ = (!crate::leanh::lean_is_exclusive(v___x_1860_)) as u8;
                    if v_isSharedCheck_1880_ == 0 {
                        v___x_1875_ = v___x_1860_;
                        v_isShared_1876_ = v_isSharedCheck_1880_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1873_);
                        crate::leanh::lean_dec(v___x_1860_);
                        v___x_1875_ = crate::leanh::lean_box(0);
                        v_isShared_1876_ = v_isSharedCheck_1880_;
                        state = 21;
                        continue;
                    }
                }
            }
            18 => {
                v_semiringInst_1865_ = crate::leanh::lean_ctor_get(v_a_1861_, 3);
                crate::leanh::lean_inc_ref(v_semiringInst_1865_);
                crate::leanh::lean_dec(v_a_1861_);
                if v_isShared_1859_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1858_, 0, v_semiringInst_1865_);
                    v___x_1867_ = v___x_1858_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1871_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_semiringInst_1865_);
                    v___x_1867_ = v_reuseFailAlloc_1871_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_1864_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1863_, 0, v___x_1867_);
                    v___x_1869_ = v___x_1863_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1870_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
                    v___x_1869_ = v_reuseFailAlloc_1870_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1869_;
            }
            21 => {
                if v_isShared_1876_ == 0 {
                    v___x_1878_ = v___x_1875_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1879_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
                    v___x_1878_ = v_reuseFailAlloc_1879_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_1878_;
            }
            23 => {
                return v___x_1884_;
            }
            24 => {
                if v_isShared_1890_ == 0 {
                    v___x_1892_ = v___x_1889_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_1893_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_a_1887_);
                    v___x_1892_ = v_reuseFailAlloc_1893_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_1892_;
            }
            26 => {
                if v_isShared_1898_ == 0 {
                    v___x_1900_ = v___x_1897_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1901_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1895_);
                    v___x_1900_ = v_reuseFailAlloc_1901_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_1900_;
            }
            28 => {
                if v_isShared_1906_ == 0 {
                    v___x_1908_ = v___x_1905_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_1909_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
                    v___x_1908_ = v_reuseFailAlloc_1909_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_1908_;
            }
            30 => {
                if v_isShared_1915_ == 0 {
                    v___x_1917_ = v___x_1914_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_1918_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
                    v___x_1917_ = v_reuseFailAlloc_1918_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_1917_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f___boxed(
    mut v_type_1922_: *mut crate::leanh::LeanObject,
    mut v_a_1923_: *mut crate::leanh::LeanObject,
    mut v_a_1924_: *mut crate::leanh::LeanObject,
    mut v_a_1925_: *mut crate::leanh::LeanObject,
    mut v_a_1926_: *mut crate::leanh::LeanObject,
    mut v_a_1927_: *mut crate::leanh::LeanObject,
    mut v_a_1928_: *mut crate::leanh::LeanObject,
    mut v_a_1929_: *mut crate::leanh::LeanObject,
    mut v_a_1930_: *mut crate::leanh::LeanObject,
    mut v_a_1931_: *mut crate::leanh::LeanObject,
    mut v_a_1932_: *mut crate::leanh::LeanObject,
    mut v_a_1933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1934_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f(v_type_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_);
    crate::leanh::lean_dec(v_a_1932_);
    crate::leanh::lean_dec_ref(v_a_1931_);
    crate::leanh::lean_dec(v_a_1930_);
    crate::leanh::lean_dec_ref(v_a_1929_);
    crate::leanh::lean_dec(v_a_1928_);
    crate::leanh::lean_dec_ref(v_a_1927_);
    crate::leanh::lean_dec(v_a_1926_);
    crate::leanh::lean_dec_ref(v_a_1925_);
    crate::leanh::lean_dec(v_a_1924_);
    crate::leanh::lean_dec(v_a_1923_);
    return v_res_1934_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(
    mut v_a_1940_: *mut crate::leanh::LeanObject,
    mut v_a_1941_: *mut crate::leanh::LeanObject,
    mut v_a_1942_: *mut crate::leanh::LeanObject,
    mut v_a_1943_: *mut crate::leanh::LeanObject,
    mut v_a_1944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: u8 = 0;
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: u8 = 0;
    let mut v_arg_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: u8 = 0;
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: u8 = 0;
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1949_ = l_Lean_Expr_cleanupAnnotations(v_a_1940_);
                v___x_1950_ = l_Lean_Expr_isApp(v___x_1949_);
                if v___x_1950_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1949_);
                    state = 1;
                    continue;
                } else {
                    v___x_1951_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1949_);
                    v___x_1952_ = l_Lean_Expr_isApp(v___x_1951_);
                    if v___x_1952_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_1951_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_1953_ = crate::leanh::lean_ctor_get(v___x_1951_, 1);
                        crate::leanh::lean_inc_ref(v_arg_1953_);
                        v___x_1954_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1951_);
                        v___x_1955_ = l_Lean_Expr_isApp(v___x_1954_);
                        if v___x_1955_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1954_);
                            crate::leanh::lean_dec_ref(v_arg_1953_);
                            state = 1;
                            continue;
                        } else {
                            v___x_1956_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1954_);
                            v___x_1957_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__2;
                            v___x_1958_ = l_Lean_Expr_isConstOf(v___x_1956_, v___x_1957_);
                            crate::leanh::lean_dec_ref(v___x_1956_);
                            if v___x_1958_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_1953_);
                                state = 1;
                                continue;
                            } else {
                                v___x_1959_ = l_Lean_Meta_getNatValue_x3f(
                                    v_arg_1953_,
                                    v_a_1941_,
                                    v_a_1942_,
                                    v_a_1943_,
                                    v_a_1944_,
                                );
                                crate::leanh::lean_dec_ref(v_arg_1953_);
                                return v___x_1959_;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1947_ = crate::leanh::lean_box(0);
                v___x_1948_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1948_, 0, v___x_1947_);
                return v___x_1948_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___boxed(
    mut v_a_1960_: *mut crate::leanh::LeanObject,
    mut v_a_1961_: *mut crate::leanh::LeanObject,
    mut v_a_1962_: *mut crate::leanh::LeanObject,
    mut v_a_1963_: *mut crate::leanh::LeanObject,
    mut v_a_1964_: *mut crate::leanh::LeanObject,
    mut v_a_1965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1966_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(
            v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_,
        );
    crate::leanh::lean_dec(v_a_1964_);
    crate::leanh::lean_dec_ref(v_a_1963_);
    crate::leanh::lean_dec(v_a_1962_);
    crate::leanh::lean_dec_ref(v_a_1961_);
    return v_res_1966_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateMul(
    mut v_e_1997_: *mut crate::leanh::LeanObject,
    mut v_a_1998_: *mut crate::leanh::LeanObject,
    mut v_a_1999_: *mut crate::leanh::LeanObject,
    mut v_a_2000_: *mut crate::leanh::LeanObject,
    mut v_a_2001_: *mut crate::leanh::LeanObject,
    mut v_a_2002_: *mut crate::leanh::LeanObject,
    mut v_a_2003_: *mut crate::leanh::LeanObject,
    mut v_a_2004_: *mut crate::leanh::LeanObject,
    mut v_a_2005_: *mut crate::leanh::LeanObject,
    mut v_a_2006_: *mut crate::leanh::LeanObject,
    mut v_a_2007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: u8 = 0;
    let mut v_arg_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: u8 = 0;
    let mut v_arg_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: u8 = 0;
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: u8 = 0;
    let mut v_arg_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: u8 = 0;
    let mut v_arg_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: u8 = 0;
    let mut v_arg_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: u8 = 0;
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2036_: u8 = 0;
    let mut v_val_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2039_: u8 = 0;
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2048_: u8 = 0;
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2059_: u8 = 0;
    let mut v_val_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: u8 = 0;
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: u8 = 0;
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2082_: u8 = 0;
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2086_: u8 = 0;
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: u8 = 0;
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2101_: u8 = 0;
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2105_: u8 = 0;
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2110_: u8 = 0;
    let mut v_val_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: u8 = 0;
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: u8 = 0;
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2133_: u8 = 0;
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2137_: u8 = 0;
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: u8 = 0;
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2152_: u8 = 0;
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2156_: u8 = 0;
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2161_: u8 = 0;
    let mut v_a_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2165_: u8 = 0;
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2169_: u8 = 0;
    let mut v_isSharedCheck_2170_: u8 = 0;
    let mut v_a_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2174_: u8 = 0;
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2178_: u8 = 0;
    let mut v_a_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2182_: u8 = 0;
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2186_: u8 = 0;
    let mut v_a_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2190_: u8 = 0;
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2194_: u8 = 0;
    let mut v_isSharedCheck_2195_: u8 = 0;
    let mut v_unused_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: u8 = 0;
    let mut v___x_2202_: u8 = 0;
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2207_: u8 = 0;
    let mut v_a_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2211_: u8 = 0;
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2215_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_1997_);
                v___x_2012_ = l_Lean_Expr_cleanupAnnotations(v_e_1997_);
                v___x_2013_ = l_Lean_Expr_isApp(v___x_2012_);
                if v___x_2013_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2012_);
                    crate::leanh::lean_dec_ref(v_e_1997_);
                    state = 1;
                    continue;
                } else {
                    v_arg_2014_ = crate::leanh::lean_ctor_get(v___x_2012_, 1);
                    crate::leanh::lean_inc_ref(v_arg_2014_);
                    v___x_2015_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2012_);
                    v___x_2016_ = l_Lean_Expr_isApp(v___x_2015_);
                    if v___x_2016_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2015_);
                        crate::leanh::lean_dec_ref(v_arg_2014_);
                        crate::leanh::lean_dec_ref(v_e_1997_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_2017_ = crate::leanh::lean_ctor_get(v___x_2015_, 1);
                        crate::leanh::lean_inc_ref(v_arg_2017_);
                        v___x_2018_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2015_);
                        v___x_2019_ = l_Lean_Expr_isApp(v___x_2018_);
                        if v___x_2019_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2018_);
                            crate::leanh::lean_dec_ref(v_arg_2017_);
                            crate::leanh::lean_dec_ref(v_arg_2014_);
                            crate::leanh::lean_dec_ref(v_e_1997_);
                            state = 1;
                            continue;
                        } else {
                            v___x_2020_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2018_);
                            v___x_2021_ = l_Lean_Expr_isApp(v___x_2020_);
                            if v___x_2021_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_2020_);
                                crate::leanh::lean_dec_ref(v_arg_2017_);
                                crate::leanh::lean_dec_ref(v_arg_2014_);
                                crate::leanh::lean_dec_ref(v_e_1997_);
                                state = 1;
                                continue;
                            } else {
                                v_arg_2022_ = crate::leanh::lean_ctor_get(v___x_2020_, 1);
                                crate::leanh::lean_inc_ref(v_arg_2022_);
                                v___x_2023_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2020_);
                                v___x_2024_ = l_Lean_Expr_isApp(v___x_2023_);
                                if v___x_2024_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_2023_);
                                    crate::leanh::lean_dec_ref(v_arg_2022_);
                                    crate::leanh::lean_dec_ref(v_arg_2017_);
                                    crate::leanh::lean_dec_ref(v_arg_2014_);
                                    crate::leanh::lean_dec_ref(v_e_1997_);
                                    state = 1;
                                    continue;
                                } else {
                                    v_arg_2025_ = crate::leanh::lean_ctor_get(v___x_2023_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_2025_);
                                    v___x_2026_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2023_);
                                    v___x_2027_ = l_Lean_Expr_isApp(v___x_2026_);
                                    if v___x_2027_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_2026_);
                                        crate::leanh::lean_dec_ref(v_arg_2025_);
                                        crate::leanh::lean_dec_ref(v_arg_2022_);
                                        crate::leanh::lean_dec_ref(v_arg_2017_);
                                        crate::leanh::lean_dec_ref(v_arg_2014_);
                                        crate::leanh::lean_dec_ref(v_e_1997_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v_arg_2028_ = crate::leanh::lean_ctor_get(v___x_2026_, 1);
                                        crate::leanh::lean_inc_ref(v_arg_2028_);
                                        v___x_2029_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_2026_);
                                        v___x_2030_ =
                                            l_Lean_Meta_Grind_Arith_propagateMul___closed__2;
                                        v___x_2031_ =
                                            l_Lean_Expr_isConstOf(v___x_2029_, v___x_2030_);
                                        if v___x_2031_ == 0 {
                                            crate::leanh::lean_dec_ref(v___x_2029_);
                                            crate::leanh::lean_dec_ref(v_arg_2028_);
                                            crate::leanh::lean_dec_ref(v_arg_2025_);
                                            crate::leanh::lean_dec_ref(v_arg_2022_);
                                            crate::leanh::lean_dec_ref(v_arg_2017_);
                                            crate::leanh::lean_dec_ref(v_arg_2014_);
                                            crate::leanh::lean_dec_ref(v_e_1997_);
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc_ref(v_arg_2028_);
                                            v___x_2032_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f(v_arg_2028_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_);
                                            if crate::leanh::lean_obj_tag(v___x_2032_) == 0 {
                                                v_a_2033_ =
                                                    crate::leanh::lean_ctor_get(v___x_2032_, 0);
                                                v_isSharedCheck_2207_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_2032_))
                                                        as u8;
                                                if v_isSharedCheck_2207_ == 0 {
                                                    v___x_2035_ = v___x_2032_;
                                                    v_isShared_2036_ = v_isSharedCheck_2207_;
                                                    state = 2;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_2033_);
                                                    crate::leanh::lean_dec(v___x_2032_);
                                                    v___x_2035_ = crate::leanh::lean_box(0);
                                                    v_isShared_2036_ = v_isSharedCheck_2207_;
                                                    state = 2;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v___x_2029_);
                                                crate::leanh::lean_dec_ref(v_arg_2028_);
                                                crate::leanh::lean_dec_ref(v_arg_2025_);
                                                crate::leanh::lean_dec_ref(v_arg_2022_);
                                                crate::leanh::lean_dec_ref(v_arg_2017_);
                                                crate::leanh::lean_dec_ref(v_arg_2014_);
                                                crate::leanh::lean_dec_ref(v_e_1997_);
                                                v_a_2208_ =
                                                    crate::leanh::lean_ctor_get(v___x_2032_, 0);
                                                v_isSharedCheck_2215_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_2032_))
                                                        as u8;
                                                if v_isSharedCheck_2215_ == 0 {
                                                    v___x_2210_ = v___x_2032_;
                                                    v_isShared_2211_ = v_isSharedCheck_2215_;
                                                    state = 33;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_2208_);
                                                    crate::leanh::lean_dec(v___x_2032_);
                                                    v___x_2210_ = crate::leanh::lean_box(0);
                                                    v_isShared_2211_ = v_isSharedCheck_2215_;
                                                    state = 33;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2010_ = crate::leanh::lean_box(0);
                v___x_2011_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2011_, 0, v___x_2010_);
                return v___x_2011_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_2033_) == 1 {
                    v_val_2037_ = crate::leanh::lean_ctor_get(v_a_2033_, 0);
                    crate::leanh::lean_inc(v_val_2037_);
                    crate::leanh::lean_dec_ref_known(v_a_2033_, 1);
                    v___x_2201_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_arg_2028_,
                            v_arg_2025_,
                        );
                    crate::leanh::lean_dec_ref(v_arg_2025_);
                    if v___x_2201_ == 0 {
                        crate::leanh::lean_dec_ref(v_arg_2022_);
                        v___y_2039_ = v___x_2201_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2202_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v_arg_2028_,
                                v_arg_2022_,
                            );
                        crate::leanh::lean_dec_ref(v_arg_2022_);
                        v___y_2039_ = v___x_2202_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2033_);
                    crate::leanh::lean_dec_ref(v___x_2029_);
                    crate::leanh::lean_dec_ref(v_arg_2028_);
                    crate::leanh::lean_dec_ref(v_arg_2025_);
                    crate::leanh::lean_dec_ref(v_arg_2022_);
                    crate::leanh::lean_dec_ref(v_arg_2017_);
                    crate::leanh::lean_dec_ref(v_arg_2014_);
                    crate::leanh::lean_dec_ref(v_e_1997_);
                    v___x_2203_ = crate::leanh::lean_box(0);
                    if v_isShared_2036_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2035_, 0, v___x_2203_);
                        v___x_2205_ = v___x_2035_;
                        state = 32;
                        continue;
                    } else {
                        v_reuseFailAlloc_2206_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2203_);
                        v___x_2205_ = v_reuseFailAlloc_2206_;
                        state = 32;
                        continue;
                    }
                }
            }
            3 => {
                if v___y_2039_ == 0 {
                    crate::leanh::lean_dec(v_val_2037_);
                    crate::leanh::lean_dec_ref(v___x_2029_);
                    crate::leanh::lean_dec_ref(v_arg_2028_);
                    crate::leanh::lean_dec_ref(v_arg_2017_);
                    crate::leanh::lean_dec_ref(v_arg_2014_);
                    crate::leanh::lean_dec_ref(v_e_1997_);
                    v___x_2040_ = crate::leanh::lean_box(0);
                    if v_isShared_2036_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2035_, 0, v___x_2040_);
                        v___x_2042_ = v___x_2035_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2043_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2040_);
                        v___x_2042_ = v_reuseFailAlloc_2043_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_2044_ = l_Lean_Expr_constLevels_x21(v___x_2029_);
                    crate::leanh::lean_dec_ref(v___x_2029_);
                    if crate::leanh::lean_obj_tag(v___x_2044_) == 1 {
                        crate::leanh::lean_del_object(v___x_2035_);
                        v_head_2045_ = crate::leanh::lean_ctor_get(v___x_2044_, 0);
                        v_isSharedCheck_2195_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2044_)) as u8;
                        if v_isSharedCheck_2195_ == 0 {
                            v_unused_2196_ = crate::leanh::lean_ctor_get(v___x_2044_, 1);
                            crate::leanh::lean_dec(v_unused_2196_);
                            v___x_2047_ = v___x_2044_;
                            v_isShared_2048_ = v_isSharedCheck_2195_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_head_2045_);
                            crate::leanh::lean_dec(v___x_2044_);
                            v___x_2047_ = crate::leanh::lean_box(0);
                            v_isShared_2048_ = v_isSharedCheck_2195_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2044_);
                        crate::leanh::lean_dec(v_val_2037_);
                        crate::leanh::lean_dec_ref(v_arg_2028_);
                        crate::leanh::lean_dec_ref(v_arg_2017_);
                        crate::leanh::lean_dec_ref(v_arg_2014_);
                        crate::leanh::lean_dec_ref(v_e_1997_);
                        v___x_2197_ = crate::leanh::lean_box(0);
                        if v_isShared_2036_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2035_, 0, v___x_2197_);
                            v___x_2199_ = v___x_2035_;
                            state = 31;
                            continue;
                        } else {
                            v_reuseFailAlloc_2200_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2197_);
                            v___x_2199_ = v_reuseFailAlloc_2200_;
                            state = 31;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_2042_;
            }
            5 => {
                v___x_2049_ = lean_st_ref_get(v_a_1998_);
                crate::leanh::lean_inc_ref(v_arg_2017_);
                v___x_2050_ = l_Lean_Meta_Grind_Goal_getRoot(
                    v___x_2049_,
                    v_arg_2017_,
                    v_a_2004_,
                    v_a_2005_,
                    v_a_2006_,
                    v_a_2007_,
                );
                crate::leanh::lean_dec(v___x_2049_);
                if crate::leanh::lean_obj_tag(v___x_2050_) == 0 {
                    v_a_2051_ = crate::leanh::lean_ctor_get(v___x_2050_, 0);
                    crate::leanh::lean_inc(v_a_2051_);
                    crate::leanh::lean_dec_ref_known(v___x_2050_, 1);
                    v___x_2052_ = lean_st_ref_get(v_a_1998_);
                    crate::leanh::lean_inc_ref(v_arg_2014_);
                    v___x_2053_ = l_Lean_Meta_Grind_Goal_getRoot(
                        v___x_2052_,
                        v_arg_2014_,
                        v_a_2004_,
                        v_a_2005_,
                        v_a_2006_,
                        v_a_2007_,
                    );
                    crate::leanh::lean_dec(v___x_2052_);
                    if crate::leanh::lean_obj_tag(v___x_2053_) == 0 {
                        v_a_2054_ = crate::leanh::lean_ctor_get(v___x_2053_, 0);
                        crate::leanh::lean_inc(v_a_2054_);
                        crate::leanh::lean_dec_ref_known(v___x_2053_, 1);
                        crate::leanh::lean_inc(v_a_2051_);
                        v___x_2055_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(v_a_2051_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_);
                        if crate::leanh::lean_obj_tag(v___x_2055_) == 0 {
                            v_a_2056_ = crate::leanh::lean_ctor_get(v___x_2055_, 0);
                            v_isSharedCheck_2170_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2055_)) as u8;
                            if v_isSharedCheck_2170_ == 0 {
                                v___x_2058_ = v___x_2055_;
                                v_isShared_2059_ = v_isSharedCheck_2170_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2056_);
                                crate::leanh::lean_dec(v___x_2055_);
                                v___x_2058_ = crate::leanh::lean_box(0);
                                v_isShared_2059_ = v_isSharedCheck_2170_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2054_);
                            crate::leanh::lean_dec(v_a_2051_);
                            crate::leanh::lean_del_object(v___x_2047_);
                            crate::leanh::lean_dec(v_head_2045_);
                            crate::leanh::lean_dec(v_val_2037_);
                            crate::leanh::lean_dec_ref(v_arg_2028_);
                            crate::leanh::lean_dec_ref(v_arg_2017_);
                            crate::leanh::lean_dec_ref(v_arg_2014_);
                            crate::leanh::lean_dec_ref(v_e_1997_);
                            v_a_2171_ = crate::leanh::lean_ctor_get(v___x_2055_, 0);
                            v_isSharedCheck_2178_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2055_)) as u8;
                            if v_isSharedCheck_2178_ == 0 {
                                v___x_2173_ = v___x_2055_;
                                v_isShared_2174_ = v_isSharedCheck_2178_;
                                state = 25;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2171_);
                                crate::leanh::lean_dec(v___x_2055_);
                                v___x_2173_ = crate::leanh::lean_box(0);
                                v_isShared_2174_ = v_isSharedCheck_2178_;
                                state = 25;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2051_);
                        crate::leanh::lean_del_object(v___x_2047_);
                        crate::leanh::lean_dec(v_head_2045_);
                        crate::leanh::lean_dec(v_val_2037_);
                        crate::leanh::lean_dec_ref(v_arg_2028_);
                        crate::leanh::lean_dec_ref(v_arg_2017_);
                        crate::leanh::lean_dec_ref(v_arg_2014_);
                        crate::leanh::lean_dec_ref(v_e_1997_);
                        v_a_2179_ = crate::leanh::lean_ctor_get(v___x_2053_, 0);
                        v_isSharedCheck_2186_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2053_)) as u8;
                        if v_isSharedCheck_2186_ == 0 {
                            v___x_2181_ = v___x_2053_;
                            v_isShared_2182_ = v_isSharedCheck_2186_;
                            state = 27;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2179_);
                            crate::leanh::lean_dec(v___x_2053_);
                            v___x_2181_ = crate::leanh::lean_box(0);
                            v_isShared_2182_ = v_isSharedCheck_2186_;
                            state = 27;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2047_);
                    crate::leanh::lean_dec(v_head_2045_);
                    crate::leanh::lean_dec(v_val_2037_);
                    crate::leanh::lean_dec_ref(v_arg_2028_);
                    crate::leanh::lean_dec_ref(v_arg_2017_);
                    crate::leanh::lean_dec_ref(v_arg_2014_);
                    crate::leanh::lean_dec_ref(v_e_1997_);
                    v_a_2187_ = crate::leanh::lean_ctor_get(v___x_2050_, 0);
                    v_isSharedCheck_2194_ = (!crate::leanh::lean_is_exclusive(v___x_2050_)) as u8;
                    if v_isSharedCheck_2194_ == 0 {
                        v___x_2189_ = v___x_2050_;
                        v_isShared_2190_ = v_isSharedCheck_2194_;
                        state = 29;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2187_);
                        crate::leanh::lean_dec(v___x_2050_);
                        v___x_2189_ = crate::leanh::lean_box(0);
                        v_isShared_2190_ = v_isSharedCheck_2194_;
                        state = 29;
                        continue;
                    }
                }
            }
            6 => {
                if crate::leanh::lean_obj_tag(v_a_2056_) == 1 {
                    crate::leanh::lean_dec(v_a_2054_);
                    v_val_2060_ = crate::leanh::lean_ctor_get(v_a_2056_, 0);
                    crate::leanh::lean_inc(v_val_2060_);
                    crate::leanh::lean_dec_ref_known(v_a_2056_, 1);
                    v___x_2061_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2062_ = lean_nat_dec_eq(v_val_2060_, v___x_2061_);
                    if v___x_2062_ == 0 {
                        v___x_2063_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2064_ = lean_nat_dec_eq(v_val_2060_, v___x_2063_);
                        crate::leanh::lean_dec(v_val_2060_);
                        if v___x_2064_ == 0 {
                            crate::leanh::lean_dec(v_a_2051_);
                            crate::leanh::lean_del_object(v___x_2047_);
                            crate::leanh::lean_dec(v_head_2045_);
                            crate::leanh::lean_dec(v_val_2037_);
                            crate::leanh::lean_dec_ref(v_arg_2028_);
                            crate::leanh::lean_dec_ref(v_arg_2017_);
                            crate::leanh::lean_dec_ref(v_arg_2014_);
                            crate::leanh::lean_dec_ref(v_e_1997_);
                            v___x_2065_ = crate::leanh::lean_box(0);
                            if v_isShared_2059_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2058_, 0, v___x_2065_);
                                v___x_2067_ = v___x_2058_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_2068_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2065_);
                                v___x_2067_ = v_reuseFailAlloc_2068_;
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_2058_);
                            crate::leanh::lean_inc(v_a_2007_);
                            crate::leanh::lean_inc_ref(v_a_2006_);
                            crate::leanh::lean_inc(v_a_2005_);
                            crate::leanh::lean_inc_ref(v_a_2004_);
                            crate::leanh::lean_inc(v_a_2003_);
                            crate::leanh::lean_inc_ref(v_a_2002_);
                            crate::leanh::lean_inc(v_a_2001_);
                            crate::leanh::lean_inc_ref(v_a_2000_);
                            crate::leanh::lean_inc(v_a_1999_);
                            crate::leanh::lean_inc(v_a_1998_);
                            crate::leanh::lean_inc_ref(v_arg_2017_);
                            v___x_2069_ = lean_grind_mk_eq_proof(
                                v_arg_2017_,
                                v_a_2051_,
                                v_a_1998_,
                                v_a_1999_,
                                v_a_2000_,
                                v_a_2001_,
                                v_a_2002_,
                                v_a_2003_,
                                v_a_2004_,
                                v_a_2005_,
                                v_a_2006_,
                                v_a_2007_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2069_) == 0 {
                                v_a_2070_ = crate::leanh::lean_ctor_get(v___x_2069_, 0);
                                crate::leanh::lean_inc(v_a_2070_);
                                crate::leanh::lean_dec_ref_known(v___x_2069_, 1);
                                v___x_2071_ = l_Lean_Meta_Grind_Arith_propagateMul___closed__5;
                                v___x_2072_ = crate::leanh::lean_box(0);
                                if v_isShared_2048_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2047_, 1, v___x_2072_);
                                    v___x_2074_ = v___x_2047_;
                                    state = 8;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2078_ =
                                        crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2078_,
                                        0,
                                        v_head_2045_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2078_,
                                        1,
                                        v___x_2072_,
                                    );
                                    v___x_2074_ = v_reuseFailAlloc_2078_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_2047_);
                                crate::leanh::lean_dec(v_head_2045_);
                                crate::leanh::lean_dec(v_val_2037_);
                                crate::leanh::lean_dec_ref(v_arg_2028_);
                                crate::leanh::lean_dec_ref(v_arg_2017_);
                                crate::leanh::lean_dec_ref(v_arg_2014_);
                                crate::leanh::lean_dec_ref(v_e_1997_);
                                v_a_2079_ = crate::leanh::lean_ctor_get(v___x_2069_, 0);
                                v_isSharedCheck_2086_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2069_)) as u8;
                                if v_isSharedCheck_2086_ == 0 {
                                    v___x_2081_ = v___x_2069_;
                                    v_isShared_2082_ = v_isSharedCheck_2086_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2079_);
                                    crate::leanh::lean_dec(v___x_2069_);
                                    v___x_2081_ = crate::leanh::lean_box(0);
                                    v_isShared_2082_ = v_isSharedCheck_2086_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_2060_);
                        crate::leanh::lean_del_object(v___x_2058_);
                        crate::leanh::lean_inc(v_a_2007_);
                        crate::leanh::lean_inc_ref(v_a_2006_);
                        crate::leanh::lean_inc(v_a_2005_);
                        crate::leanh::lean_inc_ref(v_a_2004_);
                        crate::leanh::lean_inc(v_a_2003_);
                        crate::leanh::lean_inc_ref(v_a_2002_);
                        crate::leanh::lean_inc(v_a_2001_);
                        crate::leanh::lean_inc_ref(v_a_2000_);
                        crate::leanh::lean_inc(v_a_1999_);
                        crate::leanh::lean_inc(v_a_1998_);
                        crate::leanh::lean_inc(v_a_2051_);
                        crate::leanh::lean_inc_ref(v_arg_2017_);
                        v___x_2087_ = lean_grind_mk_eq_proof(
                            v_arg_2017_,
                            v_a_2051_,
                            v_a_1998_,
                            v_a_1999_,
                            v_a_2000_,
                            v_a_2001_,
                            v_a_2002_,
                            v_a_2003_,
                            v_a_2004_,
                            v_a_2005_,
                            v_a_2006_,
                            v_a_2007_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2087_) == 0 {
                            v_a_2088_ = crate::leanh::lean_ctor_get(v___x_2087_, 0);
                            crate::leanh::lean_inc(v_a_2088_);
                            crate::leanh::lean_dec_ref_known(v___x_2087_, 1);
                            v___x_2089_ = l_Lean_Meta_Grind_Arith_propagateMul___closed__7;
                            v___x_2090_ = crate::leanh::lean_box(0);
                            if v_isShared_2048_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2047_, 1, v___x_2090_);
                                v___x_2092_ = v___x_2047_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_2097_ =
                                    crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2097_,
                                    0,
                                    v_head_2045_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2097_, 1, v___x_2090_);
                                v___x_2092_ = v_reuseFailAlloc_2097_;
                                state = 11;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2051_);
                            crate::leanh::lean_del_object(v___x_2047_);
                            crate::leanh::lean_dec(v_head_2045_);
                            crate::leanh::lean_dec(v_val_2037_);
                            crate::leanh::lean_dec_ref(v_arg_2028_);
                            crate::leanh::lean_dec_ref(v_arg_2017_);
                            crate::leanh::lean_dec_ref(v_arg_2014_);
                            crate::leanh::lean_dec_ref(v_e_1997_);
                            v_a_2098_ = crate::leanh::lean_ctor_get(v___x_2087_, 0);
                            v_isSharedCheck_2105_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2087_)) as u8;
                            if v_isSharedCheck_2105_ == 0 {
                                v___x_2100_ = v___x_2087_;
                                v_isShared_2101_ = v_isSharedCheck_2105_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2098_);
                                crate::leanh::lean_dec(v___x_2087_);
                                v___x_2100_ = crate::leanh::lean_box(0);
                                v_isShared_2101_ = v_isSharedCheck_2105_;
                                state = 12;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2058_);
                    crate::leanh::lean_dec(v_a_2056_);
                    crate::leanh::lean_dec(v_a_2051_);
                    crate::leanh::lean_inc(v_a_2054_);
                    v___x_2106_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(v_a_2054_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_);
                    if crate::leanh::lean_obj_tag(v___x_2106_) == 0 {
                        v_a_2107_ = crate::leanh::lean_ctor_get(v___x_2106_, 0);
                        v_isSharedCheck_2161_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2106_)) as u8;
                        if v_isSharedCheck_2161_ == 0 {
                            v___x_2109_ = v___x_2106_;
                            v_isShared_2110_ = v_isSharedCheck_2161_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2107_);
                            crate::leanh::lean_dec(v___x_2106_);
                            v___x_2109_ = crate::leanh::lean_box(0);
                            v_isShared_2110_ = v_isSharedCheck_2161_;
                            state = 14;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2054_);
                        crate::leanh::lean_del_object(v___x_2047_);
                        crate::leanh::lean_dec(v_head_2045_);
                        crate::leanh::lean_dec(v_val_2037_);
                        crate::leanh::lean_dec_ref(v_arg_2028_);
                        crate::leanh::lean_dec_ref(v_arg_2017_);
                        crate::leanh::lean_dec_ref(v_arg_2014_);
                        crate::leanh::lean_dec_ref(v_e_1997_);
                        v_a_2162_ = crate::leanh::lean_ctor_get(v___x_2106_, 0);
                        v_isSharedCheck_2169_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2106_)) as u8;
                        if v_isSharedCheck_2169_ == 0 {
                            v___x_2164_ = v___x_2106_;
                            v_isShared_2165_ = v_isSharedCheck_2169_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2162_);
                            crate::leanh::lean_dec(v___x_2106_);
                            v___x_2164_ = crate::leanh::lean_box(0);
                            v_isShared_2165_ = v_isSharedCheck_2169_;
                            state = 23;
                            continue;
                        }
                    }
                }
            }
            7 => {
                return v___x_2067_;
            }
            8 => {
                v___x_2075_ = l_Lean_mkConst(v___x_2071_, v___x_2074_);
                crate::leanh::lean_inc_ref(v_arg_2014_);
                v___x_2076_ = l_Lean_mkApp5(
                    v___x_2075_,
                    v_arg_2028_,
                    v_val_2037_,
                    v_arg_2017_,
                    v_arg_2014_,
                    v_a_2070_,
                );
                v___x_2077_ = l_Lean_Meta_Grind_pushEqCore___redArg(
                    v_e_1997_,
                    v_arg_2014_,
                    v___x_2076_,
                    v___x_2062_,
                    v_a_1998_,
                    v_a_2000_,
                    v_a_2004_,
                    v_a_2005_,
                    v_a_2006_,
                    v_a_2007_,
                );
                return v___x_2077_;
            }
            9 => {
                if v_isShared_2082_ == 0 {
                    v___x_2084_ = v___x_2081_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2085_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
                    v___x_2084_ = v_reuseFailAlloc_2085_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2084_;
            }
            11 => {
                v___x_2093_ = l_Lean_mkConst(v___x_2089_, v___x_2092_);
                v___x_2094_ = l_Lean_mkApp5(
                    v___x_2093_,
                    v_arg_2028_,
                    v_val_2037_,
                    v_arg_2017_,
                    v_arg_2014_,
                    v_a_2088_,
                );
                v___x_2095_ = 0;
                v___x_2096_ = l_Lean_Meta_Grind_pushEqCore___redArg(
                    v_e_1997_,
                    v_a_2051_,
                    v___x_2094_,
                    v___x_2095_,
                    v_a_1998_,
                    v_a_2000_,
                    v_a_2004_,
                    v_a_2005_,
                    v_a_2006_,
                    v_a_2007_,
                );
                return v___x_2096_;
            }
            12 => {
                if v_isShared_2101_ == 0 {
                    v___x_2103_ = v___x_2100_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2104_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
                    v___x_2103_ = v_reuseFailAlloc_2104_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2103_;
            }
            14 => {
                if crate::leanh::lean_obj_tag(v_a_2107_) == 1 {
                    v_val_2111_ = crate::leanh::lean_ctor_get(v_a_2107_, 0);
                    crate::leanh::lean_inc(v_val_2111_);
                    crate::leanh::lean_dec_ref_known(v_a_2107_, 1);
                    v___x_2112_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2113_ = lean_nat_dec_eq(v_val_2111_, v___x_2112_);
                    if v___x_2113_ == 0 {
                        v___x_2114_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2115_ = lean_nat_dec_eq(v_val_2111_, v___x_2114_);
                        crate::leanh::lean_dec(v_val_2111_);
                        if v___x_2115_ == 0 {
                            crate::leanh::lean_dec(v_a_2054_);
                            crate::leanh::lean_del_object(v___x_2047_);
                            crate::leanh::lean_dec(v_head_2045_);
                            crate::leanh::lean_dec(v_val_2037_);
                            crate::leanh::lean_dec_ref(v_arg_2028_);
                            crate::leanh::lean_dec_ref(v_arg_2017_);
                            crate::leanh::lean_dec_ref(v_arg_2014_);
                            crate::leanh::lean_dec_ref(v_e_1997_);
                            v___x_2116_ = crate::leanh::lean_box(0);
                            if v_isShared_2110_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2109_, 0, v___x_2116_);
                                v___x_2118_ = v___x_2109_;
                                state = 15;
                                continue;
                            } else {
                                v_reuseFailAlloc_2119_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2116_);
                                v___x_2118_ = v_reuseFailAlloc_2119_;
                                state = 15;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_2109_);
                            crate::leanh::lean_inc(v_a_2007_);
                            crate::leanh::lean_inc_ref(v_a_2006_);
                            crate::leanh::lean_inc(v_a_2005_);
                            crate::leanh::lean_inc_ref(v_a_2004_);
                            crate::leanh::lean_inc(v_a_2003_);
                            crate::leanh::lean_inc_ref(v_a_2002_);
                            crate::leanh::lean_inc(v_a_2001_);
                            crate::leanh::lean_inc_ref(v_a_2000_);
                            crate::leanh::lean_inc(v_a_1999_);
                            crate::leanh::lean_inc(v_a_1998_);
                            crate::leanh::lean_inc_ref(v_arg_2014_);
                            v___x_2120_ = lean_grind_mk_eq_proof(
                                v_arg_2014_,
                                v_a_2054_,
                                v_a_1998_,
                                v_a_1999_,
                                v_a_2000_,
                                v_a_2001_,
                                v_a_2002_,
                                v_a_2003_,
                                v_a_2004_,
                                v_a_2005_,
                                v_a_2006_,
                                v_a_2007_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2120_) == 0 {
                                v_a_2121_ = crate::leanh::lean_ctor_get(v___x_2120_, 0);
                                crate::leanh::lean_inc(v_a_2121_);
                                crate::leanh::lean_dec_ref_known(v___x_2120_, 1);
                                v___x_2122_ = l_Lean_Meta_Grind_Arith_propagateMul___closed__9;
                                v___x_2123_ = crate::leanh::lean_box(0);
                                if v_isShared_2048_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2047_, 1, v___x_2123_);
                                    v___x_2125_ = v___x_2047_;
                                    state = 16;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2129_ =
                                        crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2129_,
                                        0,
                                        v_head_2045_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2129_,
                                        1,
                                        v___x_2123_,
                                    );
                                    v___x_2125_ = v_reuseFailAlloc_2129_;
                                    state = 16;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_2047_);
                                crate::leanh::lean_dec(v_head_2045_);
                                crate::leanh::lean_dec(v_val_2037_);
                                crate::leanh::lean_dec_ref(v_arg_2028_);
                                crate::leanh::lean_dec_ref(v_arg_2017_);
                                crate::leanh::lean_dec_ref(v_arg_2014_);
                                crate::leanh::lean_dec_ref(v_e_1997_);
                                v_a_2130_ = crate::leanh::lean_ctor_get(v___x_2120_, 0);
                                v_isSharedCheck_2137_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2120_)) as u8;
                                if v_isSharedCheck_2137_ == 0 {
                                    v___x_2132_ = v___x_2120_;
                                    v_isShared_2133_ = v_isSharedCheck_2137_;
                                    state = 17;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2130_);
                                    crate::leanh::lean_dec(v___x_2120_);
                                    v___x_2132_ = crate::leanh::lean_box(0);
                                    v_isShared_2133_ = v_isSharedCheck_2137_;
                                    state = 17;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_2111_);
                        crate::leanh::lean_del_object(v___x_2109_);
                        crate::leanh::lean_inc(v_a_2007_);
                        crate::leanh::lean_inc_ref(v_a_2006_);
                        crate::leanh::lean_inc(v_a_2005_);
                        crate::leanh::lean_inc_ref(v_a_2004_);
                        crate::leanh::lean_inc(v_a_2003_);
                        crate::leanh::lean_inc_ref(v_a_2002_);
                        crate::leanh::lean_inc(v_a_2001_);
                        crate::leanh::lean_inc_ref(v_a_2000_);
                        crate::leanh::lean_inc(v_a_1999_);
                        crate::leanh::lean_inc(v_a_1998_);
                        crate::leanh::lean_inc(v_a_2054_);
                        crate::leanh::lean_inc_ref(v_arg_2014_);
                        v___x_2138_ = lean_grind_mk_eq_proof(
                            v_arg_2014_,
                            v_a_2054_,
                            v_a_1998_,
                            v_a_1999_,
                            v_a_2000_,
                            v_a_2001_,
                            v_a_2002_,
                            v_a_2003_,
                            v_a_2004_,
                            v_a_2005_,
                            v_a_2006_,
                            v_a_2007_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2138_) == 0 {
                            v_a_2139_ = crate::leanh::lean_ctor_get(v___x_2138_, 0);
                            crate::leanh::lean_inc(v_a_2139_);
                            crate::leanh::lean_dec_ref_known(v___x_2138_, 1);
                            v___x_2140_ = l_Lean_Meta_Grind_Arith_propagateMul___closed__11;
                            v___x_2141_ = crate::leanh::lean_box(0);
                            if v_isShared_2048_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2047_, 1, v___x_2141_);
                                v___x_2143_ = v___x_2047_;
                                state = 19;
                                continue;
                            } else {
                                v_reuseFailAlloc_2148_ =
                                    crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2148_,
                                    0,
                                    v_head_2045_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2148_, 1, v___x_2141_);
                                v___x_2143_ = v_reuseFailAlloc_2148_;
                                state = 19;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2054_);
                            crate::leanh::lean_del_object(v___x_2047_);
                            crate::leanh::lean_dec(v_head_2045_);
                            crate::leanh::lean_dec(v_val_2037_);
                            crate::leanh::lean_dec_ref(v_arg_2028_);
                            crate::leanh::lean_dec_ref(v_arg_2017_);
                            crate::leanh::lean_dec_ref(v_arg_2014_);
                            crate::leanh::lean_dec_ref(v_e_1997_);
                            v_a_2149_ = crate::leanh::lean_ctor_get(v___x_2138_, 0);
                            v_isSharedCheck_2156_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2138_)) as u8;
                            if v_isSharedCheck_2156_ == 0 {
                                v___x_2151_ = v___x_2138_;
                                v_isShared_2152_ = v_isSharedCheck_2156_;
                                state = 20;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2149_);
                                crate::leanh::lean_dec(v___x_2138_);
                                v___x_2151_ = crate::leanh::lean_box(0);
                                v_isShared_2152_ = v_isSharedCheck_2156_;
                                state = 20;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2107_);
                    crate::leanh::lean_dec(v_a_2054_);
                    crate::leanh::lean_del_object(v___x_2047_);
                    crate::leanh::lean_dec(v_head_2045_);
                    crate::leanh::lean_dec(v_val_2037_);
                    crate::leanh::lean_dec_ref(v_arg_2028_);
                    crate::leanh::lean_dec_ref(v_arg_2017_);
                    crate::leanh::lean_dec_ref(v_arg_2014_);
                    crate::leanh::lean_dec_ref(v_e_1997_);
                    v___x_2157_ = crate::leanh::lean_box(0);
                    if v_isShared_2110_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2109_, 0, v___x_2157_);
                        v___x_2159_ = v___x_2109_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_2160_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2157_);
                        v___x_2159_ = v_reuseFailAlloc_2160_;
                        state = 22;
                        continue;
                    }
                }
            }
            15 => {
                return v___x_2118_;
            }
            16 => {
                v___x_2126_ = l_Lean_mkConst(v___x_2122_, v___x_2125_);
                crate::leanh::lean_inc_ref(v_arg_2017_);
                v___x_2127_ = l_Lean_mkApp5(
                    v___x_2126_,
                    v_arg_2028_,
                    v_val_2037_,
                    v_arg_2017_,
                    v_arg_2014_,
                    v_a_2121_,
                );
                v___x_2128_ = l_Lean_Meta_Grind_pushEqCore___redArg(
                    v_e_1997_,
                    v_arg_2017_,
                    v___x_2127_,
                    v___x_2113_,
                    v_a_1998_,
                    v_a_2000_,
                    v_a_2004_,
                    v_a_2005_,
                    v_a_2006_,
                    v_a_2007_,
                );
                return v___x_2128_;
            }
            17 => {
                if v_isShared_2133_ == 0 {
                    v___x_2135_ = v___x_2132_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2136_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
                    v___x_2135_ = v_reuseFailAlloc_2136_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2135_;
            }
            19 => {
                v___x_2144_ = l_Lean_mkConst(v___x_2140_, v___x_2143_);
                v___x_2145_ = l_Lean_mkApp5(
                    v___x_2144_,
                    v_arg_2028_,
                    v_val_2037_,
                    v_arg_2017_,
                    v_arg_2014_,
                    v_a_2139_,
                );
                v___x_2146_ = 0;
                v___x_2147_ = l_Lean_Meta_Grind_pushEqCore___redArg(
                    v_e_1997_,
                    v_a_2054_,
                    v___x_2145_,
                    v___x_2146_,
                    v_a_1998_,
                    v_a_2000_,
                    v_a_2004_,
                    v_a_2005_,
                    v_a_2006_,
                    v_a_2007_,
                );
                return v___x_2147_;
            }
            20 => {
                if v_isShared_2152_ == 0 {
                    v___x_2154_ = v___x_2151_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2155_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2149_);
                    v___x_2154_ = v_reuseFailAlloc_2155_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2154_;
            }
            22 => {
                return v___x_2159_;
            }
            23 => {
                if v_isShared_2165_ == 0 {
                    v___x_2167_ = v___x_2164_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2168_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
                    v___x_2167_ = v_reuseFailAlloc_2168_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2167_;
            }
            25 => {
                if v_isShared_2174_ == 0 {
                    v___x_2176_ = v___x_2173_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_2177_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
                    v___x_2176_ = v_reuseFailAlloc_2177_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_2176_;
            }
            27 => {
                if v_isShared_2182_ == 0 {
                    v___x_2184_ = v___x_2181_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2185_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
                    v___x_2184_ = v_reuseFailAlloc_2185_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_2184_;
            }
            29 => {
                if v_isShared_2190_ == 0 {
                    v___x_2192_ = v___x_2189_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2193_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2187_);
                    v___x_2192_ = v_reuseFailAlloc_2193_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_2192_;
            }
            31 => {
                return v___x_2199_;
            }
            32 => {
                return v___x_2205_;
            }
            33 => {
                if v_isShared_2211_ == 0 {
                    v___x_2213_ = v___x_2210_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_2214_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
                    v___x_2213_ = v_reuseFailAlloc_2214_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_2213_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_propagateMul___boxed(
    mut v_e_2216_: *mut crate::leanh::LeanObject,
    mut v_a_2217_: *mut crate::leanh::LeanObject,
    mut v_a_2218_: *mut crate::leanh::LeanObject,
    mut v_a_2219_: *mut crate::leanh::LeanObject,
    mut v_a_2220_: *mut crate::leanh::LeanObject,
    mut v_a_2221_: *mut crate::leanh::LeanObject,
    mut v_a_2222_: *mut crate::leanh::LeanObject,
    mut v_a_2223_: *mut crate::leanh::LeanObject,
    mut v_a_2224_: *mut crate::leanh::LeanObject,
    mut v_a_2225_: *mut crate::leanh::LeanObject,
    mut v_a_2226_: *mut crate::leanh::LeanObject,
    mut v_a_2227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2228_ = l_Lean_Meta_Grind_Arith_propagateMul(
        v_e_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_,
        v_a_2224_, v_a_2225_, v_a_2226_,
    );
    crate::leanh::lean_dec(v_a_2226_);
    crate::leanh::lean_dec_ref(v_a_2225_);
    crate::leanh::lean_dec(v_a_2224_);
    crate::leanh::lean_dec_ref(v_a_2223_);
    crate::leanh::lean_dec(v_a_2222_);
    crate::leanh::lean_dec_ref(v_a_2221_);
    crate::leanh::lean_dec(v_a_2220_);
    crate::leanh::lean_dec_ref(v_a_2219_);
    crate::leanh::lean_dec(v_a_2218_);
    crate::leanh::lean_dec(v_a_2217_);
    return v_res_2228_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_8_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2230_ = l_Lean_Meta_Grind_Arith_propagateMul___closed__2;
    v___x_2231_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_propagateMul___boxed as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_2232_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_2230_, v___x_2231_);
    return v___x_2232_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_8____boxed(
    mut v_a_2233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2234_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_8_();
    return v_res_2234_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Propagate(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_8_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_8_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_8_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_8_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_8_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring();
    crate::leanh::lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_8_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Propagate(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Propagate(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Propagate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Propagate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Propagate(builtin);
}
