// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr
// Imports: Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Init.Data.Int.OfNat Init.Grind.Propagator Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Grind.Arith.Cutsat.Var Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat Lean.Meta.Tactic.Grind.Arith.Cutsat.Proof Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm Lean.Meta.Tactic.Grind.Arith.Cutsat.CommRing Lean.Meta.NatInstTesters Lean.Meta.Tactic.Grind.PropagatorAttr Init.Data.Nat.Dvd
use crate::r#gen::Init::Data::Int::Linear::{
    l_Int_Linear_Expr_norm, l_Int_Linear_Poly_coeff, l_Int_Linear_Poly_combine,
    l_Int_Linear_Poly_div, l_Int_Linear_Poly_gcdCoeffs, l_Int_Linear_Poly_getConst,
    l_Int_Linear_Poly_isUnsatDvd, l_Int_Linear_Poly_mul, l_Int_Linear_Poly_norm,
};
use crate::r#gen::Init::Data::Int::OfNat::{
    initialize_Init_Data_Int_OfNat, runtime_initialize_Init_Data_Int_OfNat,
};
use crate::r#gen::Init::Data::Nat::Dvd::{
    initialize_Init_Data_Nat_Dvd, runtime_initialize_Init_Data_Nat_Dvd,
};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::GetElem::l_outOfBounds___redArg;
use crate::r#gen::Init::Grind::Propagator::{
    initialize_Init_Grind_Propagator, runtime_initialize_Init_Grind_Propagator,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr4, l_Lean_maxRecDepthErrorMessage,
};
use crate::r#gen::Lean::Data::LBool::l_Lean_instBEqLBool_beq;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_get_x21___redArg, l_Lean_PersistentArray_push___redArg,
    l_Lean_PersistentArray_set___redArg,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_isApp,
    l_Lean_Expr_isConstOf, l_Lean_eagerReflBoolTrue, l_Lean_mkApp3, l_Lean_mkApp4, l_Lean_mkApp6,
    l_Lean_mkConst,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_indentExpr,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::l_Lean_Meta_mkOfEqFalseCore;
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_instantiateMVarsIfMVarApp___redArg;
use crate::r#gen::Lean::Meta::IntInstTesters::l_Lean_Meta_Structural_isInstDvdInt___redArg;
use crate::r#gen::Lean::Meta::LitValues::{
    l_Lean_Meta_getIntValue_x3f, l_Lean_Meta_getNatValue_x3f,
};
use crate::r#gen::Lean::Meta::NatInstTesters::{
    initialize_Lean_Meta_NatInstTesters, l_Lean_Meta_Structural_isInstDvdNat___redArg,
    runtime_initialize_Lean_Meta_NatInstTesters,
};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    l_Lean_Meta_Sym_getConfig___redArg, l_Lean_Meta_Sym_reportIssue,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::CommRing::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing, l_Int_Linear_Poly_normCommRing_x3f,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Nat::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat, l_Lean_Meta_Grind_Arith_Cutsat_natToInt,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Norm::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm,
    l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Proof::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof,
    l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Types::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types, l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Util::{
    l_Int_Linear_Poly_findVarToSubst___redArg, l_Int_Linear_Poly_isSorted,
    l_Int_Linear_Poly_updateOccs___redArg, l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial,
    l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg,
    l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg,
    l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg,
    l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg,
    l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg,
    l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg,
    l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg,
    l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Var::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var, l_Lean_Meta_Grind_Arith_Cutsat_toPoly,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Util::l_Lean_Meta_Grind_Arith_gcdExt;
use crate::r#gen::Lean::Meta::Tactic::Grind::PropagatorAttr::{
    initialize_Lean_Meta_Tactic_Grind_PropagatorAttr,
    l_Lean_Meta_Grind_registerBuiltinDownwardPropagator,
    runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Simp::{
    initialize_Lean_Meta_Tactic_Grind_Simp, l_Lean_Meta_Grind_pushNewFact,
    runtime_initialize_Lean_Meta_Tactic_Grind_Simp,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg,
    l_Lean_Meta_Grind_getConfig___redArg, l_Lean_Meta_Grind_getGeneration___redArg,
    l_Lean_Meta_Grind_isEqFalse___redArg, l_Lean_Meta_Grind_isEqTrue___redArg,
    l_Lean_Meta_Grind_mkEqFalseProof,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_eq, lean_int_dec_lt, lean_int_mul, lean_int_neg, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::{lean_int_ediv, lean_int_emod};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0_value:
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
    m_data: [103, 114, 105, 110, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1_value:
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
    m_data: [100, 101, 98, 117, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2_value:
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
    m_data: [108, 105, 97, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3_value:
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
    m_data: [115, 117, 98, 115, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15947788021050471391 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1_value)
            as *mut crate::leanh::LeanObject,
        5637236024813792860 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2_value)
            as *mut crate::leanh::LeanObject,
        12441483040187581015 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3_value)
            as *mut crate::leanh::LeanObject,
        1504612912130463053 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5_value:
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
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5_value)
            as *mut crate::leanh::LeanObject,
        14231257465488249300 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8_value:
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
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,7310567555909517314 as *mut crate::leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,273128857561458264 as *mut crate::leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0_value:
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
    m_data: [115, 116, 111, 114, 101, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [116, 114, 105, 118, 105, 97, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2_value:
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
    m_data: [117, 110, 115, 97, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3_value:
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
    m_data: [97, 115, 115, 101, 114, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15947788021050471391 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2_value)
            as *mut crate::leanh::LeanObject,
        11074150007773075224 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3_value)
            as *mut crate::leanh::LeanObject,
        10199653630302390726 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0_value:
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
    m_data: [68, 118, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1_value:
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
    m_data: [100, 118, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0_value)
            as *mut crate::leanh::LeanObject,
        4493959381811283967 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1_value)
            as *mut crate::leanh::LeanObject,
        1297950917268934889 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3_value:
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
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4_value:
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
    m_data: [76, 105, 110, 101, 97, 114, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5_value:
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
    m_data: [111, 102, 95, 110, 111, 116, 95, 100, 118, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4_value)
            as *mut crate::leanh::LeanObject,
        5856160982567210200 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5_value)
            as *mut crate::leanh::LeanObject,
        10013225460834363961 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8_value:
    crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        110, 111, 110, 45, 108, 105, 110, 101, 97, 114, 32, 100, 105, 118, 105, 115, 105, 98, 105,
        108, 105, 116, 121, 32, 99, 111, 110, 115, 116, 114, 97, 105, 110, 116, 32, 102, 111, 117,
        110, 100, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0_value:
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
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        101, 109, 111, 100, 95, 112, 111, 115, 95, 111, 102, 95, 110, 111, 116, 95, 100, 118, 100,
        0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11442535297760353691 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1_value)
            as *mut crate::leanh::LeanObject,
        12422191932485571110 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4_value:
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
    m_data: [84, 111, 73, 110, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__5_value:
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
    m_data: [111, 102, 95, 100, 118, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11442535297760353691 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4_value)
            as *mut crate::leanh::LeanObject,
        16002102443310951684 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__5_value)
            as *mut crate::leanh::LeanObject,
        9691051192635189215 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11442535297760353691 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1367_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1368_ = lean_nat_to_int(v___x_1367_);
    return v___x_1368_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1369_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1370_ = lean_nat_to_int(v___x_1369_);
    return v___x_1370_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(
    mut v_c_1371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1377_: u8 = 0;
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: u8 = 0;
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: u8 = 0;
    let mut v___y_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_g_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: u8 = 0;
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: u8 = 0;
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_d_1401_ = crate::leanh::lean_ctor_get(v_c_1371_, 0);
                crate::leanh::lean_inc(v_d_1401_);
                v_p_1402_ = crate::leanh::lean_ctor_get(v_c_1371_, 1);
                v___x_1403_ = l_Int_Linear_Poly_isSorted(v_p_1402_);
                if v___x_1403_ == 0 {
                    crate::leanh::lean_inc_ref(v_p_1402_);
                    v___x_1404_ = l_Int_Linear_Poly_norm(v_p_1402_);
                    v___x_1405_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1405_, 0, v_c_1371_);
                    crate::leanh::lean_inc_ref(v___x_1404_);
                    crate::leanh::lean_inc(v_d_1401_);
                    v___x_1406_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1406_, 0, v_d_1401_);
                    crate::leanh::lean_ctor_set(v___x_1406_, 1, v___x_1404_);
                    crate::leanh::lean_ctor_set(v___x_1406_, 2, v___x_1405_);
                    v___y_1394_ = v___x_1406_;
                    v_d_1395_ = v_d_1401_;
                    v_p_1396_ = v___x_1404_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_p_1402_);
                    v___y_1394_ = v_c_1371_;
                    v_d_1395_ = v_d_1401_;
                    v_p_1396_ = v_p_1402_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                if v___y_1377_ == 0 {
                    crate::leanh::lean_dec(v___y_1376_);
                    crate::leanh::lean_dec_ref(v___y_1375_);
                    crate::leanh::lean_dec(v___y_1374_);
                    return v___y_1373_;
                } else {
                    v___x_1378_ = lean_int_ediv(v___y_1374_, v___y_1376_);
                    crate::leanh::lean_dec(v___y_1374_);
                    v___x_1379_ = l_Int_Linear_Poly_div(v___y_1376_, v___y_1375_);
                    crate::leanh::lean_dec(v___y_1376_);
                    v___x_1380_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1380_, 0, v___y_1373_);
                    v___x_1381_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1381_, 0, v___x_1378_);
                    crate::leanh::lean_ctor_set(v___x_1381_, 1, v___x_1379_);
                    crate::leanh::lean_ctor_set(v___x_1381_, 2, v___x_1380_);
                    return v___x_1381_;
                }
            }
            2 => {
                v___x_1388_ = l_Int_Linear_Poly_getConst(v___y_1386_);
                v___x_1389_ = lean_int_emod(v___x_1388_, v___y_1387_);
                crate::leanh::lean_dec(v___x_1388_);
                v___x_1390_ = lean_int_dec_eq(v___x_1389_, v___y_1383_);
                crate::leanh::lean_dec(v___x_1389_);
                if v___x_1390_ == 0 {
                    v___y_1373_ = v___y_1384_;
                    v___y_1374_ = v___y_1385_;
                    v___y_1375_ = v___y_1386_;
                    v___y_1376_ = v___y_1387_;
                    v___y_1377_ = v___x_1390_;
                    state = 1;
                    continue;
                } else {
                    v___x_1391_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0,
                    );
                    v___x_1392_ = lean_int_dec_eq(v___y_1387_, v___x_1391_);
                    if v___x_1392_ == 0 {
                        v___y_1373_ = v___y_1384_;
                        v___y_1374_ = v___y_1385_;
                        v___y_1375_ = v___y_1386_;
                        v___y_1376_ = v___y_1387_;
                        v___y_1377_ = v___x_1390_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___y_1387_);
                        crate::leanh::lean_dec_ref(v___y_1386_);
                        crate::leanh::lean_dec(v___y_1385_);
                        return v___y_1384_;
                    }
                }
            }
            3 => {
                crate::leanh::lean_inc(v_d_1395_);
                v_g_1397_ = l_Int_Linear_Poly_gcdCoeffs(v_p_1396_, v_d_1395_);
                v___x_1398_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1,
                );
                v___x_1399_ = lean_int_dec_lt(v_d_1395_, v___x_1398_);
                if v___x_1399_ == 0 {
                    v___y_1383_ = v___x_1398_;
                    v___y_1384_ = v___y_1394_;
                    v___y_1385_ = v_d_1395_;
                    v___y_1386_ = v_p_1396_;
                    v___y_1387_ = v_g_1397_;
                    state = 2;
                    continue;
                } else {
                    v___x_1400_ = lean_int_neg(v_g_1397_);
                    crate::leanh::lean_dec(v_g_1397_);
                    v___y_1383_ = v___x_1398_;
                    v___y_1384_ = v___y_1394_;
                    v___y_1385_ = v_d_1395_;
                    v___y_1386_ = v_p_1396_;
                    v___y_1387_ = v___x_1400_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(
    mut v_msgData_1407_: *mut crate::leanh::LeanObject,
    mut v___y_1408_: *mut crate::leanh::LeanObject,
    mut v___y_1409_: *mut crate::leanh::LeanObject,
    mut v___y_1410_: *mut crate::leanh::LeanObject,
    mut v___y_1411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1413_ = lean_st_ref_get(v___y_1411_);
    v_env_1414_ = crate::leanh::lean_ctor_get(v___x_1413_, 0);
    crate::leanh::lean_inc_ref(v_env_1414_);
    crate::leanh::lean_dec(v___x_1413_);
    v___x_1415_ = lean_st_ref_get(v___y_1409_);
    v_mctx_1416_ = crate::leanh::lean_ctor_get(v___x_1415_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1416_);
    crate::leanh::lean_dec(v___x_1415_);
    v_lctx_1417_ = crate::leanh::lean_ctor_get(v___y_1408_, 2);
    v_options_1418_ = crate::leanh::lean_ctor_get(v___y_1410_, 2);
    crate::leanh::lean_inc_ref(v_options_1418_);
    crate::leanh::lean_inc_ref(v_lctx_1417_);
    v___x_1419_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1419_, 0, v_env_1414_);
    crate::leanh::lean_ctor_set(v___x_1419_, 1, v_mctx_1416_);
    crate::leanh::lean_ctor_set(v___x_1419_, 2, v_lctx_1417_);
    crate::leanh::lean_ctor_set(v___x_1419_, 3, v_options_1418_);
    v___x_1420_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1420_, 0, v___x_1419_);
    crate::leanh::lean_ctor_set(v___x_1420_, 1, v_msgData_1407_);
    v___x_1421_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1421_, 0, v___x_1420_);
    return v___x_1421_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0___boxed(
    mut v_msgData_1422_: *mut crate::leanh::LeanObject,
    mut v___y_1423_: *mut crate::leanh::LeanObject,
    mut v___y_1424_: *mut crate::leanh::LeanObject,
    mut v___y_1425_: *mut crate::leanh::LeanObject,
    mut v___y_1426_: *mut crate::leanh::LeanObject,
    mut v___y_1427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1428_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(v_msgData_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
    crate::leanh::lean_dec(v___y_1426_);
    crate::leanh::lean_dec_ref(v___y_1425_);
    crate::leanh::lean_dec(v___y_1424_);
    crate::leanh::lean_dec_ref(v___y_1423_);
    return v_res_1428_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0()
-> f64 {
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: f64 = 0.0;
    v___x_1429_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1430_ = lean_float_of_nat(v___x_1429_);
    return v___x_1430_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(
    mut v_cls_1434_: *mut crate::leanh::LeanObject,
    mut v_msg_1435_: *mut crate::leanh::LeanObject,
    mut v___y_1436_: *mut crate::leanh::LeanObject,
    mut v___y_1437_: *mut crate::leanh::LeanObject,
    mut v___y_1438_: *mut crate::leanh::LeanObject,
    mut v___y_1439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1446_: u8 = 0;
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1459_: u8 = 0;
    let mut v_tid_1460_: u64 = 0;
    let mut v_traces_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1464_: u8 = 0;
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: f64 = 0.0;
    let mut v___x_1467_: u8 = 0;
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1485_: u8 = 0;
    let mut v_isSharedCheck_1486_: u8 = 0;
    let mut v_isSharedCheck_1487_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1441_ = crate::leanh::lean_ctor_get(v___y_1438_, 5);
                v___x_1442_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(v_msg_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
                v_a_1443_ = crate::leanh::lean_ctor_get(v___x_1442_, 0);
                v_isSharedCheck_1487_ = (!crate::leanh::lean_is_exclusive(v___x_1442_)) as u8;
                if v_isSharedCheck_1487_ == 0 {
                    v___x_1445_ = v___x_1442_;
                    v_isShared_1446_ = v_isSharedCheck_1487_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1443_);
                    crate::leanh::lean_dec(v___x_1442_);
                    v___x_1445_ = crate::leanh::lean_box(0);
                    v_isShared_1446_ = v_isSharedCheck_1487_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1447_ = lean_st_ref_take(v___y_1439_);
                v_traceState_1448_ = crate::leanh::lean_ctor_get(v___x_1447_, 4);
                v_env_1449_ = crate::leanh::lean_ctor_get(v___x_1447_, 0);
                v_nextMacroScope_1450_ = crate::leanh::lean_ctor_get(v___x_1447_, 1);
                v_ngen_1451_ = crate::leanh::lean_ctor_get(v___x_1447_, 2);
                v_auxDeclNGen_1452_ = crate::leanh::lean_ctor_get(v___x_1447_, 3);
                v_cache_1453_ = crate::leanh::lean_ctor_get(v___x_1447_, 5);
                v_messages_1454_ = crate::leanh::lean_ctor_get(v___x_1447_, 6);
                v_infoState_1455_ = crate::leanh::lean_ctor_get(v___x_1447_, 7);
                v_snapshotTasks_1456_ = crate::leanh::lean_ctor_get(v___x_1447_, 8);
                v_isSharedCheck_1486_ = (!crate::leanh::lean_is_exclusive(v___x_1447_)) as u8;
                if v_isSharedCheck_1486_ == 0 {
                    v___x_1458_ = v___x_1447_;
                    v_isShared_1459_ = v_isSharedCheck_1486_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1456_);
                    crate::leanh::lean_inc(v_infoState_1455_);
                    crate::leanh::lean_inc(v_messages_1454_);
                    crate::leanh::lean_inc(v_cache_1453_);
                    crate::leanh::lean_inc(v_traceState_1448_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1452_);
                    crate::leanh::lean_inc(v_ngen_1451_);
                    crate::leanh::lean_inc(v_nextMacroScope_1450_);
                    crate::leanh::lean_inc(v_env_1449_);
                    crate::leanh::lean_dec(v___x_1447_);
                    v___x_1458_ = crate::leanh::lean_box(0);
                    v_isShared_1459_ = v_isSharedCheck_1486_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_1460_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_1448_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_1461_ = crate::leanh::lean_ctor_get(v_traceState_1448_, 0);
                v_isSharedCheck_1485_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_1448_)) as u8;
                if v_isSharedCheck_1485_ == 0 {
                    v___x_1463_ = v_traceState_1448_;
                    v_isShared_1464_ = v_isSharedCheck_1485_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_1461_);
                    crate::leanh::lean_dec(v_traceState_1448_);
                    v___x_1463_ = crate::leanh::lean_box(0);
                    v_isShared_1464_ = v_isSharedCheck_1485_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1465_ = crate::leanh::lean_box(0);
                v___x_1466_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0);
                v___x_1467_ = 0;
                v___x_1468_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1;
                v___x_1469_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_1469_, 0, v_cls_1434_);
                crate::leanh::lean_ctor_set(v___x_1469_, 1, v___x_1465_);
                crate::leanh::lean_ctor_set(v___x_1469_, 2, v___x_1468_);
                crate::leanh::lean_ctor_set_float(
                    v___x_1469_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_1466_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_1469_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_1466_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1469_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_1467_,
                );
                v___x_1470_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__2;
                v___x_1471_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1471_, 0, v___x_1469_);
                crate::leanh::lean_ctor_set(v___x_1471_, 1, v_a_1443_);
                crate::leanh::lean_ctor_set(v___x_1471_, 2, v___x_1470_);
                crate::leanh::lean_inc(v_ref_1441_);
                v___x_1472_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1472_, 0, v_ref_1441_);
                crate::leanh::lean_ctor_set(v___x_1472_, 1, v___x_1471_);
                v___x_1473_ = l_Lean_PersistentArray_push___redArg(v_traces_1461_, v___x_1472_);
                if v_isShared_1464_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1463_, 0, v___x_1473_);
                    v___x_1475_ = v___x_1463_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1484_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1473_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_1484_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_1460_,
                    );
                    v___x_1475_ = v_reuseFailAlloc_1484_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1459_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1458_, 4, v___x_1475_);
                    v___x_1477_ = v___x_1458_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1483_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_env_1449_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_nextMacroScope_1450_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 2, v_ngen_1451_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 3, v_auxDeclNGen_1452_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 4, v___x_1475_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 5, v_cache_1453_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 6, v_messages_1454_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 7, v_infoState_1455_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 8, v_snapshotTasks_1456_);
                    v___x_1477_ = v_reuseFailAlloc_1483_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1478_ = lean_st_ref_set(v___y_1439_, v___x_1477_);
                v___x_1479_ = crate::leanh::lean_box(0);
                if v_isShared_1446_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1445_, 0, v___x_1479_);
                    v___x_1481_ = v___x_1445_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1482_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1479_);
                    v___x_1481_ = v_reuseFailAlloc_1482_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1481_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___boxed(
    mut v_cls_1488_: *mut crate::leanh::LeanObject,
    mut v_msg_1489_: *mut crate::leanh::LeanObject,
    mut v___y_1490_: *mut crate::leanh::LeanObject,
    mut v___y_1491_: *mut crate::leanh::LeanObject,
    mut v___y_1492_: *mut crate::leanh::LeanObject,
    mut v___y_1493_: *mut crate::leanh::LeanObject,
    mut v___y_1494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1495_ =
        l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(
            v_cls_1488_,
            v_msg_1489_,
            v___y_1490_,
            v___y_1491_,
            v___y_1492_,
            v___y_1493_,
        );
    crate::leanh::lean_dec(v___y_1493_);
    crate::leanh::lean_dec_ref(v___y_1492_);
    crate::leanh::lean_dec(v___y_1491_);
    crate::leanh::lean_dec_ref(v___y_1490_);
    return v_res_1495_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v_cls_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cls_1508_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4;
    v___x_1509_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
    v___x_1510_ = l_Lean_Name_append(v___x_1509_, v_cls_1508_);
    return v___x_1510_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1512_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8;
    v___x_1513_ = l_Lean_stringToMessageData(v___x_1512_);
    return v___x_1513_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(
    mut v_a_1514_: *mut crate::leanh::LeanObject,
    mut v_x_1515_: *mut crate::leanh::LeanObject,
    mut v_c_u2081_1516_: *mut crate::leanh::LeanObject,
    mut v_b_1517_: *mut crate::leanh::LeanObject,
    mut v_c_u2082_1518_: *mut crate::leanh::LeanObject,
    mut v_a_1519_: *mut crate::leanh::LeanObject,
    mut v_a_1520_: *mut crate::leanh::LeanObject,
    mut v_a_1521_: *mut crate::leanh::LeanObject,
    mut v_a_1522_: *mut crate::leanh::LeanObject,
    mut v_a_1523_: *mut crate::leanh::LeanObject,
    mut v_a_1524_: *mut crate::leanh::LeanObject,
    mut v_a_1525_: *mut crate::leanh::LeanObject,
    mut v_a_1526_: *mut crate::leanh::LeanObject,
    mut v_a_1527_: *mut crate::leanh::LeanObject,
    mut v_a_1528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1535_: u8 = 0;
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: u8 = 0;
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1566_: u8 = 0;
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1570_: u8 = 0;
    let mut v_a_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1574_: u8 = 0;
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1578_: u8 = 0;
    let mut v_a_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1582_: u8 = 0;
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1586_: u8 = 0;
    let mut v_a_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1590_: u8 = 0;
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1594_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_1530_ = crate::leanh::lean_ctor_get(v_a_1527_, 2);
                v_p_1531_ = crate::leanh::lean_ctor_get(v_c_u2081_1516_, 0);
                v_d_1532_ = crate::leanh::lean_ctor_get(v_c_u2082_1518_, 0);
                v_p_1533_ = crate::leanh::lean_ctor_get(v_c_u2082_1518_, 1);
                v_inheritedTraceOptions_1534_ = crate::leanh::lean_ctor_get(v_a_1527_, 13);
                v_hasTrace_1535_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_1530_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v___x_1536_ = lean_int_mul(v_a_1514_, v_d_1532_);
                v___x_1537_ = lean_nat_abs(v___x_1536_);
                crate::leanh::lean_dec(v___x_1536_);
                v_d_1538_ = lean_nat_to_int(v___x_1537_);
                crate::leanh::lean_inc_ref(v_p_1533_);
                v___x_1539_ = l_Int_Linear_Poly_mul(v_p_1533_, v_a_1514_);
                v___x_1540_ = lean_int_neg(v_b_1517_);
                crate::leanh::lean_inc_ref(v_p_1531_);
                v___x_1541_ = l_Int_Linear_Poly_mul(v_p_1531_, v___x_1540_);
                crate::leanh::lean_dec(v___x_1540_);
                v_p_1542_ = l_Int_Linear_Poly_combine(v___x_1539_, v___x_1541_);
                if v_hasTrace_1535_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v_cls_1547_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4;
                    v___x_1548_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7,
                    );
                    v___x_1549_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_1534_,
                        v_options_1530_,
                        v___x_1548_,
                    );
                    if v___x_1549_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_1550_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(
                            v_x_1515_, v_a_1519_, v_a_1527_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1550_) == 0 {
                            v_a_1551_ = crate::leanh::lean_ctor_get(v___x_1550_, 0);
                            crate::leanh::lean_inc(v_a_1551_);
                            crate::leanh::lean_dec_ref_known(v___x_1550_, 1);
                            crate::leanh::lean_inc_ref(v_c_u2081_1516_);
                            v___x_1552_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(
                                v_c_u2081_1516_,
                                v_a_1519_,
                                v_a_1527_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1552_) == 0 {
                                v_a_1553_ = crate::leanh::lean_ctor_get(v___x_1552_, 0);
                                crate::leanh::lean_inc(v_a_1553_);
                                crate::leanh::lean_dec_ref_known(v___x_1552_, 1);
                                crate::leanh::lean_inc_ref(v_c_u2082_1518_);
                                v___x_1554_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(
                                    v_c_u2082_1518_,
                                    v_a_1519_,
                                    v_a_1527_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1554_) == 0 {
                                    v_a_1555_ = crate::leanh::lean_ctor_get(v___x_1554_, 0);
                                    crate::leanh::lean_inc(v_a_1555_);
                                    crate::leanh::lean_dec_ref_known(v___x_1554_, 1);
                                    v___x_1556_ = l_Lean_MessageData_ofExpr(v_a_1551_);
                                    v___x_1557_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9);
                                    v___x_1558_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_1558_, 0, v___x_1556_);
                                    crate::leanh::lean_ctor_set(v___x_1558_, 1, v___x_1557_);
                                    v___x_1559_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_1559_, 0, v___x_1558_);
                                    crate::leanh::lean_ctor_set(v___x_1559_, 1, v_a_1553_);
                                    v___x_1560_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_1560_, 0, v___x_1559_);
                                    crate::leanh::lean_ctor_set(v___x_1560_, 1, v___x_1557_);
                                    v___x_1561_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_1561_, 0, v___x_1560_);
                                    crate::leanh::lean_ctor_set(v___x_1561_, 1, v_a_1555_);
                                    v___x_1562_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_1547_, v___x_1561_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_);
                                    if crate::leanh::lean_obj_tag(v___x_1562_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_1562_, 1);
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec_ref(v_p_1542_);
                                        crate::leanh::lean_dec(v_d_1538_);
                                        crate::leanh::lean_dec_ref(v_c_u2082_1518_);
                                        crate::leanh::lean_dec_ref(v_c_u2081_1516_);
                                        crate::leanh::lean_dec(v_x_1515_);
                                        v_a_1563_ = crate::leanh::lean_ctor_get(v___x_1562_, 0);
                                        v_isSharedCheck_1570_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1562_)) as u8;
                                        if v_isSharedCheck_1570_ == 0 {
                                            v___x_1565_ = v___x_1562_;
                                            v_isShared_1566_ = v_isSharedCheck_1570_;
                                            state = 2;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1563_);
                                            crate::leanh::lean_dec(v___x_1562_);
                                            v___x_1565_ = crate::leanh::lean_box(0);
                                            v_isShared_1566_ = v_isSharedCheck_1570_;
                                            state = 2;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_1553_);
                                    crate::leanh::lean_dec(v_a_1551_);
                                    crate::leanh::lean_dec_ref(v_p_1542_);
                                    crate::leanh::lean_dec(v_d_1538_);
                                    crate::leanh::lean_dec_ref(v_c_u2082_1518_);
                                    crate::leanh::lean_dec_ref(v_c_u2081_1516_);
                                    crate::leanh::lean_dec(v_x_1515_);
                                    v_a_1571_ = crate::leanh::lean_ctor_get(v___x_1554_, 0);
                                    v_isSharedCheck_1578_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1554_)) as u8;
                                    if v_isSharedCheck_1578_ == 0 {
                                        v___x_1573_ = v___x_1554_;
                                        v_isShared_1574_ = v_isSharedCheck_1578_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1571_);
                                        crate::leanh::lean_dec(v___x_1554_);
                                        v___x_1573_ = crate::leanh::lean_box(0);
                                        v_isShared_1574_ = v_isSharedCheck_1578_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_1551_);
                                crate::leanh::lean_dec_ref(v_p_1542_);
                                crate::leanh::lean_dec(v_d_1538_);
                                crate::leanh::lean_dec_ref(v_c_u2082_1518_);
                                crate::leanh::lean_dec_ref(v_c_u2081_1516_);
                                crate::leanh::lean_dec(v_x_1515_);
                                v_a_1579_ = crate::leanh::lean_ctor_get(v___x_1552_, 0);
                                v_isSharedCheck_1586_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1552_)) as u8;
                                if v_isSharedCheck_1586_ == 0 {
                                    v___x_1581_ = v___x_1552_;
                                    v_isShared_1582_ = v_isSharedCheck_1586_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1579_);
                                    crate::leanh::lean_dec(v___x_1552_);
                                    v___x_1581_ = crate::leanh::lean_box(0);
                                    v_isShared_1582_ = v_isSharedCheck_1586_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_p_1542_);
                            crate::leanh::lean_dec(v_d_1538_);
                            crate::leanh::lean_dec_ref(v_c_u2082_1518_);
                            crate::leanh::lean_dec_ref(v_c_u2081_1516_);
                            crate::leanh::lean_dec(v_x_1515_);
                            v_a_1587_ = crate::leanh::lean_ctor_get(v___x_1550_, 0);
                            v_isSharedCheck_1594_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1550_)) as u8;
                            if v_isSharedCheck_1594_ == 0 {
                                v___x_1589_ = v___x_1550_;
                                v_isShared_1590_ = v_isSharedCheck_1594_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1587_);
                                crate::leanh::lean_dec(v___x_1550_);
                                v___x_1589_ = crate::leanh::lean_box(0);
                                v_isShared_1590_ = v_isSharedCheck_1594_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1544_ = crate::leanh::lean_alloc_ctor(8, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1544_, 0, v_x_1515_);
                crate::leanh::lean_ctor_set(v___x_1544_, 1, v_c_u2081_1516_);
                crate::leanh::lean_ctor_set(v___x_1544_, 2, v_c_u2082_1518_);
                v___x_1545_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1545_, 0, v_d_1538_);
                crate::leanh::lean_ctor_set(v___x_1545_, 1, v_p_1542_);
                crate::leanh::lean_ctor_set(v___x_1545_, 2, v___x_1544_);
                v___x_1546_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1546_, 0, v___x_1545_);
                return v___x_1546_;
            }
            2 => {
                if v_isShared_1566_ == 0 {
                    v___x_1568_ = v___x_1565_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1569_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
                    v___x_1568_ = v_reuseFailAlloc_1569_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1568_;
            }
            4 => {
                if v_isShared_1574_ == 0 {
                    v___x_1576_ = v___x_1573_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1577_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
                    v___x_1576_ = v_reuseFailAlloc_1577_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1576_;
            }
            6 => {
                if v_isShared_1582_ == 0 {
                    v___x_1584_ = v___x_1581_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1585_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
                    v___x_1584_ = v_reuseFailAlloc_1585_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1584_;
            }
            8 => {
                if v_isShared_1590_ == 0 {
                    v___x_1592_ = v___x_1589_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1593_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
                    v___x_1592_ = v_reuseFailAlloc_1593_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1592_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(
    mut v_a_1595_: *mut crate::leanh::LeanObject,
    mut v_x_1596_: *mut crate::leanh::LeanObject,
    mut v_c_u2081_1597_: *mut crate::leanh::LeanObject,
    mut v_b_1598_: *mut crate::leanh::LeanObject,
    mut v_c_u2082_1599_: *mut crate::leanh::LeanObject,
    mut v_a_1600_: *mut crate::leanh::LeanObject,
    mut v_a_1601_: *mut crate::leanh::LeanObject,
    mut v_a_1602_: *mut crate::leanh::LeanObject,
    mut v_a_1603_: *mut crate::leanh::LeanObject,
    mut v_a_1604_: *mut crate::leanh::LeanObject,
    mut v_a_1605_: *mut crate::leanh::LeanObject,
    mut v_a_1606_: *mut crate::leanh::LeanObject,
    mut v_a_1607_: *mut crate::leanh::LeanObject,
    mut v_a_1608_: *mut crate::leanh::LeanObject,
    mut v_a_1609_: *mut crate::leanh::LeanObject,
    mut v_a_1610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1611_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(
        v_a_1595_,
        v_x_1596_,
        v_c_u2081_1597_,
        v_b_1598_,
        v_c_u2082_1599_,
        v_a_1600_,
        v_a_1601_,
        v_a_1602_,
        v_a_1603_,
        v_a_1604_,
        v_a_1605_,
        v_a_1606_,
        v_a_1607_,
        v_a_1608_,
        v_a_1609_,
    );
    crate::leanh::lean_dec(v_a_1609_);
    crate::leanh::lean_dec_ref(v_a_1608_);
    crate::leanh::lean_dec(v_a_1607_);
    crate::leanh::lean_dec_ref(v_a_1606_);
    crate::leanh::lean_dec(v_a_1605_);
    crate::leanh::lean_dec_ref(v_a_1604_);
    crate::leanh::lean_dec(v_a_1603_);
    crate::leanh::lean_dec_ref(v_a_1602_);
    crate::leanh::lean_dec(v_a_1601_);
    crate::leanh::lean_dec(v_a_1600_);
    crate::leanh::lean_dec(v_b_1598_);
    crate::leanh::lean_dec(v_a_1595_);
    return v_res_1611_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(
    mut v_cls_1612_: *mut crate::leanh::LeanObject,
    mut v_msg_1613_: *mut crate::leanh::LeanObject,
    mut v___y_1614_: *mut crate::leanh::LeanObject,
    mut v___y_1615_: *mut crate::leanh::LeanObject,
    mut v___y_1616_: *mut crate::leanh::LeanObject,
    mut v___y_1617_: *mut crate::leanh::LeanObject,
    mut v___y_1618_: *mut crate::leanh::LeanObject,
    mut v___y_1619_: *mut crate::leanh::LeanObject,
    mut v___y_1620_: *mut crate::leanh::LeanObject,
    mut v___y_1621_: *mut crate::leanh::LeanObject,
    mut v___y_1622_: *mut crate::leanh::LeanObject,
    mut v___y_1623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1625_ =
        l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(
            v_cls_1612_,
            v_msg_1613_,
            v___y_1620_,
            v___y_1621_,
            v___y_1622_,
            v___y_1623_,
        );
    return v___x_1625_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___boxed(
    mut v_cls_1626_: *mut crate::leanh::LeanObject,
    mut v_msg_1627_: *mut crate::leanh::LeanObject,
    mut v___y_1628_: *mut crate::leanh::LeanObject,
    mut v___y_1629_: *mut crate::leanh::LeanObject,
    mut v___y_1630_: *mut crate::leanh::LeanObject,
    mut v___y_1631_: *mut crate::leanh::LeanObject,
    mut v___y_1632_: *mut crate::leanh::LeanObject,
    mut v___y_1633_: *mut crate::leanh::LeanObject,
    mut v___y_1634_: *mut crate::leanh::LeanObject,
    mut v___y_1635_: *mut crate::leanh::LeanObject,
    mut v___y_1636_: *mut crate::leanh::LeanObject,
    mut v___y_1637_: *mut crate::leanh::LeanObject,
    mut v___y_1638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1639_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(
        v_cls_1626_,
        v_msg_1627_,
        v___y_1628_,
        v___y_1629_,
        v___y_1630_,
        v___y_1631_,
        v___y_1632_,
        v___y_1633_,
        v___y_1634_,
        v___y_1635_,
        v___y_1636_,
        v___y_1637_,
    );
    crate::leanh::lean_dec(v___y_1637_);
    crate::leanh::lean_dec_ref(v___y_1636_);
    crate::leanh::lean_dec(v___y_1635_);
    crate::leanh::lean_dec_ref(v___y_1634_);
    crate::leanh::lean_dec(v___y_1633_);
    crate::leanh::lean_dec_ref(v___y_1632_);
    crate::leanh::lean_dec(v___y_1631_);
    crate::leanh::lean_dec_ref(v___y_1630_);
    crate::leanh::lean_dec(v___y_1629_);
    crate::leanh::lean_dec(v___y_1628_);
    return v_res_1639_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1645_ = l_Lean_maxRecDepthErrorMessage;
    v___x_1646_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1646_, 0, v___x_1645_);
    return v___x_1646_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1647_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3);
    v___x_1648_ = l_Lean_MessageData_ofFormat(v___x_1647_);
    return v___x_1648_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1649_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4);
    v___x_1650_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2;
    v___x_1651_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1651_, 0, v___x_1650_);
    crate::leanh::lean_ctor_set(v___x_1651_, 1, v___x_1649_);
    return v___x_1651_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(
    mut v_ref_1652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1654_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5);
    v___x_1655_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1655_, 0, v_ref_1652_);
    crate::leanh::lean_ctor_set(v___x_1655_, 1, v___x_1654_);
    v___x_1656_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1656_, 0, v___x_1655_);
    return v___x_1656_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___boxed(
    mut v_ref_1657_: *mut crate::leanh::LeanObject,
    mut v___y_1658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1659_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_1657_);
    return v_res_1659_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(
    mut v_00_u03b1_1660_: *mut crate::leanh::LeanObject,
    mut v_ref_1661_: *mut crate::leanh::LeanObject,
    mut v___y_1662_: *mut crate::leanh::LeanObject,
    mut v___y_1663_: *mut crate::leanh::LeanObject,
    mut v___y_1664_: *mut crate::leanh::LeanObject,
    mut v___y_1665_: *mut crate::leanh::LeanObject,
    mut v___y_1666_: *mut crate::leanh::LeanObject,
    mut v___y_1667_: *mut crate::leanh::LeanObject,
    mut v___y_1668_: *mut crate::leanh::LeanObject,
    mut v___y_1669_: *mut crate::leanh::LeanObject,
    mut v___y_1670_: *mut crate::leanh::LeanObject,
    mut v___y_1671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1673_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_1661_);
    return v___x_1673_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___boxed(
    mut v_00_u03b1_1674_: *mut crate::leanh::LeanObject,
    mut v_ref_1675_: *mut crate::leanh::LeanObject,
    mut v___y_1676_: *mut crate::leanh::LeanObject,
    mut v___y_1677_: *mut crate::leanh::LeanObject,
    mut v___y_1678_: *mut crate::leanh::LeanObject,
    mut v___y_1679_: *mut crate::leanh::LeanObject,
    mut v___y_1680_: *mut crate::leanh::LeanObject,
    mut v___y_1681_: *mut crate::leanh::LeanObject,
    mut v___y_1682_: *mut crate::leanh::LeanObject,
    mut v___y_1683_: *mut crate::leanh::LeanObject,
    mut v___y_1684_: *mut crate::leanh::LeanObject,
    mut v___y_1685_: *mut crate::leanh::LeanObject,
    mut v___y_1686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1687_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(v_00_u03b1_1674_, v_ref_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_);
    crate::leanh::lean_dec(v___y_1685_);
    crate::leanh::lean_dec_ref(v___y_1684_);
    crate::leanh::lean_dec(v___y_1683_);
    crate::leanh::lean_dec_ref(v___y_1682_);
    crate::leanh::lean_dec(v___y_1681_);
    crate::leanh::lean_dec_ref(v___y_1680_);
    crate::leanh::lean_dec(v___y_1679_);
    crate::leanh::lean_dec_ref(v___y_1678_);
    crate::leanh::lean_dec(v___y_1677_);
    crate::leanh::lean_dec(v___y_1676_);
    return v_res_1687_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(
    mut v_c_1688_: *mut crate::leanh::LeanObject,
    mut v_a_1689_: *mut crate::leanh::LeanObject,
    mut v_a_1690_: *mut crate::leanh::LeanObject,
    mut v_a_1691_: *mut crate::leanh::LeanObject,
    mut v_a_1692_: *mut crate::leanh::LeanObject,
    mut v_a_1693_: *mut crate::leanh::LeanObject,
    mut v_a_1694_: *mut crate::leanh::LeanObject,
    mut v_a_1695_: *mut crate::leanh::LeanObject,
    mut v_a_1696_: *mut crate::leanh::LeanObject,
    mut v_a_1697_: *mut crate::leanh::LeanObject,
    mut v_a_1698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_p_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1713_: u8 = 0;
    let mut v_cancelTk_x3f_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1715_: u8 = 0;
    let mut v_inheritedTraceOptions_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1725_: u8 = 0;
    let mut v_val_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1739_: u8 = 0;
    let mut v_a_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1743_: u8 = 0;
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1747_: u8 = 0;
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: u8 = 0;
    let mut v___x_1750_: u8 = 0;
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_p_1700_ = crate::leanh::lean_ctor_get(v_c_1688_, 1);
                v_fileName_1701_ = crate::leanh::lean_ctor_get(v_a_1697_, 0);
                crate::leanh::lean_inc_ref(v_fileName_1701_);
                v_fileMap_1702_ = crate::leanh::lean_ctor_get(v_a_1697_, 1);
                crate::leanh::lean_inc_ref(v_fileMap_1702_);
                v_options_1703_ = crate::leanh::lean_ctor_get(v_a_1697_, 2);
                crate::leanh::lean_inc_ref(v_options_1703_);
                v_currRecDepth_1704_ = crate::leanh::lean_ctor_get(v_a_1697_, 3);
                crate::leanh::lean_inc(v_currRecDepth_1704_);
                v_maxRecDepth_1705_ = crate::leanh::lean_ctor_get(v_a_1697_, 4);
                crate::leanh::lean_inc(v_maxRecDepth_1705_);
                v_ref_1706_ = crate::leanh::lean_ctor_get(v_a_1697_, 5);
                crate::leanh::lean_inc(v_ref_1706_);
                v_currNamespace_1707_ = crate::leanh::lean_ctor_get(v_a_1697_, 6);
                crate::leanh::lean_inc(v_currNamespace_1707_);
                v_openDecls_1708_ = crate::leanh::lean_ctor_get(v_a_1697_, 7);
                crate::leanh::lean_inc(v_openDecls_1708_);
                v_initHeartbeats_1709_ = crate::leanh::lean_ctor_get(v_a_1697_, 8);
                crate::leanh::lean_inc(v_initHeartbeats_1709_);
                v_maxHeartbeats_1710_ = crate::leanh::lean_ctor_get(v_a_1697_, 9);
                crate::leanh::lean_inc(v_maxHeartbeats_1710_);
                v_quotContext_1711_ = crate::leanh::lean_ctor_get(v_a_1697_, 10);
                crate::leanh::lean_inc(v_quotContext_1711_);
                v_currMacroScope_1712_ = crate::leanh::lean_ctor_get(v_a_1697_, 11);
                crate::leanh::lean_inc(v_currMacroScope_1712_);
                v_diag_1713_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1697_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_1714_ = crate::leanh::lean_ctor_get(v_a_1697_, 12);
                crate::leanh::lean_inc(v_cancelTk_x3f_1714_);
                v_suppressElabErrors_1715_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1697_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_1716_ = crate::leanh::lean_ctor_get(v_a_1697_, 13);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_1716_);
                crate::leanh::lean_dec_ref(v_a_1697_);
                v___x_1748_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1749_ = lean_nat_dec_eq(v_maxRecDepth_1705_, v___x_1748_);
                if v___x_1749_ == 0 {
                    v___x_1750_ = lean_nat_dec_eq(v_currRecDepth_1704_, v_maxRecDepth_1705_);
                    if v___x_1750_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_inheritedTraceOptions_1716_);
                        crate::leanh::lean_dec(v_cancelTk_x3f_1714_);
                        crate::leanh::lean_dec(v_currMacroScope_1712_);
                        crate::leanh::lean_dec(v_quotContext_1711_);
                        crate::leanh::lean_dec(v_maxHeartbeats_1710_);
                        crate::leanh::lean_dec(v_initHeartbeats_1709_);
                        crate::leanh::lean_dec(v_openDecls_1708_);
                        crate::leanh::lean_dec(v_currNamespace_1707_);
                        crate::leanh::lean_dec(v_maxRecDepth_1705_);
                        crate::leanh::lean_dec(v_currRecDepth_1704_);
                        crate::leanh::lean_dec_ref(v_options_1703_);
                        crate::leanh::lean_dec_ref(v_fileMap_1702_);
                        crate::leanh::lean_dec_ref(v_fileName_1701_);
                        crate::leanh::lean_dec_ref(v_c_1688_);
                        v___x_1751_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_1706_);
                        return v___x_1751_;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1718_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1719_ = lean_nat_add(v_currRecDepth_1704_, v___x_1718_);
                crate::leanh::lean_dec(v_currRecDepth_1704_);
                v___x_1720_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_1720_, 0, v_fileName_1701_);
                crate::leanh::lean_ctor_set(v___x_1720_, 1, v_fileMap_1702_);
                crate::leanh::lean_ctor_set(v___x_1720_, 2, v_options_1703_);
                crate::leanh::lean_ctor_set(v___x_1720_, 3, v___x_1719_);
                crate::leanh::lean_ctor_set(v___x_1720_, 4, v_maxRecDepth_1705_);
                crate::leanh::lean_ctor_set(v___x_1720_, 5, v_ref_1706_);
                crate::leanh::lean_ctor_set(v___x_1720_, 6, v_currNamespace_1707_);
                crate::leanh::lean_ctor_set(v___x_1720_, 7, v_openDecls_1708_);
                crate::leanh::lean_ctor_set(v___x_1720_, 8, v_initHeartbeats_1709_);
                crate::leanh::lean_ctor_set(v___x_1720_, 9, v_maxHeartbeats_1710_);
                crate::leanh::lean_ctor_set(v___x_1720_, 10, v_quotContext_1711_);
                crate::leanh::lean_ctor_set(v___x_1720_, 11, v_currMacroScope_1712_);
                crate::leanh::lean_ctor_set(v___x_1720_, 12, v_cancelTk_x3f_1714_);
                crate::leanh::lean_ctor_set(v___x_1720_, 13, v_inheritedTraceOptions_1716_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1720_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_1713_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1720_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_1715_,
                );
                crate::leanh::lean_inc_ref(v_p_1700_);
                v___x_1721_ =
                    l_Int_Linear_Poly_findVarToSubst___redArg(v_p_1700_, v_a_1689_, v___x_1720_);
                if crate::leanh::lean_obj_tag(v___x_1721_) == 0 {
                    v_a_1722_ = crate::leanh::lean_ctor_get(v___x_1721_, 0);
                    v_isSharedCheck_1739_ = (!crate::leanh::lean_is_exclusive(v___x_1721_)) as u8;
                    if v_isSharedCheck_1739_ == 0 {
                        v___x_1724_ = v___x_1721_;
                        v_isShared_1725_ = v_isSharedCheck_1739_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1722_);
                        crate::leanh::lean_dec(v___x_1721_);
                        v___x_1724_ = crate::leanh::lean_box(0);
                        v_isShared_1725_ = v_isSharedCheck_1739_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_1720_, 14);
                    crate::leanh::lean_dec_ref(v_c_1688_);
                    v_a_1740_ = crate::leanh::lean_ctor_get(v___x_1721_, 0);
                    v_isSharedCheck_1747_ = (!crate::leanh::lean_is_exclusive(v___x_1721_)) as u8;
                    if v_isSharedCheck_1747_ == 0 {
                        v___x_1742_ = v___x_1721_;
                        v_isShared_1743_ = v_isSharedCheck_1747_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1740_);
                        crate::leanh::lean_dec(v___x_1721_);
                        v___x_1742_ = crate::leanh::lean_box(0);
                        v_isShared_1743_ = v_isSharedCheck_1747_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_1722_) == 1 {
                    crate::leanh::lean_del_object(v___x_1724_);
                    v_val_1726_ = crate::leanh::lean_ctor_get(v_a_1722_, 0);
                    crate::leanh::lean_inc(v_val_1726_);
                    crate::leanh::lean_dec_ref_known(v_a_1722_, 1);
                    v_snd_1727_ = crate::leanh::lean_ctor_get(v_val_1726_, 1);
                    crate::leanh::lean_inc(v_snd_1727_);
                    v_snd_1728_ = crate::leanh::lean_ctor_get(v_snd_1727_, 1);
                    crate::leanh::lean_inc(v_snd_1728_);
                    v_fst_1729_ = crate::leanh::lean_ctor_get(v_val_1726_, 0);
                    crate::leanh::lean_inc(v_fst_1729_);
                    crate::leanh::lean_dec(v_val_1726_);
                    v_fst_1730_ = crate::leanh::lean_ctor_get(v_snd_1727_, 0);
                    crate::leanh::lean_inc(v_fst_1730_);
                    crate::leanh::lean_dec(v_snd_1727_);
                    v_p_1731_ = crate::leanh::lean_ctor_get(v_snd_1728_, 0);
                    v___x_1732_ = l_Int_Linear_Poly_coeff(v_p_1731_, v_fst_1730_);
                    v___x_1733_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(
                        v___x_1732_,
                        v_fst_1730_,
                        v_snd_1728_,
                        v_fst_1729_,
                        v_c_1688_,
                        v_a_1689_,
                        v_a_1690_,
                        v_a_1691_,
                        v_a_1692_,
                        v_a_1693_,
                        v_a_1694_,
                        v_a_1695_,
                        v_a_1696_,
                        v___x_1720_,
                        v_a_1698_,
                    );
                    crate::leanh::lean_dec(v_fst_1729_);
                    crate::leanh::lean_dec(v___x_1732_);
                    if crate::leanh::lean_obj_tag(v___x_1733_) == 0 {
                        v_a_1734_ = crate::leanh::lean_ctor_get(v___x_1733_, 0);
                        crate::leanh::lean_inc(v_a_1734_);
                        crate::leanh::lean_dec_ref_known(v___x_1733_, 1);
                        v_c_1688_ = v_a_1734_;
                        v_a_1697_ = v___x_1720_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_1720_, 14);
                        return v___x_1733_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1722_);
                    crate::leanh::lean_dec_ref_known(v___x_1720_, 14);
                    if v_isShared_1725_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1724_, 0, v_c_1688_);
                        v___x_1737_ = v___x_1724_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1738_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_c_1688_);
                        v___x_1737_ = v_reuseFailAlloc_1738_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1737_;
            }
            4 => {
                if v_isShared_1743_ == 0 {
                    v___x_1745_ = v___x_1742_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1746_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
                    v___x_1745_ = v_reuseFailAlloc_1746_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1745_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(
    mut v_c_1752_: *mut crate::leanh::LeanObject,
    mut v_a_1753_: *mut crate::leanh::LeanObject,
    mut v_a_1754_: *mut crate::leanh::LeanObject,
    mut v_a_1755_: *mut crate::leanh::LeanObject,
    mut v_a_1756_: *mut crate::leanh::LeanObject,
    mut v_a_1757_: *mut crate::leanh::LeanObject,
    mut v_a_1758_: *mut crate::leanh::LeanObject,
    mut v_a_1759_: *mut crate::leanh::LeanObject,
    mut v_a_1760_: *mut crate::leanh::LeanObject,
    mut v_a_1761_: *mut crate::leanh::LeanObject,
    mut v_a_1762_: *mut crate::leanh::LeanObject,
    mut v_a_1763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1764_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(
        v_c_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_,
        v_a_1760_, v_a_1761_, v_a_1762_,
    );
    crate::leanh::lean_dec(v_a_1762_);
    crate::leanh::lean_dec(v_a_1760_);
    crate::leanh::lean_dec_ref(v_a_1759_);
    crate::leanh::lean_dec(v_a_1758_);
    crate::leanh::lean_dec_ref(v_a_1757_);
    crate::leanh::lean_dec(v_a_1756_);
    crate::leanh::lean_dec_ref(v_a_1755_);
    crate::leanh::lean_dec(v_a_1754_);
    crate::leanh::lean_dec(v_a_1753_);
    return v_res_1764_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(
    mut v_a_1765_: *mut crate::leanh::LeanObject,
    mut v_v_1766_: *mut crate::leanh::LeanObject,
    mut v_s_1767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vars_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_x27_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_x27_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natToIntMap_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natDef_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dvds_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lowers_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uppers_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elimEqs_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elimStack_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_occurs_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignment_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextCnstrId_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_caseSplits_1783_: u8 = 0;
    let mut v_conflict_x3f_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqSplits_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_divMod_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntIds_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntInfos_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntTermMap_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntVarMap_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedCommRing_1791_: u8 = 0;
    let mut v_nonlinearOccs_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1795_: u8 = 0;
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1801_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vars_1768_ = crate::leanh::lean_ctor_get(v_s_1767_, 0);
                v_varMap_1769_ = crate::leanh::lean_ctor_get(v_s_1767_, 1);
                v_vars_x27_1770_ = crate::leanh::lean_ctor_get(v_s_1767_, 2);
                v_varMap_x27_1771_ = crate::leanh::lean_ctor_get(v_s_1767_, 3);
                v_natToIntMap_1772_ = crate::leanh::lean_ctor_get(v_s_1767_, 4);
                v_natDef_1773_ = crate::leanh::lean_ctor_get(v_s_1767_, 5);
                v_dvds_1774_ = crate::leanh::lean_ctor_get(v_s_1767_, 6);
                v_lowers_1775_ = crate::leanh::lean_ctor_get(v_s_1767_, 7);
                v_uppers_1776_ = crate::leanh::lean_ctor_get(v_s_1767_, 8);
                v_diseqs_1777_ = crate::leanh::lean_ctor_get(v_s_1767_, 9);
                v_elimEqs_1778_ = crate::leanh::lean_ctor_get(v_s_1767_, 10);
                v_elimStack_1779_ = crate::leanh::lean_ctor_get(v_s_1767_, 11);
                v_occurs_1780_ = crate::leanh::lean_ctor_get(v_s_1767_, 12);
                v_assignment_1781_ = crate::leanh::lean_ctor_get(v_s_1767_, 13);
                v_nextCnstrId_1782_ = crate::leanh::lean_ctor_get(v_s_1767_, 14);
                v_caseSplits_1783_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_1767_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 23) as u32,
                );
                v_conflict_x3f_1784_ = crate::leanh::lean_ctor_get(v_s_1767_, 15);
                v_diseqSplits_1785_ = crate::leanh::lean_ctor_get(v_s_1767_, 16);
                v_divMod_1786_ = crate::leanh::lean_ctor_get(v_s_1767_, 17);
                v_toIntIds_1787_ = crate::leanh::lean_ctor_get(v_s_1767_, 18);
                v_toIntInfos_1788_ = crate::leanh::lean_ctor_get(v_s_1767_, 19);
                v_toIntTermMap_1789_ = crate::leanh::lean_ctor_get(v_s_1767_, 20);
                v_toIntVarMap_1790_ = crate::leanh::lean_ctor_get(v_s_1767_, 21);
                v_usedCommRing_1791_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_1767_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 23 + 1) as u32,
                );
                v_nonlinearOccs_1792_ = crate::leanh::lean_ctor_get(v_s_1767_, 22);
                v_isSharedCheck_1801_ = (!crate::leanh::lean_is_exclusive(v_s_1767_)) as u8;
                if v_isSharedCheck_1801_ == 0 {
                    v___x_1794_ = v_s_1767_;
                    v_isShared_1795_ = v_isSharedCheck_1801_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nonlinearOccs_1792_);
                    crate::leanh::lean_inc(v_toIntVarMap_1790_);
                    crate::leanh::lean_inc(v_toIntTermMap_1789_);
                    crate::leanh::lean_inc(v_toIntInfos_1788_);
                    crate::leanh::lean_inc(v_toIntIds_1787_);
                    crate::leanh::lean_inc(v_divMod_1786_);
                    crate::leanh::lean_inc(v_diseqSplits_1785_);
                    crate::leanh::lean_inc(v_conflict_x3f_1784_);
                    crate::leanh::lean_inc(v_nextCnstrId_1782_);
                    crate::leanh::lean_inc(v_assignment_1781_);
                    crate::leanh::lean_inc(v_occurs_1780_);
                    crate::leanh::lean_inc(v_elimStack_1779_);
                    crate::leanh::lean_inc(v_elimEqs_1778_);
                    crate::leanh::lean_inc(v_diseqs_1777_);
                    crate::leanh::lean_inc(v_uppers_1776_);
                    crate::leanh::lean_inc(v_lowers_1775_);
                    crate::leanh::lean_inc(v_dvds_1774_);
                    crate::leanh::lean_inc(v_natDef_1773_);
                    crate::leanh::lean_inc(v_natToIntMap_1772_);
                    crate::leanh::lean_inc(v_varMap_x27_1771_);
                    crate::leanh::lean_inc(v_vars_x27_1770_);
                    crate::leanh::lean_inc(v_varMap_1769_);
                    crate::leanh::lean_inc(v_vars_1768_);
                    crate::leanh::lean_dec(v_s_1767_);
                    v___x_1794_ = crate::leanh::lean_box(0);
                    v_isShared_1795_ = v_isSharedCheck_1801_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1796_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1796_, 0, v_a_1765_);
                v___x_1797_ =
                    l_Lean_PersistentArray_set___redArg(v_dvds_1774_, v_v_1766_, v___x_1796_);
                if v_isShared_1795_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1794_, 6, v___x_1797_);
                    v___x_1799_ = v___x_1794_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1800_ = crate::leanh::lean_alloc_ctor(0, 23, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_vars_1768_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 1, v_varMap_1769_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 2, v_vars_x27_1770_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 3, v_varMap_x27_1771_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 4, v_natToIntMap_1772_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 5, v_natDef_1773_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 6, v___x_1797_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 7, v_lowers_1775_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 8, v_uppers_1776_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 9, v_diseqs_1777_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 10, v_elimEqs_1778_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 11, v_elimStack_1779_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 12, v_occurs_1780_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 13, v_assignment_1781_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 14, v_nextCnstrId_1782_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 15, v_conflict_x3f_1784_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 16, v_diseqSplits_1785_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 17, v_divMod_1786_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 18, v_toIntIds_1787_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 19, v_toIntInfos_1788_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 20, v_toIntTermMap_1789_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 21, v_toIntVarMap_1790_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 22, v_nonlinearOccs_1792_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1800_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 23) as u32,
                        v_caseSplits_1783_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1800_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 23 + 1) as u32,
                        v_usedCommRing_1791_,
                    );
                    v___x_1799_ = v_reuseFailAlloc_1800_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1799_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(
    mut v_a_1802_: *mut crate::leanh::LeanObject,
    mut v_v_1803_: *mut crate::leanh::LeanObject,
    mut v_s_1804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1805_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(v_a_1802_, v_v_1803_, v_s_1804_);
    crate::leanh::lean_dec(v_v_1803_);
    return v_res_1805_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(
    mut v_v_1806_: *mut crate::leanh::LeanObject,
    mut v_s_1807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vars_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_x27_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_x27_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natToIntMap_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natDef_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dvds_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lowers_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uppers_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elimEqs_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elimStack_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_occurs_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignment_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextCnstrId_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_caseSplits_1823_: u8 = 0;
    let mut v_conflict_x3f_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqSplits_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_divMod_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntIds_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntInfos_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntTermMap_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntVarMap_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedCommRing_1831_: u8 = 0;
    let mut v_nonlinearOccs_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1835_: u8 = 0;
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1841_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vars_1808_ = crate::leanh::lean_ctor_get(v_s_1807_, 0);
                v_varMap_1809_ = crate::leanh::lean_ctor_get(v_s_1807_, 1);
                v_vars_x27_1810_ = crate::leanh::lean_ctor_get(v_s_1807_, 2);
                v_varMap_x27_1811_ = crate::leanh::lean_ctor_get(v_s_1807_, 3);
                v_natToIntMap_1812_ = crate::leanh::lean_ctor_get(v_s_1807_, 4);
                v_natDef_1813_ = crate::leanh::lean_ctor_get(v_s_1807_, 5);
                v_dvds_1814_ = crate::leanh::lean_ctor_get(v_s_1807_, 6);
                v_lowers_1815_ = crate::leanh::lean_ctor_get(v_s_1807_, 7);
                v_uppers_1816_ = crate::leanh::lean_ctor_get(v_s_1807_, 8);
                v_diseqs_1817_ = crate::leanh::lean_ctor_get(v_s_1807_, 9);
                v_elimEqs_1818_ = crate::leanh::lean_ctor_get(v_s_1807_, 10);
                v_elimStack_1819_ = crate::leanh::lean_ctor_get(v_s_1807_, 11);
                v_occurs_1820_ = crate::leanh::lean_ctor_get(v_s_1807_, 12);
                v_assignment_1821_ = crate::leanh::lean_ctor_get(v_s_1807_, 13);
                v_nextCnstrId_1822_ = crate::leanh::lean_ctor_get(v_s_1807_, 14);
                v_caseSplits_1823_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_1807_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 23) as u32,
                );
                v_conflict_x3f_1824_ = crate::leanh::lean_ctor_get(v_s_1807_, 15);
                v_diseqSplits_1825_ = crate::leanh::lean_ctor_get(v_s_1807_, 16);
                v_divMod_1826_ = crate::leanh::lean_ctor_get(v_s_1807_, 17);
                v_toIntIds_1827_ = crate::leanh::lean_ctor_get(v_s_1807_, 18);
                v_toIntInfos_1828_ = crate::leanh::lean_ctor_get(v_s_1807_, 19);
                v_toIntTermMap_1829_ = crate::leanh::lean_ctor_get(v_s_1807_, 20);
                v_toIntVarMap_1830_ = crate::leanh::lean_ctor_get(v_s_1807_, 21);
                v_usedCommRing_1831_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_1807_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 23 + 1) as u32,
                );
                v_nonlinearOccs_1832_ = crate::leanh::lean_ctor_get(v_s_1807_, 22);
                v_isSharedCheck_1841_ = (!crate::leanh::lean_is_exclusive(v_s_1807_)) as u8;
                if v_isSharedCheck_1841_ == 0 {
                    v___x_1834_ = v_s_1807_;
                    v_isShared_1835_ = v_isSharedCheck_1841_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nonlinearOccs_1832_);
                    crate::leanh::lean_inc(v_toIntVarMap_1830_);
                    crate::leanh::lean_inc(v_toIntTermMap_1829_);
                    crate::leanh::lean_inc(v_toIntInfos_1828_);
                    crate::leanh::lean_inc(v_toIntIds_1827_);
                    crate::leanh::lean_inc(v_divMod_1826_);
                    crate::leanh::lean_inc(v_diseqSplits_1825_);
                    crate::leanh::lean_inc(v_conflict_x3f_1824_);
                    crate::leanh::lean_inc(v_nextCnstrId_1822_);
                    crate::leanh::lean_inc(v_assignment_1821_);
                    crate::leanh::lean_inc(v_occurs_1820_);
                    crate::leanh::lean_inc(v_elimStack_1819_);
                    crate::leanh::lean_inc(v_elimEqs_1818_);
                    crate::leanh::lean_inc(v_diseqs_1817_);
                    crate::leanh::lean_inc(v_uppers_1816_);
                    crate::leanh::lean_inc(v_lowers_1815_);
                    crate::leanh::lean_inc(v_dvds_1814_);
                    crate::leanh::lean_inc(v_natDef_1813_);
                    crate::leanh::lean_inc(v_natToIntMap_1812_);
                    crate::leanh::lean_inc(v_varMap_x27_1811_);
                    crate::leanh::lean_inc(v_vars_x27_1810_);
                    crate::leanh::lean_inc(v_varMap_1809_);
                    crate::leanh::lean_inc(v_vars_1808_);
                    crate::leanh::lean_dec(v_s_1807_);
                    v___x_1834_ = crate::leanh::lean_box(0);
                    v_isShared_1835_ = v_isSharedCheck_1841_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1836_ = crate::leanh::lean_box(0);
                v___x_1837_ =
                    l_Lean_PersistentArray_set___redArg(v_dvds_1814_, v_v_1806_, v___x_1836_);
                if v_isShared_1835_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1834_, 6, v___x_1837_);
                    v___x_1839_ = v___x_1834_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1840_ = crate::leanh::lean_alloc_ctor(0, 23, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_vars_1808_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 1, v_varMap_1809_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 2, v_vars_x27_1810_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 3, v_varMap_x27_1811_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 4, v_natToIntMap_1812_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 5, v_natDef_1813_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 6, v___x_1837_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 7, v_lowers_1815_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 8, v_uppers_1816_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 9, v_diseqs_1817_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 10, v_elimEqs_1818_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 11, v_elimStack_1819_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 12, v_occurs_1820_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 13, v_assignment_1821_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 14, v_nextCnstrId_1822_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 15, v_conflict_x3f_1824_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 16, v_diseqSplits_1825_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 17, v_divMod_1826_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 18, v_toIntIds_1827_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 19, v_toIntInfos_1828_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 20, v_toIntTermMap_1829_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 21, v_toIntVarMap_1830_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 22, v_nonlinearOccs_1832_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1840_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 23) as u32,
                        v_caseSplits_1823_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1840_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 23 + 1) as u32,
                        v_usedCommRing_1831_,
                    );
                    v___x_1839_ = v_reuseFailAlloc_1840_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1839_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed(
    mut v_v_1842_: *mut crate::leanh::LeanObject,
    mut v_s_1843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1844_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(v_v_1842_, v_s_1843_);
    crate::leanh::lean_dec(v_v_1842_);
    return v_res_1844_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1853_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4;
    v___x_1854_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
    v___x_1855_ = l_Lean_Name_append(v___x_1854_, v___x_1853_);
    return v___x_1855_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(
    mut v_c_1856_: *mut crate::leanh::LeanObject,
    mut v_a_1857_: *mut crate::leanh::LeanObject,
    mut v_a_1858_: *mut crate::leanh::LeanObject,
    mut v_a_1859_: *mut crate::leanh::LeanObject,
    mut v_a_1860_: *mut crate::leanh::LeanObject,
    mut v_a_1861_: *mut crate::leanh::LeanObject,
    mut v_a_1862_: *mut crate::leanh::LeanObject,
    mut v_a_1863_: *mut crate::leanh::LeanObject,
    mut v_a_1864_: *mut crate::leanh::LeanObject,
    mut v_a_1865_: *mut crate::leanh::LeanObject,
    mut v_a_1866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1912_: u8 = 0;
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1920_: u8 = 0;
    let mut v_fst_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1925_: u8 = 0;
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1948_: u8 = 0;
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1953_: u8 = 0;
    let mut v_unused_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1960_: u8 = 0;
    let mut v_isSharedCheck_1961_: u8 = 0;
    let mut v_isSharedCheck_1962_: u8 = 0;
    let mut v_unused_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1966_: u8 = 0;
    let mut v_inheritedTraceOptions_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: u8 = 0;
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1979_: u8 = 0;
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1983_: u8 = 0;
    let mut v___y_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dvds_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: u8 = 0;
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2017_: u8 = 0;
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2021_: u8 = 0;
    let mut v___y_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2038_: u8 = 0;
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2043_: u8 = 0;
    let mut v_unused_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: u8 = 0;
    let mut v___x_2065_: u8 = 0;
    let mut v_k_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: u8 = 0;
    let mut v___x_2074_: u8 = 0;
    let mut v___x_2075_: u8 = 0;
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2080_: u8 = 0;
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2084_: u8 = 0;
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2087_: u8 = 0;
    let mut v_inheritedTraceOptions_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: u8 = 0;
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2100_: u8 = 0;
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2104_: u8 = 0;
    let mut v_options_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2106_: u8 = 0;
    let mut v_inheritedTraceOptions_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: u8 = 0;
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2119_: u8 = 0;
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2123_: u8 = 0;
    let mut v_a_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2127_: u8 = 0;
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2131_: u8 = 0;
    let mut v_fileName_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2144_: u8 = 0;
    let mut v_cancelTk_x3f_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2146_: u8 = 0;
    let mut v_inheritedTraceOptions_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2156_: u8 = 0;
    let mut v___x_2157_: u8 = 0;
    let mut v_hasTrace_2158_: u8 = 0;
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: u8 = 0;
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2171_: u8 = 0;
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2175_: u8 = 0;
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2180_: u8 = 0;
    let mut v_a_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2184_: u8 = 0;
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2188_: u8 = 0;
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: u8 = 0;
    let mut v___x_2191_: u8 = 0;
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_2132_ = crate::leanh::lean_ctor_get(v_a_1865_, 0);
                crate::leanh::lean_inc_ref(v_fileName_2132_);
                v_fileMap_2133_ = crate::leanh::lean_ctor_get(v_a_1865_, 1);
                crate::leanh::lean_inc_ref(v_fileMap_2133_);
                v_options_2134_ = crate::leanh::lean_ctor_get(v_a_1865_, 2);
                crate::leanh::lean_inc_ref(v_options_2134_);
                v_currRecDepth_2135_ = crate::leanh::lean_ctor_get(v_a_1865_, 3);
                crate::leanh::lean_inc(v_currRecDepth_2135_);
                v_maxRecDepth_2136_ = crate::leanh::lean_ctor_get(v_a_1865_, 4);
                crate::leanh::lean_inc(v_maxRecDepth_2136_);
                v_ref_2137_ = crate::leanh::lean_ctor_get(v_a_1865_, 5);
                crate::leanh::lean_inc(v_ref_2137_);
                v_currNamespace_2138_ = crate::leanh::lean_ctor_get(v_a_1865_, 6);
                crate::leanh::lean_inc(v_currNamespace_2138_);
                v_openDecls_2139_ = crate::leanh::lean_ctor_get(v_a_1865_, 7);
                crate::leanh::lean_inc(v_openDecls_2139_);
                v_initHeartbeats_2140_ = crate::leanh::lean_ctor_get(v_a_1865_, 8);
                crate::leanh::lean_inc(v_initHeartbeats_2140_);
                v_maxHeartbeats_2141_ = crate::leanh::lean_ctor_get(v_a_1865_, 9);
                crate::leanh::lean_inc(v_maxHeartbeats_2141_);
                v_quotContext_2142_ = crate::leanh::lean_ctor_get(v_a_1865_, 10);
                crate::leanh::lean_inc(v_quotContext_2142_);
                v_currMacroScope_2143_ = crate::leanh::lean_ctor_get(v_a_1865_, 11);
                crate::leanh::lean_inc(v_currMacroScope_2143_);
                v_diag_2144_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1865_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_2145_ = crate::leanh::lean_ctor_get(v_a_1865_, 12);
                crate::leanh::lean_inc(v_cancelTk_x3f_2145_);
                v_suppressElabErrors_2146_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1865_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_2147_ = crate::leanh::lean_ctor_get(v_a_1865_, 13);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_2147_);
                crate::leanh::lean_dec_ref(v_a_1865_);
                v___x_2189_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2190_ = lean_nat_dec_eq(v_maxRecDepth_2136_, v___x_2189_);
                if v___x_2190_ == 0 {
                    v___x_2191_ = lean_nat_dec_eq(v_currRecDepth_2135_, v_maxRecDepth_2136_);
                    if v___x_2191_ == 0 {
                        state = 29;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_inheritedTraceOptions_2147_);
                        crate::leanh::lean_dec(v_cancelTk_x3f_2145_);
                        crate::leanh::lean_dec(v_currMacroScope_2143_);
                        crate::leanh::lean_dec(v_quotContext_2142_);
                        crate::leanh::lean_dec(v_maxHeartbeats_2141_);
                        crate::leanh::lean_dec(v_initHeartbeats_2140_);
                        crate::leanh::lean_dec(v_openDecls_2139_);
                        crate::leanh::lean_dec(v_currNamespace_2138_);
                        crate::leanh::lean_dec(v_maxRecDepth_2136_);
                        crate::leanh::lean_dec(v_currRecDepth_2135_);
                        crate::leanh::lean_dec_ref(v_options_2134_);
                        crate::leanh::lean_dec_ref(v_fileMap_2133_);
                        crate::leanh::lean_dec_ref(v_fileName_2132_);
                        crate::leanh::lean_dec_ref(v_c_1856_);
                        v___x_2192_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_2137_);
                        return v___x_2192_;
                    }
                } else {
                    state = 29;
                    continue;
                }
            }
            1 => {
                v___x_1869_ = crate::leanh::lean_box(0);
                v___x_1870_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1870_, 0, v___x_1869_);
                return v___x_1870_;
            }
            2 => {
                v___x_1879_ = l_Int_Linear_Poly_updateOccs___redArg(
                    v___y_1873_,
                    v___y_1874_,
                    v___y_1875_,
                    v___y_1876_,
                    v___y_1877_,
                    v___y_1878_,
                );
                crate::leanh::lean_dec_ref(v___y_1877_);
                if crate::leanh::lean_obj_tag(v___x_1879_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1879_, 1);
                    v___x_1880_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
                    v___x_1881_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1880_, v___y_1872_, v___y_1874_);
                    return v___x_1881_;
                } else {
                    crate::leanh::lean_dec_ref(v___y_1872_);
                    return v___x_1879_;
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v___y_1904_) == 1 {
                    crate::leanh::lean_dec_ref(v___y_1897_);
                    crate::leanh::lean_dec_ref(v___y_1892_);
                    v_val_1905_ = crate::leanh::lean_ctor_get(v___y_1904_, 0);
                    crate::leanh::lean_inc(v_val_1905_);
                    crate::leanh::lean_dec_ref_known(v___y_1904_, 1);
                    v_p_1906_ = crate::leanh::lean_ctor_get(v_val_1905_, 1);
                    crate::leanh::lean_inc_ref(v_p_1906_);
                    if crate::leanh::lean_obj_tag(v_p_1906_) == 1 {
                        v_d_1907_ = crate::leanh::lean_ctor_get(v_val_1905_, 0);
                        v_k_1908_ = crate::leanh::lean_ctor_get(v_p_1906_, 0);
                        v_p_1909_ = crate::leanh::lean_ctor_get(v_p_1906_, 2);
                        v_isSharedCheck_1962_ = (!crate::leanh::lean_is_exclusive(v_p_1906_)) as u8;
                        if v_isSharedCheck_1962_ == 0 {
                            v_unused_1963_ = crate::leanh::lean_ctor_get(v_p_1906_, 1);
                            crate::leanh::lean_dec(v_unused_1963_);
                            v___x_1911_ = v_p_1906_;
                            v_isShared_1912_ = v_isSharedCheck_1962_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_p_1909_);
                            crate::leanh::lean_inc(v_k_1908_);
                            crate::leanh::lean_dec(v_p_1906_);
                            v___x_1911_ = crate::leanh::lean_box(0);
                            v_isShared_1912_ = v_isSharedCheck_1962_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_p_1906_);
                        crate::leanh::lean_dec(v___y_1901_);
                        crate::leanh::lean_dec_ref(v___y_1896_);
                        crate::leanh::lean_dec(v___y_1893_);
                        crate::leanh::lean_dec_ref(v___y_1890_);
                        crate::leanh::lean_dec_ref(v___y_1889_);
                        crate::leanh::lean_dec(v___y_1884_);
                        v___x_1964_ =
                            l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(
                                v_val_1905_,
                                v___y_1888_,
                                v___y_1900_,
                                v___y_1885_,
                                v___y_1886_,
                                v___y_1894_,
                                v___y_1899_,
                                v___y_1895_,
                                v___y_1903_,
                                v___y_1883_,
                                v___y_1902_,
                            );
                        crate::leanh::lean_dec_ref(v___y_1883_);
                        return v___x_1964_;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_1904_);
                    crate::leanh::lean_dec(v___y_1901_);
                    crate::leanh::lean_dec_ref(v___y_1896_);
                    crate::leanh::lean_dec(v___y_1893_);
                    crate::leanh::lean_dec_ref(v___y_1890_);
                    crate::leanh::lean_dec(v___y_1884_);
                    v_options_1965_ = crate::leanh::lean_ctor_get(v___y_1883_, 2);
                    v_hasTrace_1966_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_1965_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_1966_ == 0 {
                        crate::leanh::lean_dec_ref(v___y_1889_);
                        v___y_1872_ = v___y_1897_;
                        v___y_1873_ = v___y_1892_;
                        v___y_1874_ = v___y_1888_;
                        v___y_1875_ = v___y_1895_;
                        v___y_1876_ = v___y_1903_;
                        v___y_1877_ = v___y_1883_;
                        v___y_1878_ = v___y_1902_;
                        state = 2;
                        continue;
                    } else {
                        v_inheritedTraceOptions_1967_ =
                            crate::leanh::lean_ctor_get(v___y_1883_, 13);
                        v___x_1968_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
                        crate::leanh::lean_inc_ref(v___y_1891_);
                        crate::leanh::lean_inc_ref(v___y_1898_);
                        crate::leanh::lean_inc_ref(v___y_1887_);
                        v___x_1969_ =
                            l_Lean_Name_mkStr4(v___y_1887_, v___y_1898_, v___y_1891_, v___x_1968_);
                        v___x_1970_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
                        crate::leanh::lean_inc(v___x_1969_);
                        v___x_1971_ = l_Lean_Name_append(v___x_1970_, v___x_1969_);
                        v___x_1972_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_1967_,
                            v_options_1965_,
                            v___x_1971_,
                        );
                        crate::leanh::lean_dec(v___x_1971_);
                        if v___x_1972_ == 0 {
                            crate::leanh::lean_dec(v___x_1969_);
                            crate::leanh::lean_dec_ref(v___y_1889_);
                            v___y_1872_ = v___y_1897_;
                            v___y_1873_ = v___y_1892_;
                            v___y_1874_ = v___y_1888_;
                            v___y_1875_ = v___y_1895_;
                            v___y_1876_ = v___y_1903_;
                            v___y_1877_ = v___y_1883_;
                            v___y_1878_ = v___y_1902_;
                            state = 2;
                            continue;
                        } else {
                            v___x_1973_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(
                                v___y_1889_,
                                v___y_1888_,
                                v___y_1883_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1973_) == 0 {
                                v_a_1974_ = crate::leanh::lean_ctor_get(v___x_1973_, 0);
                                crate::leanh::lean_inc(v_a_1974_);
                                crate::leanh::lean_dec_ref_known(v___x_1973_, 1);
                                v___x_1975_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_1969_, v_a_1974_, v___y_1895_, v___y_1903_, v___y_1883_, v___y_1902_);
                                if crate::leanh::lean_obj_tag(v___x_1975_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_1975_, 1);
                                    v___y_1872_ = v___y_1897_;
                                    v___y_1873_ = v___y_1892_;
                                    v___y_1874_ = v___y_1888_;
                                    v___y_1875_ = v___y_1895_;
                                    v___y_1876_ = v___y_1903_;
                                    v___y_1877_ = v___y_1883_;
                                    v___y_1878_ = v___y_1902_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v___y_1897_);
                                    crate::leanh::lean_dec_ref(v___y_1892_);
                                    crate::leanh::lean_dec_ref(v___y_1883_);
                                    return v___x_1975_;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_1969_);
                                crate::leanh::lean_dec_ref(v___y_1897_);
                                crate::leanh::lean_dec_ref(v___y_1892_);
                                crate::leanh::lean_dec_ref(v___y_1883_);
                                v_a_1976_ = crate::leanh::lean_ctor_get(v___x_1973_, 0);
                                v_isSharedCheck_1983_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1973_)) as u8;
                                if v_isSharedCheck_1983_ == 0 {
                                    v___x_1978_ = v___x_1973_;
                                    v_isShared_1979_ = v_isSharedCheck_1983_;
                                    state = 12;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1976_);
                                    crate::leanh::lean_dec(v___x_1973_);
                                    v___x_1978_ = crate::leanh::lean_box(0);
                                    v_isShared_1979_ = v_isSharedCheck_1983_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            4 => {
                v___x_1913_ = lean_int_mul(v___y_1893_, v_d_1907_);
                v___x_1914_ = lean_int_mul(v_k_1908_, v___y_1901_);
                v___x_1915_ = l_Lean_Meta_Grind_Arith_gcdExt(v___x_1913_, v___x_1914_);
                crate::leanh::lean_dec(v___x_1914_);
                crate::leanh::lean_dec(v___x_1913_);
                v_snd_1916_ = crate::leanh::lean_ctor_get(v___x_1915_, 1);
                v_fst_1917_ = crate::leanh::lean_ctor_get(v___x_1915_, 0);
                v_isSharedCheck_1961_ = (!crate::leanh::lean_is_exclusive(v___x_1915_)) as u8;
                if v_isSharedCheck_1961_ == 0 {
                    v___x_1919_ = v___x_1915_;
                    v_isShared_1920_ = v_isSharedCheck_1961_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1916_);
                    crate::leanh::lean_inc(v_fst_1917_);
                    crate::leanh::lean_dec(v___x_1915_);
                    v___x_1919_ = crate::leanh::lean_box(0);
                    v_isShared_1920_ = v_isSharedCheck_1961_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_fst_1921_ = crate::leanh::lean_ctor_get(v_snd_1916_, 0);
                v_snd_1922_ = crate::leanh::lean_ctor_get(v_snd_1916_, 1);
                v_isSharedCheck_1960_ = (!crate::leanh::lean_is_exclusive(v_snd_1916_)) as u8;
                if v_isSharedCheck_1960_ == 0 {
                    v___x_1924_ = v_snd_1916_;
                    v_isShared_1925_ = v_isSharedCheck_1960_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1922_);
                    crate::leanh::lean_inc(v_fst_1921_);
                    crate::leanh::lean_dec(v_snd_1916_);
                    v___x_1924_ = crate::leanh::lean_box(0);
                    v_isShared_1925_ = v_isSharedCheck_1960_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1926_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
                v___x_1927_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1926_, v___y_1896_, v___y_1888_);
                if crate::leanh::lean_obj_tag(v___x_1927_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1927_, 1);
                    v___x_1928_ = lean_int_mul(v_fst_1921_, v_d_1907_);
                    crate::leanh::lean_dec(v_fst_1921_);
                    crate::leanh::lean_inc_ref(v___y_1890_);
                    v___x_1929_ = l_Int_Linear_Poly_mul(v___y_1890_, v___x_1928_);
                    crate::leanh::lean_dec(v___x_1928_);
                    v___x_1930_ = lean_int_mul(v_snd_1922_, v___y_1901_);
                    crate::leanh::lean_dec(v_snd_1922_);
                    crate::leanh::lean_inc_ref(v_p_1909_);
                    v___x_1931_ = l_Int_Linear_Poly_mul(v_p_1909_, v___x_1930_);
                    crate::leanh::lean_dec(v___x_1930_);
                    v___x_1932_ = lean_int_mul(v___y_1901_, v_d_1907_);
                    crate::leanh::lean_dec(v___y_1901_);
                    v___x_1933_ = l_Int_Linear_Poly_combine(v___x_1929_, v___x_1931_);
                    crate::leanh::lean_inc(v_fst_1917_);
                    if v_isShared_1912_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1911_, 2, v___x_1933_);
                        crate::leanh::lean_ctor_set(v___x_1911_, 1, v___y_1884_);
                        crate::leanh::lean_ctor_set(v___x_1911_, 0, v_fst_1917_);
                        v___x_1935_ = v___x_1911_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1959_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_fst_1917_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1959_, 1, v___y_1884_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1959_, 2, v___x_1933_);
                        v___x_1935_ = v_reuseFailAlloc_1959_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1924_);
                    crate::leanh::lean_dec(v_snd_1922_);
                    crate::leanh::lean_dec(v_fst_1921_);
                    crate::leanh::lean_del_object(v___x_1919_);
                    crate::leanh::lean_dec(v_fst_1917_);
                    crate::leanh::lean_del_object(v___x_1911_);
                    crate::leanh::lean_dec_ref(v_p_1909_);
                    crate::leanh::lean_dec(v_k_1908_);
                    crate::leanh::lean_dec(v_val_1905_);
                    crate::leanh::lean_dec(v___y_1901_);
                    crate::leanh::lean_dec(v___y_1893_);
                    crate::leanh::lean_dec_ref(v___y_1890_);
                    crate::leanh::lean_dec_ref(v___y_1889_);
                    crate::leanh::lean_dec(v___y_1884_);
                    crate::leanh::lean_dec_ref(v___y_1883_);
                    return v___x_1927_;
                }
            }
            7 => {
                crate::leanh::lean_inc(v_val_1905_);
                crate::leanh::lean_inc_ref(v___y_1889_);
                if v_isShared_1925_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1924_, 4);
                    crate::leanh::lean_ctor_set(v___x_1924_, 1, v_val_1905_);
                    crate::leanh::lean_ctor_set(v___x_1924_, 0, v___y_1889_);
                    v___x_1937_ = v___x_1924_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1958_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___y_1889_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_val_1905_);
                    v___x_1937_ = v_reuseFailAlloc_1958_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1938_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1938_, 0, v___x_1932_);
                crate::leanh::lean_ctor_set(v___x_1938_, 1, v___x_1935_);
                crate::leanh::lean_ctor_set(v___x_1938_, 2, v___x_1937_);
                crate::leanh::lean_inc_ref(v___y_1883_);
                v___x_1939_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(
                    v___x_1938_,
                    v___y_1888_,
                    v___y_1900_,
                    v___y_1885_,
                    v___y_1886_,
                    v___y_1894_,
                    v___y_1899_,
                    v___y_1895_,
                    v___y_1903_,
                    v___y_1883_,
                    v___y_1902_,
                );
                if crate::leanh::lean_obj_tag(v___x_1939_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1939_, 1);
                    v___x_1940_ = l_Int_Linear_Poly_mul(v___y_1890_, v_k_1908_);
                    crate::leanh::lean_dec(v_k_1908_);
                    v___x_1941_ = lean_int_neg(v___y_1893_);
                    crate::leanh::lean_dec(v___y_1893_);
                    v___x_1942_ = l_Int_Linear_Poly_mul(v_p_1909_, v___x_1941_);
                    crate::leanh::lean_dec(v___x_1941_);
                    v___x_1943_ = l_Int_Linear_Poly_combine(v___x_1940_, v___x_1942_);
                    crate::leanh::lean_inc(v_val_1905_);
                    if v_isShared_1920_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1919_, 5);
                        crate::leanh::lean_ctor_set(v___x_1919_, 1, v_val_1905_);
                        crate::leanh::lean_ctor_set(v___x_1919_, 0, v___y_1889_);
                        v___x_1945_ = v___x_1919_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1957_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___y_1889_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1957_, 1, v_val_1905_);
                        v___x_1945_ = v_reuseFailAlloc_1957_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1919_);
                    crate::leanh::lean_dec(v_fst_1917_);
                    crate::leanh::lean_dec_ref(v_p_1909_);
                    crate::leanh::lean_dec(v_k_1908_);
                    crate::leanh::lean_dec(v_val_1905_);
                    crate::leanh::lean_dec(v___y_1893_);
                    crate::leanh::lean_dec_ref(v___y_1890_);
                    crate::leanh::lean_dec_ref(v___y_1889_);
                    crate::leanh::lean_dec_ref(v___y_1883_);
                    return v___x_1939_;
                }
            }
            9 => {
                v_isSharedCheck_1953_ = (!crate::leanh::lean_is_exclusive(v_val_1905_)) as u8;
                if v_isSharedCheck_1953_ == 0 {
                    v_unused_1954_ = crate::leanh::lean_ctor_get(v_val_1905_, 2);
                    crate::leanh::lean_dec(v_unused_1954_);
                    v_unused_1955_ = crate::leanh::lean_ctor_get(v_val_1905_, 1);
                    crate::leanh::lean_dec(v_unused_1955_);
                    v_unused_1956_ = crate::leanh::lean_ctor_get(v_val_1905_, 0);
                    crate::leanh::lean_dec(v_unused_1956_);
                    v___x_1947_ = v_val_1905_;
                    v_isShared_1948_ = v_isSharedCheck_1953_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_1905_);
                    v___x_1947_ = crate::leanh::lean_box(0);
                    v_isShared_1948_ = v_isSharedCheck_1953_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_1948_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1947_, 2, v___x_1945_);
                    crate::leanh::lean_ctor_set(v___x_1947_, 1, v___x_1943_);
                    crate::leanh::lean_ctor_set(v___x_1947_, 0, v_fst_1917_);
                    v___x_1950_ = v___x_1947_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1952_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_fst_1917_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1952_, 1, v___x_1943_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1952_, 2, v___x_1945_);
                    v___x_1950_ = v_reuseFailAlloc_1952_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_c_1856_ = v___x_1950_;
                v_a_1857_ = v___y_1888_;
                v_a_1858_ = v___y_1900_;
                v_a_1859_ = v___y_1885_;
                v_a_1860_ = v___y_1886_;
                v_a_1861_ = v___y_1894_;
                v_a_1862_ = v___y_1899_;
                v_a_1863_ = v___y_1895_;
                v_a_1864_ = v___y_1903_;
                v_a_1865_ = v___y_1883_;
                v_a_1866_ = v___y_1902_;
                state = 0;
                continue;
            }
            12 => {
                if v_isShared_1979_ == 0 {
                    v___x_1981_ = v___x_1978_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1982_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1976_);
                    v___x_1981_ = v_reuseFailAlloc_1982_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1981_;
            }
            14 => {
                v___x_2006_ =
                    l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v___y_1996_, v___y_2004_);
                if crate::leanh::lean_obj_tag(v___x_2006_) == 0 {
                    v_a_2007_ = crate::leanh::lean_ctor_get(v___x_2006_, 0);
                    crate::leanh::lean_inc(v_a_2007_);
                    crate::leanh::lean_dec_ref_known(v___x_2006_, 1);
                    v_dvds_2008_ = crate::leanh::lean_ctor_get(v_a_2007_, 6);
                    crate::leanh::lean_inc_ref(v_dvds_2008_);
                    crate::leanh::lean_dec(v_a_2007_);
                    v_size_2009_ = crate::leanh::lean_ctor_get(v_dvds_2008_, 2);
                    v___x_2010_ = crate::leanh::lean_box(0);
                    v___x_2011_ = lean_nat_dec_lt(v___y_1985_, v_size_2009_);
                    if v___x_2011_ == 0 {
                        crate::leanh::lean_dec_ref(v_dvds_2008_);
                        v___x_2012_ = l_outOfBounds___redArg(v___x_2010_);
                        v___y_1883_ = v___y_2004_;
                        v___y_1884_ = v___y_1985_;
                        v___y_1885_ = v___y_1998_;
                        v___y_1886_ = v___y_1999_;
                        v___y_1887_ = v___y_1986_;
                        v___y_1888_ = v___y_1996_;
                        v___y_1889_ = v___y_1987_;
                        v___y_1890_ = v___y_1991_;
                        v___y_1891_ = v___y_1993_;
                        v___y_1892_ = v___y_1994_;
                        v___y_1893_ = v___y_1995_;
                        v___y_1894_ = v___y_2000_;
                        v___y_1895_ = v___y_2002_;
                        v___y_1896_ = v___y_1988_;
                        v___y_1897_ = v___y_1990_;
                        v___y_1898_ = v___y_1989_;
                        v___y_1899_ = v___y_2001_;
                        v___y_1900_ = v___y_1997_;
                        v___y_1901_ = v___y_1992_;
                        v___y_1902_ = v___y_2005_;
                        v___y_1903_ = v___y_2003_;
                        v___y_1904_ = v___x_2012_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2013_ = l_Lean_PersistentArray_get_x21___redArg(
                            v___x_2010_,
                            v_dvds_2008_,
                            v___y_1985_,
                        );
                        crate::leanh::lean_dec_ref(v_dvds_2008_);
                        v___y_1883_ = v___y_2004_;
                        v___y_1884_ = v___y_1985_;
                        v___y_1885_ = v___y_1998_;
                        v___y_1886_ = v___y_1999_;
                        v___y_1887_ = v___y_1986_;
                        v___y_1888_ = v___y_1996_;
                        v___y_1889_ = v___y_1987_;
                        v___y_1890_ = v___y_1991_;
                        v___y_1891_ = v___y_1993_;
                        v___y_1892_ = v___y_1994_;
                        v___y_1893_ = v___y_1995_;
                        v___y_1894_ = v___y_2000_;
                        v___y_1895_ = v___y_2002_;
                        v___y_1896_ = v___y_1988_;
                        v___y_1897_ = v___y_1990_;
                        v___y_1898_ = v___y_1989_;
                        v___y_1899_ = v___y_2001_;
                        v___y_1900_ = v___y_1997_;
                        v___y_1901_ = v___y_1992_;
                        v___y_1902_ = v___y_2005_;
                        v___y_1903_ = v___y_2003_;
                        v___y_1904_ = v___x_2013_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2004_);
                    crate::leanh::lean_dec(v___y_1995_);
                    crate::leanh::lean_dec_ref(v___y_1994_);
                    crate::leanh::lean_dec(v___y_1992_);
                    crate::leanh::lean_dec_ref(v___y_1991_);
                    crate::leanh::lean_dec_ref(v___y_1990_);
                    crate::leanh::lean_dec_ref(v___y_1988_);
                    crate::leanh::lean_dec_ref(v___y_1987_);
                    crate::leanh::lean_dec(v___y_1985_);
                    v_a_2014_ = crate::leanh::lean_ctor_get(v___x_2006_, 0);
                    v_isSharedCheck_2021_ = (!crate::leanh::lean_is_exclusive(v___x_2006_)) as u8;
                    if v_isSharedCheck_2021_ == 0 {
                        v___x_2016_ = v___x_2006_;
                        v_isShared_2017_ = v_isSharedCheck_2021_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2014_);
                        crate::leanh::lean_dec(v___x_2006_);
                        v___x_2016_ = crate::leanh::lean_box(0);
                        v_isShared_2017_ = v_isSharedCheck_2021_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_2017_ == 0 {
                    v___x_2019_ = v___x_2016_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2020_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_a_2014_);
                    v___x_2019_ = v_reuseFailAlloc_2020_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2019_;
            }
            17 => {
                v___x_2034_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2034_, 0, v___y_2023_);
                v___x_2035_ = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(
                    v___x_2034_,
                    v___y_2024_,
                    v___y_2025_,
                    v___y_2026_,
                    v___y_2027_,
                    v___y_2028_,
                    v___y_2029_,
                    v___y_2030_,
                    v___y_2031_,
                    v___y_2032_,
                    v___y_2033_,
                );
                crate::leanh::lean_dec_ref(v___y_2032_);
                if crate::leanh::lean_obj_tag(v___x_2035_) == 0 {
                    v_isSharedCheck_2043_ = (!crate::leanh::lean_is_exclusive(v___x_2035_)) as u8;
                    if v_isSharedCheck_2043_ == 0 {
                        v_unused_2044_ = crate::leanh::lean_ctor_get(v___x_2035_, 0);
                        crate::leanh::lean_dec(v_unused_2044_);
                        v___x_2037_ = v___x_2035_;
                        v_isShared_2038_ = v_isSharedCheck_2043_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2035_);
                        v___x_2037_ = crate::leanh::lean_box(0);
                        v_isShared_2038_ = v_isSharedCheck_2043_;
                        state = 18;
                        continue;
                    }
                } else {
                    return v___x_2035_;
                }
            }
            18 => {
                v___x_2039_ = crate::leanh::lean_box(0);
                if v_isShared_2038_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2037_, 0, v___x_2039_);
                    v___x_2041_ = v___x_2037_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2042_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2039_);
                    v___x_2041_ = v_reuseFailAlloc_2042_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2041_;
            }
            20 => {
                v___x_2059_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(v_c_1856_);
                crate::leanh::lean_inc_ref(v___y_2057_);
                v___x_2060_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(
                    v___x_2059_,
                    v___y_2049_,
                    v___y_2050_,
                    v___y_2051_,
                    v___y_2052_,
                    v___y_2053_,
                    v___y_2054_,
                    v___y_2055_,
                    v___y_2056_,
                    v___y_2057_,
                    v___y_2058_,
                );
                if crate::leanh::lean_obj_tag(v___x_2060_) == 0 {
                    v_a_2061_ = crate::leanh::lean_ctor_get(v___x_2060_, 0);
                    crate::leanh::lean_inc(v_a_2061_);
                    crate::leanh::lean_dec_ref_known(v___x_2060_, 1);
                    v_d_2062_ = crate::leanh::lean_ctor_get(v_a_2061_, 0);
                    v_p_2063_ = crate::leanh::lean_ctor_get(v_a_2061_, 1);
                    crate::leanh::lean_inc(v_d_2062_);
                    v___x_2064_ = l_Int_Linear_Poly_isUnsatDvd(v_d_2062_, v_p_2063_);
                    if v___x_2064_ == 0 {
                        v___x_2065_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v_a_2061_);
                        if v___x_2065_ == 0 {
                            if crate::leanh::lean_obj_tag(v_p_2063_) == 1 {
                                crate::leanh::lean_inc_ref(v_p_2063_);
                                crate::leanh::lean_inc(v_d_2062_);
                                v_k_2066_ = crate::leanh::lean_ctor_get(v_p_2063_, 0);
                                crate::leanh::lean_inc(v_k_2066_);
                                v_v_2067_ = crate::leanh::lean_ctor_get(v_p_2063_, 1);
                                crate::leanh::lean_inc(v_v_2067_);
                                v_p_2068_ = crate::leanh::lean_ctor_get(v_p_2063_, 2);
                                crate::leanh::lean_inc_ref(v_p_2068_);
                                crate::leanh::lean_inc(v_a_2061_);
                                v___x_2069_ =
                                    l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(
                                        v_a_2061_,
                                        v___y_2049_,
                                        v___y_2057_,
                                    );
                                if crate::leanh::lean_obj_tag(v___x_2069_) == 0 {
                                    v_a_2070_ = crate::leanh::lean_ctor_get(v___x_2069_, 0);
                                    crate::leanh::lean_inc(v_a_2070_);
                                    crate::leanh::lean_dec_ref_known(v___x_2069_, 1);
                                    crate::leanh::lean_inc_n(v_v_2067_, 2);
                                    crate::leanh::lean_inc(v_a_2061_);
                                    v___f_2071_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                                    crate::leanh::lean_closure_set(v___f_2071_, 0, v_a_2061_);
                                    crate::leanh::lean_closure_set(v___f_2071_, 1, v_v_2067_);
                                    v___f_2072_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
                                    crate::leanh::lean_closure_set(v___f_2072_, 0, v_v_2067_);
                                    v___x_2073_ = 0;
                                    v___x_2074_ = (crate::leanh::lean_unbox(v_a_2070_) as u8);
                                    crate::leanh::lean_dec(v_a_2070_);
                                    v___x_2075_ = l_Lean_instBEqLBool_beq(v___x_2074_, v___x_2073_);
                                    if v___x_2075_ == 0 {
                                        v___y_1985_ = v_v_2067_;
                                        v___y_1986_ = v___y_2046_;
                                        v___y_1987_ = v_a_2061_;
                                        v___y_1988_ = v___f_2072_;
                                        v___y_1989_ = v___y_2047_;
                                        v___y_1990_ = v___f_2071_;
                                        v___y_1991_ = v_p_2068_;
                                        v___y_1992_ = v_d_2062_;
                                        v___y_1993_ = v___y_2048_;
                                        v___y_1994_ = v_p_2063_;
                                        v___y_1995_ = v_k_2066_;
                                        v___y_1996_ = v___y_2049_;
                                        v___y_1997_ = v___y_2050_;
                                        v___y_1998_ = v___y_2051_;
                                        v___y_1999_ = v___y_2052_;
                                        v___y_2000_ = v___y_2053_;
                                        v___y_2001_ = v___y_2054_;
                                        v___y_2002_ = v___y_2055_;
                                        v___y_2003_ = v___y_2056_;
                                        v___y_2004_ = v___y_2057_;
                                        v___y_2005_ = v___y_2058_;
                                        state = 14;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_2067_);
                                        v___x_2076_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_v_2067_, v___y_2049_);
                                        if crate::leanh::lean_obj_tag(v___x_2076_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_2076_, 1);
                                            v___y_1985_ = v_v_2067_;
                                            v___y_1986_ = v___y_2046_;
                                            v___y_1987_ = v_a_2061_;
                                            v___y_1988_ = v___f_2072_;
                                            v___y_1989_ = v___y_2047_;
                                            v___y_1990_ = v___f_2071_;
                                            v___y_1991_ = v_p_2068_;
                                            v___y_1992_ = v_d_2062_;
                                            v___y_1993_ = v___y_2048_;
                                            v___y_1994_ = v_p_2063_;
                                            v___y_1995_ = v_k_2066_;
                                            v___y_1996_ = v___y_2049_;
                                            v___y_1997_ = v___y_2050_;
                                            v___y_1998_ = v___y_2051_;
                                            v___y_1999_ = v___y_2052_;
                                            v___y_2000_ = v___y_2053_;
                                            v___y_2001_ = v___y_2054_;
                                            v___y_2002_ = v___y_2055_;
                                            v___y_2003_ = v___y_2056_;
                                            v___y_2004_ = v___y_2057_;
                                            v___y_2005_ = v___y_2058_;
                                            state = 14;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec_ref(v___f_2072_);
                                            crate::leanh::lean_dec_ref(v___f_2071_);
                                            crate::leanh::lean_dec_ref(v_p_2068_);
                                            crate::leanh::lean_dec(v_v_2067_);
                                            crate::leanh::lean_dec(v_k_2066_);
                                            crate::leanh::lean_dec_ref_known(v_p_2063_, 3);
                                            crate::leanh::lean_dec(v_d_2062_);
                                            crate::leanh::lean_dec(v_a_2061_);
                                            crate::leanh::lean_dec_ref(v___y_2057_);
                                            return v___x_2076_;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_p_2068_);
                                    crate::leanh::lean_dec(v_v_2067_);
                                    crate::leanh::lean_dec(v_k_2066_);
                                    crate::leanh::lean_dec_ref_known(v_p_2063_, 3);
                                    crate::leanh::lean_dec(v_d_2062_);
                                    crate::leanh::lean_dec(v_a_2061_);
                                    crate::leanh::lean_dec_ref(v___y_2057_);
                                    v_a_2077_ = crate::leanh::lean_ctor_get(v___x_2069_, 0);
                                    v_isSharedCheck_2084_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2069_)) as u8;
                                    if v_isSharedCheck_2084_ == 0 {
                                        v___x_2079_ = v___x_2069_;
                                        v_isShared_2080_ = v_isSharedCheck_2084_;
                                        state = 21;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2077_);
                                        crate::leanh::lean_dec(v___x_2069_);
                                        v___x_2079_ = crate::leanh::lean_box(0);
                                        v_isShared_2080_ = v_isSharedCheck_2084_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            } else {
                                v___x_2085_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_a_2061_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
                                crate::leanh::lean_dec_ref(v___y_2057_);
                                return v___x_2085_;
                            }
                        } else {
                            v_options_2086_ = crate::leanh::lean_ctor_get(v___y_2057_, 2);
                            v_hasTrace_2087_ = crate::leanh::lean_ctor_get_uint8(
                                v_options_2086_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            );
                            if v_hasTrace_2087_ == 0 {
                                crate::leanh::lean_dec(v_a_2061_);
                                crate::leanh::lean_dec_ref(v___y_2057_);
                                state = 1;
                                continue;
                            } else {
                                v_inheritedTraceOptions_2088_ =
                                    crate::leanh::lean_ctor_get(v___y_2057_, 13);
                                v___x_2089_ =
                                    l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1;
                                crate::leanh::lean_inc_ref(v___y_2048_);
                                crate::leanh::lean_inc_ref(v___y_2047_);
                                crate::leanh::lean_inc_ref(v___y_2046_);
                                v___x_2090_ = l_Lean_Name_mkStr4(
                                    v___y_2046_,
                                    v___y_2047_,
                                    v___y_2048_,
                                    v___x_2089_,
                                );
                                v___x_2091_ =
                                    l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
                                crate::leanh::lean_inc(v___x_2090_);
                                v___x_2092_ = l_Lean_Name_append(v___x_2091_, v___x_2090_);
                                v___x_2093_ =
                                    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                        v_inheritedTraceOptions_2088_,
                                        v_options_2086_,
                                        v___x_2092_,
                                    );
                                crate::leanh::lean_dec(v___x_2092_);
                                if v___x_2093_ == 0 {
                                    crate::leanh::lean_dec(v___x_2090_);
                                    crate::leanh::lean_dec(v_a_2061_);
                                    crate::leanh::lean_dec_ref(v___y_2057_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_2094_ =
                                        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(
                                            v_a_2061_,
                                            v___y_2049_,
                                            v___y_2057_,
                                        );
                                    if crate::leanh::lean_obj_tag(v___x_2094_) == 0 {
                                        v_a_2095_ = crate::leanh::lean_ctor_get(v___x_2094_, 0);
                                        crate::leanh::lean_inc(v_a_2095_);
                                        crate::leanh::lean_dec_ref_known(v___x_2094_, 1);
                                        v___x_2096_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_2090_, v_a_2095_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
                                        crate::leanh::lean_dec_ref(v___y_2057_);
                                        if crate::leanh::lean_obj_tag(v___x_2096_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_2096_, 1);
                                            state = 1;
                                            continue;
                                        } else {
                                            return v___x_2096_;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v___x_2090_);
                                        crate::leanh::lean_dec_ref(v___y_2057_);
                                        v_a_2097_ = crate::leanh::lean_ctor_get(v___x_2094_, 0);
                                        v_isSharedCheck_2104_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2094_)) as u8;
                                        if v_isSharedCheck_2104_ == 0 {
                                            v___x_2099_ = v___x_2094_;
                                            v_isShared_2100_ = v_isSharedCheck_2104_;
                                            state = 23;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2097_);
                                            crate::leanh::lean_dec(v___x_2094_);
                                            v___x_2099_ = crate::leanh::lean_box(0);
                                            v_isShared_2100_ = v_isSharedCheck_2104_;
                                            state = 23;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        v_options_2105_ = crate::leanh::lean_ctor_get(v___y_2057_, 2);
                        v_hasTrace_2106_ = crate::leanh::lean_ctor_get_uint8(
                            v_options_2105_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_2106_ == 0 {
                            v___y_2023_ = v_a_2061_;
                            v___y_2024_ = v___y_2049_;
                            v___y_2025_ = v___y_2050_;
                            v___y_2026_ = v___y_2051_;
                            v___y_2027_ = v___y_2052_;
                            v___y_2028_ = v___y_2053_;
                            v___y_2029_ = v___y_2054_;
                            v___y_2030_ = v___y_2055_;
                            v___y_2031_ = v___y_2056_;
                            v___y_2032_ = v___y_2057_;
                            v___y_2033_ = v___y_2058_;
                            state = 17;
                            continue;
                        } else {
                            v_inheritedTraceOptions_2107_ =
                                crate::leanh::lean_ctor_get(v___y_2057_, 13);
                            v___x_2108_ =
                                l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
                            crate::leanh::lean_inc_ref(v___y_2048_);
                            crate::leanh::lean_inc_ref(v___y_2047_);
                            crate::leanh::lean_inc_ref(v___y_2046_);
                            v___x_2109_ = l_Lean_Name_mkStr4(
                                v___y_2046_,
                                v___y_2047_,
                                v___y_2048_,
                                v___x_2108_,
                            );
                            v___x_2110_ =
                                l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
                            crate::leanh::lean_inc(v___x_2109_);
                            v___x_2111_ = l_Lean_Name_append(v___x_2110_, v___x_2109_);
                            v___x_2112_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_2107_,
                                v_options_2105_,
                                v___x_2111_,
                            );
                            crate::leanh::lean_dec(v___x_2111_);
                            if v___x_2112_ == 0 {
                                crate::leanh::lean_dec(v___x_2109_);
                                v___y_2023_ = v_a_2061_;
                                v___y_2024_ = v___y_2049_;
                                v___y_2025_ = v___y_2050_;
                                v___y_2026_ = v___y_2051_;
                                v___y_2027_ = v___y_2052_;
                                v___y_2028_ = v___y_2053_;
                                v___y_2029_ = v___y_2054_;
                                v___y_2030_ = v___y_2055_;
                                v___y_2031_ = v___y_2056_;
                                v___y_2032_ = v___y_2057_;
                                v___y_2033_ = v___y_2058_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2061_);
                                v___x_2113_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(
                                    v_a_2061_,
                                    v___y_2049_,
                                    v___y_2057_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2113_) == 0 {
                                    v_a_2114_ = crate::leanh::lean_ctor_get(v___x_2113_, 0);
                                    crate::leanh::lean_inc(v_a_2114_);
                                    crate::leanh::lean_dec_ref_known(v___x_2113_, 1);
                                    v___x_2115_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_2109_, v_a_2114_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
                                    if crate::leanh::lean_obj_tag(v___x_2115_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_2115_, 1);
                                        v___y_2023_ = v_a_2061_;
                                        v___y_2024_ = v___y_2049_;
                                        v___y_2025_ = v___y_2050_;
                                        v___y_2026_ = v___y_2051_;
                                        v___y_2027_ = v___y_2052_;
                                        v___y_2028_ = v___y_2053_;
                                        v___y_2029_ = v___y_2054_;
                                        v___y_2030_ = v___y_2055_;
                                        v___y_2031_ = v___y_2056_;
                                        v___y_2032_ = v___y_2057_;
                                        v___y_2033_ = v___y_2058_;
                                        state = 17;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_a_2061_);
                                        crate::leanh::lean_dec_ref(v___y_2057_);
                                        return v___x_2115_;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v___x_2109_);
                                    crate::leanh::lean_dec(v_a_2061_);
                                    crate::leanh::lean_dec_ref(v___y_2057_);
                                    v_a_2116_ = crate::leanh::lean_ctor_get(v___x_2113_, 0);
                                    v_isSharedCheck_2123_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2113_)) as u8;
                                    if v_isSharedCheck_2123_ == 0 {
                                        v___x_2118_ = v___x_2113_;
                                        v_isShared_2119_ = v_isSharedCheck_2123_;
                                        state = 25;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2116_);
                                        crate::leanh::lean_dec(v___x_2113_);
                                        v___x_2118_ = crate::leanh::lean_box(0);
                                        v_isShared_2119_ = v_isSharedCheck_2123_;
                                        state = 25;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2057_);
                    v_a_2124_ = crate::leanh::lean_ctor_get(v___x_2060_, 0);
                    v_isSharedCheck_2131_ = (!crate::leanh::lean_is_exclusive(v___x_2060_)) as u8;
                    if v_isSharedCheck_2131_ == 0 {
                        v___x_2126_ = v___x_2060_;
                        v_isShared_2127_ = v_isSharedCheck_2131_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2124_);
                        crate::leanh::lean_dec(v___x_2060_);
                        v___x_2126_ = crate::leanh::lean_box(0);
                        v_isShared_2127_ = v_isSharedCheck_2131_;
                        state = 27;
                        continue;
                    }
                }
            }
            21 => {
                if v_isShared_2080_ == 0 {
                    v___x_2082_ = v___x_2079_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2083_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
                    v___x_2082_ = v_reuseFailAlloc_2083_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2082_;
            }
            23 => {
                if v_isShared_2100_ == 0 {
                    v___x_2102_ = v___x_2099_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2103_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
                    v___x_2102_ = v_reuseFailAlloc_2103_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2102_;
            }
            25 => {
                if v_isShared_2119_ == 0 {
                    v___x_2121_ = v___x_2118_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_2122_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_a_2116_);
                    v___x_2121_ = v_reuseFailAlloc_2122_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_2121_;
            }
            27 => {
                if v_isShared_2127_ == 0 {
                    v___x_2129_ = v___x_2126_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2130_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2124_);
                    v___x_2129_ = v_reuseFailAlloc_2130_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_2129_;
            }
            29 => {
                v___x_2149_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2150_ = lean_nat_add(v_currRecDepth_2135_, v___x_2149_);
                crate::leanh::lean_dec(v_currRecDepth_2135_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_2147_);
                crate::leanh::lean_inc_ref(v_options_2134_);
                v___x_2151_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_2151_, 0, v_fileName_2132_);
                crate::leanh::lean_ctor_set(v___x_2151_, 1, v_fileMap_2133_);
                crate::leanh::lean_ctor_set(v___x_2151_, 2, v_options_2134_);
                crate::leanh::lean_ctor_set(v___x_2151_, 3, v___x_2150_);
                crate::leanh::lean_ctor_set(v___x_2151_, 4, v_maxRecDepth_2136_);
                crate::leanh::lean_ctor_set(v___x_2151_, 5, v_ref_2137_);
                crate::leanh::lean_ctor_set(v___x_2151_, 6, v_currNamespace_2138_);
                crate::leanh::lean_ctor_set(v___x_2151_, 7, v_openDecls_2139_);
                crate::leanh::lean_ctor_set(v___x_2151_, 8, v_initHeartbeats_2140_);
                crate::leanh::lean_ctor_set(v___x_2151_, 9, v_maxHeartbeats_2141_);
                crate::leanh::lean_ctor_set(v___x_2151_, 10, v_quotContext_2142_);
                crate::leanh::lean_ctor_set(v___x_2151_, 11, v_currMacroScope_2143_);
                crate::leanh::lean_ctor_set(v___x_2151_, 12, v_cancelTk_x3f_2145_);
                crate::leanh::lean_ctor_set(v___x_2151_, 13, v_inheritedTraceOptions_2147_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2151_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_2144_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2151_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_2146_,
                );
                v___x_2152_ =
                    l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_1857_, v___x_2151_);
                if crate::leanh::lean_obj_tag(v___x_2152_) == 0 {
                    v_a_2153_ = crate::leanh::lean_ctor_get(v___x_2152_, 0);
                    v_isSharedCheck_2180_ = (!crate::leanh::lean_is_exclusive(v___x_2152_)) as u8;
                    if v_isSharedCheck_2180_ == 0 {
                        v___x_2155_ = v___x_2152_;
                        v_isShared_2156_ = v_isSharedCheck_2180_;
                        state = 30;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2153_);
                        crate::leanh::lean_dec(v___x_2152_);
                        v___x_2155_ = crate::leanh::lean_box(0);
                        v_isShared_2156_ = v_isSharedCheck_2180_;
                        state = 30;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_2151_, 14);
                    crate::leanh::lean_dec_ref(v_inheritedTraceOptions_2147_);
                    crate::leanh::lean_dec_ref(v_options_2134_);
                    crate::leanh::lean_dec_ref(v_c_1856_);
                    v_a_2181_ = crate::leanh::lean_ctor_get(v___x_2152_, 0);
                    v_isSharedCheck_2188_ = (!crate::leanh::lean_is_exclusive(v___x_2152_)) as u8;
                    if v_isSharedCheck_2188_ == 0 {
                        v___x_2183_ = v___x_2152_;
                        v_isShared_2184_ = v_isSharedCheck_2188_;
                        state = 34;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2181_);
                        crate::leanh::lean_dec(v___x_2152_);
                        v___x_2183_ = crate::leanh::lean_box(0);
                        v_isShared_2184_ = v_isSharedCheck_2188_;
                        state = 34;
                        continue;
                    }
                }
            }
            30 => {
                v___x_2157_ = (crate::leanh::lean_unbox(v_a_2153_) as u8);
                crate::leanh::lean_dec(v_a_2153_);
                if v___x_2157_ == 0 {
                    crate::leanh::lean_del_object(v___x_2155_);
                    v_hasTrace_2158_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_2134_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v___x_2159_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0;
                    v___x_2160_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
                    v___x_2161_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
                    if v_hasTrace_2158_ == 0 {
                        crate::leanh::lean_dec_ref(v_inheritedTraceOptions_2147_);
                        crate::leanh::lean_dec_ref(v_options_2134_);
                        v___y_2046_ = v___x_2159_;
                        v___y_2047_ = v___x_2160_;
                        v___y_2048_ = v___x_2161_;
                        v___y_2049_ = v_a_1857_;
                        v___y_2050_ = v_a_1858_;
                        v___y_2051_ = v_a_1859_;
                        v___y_2052_ = v_a_1860_;
                        v___y_2053_ = v_a_1861_;
                        v___y_2054_ = v_a_1862_;
                        v___y_2055_ = v_a_1863_;
                        v___y_2056_ = v_a_1864_;
                        v___y_2057_ = v___x_2151_;
                        v___y_2058_ = v_a_1866_;
                        state = 20;
                        continue;
                    } else {
                        v___x_2162_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4;
                        v___x_2163_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_once
                            ),
                            _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5,
                        );
                        v___x_2164_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_2147_,
                            v_options_2134_,
                            v___x_2163_,
                        );
                        crate::leanh::lean_dec_ref(v_options_2134_);
                        crate::leanh::lean_dec_ref(v_inheritedTraceOptions_2147_);
                        if v___x_2164_ == 0 {
                            v___y_2046_ = v___x_2159_;
                            v___y_2047_ = v___x_2160_;
                            v___y_2048_ = v___x_2161_;
                            v___y_2049_ = v_a_1857_;
                            v___y_2050_ = v_a_1858_;
                            v___y_2051_ = v_a_1859_;
                            v___y_2052_ = v_a_1860_;
                            v___y_2053_ = v_a_1861_;
                            v___y_2054_ = v_a_1862_;
                            v___y_2055_ = v_a_1863_;
                            v___y_2056_ = v_a_1864_;
                            v___y_2057_ = v___x_2151_;
                            v___y_2058_ = v_a_1866_;
                            state = 20;
                            continue;
                        } else {
                            crate::leanh::lean_inc_ref(v_c_1856_);
                            v___x_2165_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(
                                v_c_1856_,
                                v_a_1857_,
                                v___x_2151_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2165_) == 0 {
                                v_a_2166_ = crate::leanh::lean_ctor_get(v___x_2165_, 0);
                                crate::leanh::lean_inc(v_a_2166_);
                                crate::leanh::lean_dec_ref_known(v___x_2165_, 1);
                                v___x_2167_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_2162_, v_a_2166_, v_a_1863_, v_a_1864_, v___x_2151_, v_a_1866_);
                                if crate::leanh::lean_obj_tag(v___x_2167_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_2167_, 1);
                                    v___y_2046_ = v___x_2159_;
                                    v___y_2047_ = v___x_2160_;
                                    v___y_2048_ = v___x_2161_;
                                    v___y_2049_ = v_a_1857_;
                                    v___y_2050_ = v_a_1858_;
                                    v___y_2051_ = v_a_1859_;
                                    v___y_2052_ = v_a_1860_;
                                    v___y_2053_ = v_a_1861_;
                                    v___y_2054_ = v_a_1862_;
                                    v___y_2055_ = v_a_1863_;
                                    v___y_2056_ = v_a_1864_;
                                    v___y_2057_ = v___x_2151_;
                                    v___y_2058_ = v_a_1866_;
                                    state = 20;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref_known(v___x_2151_, 14);
                                    crate::leanh::lean_dec_ref(v_c_1856_);
                                    return v___x_2167_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_2151_, 14);
                                crate::leanh::lean_dec_ref(v_c_1856_);
                                v_a_2168_ = crate::leanh::lean_ctor_get(v___x_2165_, 0);
                                v_isSharedCheck_2175_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2165_)) as u8;
                                if v_isSharedCheck_2175_ == 0 {
                                    v___x_2170_ = v___x_2165_;
                                    v_isShared_2171_ = v_isSharedCheck_2175_;
                                    state = 31;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2168_);
                                    crate::leanh::lean_dec(v___x_2165_);
                                    v___x_2170_ = crate::leanh::lean_box(0);
                                    v_isShared_2171_ = v_isSharedCheck_2175_;
                                    state = 31;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_2151_, 14);
                    crate::leanh::lean_dec_ref(v_inheritedTraceOptions_2147_);
                    crate::leanh::lean_dec_ref(v_options_2134_);
                    crate::leanh::lean_dec_ref(v_c_1856_);
                    v___x_2176_ = crate::leanh::lean_box(0);
                    if v_isShared_2156_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2155_, 0, v___x_2176_);
                        v___x_2178_ = v___x_2155_;
                        state = 33;
                        continue;
                    } else {
                        v_reuseFailAlloc_2179_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2176_);
                        v___x_2178_ = v_reuseFailAlloc_2179_;
                        state = 33;
                        continue;
                    }
                }
            }
            31 => {
                if v_isShared_2171_ == 0 {
                    v___x_2173_ = v___x_2170_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_2174_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
                    v___x_2173_ = v_reuseFailAlloc_2174_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_2173_;
            }
            33 => {
                return v___x_2178_;
            }
            34 => {
                if v_isShared_2184_ == 0 {
                    v___x_2186_ = v___x_2183_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2187_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
                    v___x_2186_ = v_reuseFailAlloc_2187_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_2186_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___boxed(
    mut v_c_2193_: *mut crate::leanh::LeanObject,
    mut v_a_2194_: *mut crate::leanh::LeanObject,
    mut v_a_2195_: *mut crate::leanh::LeanObject,
    mut v_a_2196_: *mut crate::leanh::LeanObject,
    mut v_a_2197_: *mut crate::leanh::LeanObject,
    mut v_a_2198_: *mut crate::leanh::LeanObject,
    mut v_a_2199_: *mut crate::leanh::LeanObject,
    mut v_a_2200_: *mut crate::leanh::LeanObject,
    mut v_a_2201_: *mut crate::leanh::LeanObject,
    mut v_a_2202_: *mut crate::leanh::LeanObject,
    mut v_a_2203_: *mut crate::leanh::LeanObject,
    mut v_a_2204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2205_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(
        v_c_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_,
        v_a_2201_, v_a_2202_, v_a_2203_,
    );
    crate::leanh::lean_dec(v_a_2203_);
    crate::leanh::lean_dec(v_a_2201_);
    crate::leanh::lean_dec_ref(v_a_2200_);
    crate::leanh::lean_dec(v_a_2199_);
    crate::leanh::lean_dec_ref(v_a_2198_);
    crate::leanh::lean_dec(v_a_2197_);
    crate::leanh::lean_dec_ref(v_a_2196_);
    crate::leanh::lean_dec(v_a_2195_);
    crate::leanh::lean_dec(v_a_2194_);
    return v_res_2205_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(
    mut v_c_2206_: *mut crate::leanh::LeanObject,
    mut v_a_2207_: *mut crate::leanh::LeanObject,
    mut v_a_2208_: *mut crate::leanh::LeanObject,
    mut v_a_2209_: *mut crate::leanh::LeanObject,
    mut v_a_2210_: *mut crate::leanh::LeanObject,
    mut v_a_2211_: *mut crate::leanh::LeanObject,
    mut v_a_2212_: *mut crate::leanh::LeanObject,
    mut v_a_2213_: *mut crate::leanh::LeanObject,
    mut v_a_2214_: *mut crate::leanh::LeanObject,
    mut v_a_2215_: *mut crate::leanh::LeanObject,
    mut v_a_2216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_d_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2234_: u8 = 0;
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2238_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_d_2218_ = crate::leanh::lean_ctor_get(v_c_2206_, 0);
                v_p_2219_ = crate::leanh::lean_ctor_get(v_c_2206_, 1);
                crate::leanh::lean_inc_ref(v_p_2219_);
                v___x_2220_ = l_Int_Linear_Poly_normCommRing_x3f(
                    v_p_2219_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_,
                    v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_,
                );
                if crate::leanh::lean_obj_tag(v___x_2220_) == 0 {
                    v_a_2221_ = crate::leanh::lean_ctor_get(v___x_2220_, 0);
                    crate::leanh::lean_inc(v_a_2221_);
                    crate::leanh::lean_dec_ref_known(v___x_2220_, 1);
                    if crate::leanh::lean_obj_tag(v_a_2221_) == 1 {
                        crate::leanh::lean_inc(v_d_2218_);
                        v_val_2222_ = crate::leanh::lean_ctor_get(v_a_2221_, 0);
                        crate::leanh::lean_inc(v_val_2222_);
                        crate::leanh::lean_dec_ref_known(v_a_2221_, 1);
                        v_snd_2223_ = crate::leanh::lean_ctor_get(v_val_2222_, 1);
                        crate::leanh::lean_inc(v_snd_2223_);
                        v_fst_2224_ = crate::leanh::lean_ctor_get(v_val_2222_, 0);
                        crate::leanh::lean_inc(v_fst_2224_);
                        crate::leanh::lean_dec(v_val_2222_);
                        v_fst_2225_ = crate::leanh::lean_ctor_get(v_snd_2223_, 0);
                        crate::leanh::lean_inc(v_fst_2225_);
                        v_snd_2226_ = crate::leanh::lean_ctor_get(v_snd_2223_, 1);
                        crate::leanh::lean_inc(v_snd_2226_);
                        crate::leanh::lean_dec(v_snd_2223_);
                        v___x_2227_ = crate::leanh::lean_alloc_ctor(12, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2227_, 0, v_c_2206_);
                        crate::leanh::lean_ctor_set(v___x_2227_, 1, v_fst_2224_);
                        crate::leanh::lean_ctor_set(v___x_2227_, 2, v_fst_2225_);
                        v___x_2228_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2228_, 0, v_d_2218_);
                        crate::leanh::lean_ctor_set(v___x_2228_, 1, v_snd_2226_);
                        crate::leanh::lean_ctor_set(v___x_2228_, 2, v___x_2227_);
                        crate::leanh::lean_inc_ref(v_a_2215_);
                        v___x_2229_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(
                            v___x_2228_,
                            v_a_2207_,
                            v_a_2208_,
                            v_a_2209_,
                            v_a_2210_,
                            v_a_2211_,
                            v_a_2212_,
                            v_a_2213_,
                            v_a_2214_,
                            v_a_2215_,
                            v_a_2216_,
                        );
                        return v___x_2229_;
                    } else {
                        crate::leanh::lean_dec(v_a_2221_);
                        crate::leanh::lean_inc_ref(v_a_2215_);
                        v___x_2230_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(
                            v_c_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_,
                            v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_,
                        );
                        return v___x_2230_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_c_2206_);
                    v_a_2231_ = crate::leanh::lean_ctor_get(v___x_2220_, 0);
                    v_isSharedCheck_2238_ = (!crate::leanh::lean_is_exclusive(v___x_2220_)) as u8;
                    if v_isSharedCheck_2238_ == 0 {
                        v___x_2233_ = v___x_2220_;
                        v_isShared_2234_ = v_isSharedCheck_2238_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2231_);
                        crate::leanh::lean_dec(v___x_2220_);
                        v___x_2233_ = crate::leanh::lean_box(0);
                        v_isShared_2234_ = v_isSharedCheck_2238_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2234_ == 0 {
                    v___x_2236_ = v___x_2233_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2237_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2231_);
                    v___x_2236_ = v_reuseFailAlloc_2237_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2236_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore___boxed(
    mut v_c_2239_: *mut crate::leanh::LeanObject,
    mut v_a_2240_: *mut crate::leanh::LeanObject,
    mut v_a_2241_: *mut crate::leanh::LeanObject,
    mut v_a_2242_: *mut crate::leanh::LeanObject,
    mut v_a_2243_: *mut crate::leanh::LeanObject,
    mut v_a_2244_: *mut crate::leanh::LeanObject,
    mut v_a_2245_: *mut crate::leanh::LeanObject,
    mut v_a_2246_: *mut crate::leanh::LeanObject,
    mut v_a_2247_: *mut crate::leanh::LeanObject,
    mut v_a_2248_: *mut crate::leanh::LeanObject,
    mut v_a_2249_: *mut crate::leanh::LeanObject,
    mut v_a_2250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2251_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v_c_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
    crate::leanh::lean_dec(v_a_2249_);
    crate::leanh::lean_dec_ref(v_a_2248_);
    crate::leanh::lean_dec(v_a_2247_);
    crate::leanh::lean_dec_ref(v_a_2246_);
    crate::leanh::lean_dec(v_a_2245_);
    crate::leanh::lean_dec_ref(v_a_2244_);
    crate::leanh::lean_dec(v_a_2243_);
    crate::leanh::lean_dec_ref(v_a_2242_);
    crate::leanh::lean_dec(v_a_2241_);
    crate::leanh::lean_dec(v_a_2240_);
    return v_res_2251_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2264_ = crate::leanh::lean_box(0);
    v___x_2265_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6;
    v___x_2266_ = l_Lean_mkConst(v___x_2265_, v___x_2264_);
    return v___x_2266_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2268_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8;
    v___x_2269_ = l_Lean_stringToMessageData(v___x_2268_);
    return v___x_2269_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(
    mut v_e_2270_: *mut crate::leanh::LeanObject,
    mut v_a_2271_: *mut crate::leanh::LeanObject,
    mut v_a_2272_: *mut crate::leanh::LeanObject,
    mut v_a_2273_: *mut crate::leanh::LeanObject,
    mut v_a_2274_: *mut crate::leanh::LeanObject,
    mut v_a_2275_: *mut crate::leanh::LeanObject,
    mut v_a_2276_: *mut crate::leanh::LeanObject,
    mut v_a_2277_: *mut crate::leanh::LeanObject,
    mut v_a_2278_: *mut crate::leanh::LeanObject,
    mut v_a_2279_: *mut crate::leanh::LeanObject,
    mut v_a_2280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2289_: u8 = 0;
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: u8 = 0;
    let mut v_arg_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: u8 = 0;
    let mut v_arg_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: u8 = 0;
    let mut v_arg_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: u8 = 0;
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: u8 = 0;
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2313_: u8 = 0;
    let mut v___x_2314_: u8 = 0;
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2324_: u8 = 0;
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: u8 = 0;
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2332_: u8 = 0;
    let mut v___x_2333_: u8 = 0;
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2349_: u8 = 0;
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2353_: u8 = 0;
    let mut v_isSharedCheck_2354_: u8 = 0;
    let mut v_a_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2358_: u8 = 0;
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2362_: u8 = 0;
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2373_: u8 = 0;
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2377_: u8 = 0;
    let mut v_a_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2381_: u8 = 0;
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2385_: u8 = 0;
    let mut v_isSharedCheck_2386_: u8 = 0;
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: u8 = 0;
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2397_: u8 = 0;
    let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2401_: u8 = 0;
    let mut v_a_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2405_: u8 = 0;
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2409_: u8 = 0;
    let mut v_isSharedCheck_2410_: u8 = 0;
    let mut v_a_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2414_: u8 = 0;
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2418_: u8 = 0;
    let mut v_isSharedCheck_2419_: u8 = 0;
    let mut v_a_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2423_: u8 = 0;
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2427_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_2270_);
                v___x_2285_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2270_, v_a_2278_);
                if crate::leanh::lean_obj_tag(v___x_2285_) == 0 {
                    v_a_2286_ = crate::leanh::lean_ctor_get(v___x_2285_, 0);
                    v_isSharedCheck_2419_ = (!crate::leanh::lean_is_exclusive(v___x_2285_)) as u8;
                    if v_isSharedCheck_2419_ == 0 {
                        v___x_2288_ = v___x_2285_;
                        v_isShared_2289_ = v_isSharedCheck_2419_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2286_);
                        crate::leanh::lean_dec(v___x_2285_);
                        v___x_2288_ = crate::leanh::lean_box(0);
                        v_isShared_2289_ = v_isSharedCheck_2419_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_2270_);
                    v_a_2420_ = crate::leanh::lean_ctor_get(v___x_2285_, 0);
                    v_isSharedCheck_2427_ = (!crate::leanh::lean_is_exclusive(v___x_2285_)) as u8;
                    if v_isSharedCheck_2427_ == 0 {
                        v___x_2422_ = v___x_2285_;
                        v_isShared_2423_ = v_isSharedCheck_2427_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2420_);
                        crate::leanh::lean_dec(v___x_2285_);
                        v___x_2422_ = crate::leanh::lean_box(0);
                        v_isShared_2423_ = v_isSharedCheck_2427_;
                        state = 25;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2283_ = crate::leanh::lean_box(0);
                v___x_2284_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2284_, 0, v___x_2283_);
                return v___x_2284_;
            }
            2 => {
                v___x_2295_ = l_Lean_Expr_cleanupAnnotations(v_a_2286_);
                v___x_2296_ = l_Lean_Expr_isApp(v___x_2295_);
                if v___x_2296_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2295_);
                    crate::leanh::lean_dec_ref(v_e_2270_);
                    state = 3;
                    continue;
                } else {
                    v_arg_2297_ = crate::leanh::lean_ctor_get(v___x_2295_, 1);
                    crate::leanh::lean_inc_ref(v_arg_2297_);
                    v___x_2298_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2295_);
                    v___x_2299_ = l_Lean_Expr_isApp(v___x_2298_);
                    if v___x_2299_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2298_);
                        crate::leanh::lean_dec_ref(v_arg_2297_);
                        crate::leanh::lean_dec_ref(v_e_2270_);
                        state = 3;
                        continue;
                    } else {
                        v_arg_2300_ = crate::leanh::lean_ctor_get(v___x_2298_, 1);
                        crate::leanh::lean_inc_ref(v_arg_2300_);
                        v___x_2301_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2298_);
                        v___x_2302_ = l_Lean_Expr_isApp(v___x_2301_);
                        if v___x_2302_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2301_);
                            crate::leanh::lean_dec_ref(v_arg_2300_);
                            crate::leanh::lean_dec_ref(v_arg_2297_);
                            crate::leanh::lean_dec_ref(v_e_2270_);
                            state = 3;
                            continue;
                        } else {
                            v_arg_2303_ = crate::leanh::lean_ctor_get(v___x_2301_, 1);
                            crate::leanh::lean_inc_ref(v_arg_2303_);
                            v___x_2304_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2301_);
                            v___x_2305_ = l_Lean_Expr_isApp(v___x_2304_);
                            if v___x_2305_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_2304_);
                                crate::leanh::lean_dec_ref(v_arg_2303_);
                                crate::leanh::lean_dec_ref(v_arg_2300_);
                                crate::leanh::lean_dec_ref(v_arg_2297_);
                                crate::leanh::lean_dec_ref(v_e_2270_);
                                state = 3;
                                continue;
                            } else {
                                v___x_2306_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2304_);
                                v___x_2307_ =
                                    l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
                                v___x_2308_ = l_Lean_Expr_isConstOf(v___x_2306_, v___x_2307_);
                                crate::leanh::lean_dec_ref(v___x_2306_);
                                if v___x_2308_ == 0 {
                                    crate::leanh::lean_dec_ref(v_arg_2303_);
                                    crate::leanh::lean_dec_ref(v_arg_2300_);
                                    crate::leanh::lean_dec_ref(v_arg_2297_);
                                    crate::leanh::lean_dec_ref(v_e_2270_);
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_del_object(v___x_2288_);
                                    v___x_2309_ = l_Lean_Meta_Structural_isInstDvdInt___redArg(
                                        v_arg_2303_,
                                        v_a_2278_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2309_) == 0 {
                                        v_a_2310_ = crate::leanh::lean_ctor_get(v___x_2309_, 0);
                                        v_isSharedCheck_2410_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2309_)) as u8;
                                        if v_isSharedCheck_2410_ == 0 {
                                            v___x_2312_ = v___x_2309_;
                                            v_isShared_2313_ = v_isSharedCheck_2410_;
                                            state = 5;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2310_);
                                            crate::leanh::lean_dec(v___x_2309_);
                                            v___x_2312_ = crate::leanh::lean_box(0);
                                            v_isShared_2313_ = v_isSharedCheck_2410_;
                                            state = 5;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_arg_2300_);
                                        crate::leanh::lean_dec_ref(v_arg_2297_);
                                        crate::leanh::lean_dec_ref(v_e_2270_);
                                        v_a_2411_ = crate::leanh::lean_ctor_get(v___x_2309_, 0);
                                        v_isSharedCheck_2418_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2309_)) as u8;
                                        if v_isSharedCheck_2418_ == 0 {
                                            v___x_2413_ = v___x_2309_;
                                            v_isShared_2414_ = v_isSharedCheck_2418_;
                                            state = 23;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2411_);
                                            crate::leanh::lean_dec(v___x_2309_);
                                            v___x_2413_ = crate::leanh::lean_box(0);
                                            v_isShared_2414_ = v_isSharedCheck_2418_;
                                            state = 23;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_2291_ = crate::leanh::lean_box(0);
                if v_isShared_2289_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2288_, 0, v___x_2291_);
                    v___x_2293_ = v___x_2288_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2294_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2294_, 0, v___x_2291_);
                    v___x_2293_ = v_reuseFailAlloc_2294_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2293_;
            }
            5 => {
                v___x_2314_ = (crate::leanh::lean_unbox(v_a_2310_) as u8);
                crate::leanh::lean_dec(v_a_2310_);
                if v___x_2314_ == 0 {
                    crate::leanh::lean_dec_ref(v_arg_2300_);
                    crate::leanh::lean_dec_ref(v_arg_2297_);
                    crate::leanh::lean_dec_ref(v_e_2270_);
                    v___x_2315_ = crate::leanh::lean_box(0);
                    if v_isShared_2313_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2312_, 0, v___x_2315_);
                        v___x_2317_ = v___x_2312_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2318_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2315_);
                        v___x_2317_ = v_reuseFailAlloc_2318_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2312_);
                    crate::leanh::lean_inc_ref(v_arg_2300_);
                    v___x_2319_ = l_Lean_Meta_getIntValue_x3f(
                        v_arg_2300_,
                        v_a_2277_,
                        v_a_2278_,
                        v_a_2279_,
                        v_a_2280_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2319_) == 0 {
                        v_a_2320_ = crate::leanh::lean_ctor_get(v___x_2319_, 0);
                        crate::leanh::lean_inc(v_a_2320_);
                        crate::leanh::lean_dec_ref_known(v___x_2319_, 1);
                        if crate::leanh::lean_obj_tag(v_a_2320_) == 1 {
                            v_val_2321_ = crate::leanh::lean_ctor_get(v_a_2320_, 0);
                            v_isSharedCheck_2386_ =
                                (!crate::leanh::lean_is_exclusive(v_a_2320_)) as u8;
                            if v_isSharedCheck_2386_ == 0 {
                                v___x_2323_ = v_a_2320_;
                                v_isShared_2324_ = v_isSharedCheck_2386_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_2321_);
                                crate::leanh::lean_dec(v_a_2320_);
                                v___x_2323_ = crate::leanh::lean_box(0);
                                v_isShared_2324_ = v_isSharedCheck_2386_;
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2320_);
                            crate::leanh::lean_dec_ref(v_arg_2300_);
                            crate::leanh::lean_dec_ref(v_arg_2297_);
                            v___x_2387_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2275_);
                            if crate::leanh::lean_obj_tag(v___x_2387_) == 0 {
                                v_a_2388_ = crate::leanh::lean_ctor_get(v___x_2387_, 0);
                                crate::leanh::lean_inc(v_a_2388_);
                                crate::leanh::lean_dec_ref_known(v___x_2387_, 1);
                                v___x_2389_ = (crate::leanh::lean_unbox(v_a_2388_) as u8);
                                crate::leanh::lean_dec(v_a_2388_);
                                if v___x_2389_ == 0 {
                                    crate::leanh::lean_dec_ref(v_e_2270_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_2390_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9);
                                    v___x_2391_ = l_Lean_indentExpr(v_e_2270_);
                                    v___x_2392_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_2392_, 0, v___x_2390_);
                                    crate::leanh::lean_ctor_set(v___x_2392_, 1, v___x_2391_);
                                    v___x_2393_ = l_Lean_Meta_Sym_reportIssue(
                                        v___x_2392_,
                                        v_a_2275_,
                                        v_a_2276_,
                                        v_a_2277_,
                                        v_a_2278_,
                                        v_a_2279_,
                                        v_a_2280_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2393_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_2393_, 1);
                                        state = 1;
                                        continue;
                                    } else {
                                        return v___x_2393_;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_e_2270_);
                                v_a_2394_ = crate::leanh::lean_ctor_get(v___x_2387_, 0);
                                v_isSharedCheck_2401_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2387_)) as u8;
                                if v_isSharedCheck_2401_ == 0 {
                                    v___x_2396_ = v___x_2387_;
                                    v_isShared_2397_ = v_isSharedCheck_2401_;
                                    state = 19;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2394_);
                                    crate::leanh::lean_dec(v___x_2387_);
                                    v___x_2396_ = crate::leanh::lean_box(0);
                                    v_isShared_2397_ = v_isSharedCheck_2401_;
                                    state = 19;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_2300_);
                        crate::leanh::lean_dec_ref(v_arg_2297_);
                        crate::leanh::lean_dec_ref(v_e_2270_);
                        v_a_2402_ = crate::leanh::lean_ctor_get(v___x_2319_, 0);
                        v_isSharedCheck_2409_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2319_)) as u8;
                        if v_isSharedCheck_2409_ == 0 {
                            v___x_2404_ = v___x_2319_;
                            v_isShared_2405_ = v_isSharedCheck_2409_;
                            state = 21;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2402_);
                            crate::leanh::lean_dec(v___x_2319_);
                            v___x_2404_ = crate::leanh::lean_box(0);
                            v_isShared_2405_ = v_isSharedCheck_2409_;
                            state = 21;
                            continue;
                        }
                    }
                }
            }
            6 => {
                return v___x_2317_;
            }
            7 => {
                crate::leanh::lean_inc_ref(v_e_2270_);
                v___x_2325_ = l_Lean_Meta_Grind_isEqTrue___redArg(
                    v_e_2270_, v_a_2271_, v_a_2275_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_,
                );
                if crate::leanh::lean_obj_tag(v___x_2325_) == 0 {
                    v_a_2326_ = crate::leanh::lean_ctor_get(v___x_2325_, 0);
                    crate::leanh::lean_inc(v_a_2326_);
                    crate::leanh::lean_dec_ref_known(v___x_2325_, 1);
                    v___x_2327_ = (crate::leanh::lean_unbox(v_a_2326_) as u8);
                    crate::leanh::lean_dec(v_a_2326_);
                    if v___x_2327_ == 0 {
                        crate::leanh::lean_del_object(v___x_2323_);
                        crate::leanh::lean_dec(v_val_2321_);
                        crate::leanh::lean_inc_ref(v_e_2270_);
                        v___x_2328_ = l_Lean_Meta_Grind_isEqFalse___redArg(
                            v_e_2270_, v_a_2271_, v_a_2275_, v_a_2277_, v_a_2278_, v_a_2279_,
                            v_a_2280_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2328_) == 0 {
                            v_a_2329_ = crate::leanh::lean_ctor_get(v___x_2328_, 0);
                            v_isSharedCheck_2354_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2328_)) as u8;
                            if v_isSharedCheck_2354_ == 0 {
                                v___x_2331_ = v___x_2328_;
                                v_isShared_2332_ = v_isSharedCheck_2354_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2329_);
                                crate::leanh::lean_dec(v___x_2328_);
                                v___x_2331_ = crate::leanh::lean_box(0);
                                v_isShared_2332_ = v_isSharedCheck_2354_;
                                state = 8;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_arg_2300_);
                            crate::leanh::lean_dec_ref(v_arg_2297_);
                            crate::leanh::lean_dec_ref(v_e_2270_);
                            v_a_2355_ = crate::leanh::lean_ctor_get(v___x_2328_, 0);
                            v_isSharedCheck_2362_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2328_)) as u8;
                            if v_isSharedCheck_2362_ == 0 {
                                v___x_2357_ = v___x_2328_;
                                v_isShared_2358_ = v_isSharedCheck_2362_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2355_);
                                crate::leanh::lean_dec(v___x_2328_);
                                v___x_2357_ = crate::leanh::lean_box(0);
                                v_isShared_2358_ = v_isSharedCheck_2362_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_2300_);
                        v___x_2363_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(
                            v_arg_2297_,
                            v_a_2271_,
                            v_a_2272_,
                            v_a_2273_,
                            v_a_2274_,
                            v_a_2275_,
                            v_a_2276_,
                            v_a_2277_,
                            v_a_2278_,
                            v_a_2279_,
                            v_a_2280_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2363_) == 0 {
                            v_a_2364_ = crate::leanh::lean_ctor_get(v___x_2363_, 0);
                            crate::leanh::lean_inc(v_a_2364_);
                            crate::leanh::lean_dec_ref_known(v___x_2363_, 1);
                            if v_isShared_2324_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_2323_, 0);
                                crate::leanh::lean_ctor_set(v___x_2323_, 0, v_e_2270_);
                                v___x_2366_ = v___x_2323_;
                                state = 14;
                                continue;
                            } else {
                                v_reuseFailAlloc_2369_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_e_2270_);
                                v___x_2366_ = v_reuseFailAlloc_2369_;
                                state = 14;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_2323_);
                            crate::leanh::lean_dec(v_val_2321_);
                            crate::leanh::lean_dec_ref(v_e_2270_);
                            v_a_2370_ = crate::leanh::lean_ctor_get(v___x_2363_, 0);
                            v_isSharedCheck_2377_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2363_)) as u8;
                            if v_isSharedCheck_2377_ == 0 {
                                v___x_2372_ = v___x_2363_;
                                v_isShared_2373_ = v_isSharedCheck_2377_;
                                state = 15;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2370_);
                                crate::leanh::lean_dec(v___x_2363_);
                                v___x_2372_ = crate::leanh::lean_box(0);
                                v_isShared_2373_ = v_isSharedCheck_2377_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2323_);
                    crate::leanh::lean_dec(v_val_2321_);
                    crate::leanh::lean_dec_ref(v_arg_2300_);
                    crate::leanh::lean_dec_ref(v_arg_2297_);
                    crate::leanh::lean_dec_ref(v_e_2270_);
                    v_a_2378_ = crate::leanh::lean_ctor_get(v___x_2325_, 0);
                    v_isSharedCheck_2385_ = (!crate::leanh::lean_is_exclusive(v___x_2325_)) as u8;
                    if v_isSharedCheck_2385_ == 0 {
                        v___x_2380_ = v___x_2325_;
                        v_isShared_2381_ = v_isSharedCheck_2385_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2378_);
                        crate::leanh::lean_dec(v___x_2325_);
                        v___x_2380_ = crate::leanh::lean_box(0);
                        v_isShared_2381_ = v_isSharedCheck_2385_;
                        state = 17;
                        continue;
                    }
                }
            }
            8 => {
                v___x_2333_ = (crate::leanh::lean_unbox(v_a_2329_) as u8);
                crate::leanh::lean_dec(v_a_2329_);
                if v___x_2333_ == 0 {
                    crate::leanh::lean_dec_ref(v_arg_2300_);
                    crate::leanh::lean_dec_ref(v_arg_2297_);
                    crate::leanh::lean_dec_ref(v_e_2270_);
                    v___x_2334_ = crate::leanh::lean_box(0);
                    if v_isShared_2332_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2331_, 0, v___x_2334_);
                        v___x_2336_ = v___x_2331_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2337_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2337_, 0, v___x_2334_);
                        v___x_2336_ = v_reuseFailAlloc_2337_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2331_);
                    crate::leanh::lean_inc_ref(v_e_2270_);
                    v___x_2338_ = l_Lean_Meta_Grind_mkEqFalseProof(
                        v_e_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_,
                        v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2338_) == 0 {
                        v_a_2339_ = crate::leanh::lean_ctor_get(v___x_2338_, 0);
                        crate::leanh::lean_inc(v_a_2339_);
                        crate::leanh::lean_dec_ref_known(v___x_2338_, 1);
                        v___x_2340_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7_once
                            ),
                            _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7,
                        );
                        v___x_2341_ = l_Lean_eagerReflBoolTrue;
                        v___x_2342_ = l_Lean_Meta_mkOfEqFalseCore(v_e_2270_, v_a_2339_);
                        v___x_2343_ = l_Lean_mkApp4(
                            v___x_2340_,
                            v_arg_2300_,
                            v_arg_2297_,
                            v___x_2341_,
                            v___x_2342_,
                        );
                        v___x_2344_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2345_ = l_Lean_Meta_Grind_pushNewFact(
                            v___x_2343_,
                            v___x_2344_,
                            v_a_2271_,
                            v_a_2272_,
                            v_a_2273_,
                            v_a_2274_,
                            v_a_2275_,
                            v_a_2276_,
                            v_a_2277_,
                            v_a_2278_,
                            v_a_2279_,
                            v_a_2280_,
                        );
                        return v___x_2345_;
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_2300_);
                        crate::leanh::lean_dec_ref(v_arg_2297_);
                        crate::leanh::lean_dec_ref(v_e_2270_);
                        v_a_2346_ = crate::leanh::lean_ctor_get(v___x_2338_, 0);
                        v_isSharedCheck_2353_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2338_)) as u8;
                        if v_isSharedCheck_2353_ == 0 {
                            v___x_2348_ = v___x_2338_;
                            v_isShared_2349_ = v_isSharedCheck_2353_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2346_);
                            crate::leanh::lean_dec(v___x_2338_);
                            v___x_2348_ = crate::leanh::lean_box(0);
                            v_isShared_2349_ = v_isSharedCheck_2353_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            9 => {
                return v___x_2336_;
            }
            10 => {
                if v_isShared_2349_ == 0 {
                    v___x_2351_ = v___x_2348_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2352_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
                    v___x_2351_ = v_reuseFailAlloc_2352_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2351_;
            }
            12 => {
                if v_isShared_2358_ == 0 {
                    v___x_2360_ = v___x_2357_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2361_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
                    v___x_2360_ = v_reuseFailAlloc_2361_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2360_;
            }
            14 => {
                v___x_2367_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2367_, 0, v_val_2321_);
                crate::leanh::lean_ctor_set(v___x_2367_, 1, v_a_2364_);
                crate::leanh::lean_ctor_set(v___x_2367_, 2, v___x_2366_);
                v___x_2368_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_2367_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_);
                return v___x_2368_;
            }
            15 => {
                if v_isShared_2373_ == 0 {
                    v___x_2375_ = v___x_2372_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2376_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2370_);
                    v___x_2375_ = v_reuseFailAlloc_2376_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2375_;
            }
            17 => {
                if v_isShared_2381_ == 0 {
                    v___x_2383_ = v___x_2380_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2384_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_a_2378_);
                    v___x_2383_ = v_reuseFailAlloc_2384_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2383_;
            }
            19 => {
                if v_isShared_2397_ == 0 {
                    v___x_2399_ = v___x_2396_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2400_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2394_);
                    v___x_2399_ = v_reuseFailAlloc_2400_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2399_;
            }
            21 => {
                if v_isShared_2405_ == 0 {
                    v___x_2407_ = v___x_2404_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2408_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2402_);
                    v___x_2407_ = v_reuseFailAlloc_2408_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2407_;
            }
            23 => {
                if v_isShared_2414_ == 0 {
                    v___x_2416_ = v___x_2413_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2417_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2411_);
                    v___x_2416_ = v_reuseFailAlloc_2417_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2416_;
            }
            25 => {
                if v_isShared_2423_ == 0 {
                    v___x_2425_ = v___x_2422_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_2426_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_a_2420_);
                    v___x_2425_ = v_reuseFailAlloc_2426_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_2425_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___boxed(
    mut v_e_2428_: *mut crate::leanh::LeanObject,
    mut v_a_2429_: *mut crate::leanh::LeanObject,
    mut v_a_2430_: *mut crate::leanh::LeanObject,
    mut v_a_2431_: *mut crate::leanh::LeanObject,
    mut v_a_2432_: *mut crate::leanh::LeanObject,
    mut v_a_2433_: *mut crate::leanh::LeanObject,
    mut v_a_2434_: *mut crate::leanh::LeanObject,
    mut v_a_2435_: *mut crate::leanh::LeanObject,
    mut v_a_2436_: *mut crate::leanh::LeanObject,
    mut v_a_2437_: *mut crate::leanh::LeanObject,
    mut v_a_2438_: *mut crate::leanh::LeanObject,
    mut v_a_2439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2440_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(
        v_e_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_,
        v_a_2436_, v_a_2437_, v_a_2438_,
    );
    crate::leanh::lean_dec(v_a_2438_);
    crate::leanh::lean_dec_ref(v_a_2437_);
    crate::leanh::lean_dec(v_a_2436_);
    crate::leanh::lean_dec_ref(v_a_2435_);
    crate::leanh::lean_dec(v_a_2434_);
    crate::leanh::lean_dec_ref(v_a_2433_);
    crate::leanh::lean_dec(v_a_2432_);
    crate::leanh::lean_dec_ref(v_a_2431_);
    crate::leanh::lean_dec(v_a_2430_);
    crate::leanh::lean_dec(v_a_2429_);
    return v_res_2440_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd_spec__0(
    mut v_a_2441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2442_ = lean_nat_to_int(v_a_2441_);
    return v___x_2442_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2448_ = crate::leanh::lean_box(0);
    v___x_2449_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2;
    v___x_2450_ = l_Lean_mkConst(v___x_2449_, v___x_2448_);
    return v___x_2450_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2457_ = crate::leanh::lean_box(0);
    v___x_2458_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6;
    v___x_2459_ = l_Lean_mkConst(v___x_2458_, v___x_2457_);
    return v___x_2459_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(
    mut v_e_2460_: *mut crate::leanh::LeanObject,
    mut v_a_2461_: *mut crate::leanh::LeanObject,
    mut v_a_2462_: *mut crate::leanh::LeanObject,
    mut v_a_2463_: *mut crate::leanh::LeanObject,
    mut v_a_2464_: *mut crate::leanh::LeanObject,
    mut v_a_2465_: *mut crate::leanh::LeanObject,
    mut v_a_2466_: *mut crate::leanh::LeanObject,
    mut v_a_2467_: *mut crate::leanh::LeanObject,
    mut v_a_2468_: *mut crate::leanh::LeanObject,
    mut v_a_2469_: *mut crate::leanh::LeanObject,
    mut v_a_2470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: u8 = 0;
    let mut v_arg_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: u8 = 0;
    let mut v_arg_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: u8 = 0;
    let mut v_arg_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: u8 = 0;
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: u8 = 0;
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2496_: u8 = 0;
    let mut v___x_2497_: u8 = 0;
    let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: u8 = 0;
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2512_: u8 = 0;
    let mut v___x_2513_: u8 = 0;
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2528_: u8 = 0;
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2532_: u8 = 0;
    let mut v_isSharedCheck_2533_: u8 = 0;
    let mut v_a_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2537_: u8 = 0;
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2541_: u8 = 0;
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2564_: u8 = 0;
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2568_: u8 = 0;
    let mut v_a_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2572_: u8 = 0;
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2576_: u8 = 0;
    let mut v_a_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2580_: u8 = 0;
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2584_: u8 = 0;
    let mut v_a_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2588_: u8 = 0;
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2592_: u8 = 0;
    let mut v_a_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2596_: u8 = 0;
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2600_: u8 = 0;
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: u8 = 0;
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2611_: u8 = 0;
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2615_: u8 = 0;
    let mut v_a_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2619_: u8 = 0;
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2623_: u8 = 0;
    let mut v_isSharedCheck_2624_: u8 = 0;
    let mut v_a_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2628_: u8 = 0;
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2632_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_2460_);
                v___x_2478_ = l_Lean_Expr_cleanupAnnotations(v_e_2460_);
                v___x_2479_ = l_Lean_Expr_isApp(v___x_2478_);
                if v___x_2479_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2478_);
                    crate::leanh::lean_dec_ref(v_e_2460_);
                    state = 1;
                    continue;
                } else {
                    v_arg_2480_ = crate::leanh::lean_ctor_get(v___x_2478_, 1);
                    crate::leanh::lean_inc_ref(v_arg_2480_);
                    v___x_2481_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2478_);
                    v___x_2482_ = l_Lean_Expr_isApp(v___x_2481_);
                    if v___x_2482_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2481_);
                        crate::leanh::lean_dec_ref(v_arg_2480_);
                        crate::leanh::lean_dec_ref(v_e_2460_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_2483_ = crate::leanh::lean_ctor_get(v___x_2481_, 1);
                        crate::leanh::lean_inc_ref(v_arg_2483_);
                        v___x_2484_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2481_);
                        v___x_2485_ = l_Lean_Expr_isApp(v___x_2484_);
                        if v___x_2485_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2484_);
                            crate::leanh::lean_dec_ref(v_arg_2483_);
                            crate::leanh::lean_dec_ref(v_arg_2480_);
                            crate::leanh::lean_dec_ref(v_e_2460_);
                            state = 1;
                            continue;
                        } else {
                            v_arg_2486_ = crate::leanh::lean_ctor_get(v___x_2484_, 1);
                            crate::leanh::lean_inc_ref(v_arg_2486_);
                            v___x_2487_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2484_);
                            v___x_2488_ = l_Lean_Expr_isApp(v___x_2487_);
                            if v___x_2488_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_2487_);
                                crate::leanh::lean_dec_ref(v_arg_2486_);
                                crate::leanh::lean_dec_ref(v_arg_2483_);
                                crate::leanh::lean_dec_ref(v_arg_2480_);
                                crate::leanh::lean_dec_ref(v_e_2460_);
                                state = 1;
                                continue;
                            } else {
                                v___x_2489_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2487_);
                                v___x_2490_ =
                                    l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
                                v___x_2491_ = l_Lean_Expr_isConstOf(v___x_2489_, v___x_2490_);
                                crate::leanh::lean_dec_ref(v___x_2489_);
                                if v___x_2491_ == 0 {
                                    crate::leanh::lean_dec_ref(v_arg_2486_);
                                    crate::leanh::lean_dec_ref(v_arg_2483_);
                                    crate::leanh::lean_dec_ref(v_arg_2480_);
                                    crate::leanh::lean_dec_ref(v_e_2460_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_2492_ = l_Lean_Meta_Structural_isInstDvdNat___redArg(
                                        v_arg_2486_,
                                        v_a_2468_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2492_) == 0 {
                                        v_a_2493_ = crate::leanh::lean_ctor_get(v___x_2492_, 0);
                                        v_isSharedCheck_2624_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2492_)) as u8;
                                        if v_isSharedCheck_2624_ == 0 {
                                            v___x_2495_ = v___x_2492_;
                                            v_isShared_2496_ = v_isSharedCheck_2624_;
                                            state = 3;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2493_);
                                            crate::leanh::lean_dec(v___x_2492_);
                                            v___x_2495_ = crate::leanh::lean_box(0);
                                            v_isShared_2496_ = v_isSharedCheck_2624_;
                                            state = 3;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_arg_2483_);
                                        crate::leanh::lean_dec_ref(v_arg_2480_);
                                        crate::leanh::lean_dec_ref(v_e_2460_);
                                        v_a_2625_ = crate::leanh::lean_ctor_get(v___x_2492_, 0);
                                        v_isSharedCheck_2632_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2492_)) as u8;
                                        if v_isSharedCheck_2632_ == 0 {
                                            v___x_2627_ = v___x_2492_;
                                            v_isShared_2628_ = v_isSharedCheck_2632_;
                                            state = 25;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2625_);
                                            crate::leanh::lean_dec(v___x_2492_);
                                            v___x_2627_ = crate::leanh::lean_box(0);
                                            v_isShared_2628_ = v_isSharedCheck_2632_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2473_ = crate::leanh::lean_box(0);
                v___x_2474_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2474_, 0, v___x_2473_);
                return v___x_2474_;
            }
            2 => {
                v___x_2476_ = crate::leanh::lean_box(0);
                v___x_2477_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2477_, 0, v___x_2476_);
                return v___x_2477_;
            }
            3 => {
                v___x_2497_ = (crate::leanh::lean_unbox(v_a_2493_) as u8);
                crate::leanh::lean_dec(v_a_2493_);
                if v___x_2497_ == 0 {
                    crate::leanh::lean_dec_ref(v_arg_2483_);
                    crate::leanh::lean_dec_ref(v_arg_2480_);
                    crate::leanh::lean_dec_ref(v_e_2460_);
                    v___x_2498_ = crate::leanh::lean_box(0);
                    if v_isShared_2496_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2495_, 0, v___x_2498_);
                        v___x_2500_ = v___x_2495_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2501_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2498_);
                        v___x_2500_ = v_reuseFailAlloc_2501_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2495_);
                    v___x_2502_ = l_Lean_Meta_getNatValue_x3f(
                        v_arg_2483_,
                        v_a_2467_,
                        v_a_2468_,
                        v_a_2469_,
                        v_a_2470_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2502_) == 0 {
                        v_a_2503_ = crate::leanh::lean_ctor_get(v___x_2502_, 0);
                        crate::leanh::lean_inc(v_a_2503_);
                        crate::leanh::lean_dec_ref_known(v___x_2502_, 1);
                        if crate::leanh::lean_obj_tag(v_a_2503_) == 1 {
                            v_val_2504_ = crate::leanh::lean_ctor_get(v_a_2503_, 0);
                            crate::leanh::lean_inc(v_val_2504_);
                            crate::leanh::lean_dec_ref_known(v_a_2503_, 1);
                            crate::leanh::lean_inc_ref(v_e_2460_);
                            v___x_2505_ = l_Lean_Meta_Grind_isEqTrue___redArg(
                                v_e_2460_, v_a_2461_, v_a_2465_, v_a_2467_, v_a_2468_, v_a_2469_,
                                v_a_2470_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2505_) == 0 {
                                v_a_2506_ = crate::leanh::lean_ctor_get(v___x_2505_, 0);
                                crate::leanh::lean_inc(v_a_2506_);
                                crate::leanh::lean_dec_ref_known(v___x_2505_, 1);
                                v___x_2507_ = (crate::leanh::lean_unbox(v_a_2506_) as u8);
                                crate::leanh::lean_dec(v_a_2506_);
                                if v___x_2507_ == 0 {
                                    crate::leanh::lean_dec(v_val_2504_);
                                    crate::leanh::lean_inc_ref(v_e_2460_);
                                    v___x_2508_ = l_Lean_Meta_Grind_isEqFalse___redArg(
                                        v_e_2460_, v_a_2461_, v_a_2465_, v_a_2467_, v_a_2468_,
                                        v_a_2469_, v_a_2470_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2508_) == 0 {
                                        v_a_2509_ = crate::leanh::lean_ctor_get(v___x_2508_, 0);
                                        v_isSharedCheck_2533_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2508_)) as u8;
                                        if v_isSharedCheck_2533_ == 0 {
                                            v___x_2511_ = v___x_2508_;
                                            v_isShared_2512_ = v_isSharedCheck_2533_;
                                            state = 5;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2509_);
                                            crate::leanh::lean_dec(v___x_2508_);
                                            v___x_2511_ = crate::leanh::lean_box(0);
                                            v_isShared_2512_ = v_isSharedCheck_2533_;
                                            state = 5;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_arg_2483_);
                                        crate::leanh::lean_dec_ref(v_arg_2480_);
                                        crate::leanh::lean_dec_ref(v_e_2460_);
                                        v_a_2534_ = crate::leanh::lean_ctor_get(v___x_2508_, 0);
                                        v_isSharedCheck_2541_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2508_)) as u8;
                                        if v_isSharedCheck_2541_ == 0 {
                                            v___x_2536_ = v___x_2508_;
                                            v_isShared_2537_ = v_isSharedCheck_2541_;
                                            state = 9;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2534_);
                                            crate::leanh::lean_dec(v___x_2508_);
                                            v___x_2536_ = crate::leanh::lean_box(0);
                                            v_isShared_2537_ = v_isSharedCheck_2541_;
                                            state = 9;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_inc_ref(v_arg_2483_);
                                    v___x_2542_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(
                                        v_arg_2483_,
                                        v_a_2461_,
                                        v_a_2462_,
                                        v_a_2463_,
                                        v_a_2464_,
                                        v_a_2465_,
                                        v_a_2466_,
                                        v_a_2467_,
                                        v_a_2468_,
                                        v_a_2469_,
                                        v_a_2470_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2542_) == 0 {
                                        v_a_2543_ = crate::leanh::lean_ctor_get(v___x_2542_, 0);
                                        crate::leanh::lean_inc(v_a_2543_);
                                        crate::leanh::lean_dec_ref_known(v___x_2542_, 1);
                                        v_fst_2544_ = crate::leanh::lean_ctor_get(v_a_2543_, 0);
                                        crate::leanh::lean_inc(v_fst_2544_);
                                        v_snd_2545_ = crate::leanh::lean_ctor_get(v_a_2543_, 1);
                                        crate::leanh::lean_inc(v_snd_2545_);
                                        crate::leanh::lean_dec(v_a_2543_);
                                        crate::leanh::lean_inc_ref(v_arg_2480_);
                                        v___x_2546_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(
                                            v_arg_2480_,
                                            v_a_2461_,
                                            v_a_2462_,
                                            v_a_2463_,
                                            v_a_2464_,
                                            v_a_2465_,
                                            v_a_2466_,
                                            v_a_2467_,
                                            v_a_2468_,
                                            v_a_2469_,
                                            v_a_2470_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_2546_) == 0 {
                                            v_a_2547_ = crate::leanh::lean_ctor_get(v___x_2546_, 0);
                                            crate::leanh::lean_inc(v_a_2547_);
                                            crate::leanh::lean_dec_ref_known(v___x_2546_, 1);
                                            v_fst_2548_ = crate::leanh::lean_ctor_get(v_a_2547_, 0);
                                            crate::leanh::lean_inc(v_fst_2548_);
                                            v_snd_2549_ = crate::leanh::lean_ctor_get(v_a_2547_, 1);
                                            crate::leanh::lean_inc(v_snd_2549_);
                                            crate::leanh::lean_dec(v_a_2547_);
                                            v___x_2550_ = l_Lean_Meta_Grind_getGeneration___redArg(
                                                v_e_2460_, v_a_2461_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_2550_) == 0 {
                                                v_a_2551_ =
                                                    crate::leanh::lean_ctor_get(v___x_2550_, 0);
                                                crate::leanh::lean_inc(v_a_2551_);
                                                crate::leanh::lean_dec_ref_known(v___x_2550_, 1);
                                                crate::leanh::lean_inc(v_fst_2548_);
                                                v___x_2552_ =
                                                    l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(
                                                        v_fst_2548_,
                                                        v_a_2551_,
                                                        v_a_2461_,
                                                        v_a_2462_,
                                                        v_a_2463_,
                                                        v_a_2464_,
                                                        v_a_2465_,
                                                        v_a_2466_,
                                                        v_a_2467_,
                                                        v_a_2468_,
                                                        v_a_2469_,
                                                        v_a_2470_,
                                                    );
                                                if crate::leanh::lean_obj_tag(v___x_2552_) == 0 {
                                                    v_a_2553_ =
                                                        crate::leanh::lean_ctor_get(v___x_2552_, 0);
                                                    crate::leanh::lean_inc(v_a_2553_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_2552_,
                                                        1,
                                                    );
                                                    v___x_2554_ = l_Int_Linear_Expr_norm(v_a_2553_);
                                                    v___x_2555_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7);
                                                    v___x_2556_ = l_Lean_mkApp6(
                                                        v___x_2555_,
                                                        v_arg_2483_,
                                                        v_arg_2480_,
                                                        v_fst_2544_,
                                                        v_fst_2548_,
                                                        v_snd_2545_,
                                                        v_snd_2549_,
                                                    );
                                                    crate::leanh::lean_inc(v_val_2504_);
                                                    v___x_2557_ = lean_nat_to_int(v_val_2504_);
                                                    v___x_2558_ = crate::leanh::lean_alloc_ctor(
                                                        1,
                                                        4,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2558_,
                                                        0,
                                                        v_e_2460_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2558_,
                                                        1,
                                                        v___x_2556_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2558_,
                                                        2,
                                                        v_val_2504_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2558_,
                                                        3,
                                                        v_a_2553_,
                                                    );
                                                    v___x_2559_ = crate::leanh::lean_alloc_ctor(
                                                        0,
                                                        3,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2559_,
                                                        0,
                                                        v___x_2557_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2559_,
                                                        1,
                                                        v___x_2554_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2559_,
                                                        2,
                                                        v___x_2558_,
                                                    );
                                                    v___x_2560_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_2559_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                                                    return v___x_2560_;
                                                } else {
                                                    crate::leanh::lean_dec(v_snd_2549_);
                                                    crate::leanh::lean_dec(v_fst_2548_);
                                                    crate::leanh::lean_dec(v_snd_2545_);
                                                    crate::leanh::lean_dec(v_fst_2544_);
                                                    crate::leanh::lean_dec(v_val_2504_);
                                                    crate::leanh::lean_dec_ref(v_arg_2483_);
                                                    crate::leanh::lean_dec_ref(v_arg_2480_);
                                                    crate::leanh::lean_dec_ref(v_e_2460_);
                                                    v_a_2561_ =
                                                        crate::leanh::lean_ctor_get(v___x_2552_, 0);
                                                    v_isSharedCheck_2568_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_2552_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_2568_ == 0 {
                                                        v___x_2563_ = v___x_2552_;
                                                        v_isShared_2564_ = v_isSharedCheck_2568_;
                                                        state = 11;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_2561_);
                                                        crate::leanh::lean_dec(v___x_2552_);
                                                        v___x_2563_ = crate::leanh::lean_box(0);
                                                        v_isShared_2564_ = v_isSharedCheck_2568_;
                                                        state = 11;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v_snd_2549_);
                                                crate::leanh::lean_dec(v_fst_2548_);
                                                crate::leanh::lean_dec(v_snd_2545_);
                                                crate::leanh::lean_dec(v_fst_2544_);
                                                crate::leanh::lean_dec(v_val_2504_);
                                                crate::leanh::lean_dec_ref(v_arg_2483_);
                                                crate::leanh::lean_dec_ref(v_arg_2480_);
                                                crate::leanh::lean_dec_ref(v_e_2460_);
                                                v_a_2569_ =
                                                    crate::leanh::lean_ctor_get(v___x_2550_, 0);
                                                v_isSharedCheck_2576_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_2550_))
                                                        as u8;
                                                if v_isSharedCheck_2576_ == 0 {
                                                    v___x_2571_ = v___x_2550_;
                                                    v_isShared_2572_ = v_isSharedCheck_2576_;
                                                    state = 13;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_2569_);
                                                    crate::leanh::lean_dec(v___x_2550_);
                                                    v___x_2571_ = crate::leanh::lean_box(0);
                                                    v_isShared_2572_ = v_isSharedCheck_2576_;
                                                    state = 13;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_snd_2545_);
                                            crate::leanh::lean_dec(v_fst_2544_);
                                            crate::leanh::lean_dec(v_val_2504_);
                                            crate::leanh::lean_dec_ref(v_arg_2483_);
                                            crate::leanh::lean_dec_ref(v_arg_2480_);
                                            crate::leanh::lean_dec_ref(v_e_2460_);
                                            v_a_2577_ = crate::leanh::lean_ctor_get(v___x_2546_, 0);
                                            v_isSharedCheck_2584_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2546_))
                                                    as u8;
                                            if v_isSharedCheck_2584_ == 0 {
                                                v___x_2579_ = v___x_2546_;
                                                v_isShared_2580_ = v_isSharedCheck_2584_;
                                                state = 15;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_2577_);
                                                crate::leanh::lean_dec(v___x_2546_);
                                                v___x_2579_ = crate::leanh::lean_box(0);
                                                v_isShared_2580_ = v_isSharedCheck_2584_;
                                                state = 15;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_val_2504_);
                                        crate::leanh::lean_dec_ref(v_arg_2483_);
                                        crate::leanh::lean_dec_ref(v_arg_2480_);
                                        crate::leanh::lean_dec_ref(v_e_2460_);
                                        v_a_2585_ = crate::leanh::lean_ctor_get(v___x_2542_, 0);
                                        v_isSharedCheck_2592_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2542_)) as u8;
                                        if v_isSharedCheck_2592_ == 0 {
                                            v___x_2587_ = v___x_2542_;
                                            v_isShared_2588_ = v_isSharedCheck_2592_;
                                            state = 17;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2585_);
                                            crate::leanh::lean_dec(v___x_2542_);
                                            v___x_2587_ = crate::leanh::lean_box(0);
                                            v_isShared_2588_ = v_isSharedCheck_2592_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_val_2504_);
                                crate::leanh::lean_dec_ref(v_arg_2483_);
                                crate::leanh::lean_dec_ref(v_arg_2480_);
                                crate::leanh::lean_dec_ref(v_e_2460_);
                                v_a_2593_ = crate::leanh::lean_ctor_get(v___x_2505_, 0);
                                v_isSharedCheck_2600_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2505_)) as u8;
                                if v_isSharedCheck_2600_ == 0 {
                                    v___x_2595_ = v___x_2505_;
                                    v_isShared_2596_ = v_isSharedCheck_2600_;
                                    state = 19;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2593_);
                                    crate::leanh::lean_dec(v___x_2505_);
                                    v___x_2595_ = crate::leanh::lean_box(0);
                                    v_isShared_2596_ = v_isSharedCheck_2600_;
                                    state = 19;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2503_);
                            crate::leanh::lean_dec_ref(v_arg_2483_);
                            crate::leanh::lean_dec_ref(v_arg_2480_);
                            v___x_2601_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2465_);
                            if crate::leanh::lean_obj_tag(v___x_2601_) == 0 {
                                v_a_2602_ = crate::leanh::lean_ctor_get(v___x_2601_, 0);
                                crate::leanh::lean_inc(v_a_2602_);
                                crate::leanh::lean_dec_ref_known(v___x_2601_, 1);
                                v___x_2603_ = (crate::leanh::lean_unbox(v_a_2602_) as u8);
                                crate::leanh::lean_dec(v_a_2602_);
                                if v___x_2603_ == 0 {
                                    crate::leanh::lean_dec_ref(v_e_2460_);
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_2604_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9);
                                    v___x_2605_ = l_Lean_indentExpr(v_e_2460_);
                                    v___x_2606_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_2606_, 0, v___x_2604_);
                                    crate::leanh::lean_ctor_set(v___x_2606_, 1, v___x_2605_);
                                    v___x_2607_ = l_Lean_Meta_Sym_reportIssue(
                                        v___x_2606_,
                                        v_a_2465_,
                                        v_a_2466_,
                                        v_a_2467_,
                                        v_a_2468_,
                                        v_a_2469_,
                                        v_a_2470_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2607_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_2607_, 1);
                                        state = 2;
                                        continue;
                                    } else {
                                        return v___x_2607_;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_e_2460_);
                                v_a_2608_ = crate::leanh::lean_ctor_get(v___x_2601_, 0);
                                v_isSharedCheck_2615_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2601_)) as u8;
                                if v_isSharedCheck_2615_ == 0 {
                                    v___x_2610_ = v___x_2601_;
                                    v_isShared_2611_ = v_isSharedCheck_2615_;
                                    state = 21;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2608_);
                                    crate::leanh::lean_dec(v___x_2601_);
                                    v___x_2610_ = crate::leanh::lean_box(0);
                                    v_isShared_2611_ = v_isSharedCheck_2615_;
                                    state = 21;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_2483_);
                        crate::leanh::lean_dec_ref(v_arg_2480_);
                        crate::leanh::lean_dec_ref(v_e_2460_);
                        v_a_2616_ = crate::leanh::lean_ctor_get(v___x_2502_, 0);
                        v_isSharedCheck_2623_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2502_)) as u8;
                        if v_isSharedCheck_2623_ == 0 {
                            v___x_2618_ = v___x_2502_;
                            v_isShared_2619_ = v_isSharedCheck_2623_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2616_);
                            crate::leanh::lean_dec(v___x_2502_);
                            v___x_2618_ = crate::leanh::lean_box(0);
                            v_isShared_2619_ = v_isSharedCheck_2623_;
                            state = 23;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_2500_;
            }
            5 => {
                v___x_2513_ = (crate::leanh::lean_unbox(v_a_2509_) as u8);
                crate::leanh::lean_dec(v_a_2509_);
                if v___x_2513_ == 0 {
                    crate::leanh::lean_dec_ref(v_arg_2483_);
                    crate::leanh::lean_dec_ref(v_arg_2480_);
                    crate::leanh::lean_dec_ref(v_e_2460_);
                    v___x_2514_ = crate::leanh::lean_box(0);
                    if v_isShared_2512_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2511_, 0, v___x_2514_);
                        v___x_2516_ = v___x_2511_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2517_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2514_);
                        v___x_2516_ = v_reuseFailAlloc_2517_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2511_);
                    crate::leanh::lean_inc_ref(v_e_2460_);
                    v___x_2518_ = l_Lean_Meta_Grind_mkEqFalseProof(
                        v_e_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_,
                        v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2518_) == 0 {
                        v_a_2519_ = crate::leanh::lean_ctor_get(v___x_2518_, 0);
                        crate::leanh::lean_inc(v_a_2519_);
                        crate::leanh::lean_dec_ref_known(v___x_2518_, 1);
                        v___x_2520_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3_once
                            ),
                            _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3,
                        );
                        v___x_2521_ = l_Lean_Meta_mkOfEqFalseCore(v_e_2460_, v_a_2519_);
                        v___x_2522_ =
                            l_Lean_mkApp3(v___x_2520_, v_arg_2483_, v_arg_2480_, v___x_2521_);
                        v___x_2523_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2524_ = l_Lean_Meta_Grind_pushNewFact(
                            v___x_2522_,
                            v___x_2523_,
                            v_a_2461_,
                            v_a_2462_,
                            v_a_2463_,
                            v_a_2464_,
                            v_a_2465_,
                            v_a_2466_,
                            v_a_2467_,
                            v_a_2468_,
                            v_a_2469_,
                            v_a_2470_,
                        );
                        return v___x_2524_;
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_2483_);
                        crate::leanh::lean_dec_ref(v_arg_2480_);
                        crate::leanh::lean_dec_ref(v_e_2460_);
                        v_a_2525_ = crate::leanh::lean_ctor_get(v___x_2518_, 0);
                        v_isSharedCheck_2532_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2518_)) as u8;
                        if v_isSharedCheck_2532_ == 0 {
                            v___x_2527_ = v___x_2518_;
                            v_isShared_2528_ = v_isSharedCheck_2532_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2525_);
                            crate::leanh::lean_dec(v___x_2518_);
                            v___x_2527_ = crate::leanh::lean_box(0);
                            v_isShared_2528_ = v_isSharedCheck_2532_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            6 => {
                return v___x_2516_;
            }
            7 => {
                if v_isShared_2528_ == 0 {
                    v___x_2530_ = v___x_2527_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2531_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2525_);
                    v___x_2530_ = v_reuseFailAlloc_2531_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2530_;
            }
            9 => {
                if v_isShared_2537_ == 0 {
                    v___x_2539_ = v___x_2536_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2540_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2534_);
                    v___x_2539_ = v_reuseFailAlloc_2540_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2539_;
            }
            11 => {
                if v_isShared_2564_ == 0 {
                    v___x_2566_ = v___x_2563_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2567_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
                    v___x_2566_ = v_reuseFailAlloc_2567_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2566_;
            }
            13 => {
                if v_isShared_2572_ == 0 {
                    v___x_2574_ = v___x_2571_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2575_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
                    v___x_2574_ = v_reuseFailAlloc_2575_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2574_;
            }
            15 => {
                if v_isShared_2580_ == 0 {
                    v___x_2582_ = v___x_2579_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2583_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
                    v___x_2582_ = v_reuseFailAlloc_2583_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2582_;
            }
            17 => {
                if v_isShared_2588_ == 0 {
                    v___x_2590_ = v___x_2587_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2591_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
                    v___x_2590_ = v_reuseFailAlloc_2591_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2590_;
            }
            19 => {
                if v_isShared_2596_ == 0 {
                    v___x_2598_ = v___x_2595_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2599_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
                    v___x_2598_ = v_reuseFailAlloc_2599_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2598_;
            }
            21 => {
                if v_isShared_2611_ == 0 {
                    v___x_2613_ = v___x_2610_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2614_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
                    v___x_2613_ = v_reuseFailAlloc_2614_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2613_;
            }
            23 => {
                if v_isShared_2619_ == 0 {
                    v___x_2621_ = v___x_2618_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2622_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2616_);
                    v___x_2621_ = v_reuseFailAlloc_2622_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2621_;
            }
            25 => {
                if v_isShared_2628_ == 0 {
                    v___x_2630_ = v___x_2627_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_2631_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
                    v___x_2630_ = v_reuseFailAlloc_2631_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_2630_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___boxed(
    mut v_e_2633_: *mut crate::leanh::LeanObject,
    mut v_a_2634_: *mut crate::leanh::LeanObject,
    mut v_a_2635_: *mut crate::leanh::LeanObject,
    mut v_a_2636_: *mut crate::leanh::LeanObject,
    mut v_a_2637_: *mut crate::leanh::LeanObject,
    mut v_a_2638_: *mut crate::leanh::LeanObject,
    mut v_a_2639_: *mut crate::leanh::LeanObject,
    mut v_a_2640_: *mut crate::leanh::LeanObject,
    mut v_a_2641_: *mut crate::leanh::LeanObject,
    mut v_a_2642_: *mut crate::leanh::LeanObject,
    mut v_a_2643_: *mut crate::leanh::LeanObject,
    mut v_a_2644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2645_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(
        v_e_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_,
        v_a_2641_, v_a_2642_, v_a_2643_,
    );
    crate::leanh::lean_dec(v_a_2643_);
    crate::leanh::lean_dec_ref(v_a_2642_);
    crate::leanh::lean_dec(v_a_2641_);
    crate::leanh::lean_dec_ref(v_a_2640_);
    crate::leanh::lean_dec(v_a_2639_);
    crate::leanh::lean_dec_ref(v_a_2638_);
    crate::leanh::lean_dec(v_a_2637_);
    crate::leanh::lean_dec_ref(v_a_2636_);
    crate::leanh::lean_dec(v_a_2635_);
    crate::leanh::lean_dec(v_a_2634_);
    return v_res_2645_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(
    mut v_e_2648_: *mut crate::leanh::LeanObject,
    mut v_a_2649_: *mut crate::leanh::LeanObject,
    mut v_a_2650_: *mut crate::leanh::LeanObject,
    mut v_a_2651_: *mut crate::leanh::LeanObject,
    mut v_a_2652_: *mut crate::leanh::LeanObject,
    mut v_a_2653_: *mut crate::leanh::LeanObject,
    mut v_a_2654_: *mut crate::leanh::LeanObject,
    mut v_a_2655_: *mut crate::leanh::LeanObject,
    mut v_a_2656_: *mut crate::leanh::LeanObject,
    mut v_a_2657_: *mut crate::leanh::LeanObject,
    mut v_a_2658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2664_: u8 = 0;
    let mut v_lia_2665_: u8 = 0;
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2674_: u8 = 0;
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: u8 = 0;
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: u8 = 0;
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: u8 = 0;
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: u8 = 0;
    let mut v_arg_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: u8 = 0;
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: u8 = 0;
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2696_: u8 = 0;
    let mut v_a_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2700_: u8 = 0;
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2704_: u8 = 0;
    let mut v_isSharedCheck_2705_: u8 = 0;
    let mut v_a_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2709_: u8 = 0;
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2713_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2660_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2651_);
                if crate::leanh::lean_obj_tag(v___x_2660_) == 0 {
                    v_a_2661_ = crate::leanh::lean_ctor_get(v___x_2660_, 0);
                    v_isSharedCheck_2705_ = (!crate::leanh::lean_is_exclusive(v___x_2660_)) as u8;
                    if v_isSharedCheck_2705_ == 0 {
                        v___x_2663_ = v___x_2660_;
                        v_isShared_2664_ = v_isSharedCheck_2705_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2661_);
                        crate::leanh::lean_dec(v___x_2660_);
                        v___x_2663_ = crate::leanh::lean_box(0);
                        v_isShared_2664_ = v_isSharedCheck_2705_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_2648_);
                    v_a_2706_ = crate::leanh::lean_ctor_get(v___x_2660_, 0);
                    v_isSharedCheck_2713_ = (!crate::leanh::lean_is_exclusive(v___x_2660_)) as u8;
                    if v_isSharedCheck_2713_ == 0 {
                        v___x_2708_ = v___x_2660_;
                        v_isShared_2709_ = v_isSharedCheck_2713_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2706_);
                        crate::leanh::lean_dec(v___x_2660_);
                        v___x_2708_ = crate::leanh::lean_box(0);
                        v_isShared_2709_ = v_isSharedCheck_2713_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_lia_2665_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2661_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 23) as u32,
                );
                crate::leanh::lean_dec(v_a_2661_);
                if v_lia_2665_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_2648_);
                    v___x_2666_ = crate::leanh::lean_box(0);
                    if v_isShared_2664_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2663_, 0, v___x_2666_);
                        v___x_2668_ = v___x_2663_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2669_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2669_, 0, v___x_2666_);
                        v___x_2668_ = v_reuseFailAlloc_2669_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2663_);
                    crate::leanh::lean_inc_ref(v_e_2648_);
                    v___x_2670_ =
                        l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2648_, v_a_2656_);
                    if crate::leanh::lean_obj_tag(v___x_2670_) == 0 {
                        v_a_2671_ = crate::leanh::lean_ctor_get(v___x_2670_, 0);
                        v_isSharedCheck_2696_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2670_)) as u8;
                        if v_isSharedCheck_2696_ == 0 {
                            v___x_2673_ = v___x_2670_;
                            v_isShared_2674_ = v_isSharedCheck_2696_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2671_);
                            crate::leanh::lean_dec(v___x_2670_);
                            v___x_2673_ = crate::leanh::lean_box(0);
                            v_isShared_2674_ = v_isSharedCheck_2696_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_2648_);
                        v_a_2697_ = crate::leanh::lean_ctor_get(v___x_2670_, 0);
                        v_isSharedCheck_2704_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2670_)) as u8;
                        if v_isSharedCheck_2704_ == 0 {
                            v___x_2699_ = v___x_2670_;
                            v_isShared_2700_ = v_isSharedCheck_2704_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2697_);
                            crate::leanh::lean_dec(v___x_2670_);
                            v___x_2699_ = crate::leanh::lean_box(0);
                            v_isShared_2700_ = v_isSharedCheck_2704_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2668_;
            }
            3 => {
                v___x_2680_ = l_Lean_Expr_cleanupAnnotations(v_a_2671_);
                v___x_2681_ = l_Lean_Expr_isApp(v___x_2680_);
                if v___x_2681_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2680_);
                    crate::leanh::lean_dec_ref(v_e_2648_);
                    state = 4;
                    continue;
                } else {
                    v___x_2682_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2680_);
                    v___x_2683_ = l_Lean_Expr_isApp(v___x_2682_);
                    if v___x_2683_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2682_);
                        crate::leanh::lean_dec_ref(v_e_2648_);
                        state = 4;
                        continue;
                    } else {
                        v___x_2684_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2682_);
                        v___x_2685_ = l_Lean_Expr_isApp(v___x_2684_);
                        if v___x_2685_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2684_);
                            crate::leanh::lean_dec_ref(v_e_2648_);
                            state = 4;
                            continue;
                        } else {
                            v___x_2686_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2684_);
                            v___x_2687_ = l_Lean_Expr_isApp(v___x_2686_);
                            if v___x_2687_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_2686_);
                                crate::leanh::lean_dec_ref(v_e_2648_);
                                state = 4;
                                continue;
                            } else {
                                v_arg_2688_ = crate::leanh::lean_ctor_get(v___x_2686_, 1);
                                crate::leanh::lean_inc_ref(v_arg_2688_);
                                v___x_2689_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2686_);
                                v___x_2690_ =
                                    l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
                                v___x_2691_ = l_Lean_Expr_isConstOf(v___x_2689_, v___x_2690_);
                                crate::leanh::lean_dec_ref(v___x_2689_);
                                if v___x_2691_ == 0 {
                                    crate::leanh::lean_dec_ref(v_arg_2688_);
                                    crate::leanh::lean_dec_ref(v_e_2648_);
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_del_object(v___x_2673_);
                                    v___x_2692_ =
                                        l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0;
                                    v___x_2693_ = l_Lean_Expr_isConstOf(v_arg_2688_, v___x_2692_);
                                    crate::leanh::lean_dec_ref(v_arg_2688_);
                                    if v___x_2693_ == 0 {
                                        v___x_2694_ =
                                            l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(
                                                v_e_2648_, v_a_2649_, v_a_2650_, v_a_2651_,
                                                v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_,
                                                v_a_2656_, v_a_2657_, v_a_2658_,
                                            );
                                        return v___x_2694_;
                                    } else {
                                        v___x_2695_ =
                                            l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(
                                                v_e_2648_, v_a_2649_, v_a_2650_, v_a_2651_,
                                                v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_,
                                                v_a_2656_, v_a_2657_, v_a_2658_,
                                            );
                                        return v___x_2695_;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            4 => {
                v___x_2676_ = crate::leanh::lean_box(0);
                if v_isShared_2674_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2673_, 0, v___x_2676_);
                    v___x_2678_ = v___x_2673_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2679_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2676_);
                    v___x_2678_ = v_reuseFailAlloc_2679_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2678_;
            }
            6 => {
                if v_isShared_2700_ == 0 {
                    v___x_2702_ = v___x_2699_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2703_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2697_);
                    v___x_2702_ = v_reuseFailAlloc_2703_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2702_;
            }
            8 => {
                if v_isShared_2709_ == 0 {
                    v___x_2711_ = v___x_2708_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2712_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2706_);
                    v___x_2711_ = v_reuseFailAlloc_2712_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2711_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed(
    mut v_e_2714_: *mut crate::leanh::LeanObject,
    mut v_a_2715_: *mut crate::leanh::LeanObject,
    mut v_a_2716_: *mut crate::leanh::LeanObject,
    mut v_a_2717_: *mut crate::leanh::LeanObject,
    mut v_a_2718_: *mut crate::leanh::LeanObject,
    mut v_a_2719_: *mut crate::leanh::LeanObject,
    mut v_a_2720_: *mut crate::leanh::LeanObject,
    mut v_a_2721_: *mut crate::leanh::LeanObject,
    mut v_a_2722_: *mut crate::leanh::LeanObject,
    mut v_a_2723_: *mut crate::leanh::LeanObject,
    mut v_a_2724_: *mut crate::leanh::LeanObject,
    mut v_a_2725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2726_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(
        v_e_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_,
        v_a_2722_, v_a_2723_, v_a_2724_,
    );
    crate::leanh::lean_dec(v_a_2724_);
    crate::leanh::lean_dec_ref(v_a_2723_);
    crate::leanh::lean_dec(v_a_2722_);
    crate::leanh::lean_dec_ref(v_a_2721_);
    crate::leanh::lean_dec(v_a_2720_);
    crate::leanh::lean_dec_ref(v_a_2719_);
    crate::leanh::lean_dec(v_a_2718_);
    crate::leanh::lean_dec_ref(v_a_2717_);
    crate::leanh::lean_dec(v_a_2716_);
    crate::leanh::lean_dec(v_a_2715_);
    return v_res_2726_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2728_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
    v___x_2729_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_2730_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_2728_, v___x_2729_);
    return v___x_2730_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8____boxed(
    mut v_a_2731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2732_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_();
    return v_res_2732_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(
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
    res = runtime_initialize_Init_Data_Int_OfNat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Propagator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_NatInstTesters(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Dvd(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(
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
    res = initialize_Init_Data_Int_OfNat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Propagator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_NatInstTesters(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Dvd(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(builtin);
}
