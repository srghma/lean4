// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.SafePoly
// Imports: Lean.Meta.Tactic.Grind.Arith.CommRing.RingM Lean.Meta.Sym.Arith.Poly Lean.Meta.Tactic.Grind.Arith.EvalNum Init.Data.Nat.Linear
use crate::ffi::{
    lean_int_add, lean_int_dec_eq, lean_int_ediv, lean_int_emod, lean_int_mul, lean_int_neg,
    lean_nat_abs, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_gcd, lean_nat_sub,
    lean_nat_to_int,
};
use crate::r#gen::Init::Data::Int::Basic::l_Int_pow;
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::GetElem::l_outOfBounds___redArg;
use crate::r#gen::Init::Grind::Ring::CommSolver::{
    l_Lean_Grind_CommRing_Mon_grevlex, l_Lean_Grind_CommRing_Poly_addConst,
    l_Lean_Grind_CommRing_Poly_addConstC, l_Lean_Grind_CommRing_Poly_mulConst,
    l_Lean_Grind_CommRing_Poly_mulConstC, l_Lean_Grind_CommRing_Poly_mulMon,
    l_Lean_Grind_CommRing_Poly_mulMonC, l_Lean_Grind_CommRing_Poly_ofMon,
    l_Lean_Grind_CommRing_Poly_ofVar,
};
use crate::r#gen::Init::Prelude::l_Lean_maxRecDepthErrorMessage;
use crate::r#gen::Lean::CoreM::l_Lean_Core_checkSystem;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_get_x21___redArg;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_isApp,
    l_Lean_Expr_isConstOf, l_Lean_instInhabitedExpr,
};
use crate::r#gen::Lean::Message::l_Lean_MessageData_ofFormat;
use crate::r#gen::Lean::Meta::LitValues::l_Lean_Meta_getNatValue_x3f;
use crate::r#gen::Lean::Meta::Sym::Arith::Poly::{
    initialize_Lean_Meta_Sym_Arith_Poly, l_Lean_Grind_CommRing_Mon_div,
    l_Lean_Grind_CommRing_Mon_divides, l_Lean_Grind_CommRing_Mon_lcm,
    runtime_initialize_Lean_Meta_Sym_Arith_Poly,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::RingM::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM,
    l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::EvalNum::{
    initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum, l_Lean_Meta_Grind_Arith_checkExp___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum,
};
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__1_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject,7310567555909517314 as *mut leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject,273128857561458264 as *mut leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___closed__0_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [103, 114, 105, 110, 100, 32, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommRing_Poly_spolM___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_CommRing_Poly_spolM___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__0_value:
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
    m_data: [73, 110, 118, 0],
};
static mut l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__1_value:
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
    m_data: [105, 110, 118, 0],
};
static mut l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__0_value)
            as *mut leanh::LeanObject,
        1412621069384631438 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__2_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__1_value)
            as *mut leanh::LeanObject,
        10171450186735820607 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__3_value:
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
    m_data: [79, 102, 78, 97, 116, 0],
};
static mut l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__4_value:
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
    m_data: [111, 102, 78, 97, 116, 0],
};
static mut l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__4_value)
        as *mut leanh::LeanObject;
static l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__3_value)
            as *mut leanh::LeanObject,
        17636616155771105671 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__5_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__4_value)
            as *mut leanh::LeanObject,
        15578568367168711682 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__5_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(
    mut v___y_1702_: *mut leanh::LeanObject,
    mut v___y_1703_: *mut leanh::LeanObject,
    mut v___y_1704_: *mut leanh::LeanObject,
    mut v___y_1705_: *mut leanh::LeanObject,
    mut v___y_1706_: *mut leanh::LeanObject,
    mut v___y_1707_: *mut leanh::LeanObject,
    mut v___y_1708_: *mut leanh::LeanObject,
    mut v___y_1709_: *mut leanh::LeanObject,
    mut v___y_1710_: *mut leanh::LeanObject,
    mut v___y_1711_: *mut leanh::LeanObject,
    mut v___y_1712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1718_: u8 = 0;
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toRing_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1729_: u8 = 0;
    let mut v_snd_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: u8 = 0;
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1737_: u8 = 0;
    let mut v_isSharedCheck_1738_: u8 = 0;
    let mut v_a_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1742_: u8 = 0;
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1746_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1714_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                    v___y_1702_,
                    v___y_1703_,
                    v___y_1704_,
                    v___y_1705_,
                    v___y_1706_,
                    v___y_1707_,
                    v___y_1708_,
                    v___y_1709_,
                    v___y_1710_,
                    v___y_1711_,
                    v___y_1712_,
                );
                if leanh::lean_obj_tag(v___x_1714_) == 0 {
                    v_a_1715_ = leanh::lean_ctor_get(v___x_1714_, 0);
                    v_isSharedCheck_1738_ = (!leanh::lean_is_exclusive(v___x_1714_)) as u8;
                    if v_isSharedCheck_1738_ == 0 {
                        v___x_1717_ = v___x_1714_;
                        v_isShared_1718_ = v_isSharedCheck_1738_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1715_);
                        leanh::lean_dec(v___x_1714_);
                        v___x_1717_ = leanh::lean_box(0);
                        v_isShared_1718_ = v_isSharedCheck_1738_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1739_ = leanh::lean_ctor_get(v___x_1714_, 0);
                    v_isSharedCheck_1746_ = (!leanh::lean_is_exclusive(v___x_1714_)) as u8;
                    if v_isSharedCheck_1746_ == 0 {
                        v___x_1741_ = v___x_1714_;
                        v_isShared_1742_ = v_isSharedCheck_1746_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1739_);
                        leanh::lean_dec(v___x_1714_);
                        v___x_1741_ = leanh::lean_box(0);
                        v_isShared_1742_ = v_isSharedCheck_1746_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_toRing_1724_ = leanh::lean_ctor_get(v_a_1715_, 0);
                leanh::lean_inc_ref(v_toRing_1724_);
                leanh::lean_dec(v_a_1715_);
                v_charInst_x3f_1725_ = leanh::lean_ctor_get(v_toRing_1724_, 5);
                leanh::lean_inc(v_charInst_x3f_1725_);
                leanh::lean_dec_ref(v_toRing_1724_);
                if leanh::lean_obj_tag(v_charInst_x3f_1725_) == 1 {
                    v_val_1726_ = leanh::lean_ctor_get(v_charInst_x3f_1725_, 0);
                    v_isSharedCheck_1737_ =
                        (!leanh::lean_is_exclusive(v_charInst_x3f_1725_)) as u8;
                    if v_isSharedCheck_1737_ == 0 {
                        v___x_1728_ = v_charInst_x3f_1725_;
                        v_isShared_1729_ = v_isSharedCheck_1737_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1726_);
                        leanh::lean_dec(v_charInst_x3f_1725_);
                        v___x_1728_ = leanh::lean_box(0);
                        v_isShared_1729_ = v_isSharedCheck_1737_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_charInst_x3f_1725_);
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1720_ = leanh::lean_box(0);
                if v_isShared_1718_ == 0 {
                    leanh::lean_ctor_set(v___x_1717_, 0, v___x_1720_);
                    v___x_1722_ = v___x_1717_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1723_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1720_);
                    v___x_1722_ = v_reuseFailAlloc_1723_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1722_;
            }
            4 => {
                v_snd_1730_ = leanh::lean_ctor_get(v_val_1726_, 1);
                leanh::lean_inc(v_snd_1730_);
                leanh::lean_dec(v_val_1726_);
                v___x_1731_ = leanh::lean_unsigned_to_nat(0);
                v___x_1732_ = lean_nat_dec_eq(v_snd_1730_, v___x_1731_);
                if v___x_1732_ == 0 {
                    leanh::lean_del_object(v___x_1717_);
                    if v_isShared_1729_ == 0 {
                        leanh::lean_ctor_set(v___x_1728_, 0, v_snd_1730_);
                        v___x_1734_ = v___x_1728_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1736_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_snd_1730_);
                        v___x_1734_ = v_reuseFailAlloc_1736_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_snd_1730_);
                    leanh::lean_del_object(v___x_1728_);
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_1735_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1735_, 0, v___x_1734_);
                return v___x_1735_;
            }
            6 => {
                if v_isShared_1742_ == 0 {
                    v___x_1744_ = v___x_1741_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1745_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
                    v___x_1744_ = v_reuseFailAlloc_1745_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1744_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0___boxed(
    mut v___y_1747_: *mut leanh::LeanObject,
    mut v___y_1748_: *mut leanh::LeanObject,
    mut v___y_1749_: *mut leanh::LeanObject,
    mut v___y_1750_: *mut leanh::LeanObject,
    mut v___y_1751_: *mut leanh::LeanObject,
    mut v___y_1752_: *mut leanh::LeanObject,
    mut v___y_1753_: *mut leanh::LeanObject,
    mut v___y_1754_: *mut leanh::LeanObject,
    mut v___y_1755_: *mut leanh::LeanObject,
    mut v___y_1756_: *mut leanh::LeanObject,
    mut v___y_1757_: *mut leanh::LeanObject,
    mut v___y_1758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1759_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
    leanh::lean_dec(v___y_1757_);
    leanh::lean_dec_ref(v___y_1756_);
    leanh::lean_dec(v___y_1755_);
    leanh::lean_dec_ref(v___y_1754_);
    leanh::lean_dec(v___y_1753_);
    leanh::lean_dec_ref(v___y_1752_);
    leanh::lean_dec(v___y_1751_);
    leanh::lean_dec_ref(v___y_1750_);
    leanh::lean_dec(v___y_1749_);
    leanh::lean_dec(v___y_1748_);
    leanh::lean_dec_ref(v___y_1747_);
    return v_res_1759_;
}
pub unsafe fn l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__1(
    mut v_a_1760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1761_ = lean_nat_to_int(v_a_1760_);
    return v___x_1761_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(
    mut v_a_1762_: *mut leanh::LeanObject,
    mut v_a_1763_: *mut leanh::LeanObject,
    mut v_a_1764_: *mut leanh::LeanObject,
    mut v_a_1765_: *mut leanh::LeanObject,
    mut v_a_1766_: *mut leanh::LeanObject,
    mut v_a_1767_: *mut leanh::LeanObject,
    mut v_a_1768_: *mut leanh::LeanObject,
    mut v_a_1769_: *mut leanh::LeanObject,
    mut v_a_1770_: *mut leanh::LeanObject,
    mut v_a_1771_: *mut leanh::LeanObject,
    mut v_a_1772_: *mut leanh::LeanObject,
    mut v_a_1773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1779_: u8 = 0;
    let mut v_val_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1789_: u8 = 0;
    let mut v_a_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1793_: u8 = 0;
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1797_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1775_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_);
                if leanh::lean_obj_tag(v___x_1775_) == 0 {
                    v_a_1776_ = leanh::lean_ctor_get(v___x_1775_, 0);
                    v_isSharedCheck_1789_ = (!leanh::lean_is_exclusive(v___x_1775_)) as u8;
                    if v_isSharedCheck_1789_ == 0 {
                        v___x_1778_ = v___x_1775_;
                        v_isShared_1779_ = v_isSharedCheck_1789_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1776_);
                        leanh::lean_dec(v___x_1775_);
                        v___x_1778_ = leanh::lean_box(0);
                        v_isShared_1779_ = v_isSharedCheck_1789_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1762_);
                    v_a_1790_ = leanh::lean_ctor_get(v___x_1775_, 0);
                    v_isSharedCheck_1797_ = (!leanh::lean_is_exclusive(v___x_1775_)) as u8;
                    if v_isSharedCheck_1797_ == 0 {
                        v___x_1792_ = v___x_1775_;
                        v_isShared_1793_ = v_isSharedCheck_1797_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1790_);
                        leanh::lean_dec(v___x_1775_);
                        v___x_1792_ = leanh::lean_box(0);
                        v_isShared_1793_ = v_isSharedCheck_1797_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_1776_) == 1 {
                    v_val_1780_ = leanh::lean_ctor_get(v_a_1776_, 0);
                    leanh::lean_inc(v_val_1780_);
                    leanh::lean_dec_ref_known(v_a_1776_, 1);
                    v___x_1781_ = lean_nat_to_int(v_val_1780_);
                    v___x_1782_ = lean_int_emod(v_a_1762_, v___x_1781_);
                    leanh::lean_dec(v___x_1781_);
                    leanh::lean_dec(v_a_1762_);
                    if v_isShared_1779_ == 0 {
                        leanh::lean_ctor_set(v___x_1778_, 0, v___x_1782_);
                        v___x_1784_ = v___x_1778_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1785_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
                        v___x_1784_ = v_reuseFailAlloc_1785_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1776_);
                    if v_isShared_1779_ == 0 {
                        leanh::lean_ctor_set(v___x_1778_, 0, v_a_1762_);
                        v___x_1787_ = v___x_1778_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1788_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1762_);
                        v___x_1787_ = v_reuseFailAlloc_1788_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1784_;
            }
            3 => {
                return v___x_1787_;
            }
            4 => {
                if v_isShared_1793_ == 0 {
                    v___x_1795_ = v___x_1792_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1796_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1790_);
                    v___x_1795_ = v_reuseFailAlloc_1796_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1795_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar___boxed(
    mut v_a_1798_: *mut leanh::LeanObject,
    mut v_a_1799_: *mut leanh::LeanObject,
    mut v_a_1800_: *mut leanh::LeanObject,
    mut v_a_1801_: *mut leanh::LeanObject,
    mut v_a_1802_: *mut leanh::LeanObject,
    mut v_a_1803_: *mut leanh::LeanObject,
    mut v_a_1804_: *mut leanh::LeanObject,
    mut v_a_1805_: *mut leanh::LeanObject,
    mut v_a_1806_: *mut leanh::LeanObject,
    mut v_a_1807_: *mut leanh::LeanObject,
    mut v_a_1808_: *mut leanh::LeanObject,
    mut v_a_1809_: *mut leanh::LeanObject,
    mut v_a_1810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1811_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
    leanh::lean_dec(v_a_1809_);
    leanh::lean_dec_ref(v_a_1808_);
    leanh::lean_dec(v_a_1807_);
    leanh::lean_dec_ref(v_a_1806_);
    leanh::lean_dec(v_a_1805_);
    leanh::lean_dec_ref(v_a_1804_);
    leanh::lean_dec(v_a_1803_);
    leanh::lean_dec_ref(v_a_1802_);
    leanh::lean_dec(v_a_1801_);
    leanh::lean_dec(v_a_1800_);
    leanh::lean_dec_ref(v_a_1799_);
    return v_res_1811_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(
    mut v_p_1812_: *mut leanh::LeanObject,
    mut v_k_1813_: *mut leanh::LeanObject,
    mut v_a_1814_: *mut leanh::LeanObject,
    mut v_a_1815_: *mut leanh::LeanObject,
    mut v_a_1816_: *mut leanh::LeanObject,
    mut v_a_1817_: *mut leanh::LeanObject,
    mut v_a_1818_: *mut leanh::LeanObject,
    mut v_a_1819_: *mut leanh::LeanObject,
    mut v_a_1820_: *mut leanh::LeanObject,
    mut v_a_1821_: *mut leanh::LeanObject,
    mut v_a_1822_: *mut leanh::LeanObject,
    mut v_a_1823_: *mut leanh::LeanObject,
    mut v_a_1824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1830_: u8 = 0;
    let mut v_val_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1840_: u8 = 0;
    let mut v_a_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1844_: u8 = 0;
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1848_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1826_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_);
                if leanh::lean_obj_tag(v___x_1826_) == 0 {
                    v_a_1827_ = leanh::lean_ctor_get(v___x_1826_, 0);
                    v_isSharedCheck_1840_ = (!leanh::lean_is_exclusive(v___x_1826_)) as u8;
                    if v_isSharedCheck_1840_ == 0 {
                        v___x_1829_ = v___x_1826_;
                        v_isShared_1830_ = v_isSharedCheck_1840_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1827_);
                        leanh::lean_dec(v___x_1826_);
                        v___x_1829_ = leanh::lean_box(0);
                        v_isShared_1830_ = v_isSharedCheck_1840_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_p_1812_);
                    v_a_1841_ = leanh::lean_ctor_get(v___x_1826_, 0);
                    v_isSharedCheck_1848_ = (!leanh::lean_is_exclusive(v___x_1826_)) as u8;
                    if v_isSharedCheck_1848_ == 0 {
                        v___x_1843_ = v___x_1826_;
                        v_isShared_1844_ = v_isSharedCheck_1848_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1841_);
                        leanh::lean_dec(v___x_1826_);
                        v___x_1843_ = leanh::lean_box(0);
                        v_isShared_1844_ = v_isSharedCheck_1848_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_1827_) == 1 {
                    v_val_1831_ = leanh::lean_ctor_get(v_a_1827_, 0);
                    leanh::lean_inc(v_val_1831_);
                    leanh::lean_dec_ref_known(v_a_1827_, 1);
                    v___x_1832_ =
                        l_Lean_Grind_CommRing_Poly_addConstC(v_p_1812_, v_k_1813_, v_val_1831_);
                    if v_isShared_1830_ == 0 {
                        leanh::lean_ctor_set(v___x_1829_, 0, v___x_1832_);
                        v___x_1834_ = v___x_1829_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1835_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1832_);
                        v___x_1834_ = v_reuseFailAlloc_1835_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1827_);
                    v___x_1836_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_1812_, v_k_1813_);
                    if v_isShared_1830_ == 0 {
                        leanh::lean_ctor_set(v___x_1829_, 0, v___x_1836_);
                        v___x_1838_ = v___x_1829_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1839_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
                        v___x_1838_ = v_reuseFailAlloc_1839_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1834_;
            }
            3 => {
                return v___x_1838_;
            }
            4 => {
                if v_isShared_1844_ == 0 {
                    v___x_1846_ = v___x_1843_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1847_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
                    v___x_1846_ = v_reuseFailAlloc_1847_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1846_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst___boxed(
    mut v_p_1849_: *mut leanh::LeanObject,
    mut v_k_1850_: *mut leanh::LeanObject,
    mut v_a_1851_: *mut leanh::LeanObject,
    mut v_a_1852_: *mut leanh::LeanObject,
    mut v_a_1853_: *mut leanh::LeanObject,
    mut v_a_1854_: *mut leanh::LeanObject,
    mut v_a_1855_: *mut leanh::LeanObject,
    mut v_a_1856_: *mut leanh::LeanObject,
    mut v_a_1857_: *mut leanh::LeanObject,
    mut v_a_1858_: *mut leanh::LeanObject,
    mut v_a_1859_: *mut leanh::LeanObject,
    mut v_a_1860_: *mut leanh::LeanObject,
    mut v_a_1861_: *mut leanh::LeanObject,
    mut v_a_1862_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1863_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(v_p_1849_, v_k_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
    leanh::lean_dec(v_a_1861_);
    leanh::lean_dec_ref(v_a_1860_);
    leanh::lean_dec(v_a_1859_);
    leanh::lean_dec_ref(v_a_1858_);
    leanh::lean_dec(v_a_1857_);
    leanh::lean_dec_ref(v_a_1856_);
    leanh::lean_dec(v_a_1855_);
    leanh::lean_dec_ref(v_a_1854_);
    leanh::lean_dec(v_a_1853_);
    leanh::lean_dec(v_a_1852_);
    leanh::lean_dec_ref(v_a_1851_);
    leanh::lean_dec(v_k_1850_);
    return v_res_1863_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(
    mut v_k_1864_: *mut leanh::LeanObject,
    mut v_p_1865_: *mut leanh::LeanObject,
    mut v_a_1866_: *mut leanh::LeanObject,
    mut v_a_1867_: *mut leanh::LeanObject,
    mut v_a_1868_: *mut leanh::LeanObject,
    mut v_a_1869_: *mut leanh::LeanObject,
    mut v_a_1870_: *mut leanh::LeanObject,
    mut v_a_1871_: *mut leanh::LeanObject,
    mut v_a_1872_: *mut leanh::LeanObject,
    mut v_a_1873_: *mut leanh::LeanObject,
    mut v_a_1874_: *mut leanh::LeanObject,
    mut v_a_1875_: *mut leanh::LeanObject,
    mut v_a_1876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1882_: u8 = 0;
    let mut v_val_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1892_: u8 = 0;
    let mut v_a_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1896_: u8 = 0;
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1900_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1878_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_);
                if leanh::lean_obj_tag(v___x_1878_) == 0 {
                    v_a_1879_ = leanh::lean_ctor_get(v___x_1878_, 0);
                    v_isSharedCheck_1892_ = (!leanh::lean_is_exclusive(v___x_1878_)) as u8;
                    if v_isSharedCheck_1892_ == 0 {
                        v___x_1881_ = v___x_1878_;
                        v_isShared_1882_ = v_isSharedCheck_1892_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1879_);
                        leanh::lean_dec(v___x_1878_);
                        v___x_1881_ = leanh::lean_box(0);
                        v_isShared_1882_ = v_isSharedCheck_1892_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_p_1865_);
                    v_a_1893_ = leanh::lean_ctor_get(v___x_1878_, 0);
                    v_isSharedCheck_1900_ = (!leanh::lean_is_exclusive(v___x_1878_)) as u8;
                    if v_isSharedCheck_1900_ == 0 {
                        v___x_1895_ = v___x_1878_;
                        v_isShared_1896_ = v_isSharedCheck_1900_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1893_);
                        leanh::lean_dec(v___x_1878_);
                        v___x_1895_ = leanh::lean_box(0);
                        v_isShared_1896_ = v_isSharedCheck_1900_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_1879_) == 1 {
                    v_val_1883_ = leanh::lean_ctor_get(v_a_1879_, 0);
                    leanh::lean_inc(v_val_1883_);
                    leanh::lean_dec_ref_known(v_a_1879_, 1);
                    v___x_1884_ =
                        l_Lean_Grind_CommRing_Poly_mulConstC(v_k_1864_, v_p_1865_, v_val_1883_);
                    if v_isShared_1882_ == 0 {
                        leanh::lean_ctor_set(v___x_1881_, 0, v___x_1884_);
                        v___x_1886_ = v___x_1881_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1887_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1887_, 0, v___x_1884_);
                        v___x_1886_ = v_reuseFailAlloc_1887_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1879_);
                    v___x_1888_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_1864_, v_p_1865_);
                    if v_isShared_1882_ == 0 {
                        leanh::lean_ctor_set(v___x_1881_, 0, v___x_1888_);
                        v___x_1890_ = v___x_1881_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1891_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1888_);
                        v___x_1890_ = v_reuseFailAlloc_1891_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1886_;
            }
            3 => {
                return v___x_1890_;
            }
            4 => {
                if v_isShared_1896_ == 0 {
                    v___x_1898_ = v___x_1895_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1899_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
                    v___x_1898_ = v_reuseFailAlloc_1899_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1898_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst___boxed(
    mut v_k_1901_: *mut leanh::LeanObject,
    mut v_p_1902_: *mut leanh::LeanObject,
    mut v_a_1903_: *mut leanh::LeanObject,
    mut v_a_1904_: *mut leanh::LeanObject,
    mut v_a_1905_: *mut leanh::LeanObject,
    mut v_a_1906_: *mut leanh::LeanObject,
    mut v_a_1907_: *mut leanh::LeanObject,
    mut v_a_1908_: *mut leanh::LeanObject,
    mut v_a_1909_: *mut leanh::LeanObject,
    mut v_a_1910_: *mut leanh::LeanObject,
    mut v_a_1911_: *mut leanh::LeanObject,
    mut v_a_1912_: *mut leanh::LeanObject,
    mut v_a_1913_: *mut leanh::LeanObject,
    mut v_a_1914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1915_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v_k_1901_, v_p_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_);
    leanh::lean_dec(v_a_1913_);
    leanh::lean_dec_ref(v_a_1912_);
    leanh::lean_dec(v_a_1911_);
    leanh::lean_dec_ref(v_a_1910_);
    leanh::lean_dec(v_a_1909_);
    leanh::lean_dec_ref(v_a_1908_);
    leanh::lean_dec(v_a_1907_);
    leanh::lean_dec_ref(v_a_1906_);
    leanh::lean_dec(v_a_1905_);
    leanh::lean_dec(v_a_1904_);
    leanh::lean_dec_ref(v_a_1903_);
    leanh::lean_dec(v_k_1901_);
    return v_res_1915_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(
    mut v_k_1916_: *mut leanh::LeanObject,
    mut v_m_1917_: *mut leanh::LeanObject,
    mut v_p_1918_: *mut leanh::LeanObject,
    mut v_a_1919_: *mut leanh::LeanObject,
    mut v_a_1920_: *mut leanh::LeanObject,
    mut v_a_1921_: *mut leanh::LeanObject,
    mut v_a_1922_: *mut leanh::LeanObject,
    mut v_a_1923_: *mut leanh::LeanObject,
    mut v_a_1924_: *mut leanh::LeanObject,
    mut v_a_1925_: *mut leanh::LeanObject,
    mut v_a_1926_: *mut leanh::LeanObject,
    mut v_a_1927_: *mut leanh::LeanObject,
    mut v_a_1928_: *mut leanh::LeanObject,
    mut v_a_1929_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1935_: u8 = 0;
    let mut v_val_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1945_: u8 = 0;
    let mut v_a_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1949_: u8 = 0;
    let mut v___x_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1953_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1931_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_);
                if leanh::lean_obj_tag(v___x_1931_) == 0 {
                    v_a_1932_ = leanh::lean_ctor_get(v___x_1931_, 0);
                    v_isSharedCheck_1945_ = (!leanh::lean_is_exclusive(v___x_1931_)) as u8;
                    if v_isSharedCheck_1945_ == 0 {
                        v___x_1934_ = v___x_1931_;
                        v_isShared_1935_ = v_isSharedCheck_1945_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1932_);
                        leanh::lean_dec(v___x_1931_);
                        v___x_1934_ = leanh::lean_box(0);
                        v_isShared_1935_ = v_isSharedCheck_1945_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_p_1918_);
                    leanh::lean_dec(v_m_1917_);
                    v_a_1946_ = leanh::lean_ctor_get(v___x_1931_, 0);
                    v_isSharedCheck_1953_ = (!leanh::lean_is_exclusive(v___x_1931_)) as u8;
                    if v_isSharedCheck_1953_ == 0 {
                        v___x_1948_ = v___x_1931_;
                        v_isShared_1949_ = v_isSharedCheck_1953_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1946_);
                        leanh::lean_dec(v___x_1931_);
                        v___x_1948_ = leanh::lean_box(0);
                        v_isShared_1949_ = v_isSharedCheck_1953_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_1932_) == 1 {
                    v_val_1936_ = leanh::lean_ctor_get(v_a_1932_, 0);
                    leanh::lean_inc(v_val_1936_);
                    leanh::lean_dec_ref_known(v_a_1932_, 1);
                    v___x_1937_ = l_Lean_Grind_CommRing_Poly_mulMonC(
                        v_k_1916_,
                        v_m_1917_,
                        v_p_1918_,
                        v_val_1936_,
                    );
                    if v_isShared_1935_ == 0 {
                        leanh::lean_ctor_set(v___x_1934_, 0, v___x_1937_);
                        v___x_1939_ = v___x_1934_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1940_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1937_);
                        v___x_1939_ = v_reuseFailAlloc_1940_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1932_);
                    v___x_1941_ =
                        l_Lean_Grind_CommRing_Poly_mulMon(v_k_1916_, v_m_1917_, v_p_1918_);
                    if v_isShared_1935_ == 0 {
                        leanh::lean_ctor_set(v___x_1934_, 0, v___x_1941_);
                        v___x_1943_ = v___x_1934_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1944_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1941_);
                        v___x_1943_ = v_reuseFailAlloc_1944_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1939_;
            }
            3 => {
                return v___x_1943_;
            }
            4 => {
                if v_isShared_1949_ == 0 {
                    v___x_1951_ = v___x_1948_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1952_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
                    v___x_1951_ = v_reuseFailAlloc_1952_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1951_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon___boxed(
    mut v_k_1954_: *mut leanh::LeanObject,
    mut v_m_1955_: *mut leanh::LeanObject,
    mut v_p_1956_: *mut leanh::LeanObject,
    mut v_a_1957_: *mut leanh::LeanObject,
    mut v_a_1958_: *mut leanh::LeanObject,
    mut v_a_1959_: *mut leanh::LeanObject,
    mut v_a_1960_: *mut leanh::LeanObject,
    mut v_a_1961_: *mut leanh::LeanObject,
    mut v_a_1962_: *mut leanh::LeanObject,
    mut v_a_1963_: *mut leanh::LeanObject,
    mut v_a_1964_: *mut leanh::LeanObject,
    mut v_a_1965_: *mut leanh::LeanObject,
    mut v_a_1966_: *mut leanh::LeanObject,
    mut v_a_1967_: *mut leanh::LeanObject,
    mut v_a_1968_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1969_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_k_1954_, v_m_1955_, v_p_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_);
    leanh::lean_dec(v_a_1967_);
    leanh::lean_dec_ref(v_a_1966_);
    leanh::lean_dec(v_a_1965_);
    leanh::lean_dec_ref(v_a_1964_);
    leanh::lean_dec(v_a_1963_);
    leanh::lean_dec_ref(v_a_1962_);
    leanh::lean_dec(v_a_1961_);
    leanh::lean_dec_ref(v_a_1960_);
    leanh::lean_dec(v_a_1959_);
    leanh::lean_dec(v_a_1958_);
    leanh::lean_dec_ref(v_a_1957_);
    leanh::lean_dec(v_k_1954_);
    return v_res_1969_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1975_ = l_Lean_maxRecDepthErrorMessage;
    v___x_1976_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1976_, 0, v___x_1975_);
    return v___x_1976_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1977_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__3);
    v___x_1978_ = l_Lean_MessageData_ofFormat(v___x_1977_);
    return v___x_1978_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1979_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__4);
    v___x_1980_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__2;
    v___x_1981_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1981_, 0, v___x_1980_);
    leanh::lean_ctor_set(v___x_1981_, 1, v___x_1979_);
    return v___x_1981_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(
    mut v_ref_1982_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1984_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__5);
    v___x_1985_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1985_, 0, v_ref_1982_);
    leanh::lean_ctor_set(v___x_1985_, 1, v___x_1984_);
    v___x_1986_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1986_, 0, v___x_1985_);
    return v___x_1986_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___boxed(
    mut v_ref_1987_: *mut leanh::LeanObject,
    mut v___y_1988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1989_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(v_ref_1987_);
    return v_res_1989_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0(
    mut v_00_u03b1_1990_: *mut leanh::LeanObject,
    mut v_ref_1991_: *mut leanh::LeanObject,
    mut v___y_1992_: *mut leanh::LeanObject,
    mut v___y_1993_: *mut leanh::LeanObject,
    mut v___y_1994_: *mut leanh::LeanObject,
    mut v___y_1995_: *mut leanh::LeanObject,
    mut v___y_1996_: *mut leanh::LeanObject,
    mut v___y_1997_: *mut leanh::LeanObject,
    mut v___y_1998_: *mut leanh::LeanObject,
    mut v___y_1999_: *mut leanh::LeanObject,
    mut v___y_2000_: *mut leanh::LeanObject,
    mut v___y_2001_: *mut leanh::LeanObject,
    mut v___y_2002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2004_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(v_ref_1991_);
    return v___x_2004_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___boxed(
    mut v_00_u03b1_2005_: *mut leanh::LeanObject,
    mut v_ref_2006_: *mut leanh::LeanObject,
    mut v___y_2007_: *mut leanh::LeanObject,
    mut v___y_2008_: *mut leanh::LeanObject,
    mut v___y_2009_: *mut leanh::LeanObject,
    mut v___y_2010_: *mut leanh::LeanObject,
    mut v___y_2011_: *mut leanh::LeanObject,
    mut v___y_2012_: *mut leanh::LeanObject,
    mut v___y_2013_: *mut leanh::LeanObject,
    mut v___y_2014_: *mut leanh::LeanObject,
    mut v___y_2015_: *mut leanh::LeanObject,
    mut v___y_2016_: *mut leanh::LeanObject,
    mut v___y_2017_: *mut leanh::LeanObject,
    mut v___y_2018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2019_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0(v_00_u03b1_2005_, v_ref_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
    leanh::lean_dec(v___y_2017_);
    leanh::lean_dec_ref(v___y_2016_);
    leanh::lean_dec(v___y_2015_);
    leanh::lean_dec_ref(v___y_2014_);
    leanh::lean_dec(v___y_2013_);
    leanh::lean_dec_ref(v___y_2012_);
    leanh::lean_dec(v___y_2011_);
    leanh::lean_dec_ref(v___y_2010_);
    leanh::lean_dec(v___y_2009_);
    leanh::lean_dec(v___y_2008_);
    leanh::lean_dec_ref(v___y_2007_);
    return v_res_2019_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2020_ = leanh::lean_unsigned_to_nat(0);
    v___x_2021_ = lean_nat_to_int(v___x_2020_);
    return v___x_2021_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(
    mut v_p_u2081_2022_: *mut leanh::LeanObject,
    mut v_p_u2082_2023_: *mut leanh::LeanObject,
    mut v_a_2024_: *mut leanh::LeanObject,
    mut v_a_2025_: *mut leanh::LeanObject,
    mut v_a_2026_: *mut leanh::LeanObject,
    mut v_a_2027_: *mut leanh::LeanObject,
    mut v_a_2028_: *mut leanh::LeanObject,
    mut v_a_2029_: *mut leanh::LeanObject,
    mut v_a_2030_: *mut leanh::LeanObject,
    mut v_a_2031_: *mut leanh::LeanObject,
    mut v_a_2032_: *mut leanh::LeanObject,
    mut v_a_2033_: *mut leanh::LeanObject,
    mut v_a_2034_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2048_: u8 = 0;
    let mut v_cancelTk_x3f_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2050_: u8 = 0;
    let mut v_inheritedTraceOptions_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2060_: u8 = 0;
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2066_: u8 = 0;
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2073_: u8 = 0;
    let mut v_a_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2077_: u8 = 0;
    let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2081_: u8 = 0;
    let mut v_isSharedCheck_2082_: u8 = 0;
    let mut v_k_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: u8 = 0;
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2096_: u8 = 0;
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2101_: u8 = 0;
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2108_: u8 = 0;
    let mut v_isSharedCheck_2109_: u8 = 0;
    let mut v_unused_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2115_: u8 = 0;
    let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: u8 = 0;
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2125_: u8 = 0;
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2132_: u8 = 0;
    let mut v_a_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2137_: u8 = 0;
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2141_: u8 = 0;
    let mut v_isSharedCheck_2142_: u8 = 0;
    let mut v_unused_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2148_: u8 = 0;
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2153_: u8 = 0;
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2160_: u8 = 0;
    let mut v_isSharedCheck_2161_: u8 = 0;
    let mut v_unused_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: u8 = 0;
    let mut v___x_2167_: u8 = 0;
    let mut v___x_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_2036_ = leanh::lean_ctor_get(v_a_2033_, 0);
                leanh::lean_inc_ref(v_fileName_2036_);
                v_fileMap_2037_ = leanh::lean_ctor_get(v_a_2033_, 1);
                leanh::lean_inc_ref(v_fileMap_2037_);
                v_options_2038_ = leanh::lean_ctor_get(v_a_2033_, 2);
                leanh::lean_inc_ref(v_options_2038_);
                v_currRecDepth_2039_ = leanh::lean_ctor_get(v_a_2033_, 3);
                leanh::lean_inc(v_currRecDepth_2039_);
                v_maxRecDepth_2040_ = leanh::lean_ctor_get(v_a_2033_, 4);
                leanh::lean_inc(v_maxRecDepth_2040_);
                v_ref_2041_ = leanh::lean_ctor_get(v_a_2033_, 5);
                leanh::lean_inc(v_ref_2041_);
                v_currNamespace_2042_ = leanh::lean_ctor_get(v_a_2033_, 6);
                leanh::lean_inc(v_currNamespace_2042_);
                v_openDecls_2043_ = leanh::lean_ctor_get(v_a_2033_, 7);
                leanh::lean_inc(v_openDecls_2043_);
                v_initHeartbeats_2044_ = leanh::lean_ctor_get(v_a_2033_, 8);
                leanh::lean_inc(v_initHeartbeats_2044_);
                v_maxHeartbeats_2045_ = leanh::lean_ctor_get(v_a_2033_, 9);
                leanh::lean_inc(v_maxHeartbeats_2045_);
                v_quotContext_2046_ = leanh::lean_ctor_get(v_a_2033_, 10);
                leanh::lean_inc(v_quotContext_2046_);
                v_currMacroScope_2047_ = leanh::lean_ctor_get(v_a_2033_, 11);
                leanh::lean_inc(v_currMacroScope_2047_);
                v_diag_2048_ = leanh::lean_ctor_get_uint8(
                    v_a_2033_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_2049_ = leanh::lean_ctor_get(v_a_2033_, 12);
                leanh::lean_inc(v_cancelTk_x3f_2049_);
                v_suppressElabErrors_2050_ = leanh::lean_ctor_get_uint8(
                    v_a_2033_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_2051_ = leanh::lean_ctor_get(v_a_2033_, 13);
                leanh::lean_inc_ref(v_inheritedTraceOptions_2051_);
                leanh::lean_dec_ref(v_a_2033_);
                v___x_2165_ = leanh::lean_unsigned_to_nat(0);
                v___x_2166_ = lean_nat_dec_eq(v_maxRecDepth_2040_, v___x_2165_);
                if v___x_2166_ == 0 {
                    v___x_2167_ = lean_nat_dec_eq(v_currRecDepth_2039_, v_maxRecDepth_2040_);
                    if v___x_2167_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_inheritedTraceOptions_2051_);
                        leanh::lean_dec(v_cancelTk_x3f_2049_);
                        leanh::lean_dec(v_currMacroScope_2047_);
                        leanh::lean_dec(v_quotContext_2046_);
                        leanh::lean_dec(v_maxHeartbeats_2045_);
                        leanh::lean_dec(v_initHeartbeats_2044_);
                        leanh::lean_dec(v_openDecls_2043_);
                        leanh::lean_dec(v_currNamespace_2042_);
                        leanh::lean_dec(v_maxRecDepth_2040_);
                        leanh::lean_dec(v_currRecDepth_2039_);
                        leanh::lean_dec_ref(v_options_2038_);
                        leanh::lean_dec_ref(v_fileMap_2037_);
                        leanh::lean_dec_ref(v_fileName_2036_);
                        leanh::lean_dec_ref(v_p_u2082_2023_);
                        leanh::lean_dec_ref(v_p_u2081_2022_);
                        v___x_2168_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(v_ref_2041_);
                        return v___x_2168_;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2053_ = leanh::lean_unsigned_to_nat(1);
                v___x_2054_ = lean_nat_add(v_currRecDepth_2039_, v___x_2053_);
                leanh::lean_dec(v_currRecDepth_2039_);
                v___x_2055_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_2055_, 0, v_fileName_2036_);
                leanh::lean_ctor_set(v___x_2055_, 1, v_fileMap_2037_);
                leanh::lean_ctor_set(v___x_2055_, 2, v_options_2038_);
                leanh::lean_ctor_set(v___x_2055_, 3, v___x_2054_);
                leanh::lean_ctor_set(v___x_2055_, 4, v_maxRecDepth_2040_);
                leanh::lean_ctor_set(v___x_2055_, 5, v_ref_2041_);
                leanh::lean_ctor_set(v___x_2055_, 6, v_currNamespace_2042_);
                leanh::lean_ctor_set(v___x_2055_, 7, v_openDecls_2043_);
                leanh::lean_ctor_set(v___x_2055_, 8, v_initHeartbeats_2044_);
                leanh::lean_ctor_set(v___x_2055_, 9, v_maxHeartbeats_2045_);
                leanh::lean_ctor_set(v___x_2055_, 10, v_quotContext_2046_);
                leanh::lean_ctor_set(v___x_2055_, 11, v_currMacroScope_2047_);
                leanh::lean_ctor_set(v___x_2055_, 12, v_cancelTk_x3f_2049_);
                leanh::lean_ctor_set(v___x_2055_, 13, v_inheritedTraceOptions_2051_);
                leanh::lean_ctor_set_uint8(
                    v___x_2055_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v_diag_2048_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2055_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_2050_,
                );
                if leanh::lean_obj_tag(v_p_u2081_2022_) == 0 {
                    if leanh::lean_obj_tag(v_p_u2082_2023_) == 0 {
                        v_k_2056_ = leanh::lean_ctor_get(v_p_u2081_2022_, 0);
                        leanh::lean_inc(v_k_2056_);
                        leanh::lean_dec_ref_known(v_p_u2081_2022_, 1);
                        v_k_2057_ = leanh::lean_ctor_get(v_p_u2082_2023_, 0);
                        v_isSharedCheck_2082_ =
                            (!leanh::lean_is_exclusive(v_p_u2082_2023_)) as u8;
                        if v_isSharedCheck_2082_ == 0 {
                            v___x_2059_ = v_p_u2082_2023_;
                            v_isShared_2060_ = v_isSharedCheck_2082_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_k_2057_);
                            leanh::lean_dec(v_p_u2082_2023_);
                            v___x_2059_ = leanh::lean_box(0);
                            v_isShared_2060_ = v_isSharedCheck_2082_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_k_2083_ = leanh::lean_ctor_get(v_p_u2081_2022_, 0);
                        leanh::lean_inc(v_k_2083_);
                        leanh::lean_dec_ref_known(v_p_u2081_2022_, 1);
                        v___x_2084_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(v_p_u2082_2023_, v_k_2083_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v___x_2055_, v_a_2034_);
                        leanh::lean_dec_ref_known(v___x_2055_, 14);
                        leanh::lean_dec(v_k_2083_);
                        return v___x_2084_;
                    }
                } else {
                    if leanh::lean_obj_tag(v_p_u2082_2023_) == 0 {
                        v_k_2085_ = leanh::lean_ctor_get(v_p_u2082_2023_, 0);
                        leanh::lean_inc(v_k_2085_);
                        leanh::lean_dec_ref_known(v_p_u2082_2023_, 1);
                        v___x_2086_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(v_p_u2081_2022_, v_k_2085_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v___x_2055_, v_a_2034_);
                        leanh::lean_dec_ref_known(v___x_2055_, 14);
                        leanh::lean_dec(v_k_2085_);
                        return v___x_2086_;
                    } else {
                        v_k_2087_ = leanh::lean_ctor_get(v_p_u2081_2022_, 0);
                        v_v_2088_ = leanh::lean_ctor_get(v_p_u2081_2022_, 1);
                        v_p_2089_ = leanh::lean_ctor_get(v_p_u2081_2022_, 2);
                        v_k_2090_ = leanh::lean_ctor_get(v_p_u2082_2023_, 0);
                        v_v_2091_ = leanh::lean_ctor_get(v_p_u2082_2023_, 1);
                        v_p_2092_ = leanh::lean_ctor_get(v_p_u2082_2023_, 2);
                        v___x_2093_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_2088_, v_v_2091_);
                        match v___x_2093_ {
                            0 => {
                                leanh::lean_inc_ref(v_p_2092_);
                                leanh::lean_inc(v_v_2091_);
                                leanh::lean_inc(v_k_2090_);
                                v_isSharedCheck_2109_ =
                                    (!leanh::lean_is_exclusive(v_p_u2082_2023_)) as u8;
                                if v_isSharedCheck_2109_ == 0 {
                                    v_unused_2110_ =
                                        leanh::lean_ctor_get(v_p_u2082_2023_, 2);
                                    leanh::lean_dec(v_unused_2110_);
                                    v_unused_2111_ =
                                        leanh::lean_ctor_get(v_p_u2082_2023_, 1);
                                    leanh::lean_dec(v_unused_2111_);
                                    v_unused_2112_ =
                                        leanh::lean_ctor_get(v_p_u2082_2023_, 0);
                                    leanh::lean_dec(v_unused_2112_);
                                    v___x_2095_ = v_p_u2082_2023_;
                                    v_isShared_2096_ = v_isSharedCheck_2109_;
                                    state = 8;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_p_u2082_2023_);
                                    v___x_2095_ = leanh::lean_box(0);
                                    v_isShared_2096_ = v_isSharedCheck_2109_;
                                    state = 8;
                                    continue;
                                }
                            }
                            1 => {
                                leanh::lean_inc_ref(v_p_2092_);
                                leanh::lean_inc(v_k_2090_);
                                leanh::lean_inc_ref(v_p_2089_);
                                leanh::lean_inc(v_v_2088_);
                                leanh::lean_inc(v_k_2087_);
                                leanh::lean_dec_ref_known(v_p_u2081_2022_, 3);
                                v_isSharedCheck_2142_ =
                                    (!leanh::lean_is_exclusive(v_p_u2082_2023_)) as u8;
                                if v_isSharedCheck_2142_ == 0 {
                                    v_unused_2143_ =
                                        leanh::lean_ctor_get(v_p_u2082_2023_, 2);
                                    leanh::lean_dec(v_unused_2143_);
                                    v_unused_2144_ =
                                        leanh::lean_ctor_get(v_p_u2082_2023_, 1);
                                    leanh::lean_dec(v_unused_2144_);
                                    v_unused_2145_ =
                                        leanh::lean_ctor_get(v_p_u2082_2023_, 0);
                                    leanh::lean_dec(v_unused_2145_);
                                    v___x_2114_ = v_p_u2082_2023_;
                                    v_isShared_2115_ = v_isSharedCheck_2142_;
                                    state = 12;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_p_u2082_2023_);
                                    v___x_2114_ = leanh::lean_box(0);
                                    v_isShared_2115_ = v_isSharedCheck_2142_;
                                    state = 12;
                                    continue;
                                }
                            }
                            _ => {
                                leanh::lean_inc_ref(v_p_2089_);
                                leanh::lean_inc(v_v_2088_);
                                leanh::lean_inc(v_k_2087_);
                                v_isSharedCheck_2161_ =
                                    (!leanh::lean_is_exclusive(v_p_u2081_2022_)) as u8;
                                if v_isSharedCheck_2161_ == 0 {
                                    v_unused_2162_ =
                                        leanh::lean_ctor_get(v_p_u2081_2022_, 2);
                                    leanh::lean_dec(v_unused_2162_);
                                    v_unused_2163_ =
                                        leanh::lean_ctor_get(v_p_u2081_2022_, 1);
                                    leanh::lean_dec(v_unused_2163_);
                                    v_unused_2164_ =
                                        leanh::lean_ctor_get(v_p_u2081_2022_, 0);
                                    leanh::lean_dec(v_unused_2164_);
                                    v___x_2147_ = v_p_u2081_2022_;
                                    v_isShared_2148_ = v_isSharedCheck_2161_;
                                    state = 18;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_p_u2081_2022_);
                                    v___x_2147_ = leanh::lean_box(0);
                                    v_isShared_2148_ = v_isSharedCheck_2161_;
                                    state = 18;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_2061_ = lean_int_add(v_k_2056_, v_k_2057_);
                leanh::lean_dec(v_k_2057_);
                leanh::lean_dec(v_k_2056_);
                v___x_2062_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v___x_2061_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v___x_2055_, v_a_2034_);
                leanh::lean_dec_ref_known(v___x_2055_, 14);
                if leanh::lean_obj_tag(v___x_2062_) == 0 {
                    v_a_2063_ = leanh::lean_ctor_get(v___x_2062_, 0);
                    v_isSharedCheck_2073_ = (!leanh::lean_is_exclusive(v___x_2062_)) as u8;
                    if v_isSharedCheck_2073_ == 0 {
                        v___x_2065_ = v___x_2062_;
                        v_isShared_2066_ = v_isSharedCheck_2073_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2063_);
                        leanh::lean_dec(v___x_2062_);
                        v___x_2065_ = leanh::lean_box(0);
                        v_isShared_2066_ = v_isSharedCheck_2073_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2059_);
                    v_a_2074_ = leanh::lean_ctor_get(v___x_2062_, 0);
                    v_isSharedCheck_2081_ = (!leanh::lean_is_exclusive(v___x_2062_)) as u8;
                    if v_isSharedCheck_2081_ == 0 {
                        v___x_2076_ = v___x_2062_;
                        v_isShared_2077_ = v_isSharedCheck_2081_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2074_);
                        leanh::lean_dec(v___x_2062_);
                        v___x_2076_ = leanh::lean_box(0);
                        v_isShared_2077_ = v_isSharedCheck_2081_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2060_ == 0 {
                    leanh::lean_ctor_set(v___x_2059_, 0, v_a_2063_);
                    v___x_2068_ = v___x_2059_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2072_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2063_);
                    v___x_2068_ = v_reuseFailAlloc_2072_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2066_ == 0 {
                    leanh::lean_ctor_set(v___x_2065_, 0, v___x_2068_);
                    v___x_2070_ = v___x_2065_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2071_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2068_);
                    v___x_2070_ = v_reuseFailAlloc_2071_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2070_;
            }
            6 => {
                if v_isShared_2077_ == 0 {
                    v___x_2079_ = v___x_2076_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2080_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
                    v___x_2079_ = v_reuseFailAlloc_2080_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2079_;
            }
            8 => {
                v___x_2097_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_p_u2081_2022_, v_p_2092_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v___x_2055_, v_a_2034_);
                if leanh::lean_obj_tag(v___x_2097_) == 0 {
                    v_a_2098_ = leanh::lean_ctor_get(v___x_2097_, 0);
                    v_isSharedCheck_2108_ = (!leanh::lean_is_exclusive(v___x_2097_)) as u8;
                    if v_isSharedCheck_2108_ == 0 {
                        v___x_2100_ = v___x_2097_;
                        v_isShared_2101_ = v_isSharedCheck_2108_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2098_);
                        leanh::lean_dec(v___x_2097_);
                        v___x_2100_ = leanh::lean_box(0);
                        v_isShared_2101_ = v_isSharedCheck_2108_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2095_);
                    leanh::lean_dec(v_v_2091_);
                    leanh::lean_dec(v_k_2090_);
                    return v___x_2097_;
                }
            }
            9 => {
                if v_isShared_2096_ == 0 {
                    leanh::lean_ctor_set(v___x_2095_, 2, v_a_2098_);
                    v___x_2103_ = v___x_2095_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2107_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_k_2090_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2107_, 1, v_v_2091_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2107_, 2, v_a_2098_);
                    v___x_2103_ = v_reuseFailAlloc_2107_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_2101_ == 0 {
                    leanh::lean_ctor_set(v___x_2100_, 0, v___x_2103_);
                    v___x_2105_ = v___x_2100_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2106_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2103_);
                    v___x_2105_ = v_reuseFailAlloc_2106_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2105_;
            }
            12 => {
                v___x_2116_ = lean_int_add(v_k_2087_, v_k_2090_);
                leanh::lean_dec(v_k_2090_);
                leanh::lean_dec(v_k_2087_);
                v___x_2117_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v___x_2116_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v___x_2055_, v_a_2034_);
                if leanh::lean_obj_tag(v___x_2117_) == 0 {
                    v_a_2118_ = leanh::lean_ctor_get(v___x_2117_, 0);
                    leanh::lean_inc(v_a_2118_);
                    leanh::lean_dec_ref_known(v___x_2117_, 1);
                    v___x_2119_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
                    v___x_2120_ = lean_int_dec_eq(v_a_2118_, v___x_2119_);
                    if v___x_2120_ == 0 {
                        v___x_2121_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_p_2089_, v_p_2092_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v___x_2055_, v_a_2034_);
                        if leanh::lean_obj_tag(v___x_2121_) == 0 {
                            v_a_2122_ = leanh::lean_ctor_get(v___x_2121_, 0);
                            v_isSharedCheck_2132_ =
                                (!leanh::lean_is_exclusive(v___x_2121_)) as u8;
                            if v_isSharedCheck_2132_ == 0 {
                                v___x_2124_ = v___x_2121_;
                                v_isShared_2125_ = v_isSharedCheck_2132_;
                                state = 13;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2122_);
                                leanh::lean_dec(v___x_2121_);
                                v___x_2124_ = leanh::lean_box(0);
                                v_isShared_2125_ = v_isSharedCheck_2132_;
                                state = 13;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_2118_);
                            leanh::lean_del_object(v___x_2114_);
                            leanh::lean_dec(v_v_2088_);
                            return v___x_2121_;
                        }
                    } else {
                        leanh::lean_dec(v_a_2118_);
                        leanh::lean_del_object(v___x_2114_);
                        leanh::lean_dec(v_v_2088_);
                        v_p_u2081_2022_ = v_p_2089_;
                        v_p_u2082_2023_ = v_p_2092_;
                        v_a_2033_ = v___x_2055_;
                        state = 0;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2114_);
                    leanh::lean_dec_ref(v_p_2092_);
                    leanh::lean_dec_ref(v_p_2089_);
                    leanh::lean_dec(v_v_2088_);
                    leanh::lean_dec_ref_known(v___x_2055_, 14);
                    v_a_2134_ = leanh::lean_ctor_get(v___x_2117_, 0);
                    v_isSharedCheck_2141_ = (!leanh::lean_is_exclusive(v___x_2117_)) as u8;
                    if v_isSharedCheck_2141_ == 0 {
                        v___x_2136_ = v___x_2117_;
                        v_isShared_2137_ = v_isSharedCheck_2141_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2134_);
                        leanh::lean_dec(v___x_2117_);
                        v___x_2136_ = leanh::lean_box(0);
                        v_isShared_2137_ = v_isSharedCheck_2141_;
                        state = 16;
                        continue;
                    }
                }
            }
            13 => {
                if v_isShared_2115_ == 0 {
                    leanh::lean_ctor_set(v___x_2114_, 2, v_a_2122_);
                    leanh::lean_ctor_set(v___x_2114_, 1, v_v_2088_);
                    leanh::lean_ctor_set(v___x_2114_, 0, v_a_2118_);
                    v___x_2127_ = v___x_2114_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2131_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2118_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_v_2088_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2131_, 2, v_a_2122_);
                    v___x_2127_ = v_reuseFailAlloc_2131_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_2125_ == 0 {
                    leanh::lean_ctor_set(v___x_2124_, 0, v___x_2127_);
                    v___x_2129_ = v___x_2124_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2130_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2127_);
                    v___x_2129_ = v_reuseFailAlloc_2130_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2129_;
            }
            16 => {
                if v_isShared_2137_ == 0 {
                    v___x_2139_ = v___x_2136_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2140_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
                    v___x_2139_ = v_reuseFailAlloc_2140_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2139_;
            }
            18 => {
                v___x_2149_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_p_2089_, v_p_u2082_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v___x_2055_, v_a_2034_);
                if leanh::lean_obj_tag(v___x_2149_) == 0 {
                    v_a_2150_ = leanh::lean_ctor_get(v___x_2149_, 0);
                    v_isSharedCheck_2160_ = (!leanh::lean_is_exclusive(v___x_2149_)) as u8;
                    if v_isSharedCheck_2160_ == 0 {
                        v___x_2152_ = v___x_2149_;
                        v_isShared_2153_ = v_isSharedCheck_2160_;
                        state = 19;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2150_);
                        leanh::lean_dec(v___x_2149_);
                        v___x_2152_ = leanh::lean_box(0);
                        v_isShared_2153_ = v_isSharedCheck_2160_;
                        state = 19;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2147_);
                    leanh::lean_dec(v_v_2088_);
                    leanh::lean_dec(v_k_2087_);
                    return v___x_2149_;
                }
            }
            19 => {
                if v_isShared_2148_ == 0 {
                    leanh::lean_ctor_set(v___x_2147_, 2, v_a_2150_);
                    v___x_2155_ = v___x_2147_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2159_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_k_2087_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_v_2088_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2159_, 2, v_a_2150_);
                    v___x_2155_ = v_reuseFailAlloc_2159_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_2153_ == 0 {
                    leanh::lean_ctor_set(v___x_2152_, 0, v___x_2155_);
                    v___x_2157_ = v___x_2152_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2158_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2155_);
                    v___x_2157_ = v_reuseFailAlloc_2158_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2157_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___boxed(
    mut v_p_u2081_2169_: *mut leanh::LeanObject,
    mut v_p_u2082_2170_: *mut leanh::LeanObject,
    mut v_a_2171_: *mut leanh::LeanObject,
    mut v_a_2172_: *mut leanh::LeanObject,
    mut v_a_2173_: *mut leanh::LeanObject,
    mut v_a_2174_: *mut leanh::LeanObject,
    mut v_a_2175_: *mut leanh::LeanObject,
    mut v_a_2176_: *mut leanh::LeanObject,
    mut v_a_2177_: *mut leanh::LeanObject,
    mut v_a_2178_: *mut leanh::LeanObject,
    mut v_a_2179_: *mut leanh::LeanObject,
    mut v_a_2180_: *mut leanh::LeanObject,
    mut v_a_2181_: *mut leanh::LeanObject,
    mut v_a_2182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2183_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_p_u2081_2169_, v_p_u2082_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_);
    leanh::lean_dec(v_a_2181_);
    leanh::lean_dec(v_a_2179_);
    leanh::lean_dec_ref(v_a_2178_);
    leanh::lean_dec(v_a_2177_);
    leanh::lean_dec_ref(v_a_2176_);
    leanh::lean_dec(v_a_2175_);
    leanh::lean_dec_ref(v_a_2174_);
    leanh::lean_dec(v_a_2173_);
    leanh::lean_dec(v_a_2172_);
    leanh::lean_dec_ref(v_a_2171_);
    return v_res_2183_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__3_splitter___redArg(
    mut v_p_u2081_2184_: *mut leanh::LeanObject,
    mut v_p_u2082_2185_: *mut leanh::LeanObject,
    mut v_h__1_2186_: *mut leanh::LeanObject,
    mut v_h__2_2187_: *mut leanh::LeanObject,
    mut v_h__3_2188_: *mut leanh::LeanObject,
    mut v_h__4_2189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_p_u2081_2184_) == 0 {
        leanh::lean_dec(v_h__4_2189_);
        leanh::lean_dec(v_h__3_2188_);
        if leanh::lean_obj_tag(v_p_u2082_2185_) == 0 {
            let mut v_k_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_2187_);
            v_k_2190_ = leanh::lean_ctor_get(v_p_u2081_2184_, 0);
            leanh::lean_inc(v_k_2190_);
            leanh::lean_dec_ref_known(v_p_u2081_2184_, 1);
            v_k_2191_ = leanh::lean_ctor_get(v_p_u2082_2185_, 0);
            leanh::lean_inc(v_k_2191_);
            leanh::lean_dec_ref_known(v_p_u2082_2185_, 1);
            v___x_2192_ = leanh::lean_apply_2(v_h__1_2186_, v_k_2190_, v_k_2191_);
            return v___x_2192_;
        } else {
            let mut v_k_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_2186_);
            v_k_2193_ = leanh::lean_ctor_get(v_p_u2081_2184_, 0);
            leanh::lean_inc(v_k_2193_);
            leanh::lean_dec_ref_known(v_p_u2081_2184_, 1);
            v_k_2194_ = leanh::lean_ctor_get(v_p_u2082_2185_, 0);
            leanh::lean_inc(v_k_2194_);
            v_v_2195_ = leanh::lean_ctor_get(v_p_u2082_2185_, 1);
            leanh::lean_inc(v_v_2195_);
            v_p_2196_ = leanh::lean_ctor_get(v_p_u2082_2185_, 2);
            leanh::lean_inc_ref(v_p_2196_);
            leanh::lean_dec_ref_known(v_p_u2082_2185_, 3);
            v___x_2197_ = leanh::lean_apply_4(
                v_h__2_2187_,
                v_k_2193_,
                v_k_2194_,
                v_v_2195_,
                v_p_2196_,
            );
            return v___x_2197_;
        }
    } else {
        leanh::lean_dec(v_h__2_2187_);
        leanh::lean_dec(v_h__1_2186_);
        if leanh::lean_obj_tag(v_p_u2082_2185_) == 0 {
            let mut v_k_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_2189_);
            v_k_2198_ = leanh::lean_ctor_get(v_p_u2081_2184_, 0);
            leanh::lean_inc(v_k_2198_);
            v_v_2199_ = leanh::lean_ctor_get(v_p_u2081_2184_, 1);
            leanh::lean_inc(v_v_2199_);
            v_p_2200_ = leanh::lean_ctor_get(v_p_u2081_2184_, 2);
            leanh::lean_inc_ref(v_p_2200_);
            leanh::lean_dec_ref_known(v_p_u2081_2184_, 3);
            v_k_2201_ = leanh::lean_ctor_get(v_p_u2082_2185_, 0);
            leanh::lean_inc(v_k_2201_);
            leanh::lean_dec_ref_known(v_p_u2082_2185_, 1);
            v___x_2202_ = leanh::lean_apply_4(
                v_h__3_2188_,
                v_k_2198_,
                v_v_2199_,
                v_p_2200_,
                v_k_2201_,
            );
            return v___x_2202_;
        } else {
            let mut v_k_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_2188_);
            v_k_2203_ = leanh::lean_ctor_get(v_p_u2081_2184_, 0);
            leanh::lean_inc(v_k_2203_);
            v_v_2204_ = leanh::lean_ctor_get(v_p_u2081_2184_, 1);
            leanh::lean_inc(v_v_2204_);
            v_p_2205_ = leanh::lean_ctor_get(v_p_u2081_2184_, 2);
            leanh::lean_inc_ref(v_p_2205_);
            leanh::lean_dec_ref_known(v_p_u2081_2184_, 3);
            v_k_2206_ = leanh::lean_ctor_get(v_p_u2082_2185_, 0);
            leanh::lean_inc(v_k_2206_);
            v_v_2207_ = leanh::lean_ctor_get(v_p_u2082_2185_, 1);
            leanh::lean_inc(v_v_2207_);
            v_p_2208_ = leanh::lean_ctor_get(v_p_u2082_2185_, 2);
            leanh::lean_inc_ref(v_p_2208_);
            leanh::lean_dec_ref_known(v_p_u2082_2185_, 3);
            v___x_2209_ = leanh::lean_apply_6(
                v_h__4_2189_,
                v_k_2203_,
                v_v_2204_,
                v_p_2205_,
                v_k_2206_,
                v_v_2207_,
                v_p_2208_,
            );
            return v___x_2209_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__3_splitter(
    mut v_motive_2210_: *mut leanh::LeanObject,
    mut v_p_u2081_2211_: *mut leanh::LeanObject,
    mut v_p_u2082_2212_: *mut leanh::LeanObject,
    mut v_h__1_2213_: *mut leanh::LeanObject,
    mut v_h__2_2214_: *mut leanh::LeanObject,
    mut v_h__3_2215_: *mut leanh::LeanObject,
    mut v_h__4_2216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_p_u2081_2211_) == 0 {
        leanh::lean_dec(v_h__4_2216_);
        leanh::lean_dec(v_h__3_2215_);
        if leanh::lean_obj_tag(v_p_u2082_2212_) == 0 {
            let mut v_k_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_2214_);
            v_k_2217_ = leanh::lean_ctor_get(v_p_u2081_2211_, 0);
            leanh::lean_inc(v_k_2217_);
            leanh::lean_dec_ref_known(v_p_u2081_2211_, 1);
            v_k_2218_ = leanh::lean_ctor_get(v_p_u2082_2212_, 0);
            leanh::lean_inc(v_k_2218_);
            leanh::lean_dec_ref_known(v_p_u2082_2212_, 1);
            v___x_2219_ = leanh::lean_apply_2(v_h__1_2213_, v_k_2217_, v_k_2218_);
            return v___x_2219_;
        } else {
            let mut v_k_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_2213_);
            v_k_2220_ = leanh::lean_ctor_get(v_p_u2081_2211_, 0);
            leanh::lean_inc(v_k_2220_);
            leanh::lean_dec_ref_known(v_p_u2081_2211_, 1);
            v_k_2221_ = leanh::lean_ctor_get(v_p_u2082_2212_, 0);
            leanh::lean_inc(v_k_2221_);
            v_v_2222_ = leanh::lean_ctor_get(v_p_u2082_2212_, 1);
            leanh::lean_inc(v_v_2222_);
            v_p_2223_ = leanh::lean_ctor_get(v_p_u2082_2212_, 2);
            leanh::lean_inc_ref(v_p_2223_);
            leanh::lean_dec_ref_known(v_p_u2082_2212_, 3);
            v___x_2224_ = leanh::lean_apply_4(
                v_h__2_2214_,
                v_k_2220_,
                v_k_2221_,
                v_v_2222_,
                v_p_2223_,
            );
            return v___x_2224_;
        }
    } else {
        leanh::lean_dec(v_h__2_2214_);
        leanh::lean_dec(v_h__1_2213_);
        if leanh::lean_obj_tag(v_p_u2082_2212_) == 0 {
            let mut v_k_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_2216_);
            v_k_2225_ = leanh::lean_ctor_get(v_p_u2081_2211_, 0);
            leanh::lean_inc(v_k_2225_);
            v_v_2226_ = leanh::lean_ctor_get(v_p_u2081_2211_, 1);
            leanh::lean_inc(v_v_2226_);
            v_p_2227_ = leanh::lean_ctor_get(v_p_u2081_2211_, 2);
            leanh::lean_inc_ref(v_p_2227_);
            leanh::lean_dec_ref_known(v_p_u2081_2211_, 3);
            v_k_2228_ = leanh::lean_ctor_get(v_p_u2082_2212_, 0);
            leanh::lean_inc(v_k_2228_);
            leanh::lean_dec_ref_known(v_p_u2082_2212_, 1);
            v___x_2229_ = leanh::lean_apply_4(
                v_h__3_2215_,
                v_k_2225_,
                v_v_2226_,
                v_p_2227_,
                v_k_2228_,
            );
            return v___x_2229_;
        } else {
            let mut v_k_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_2215_);
            v_k_2230_ = leanh::lean_ctor_get(v_p_u2081_2211_, 0);
            leanh::lean_inc(v_k_2230_);
            v_v_2231_ = leanh::lean_ctor_get(v_p_u2081_2211_, 1);
            leanh::lean_inc(v_v_2231_);
            v_p_2232_ = leanh::lean_ctor_get(v_p_u2081_2211_, 2);
            leanh::lean_inc_ref(v_p_2232_);
            leanh::lean_dec_ref_known(v_p_u2081_2211_, 3);
            v_k_2233_ = leanh::lean_ctor_get(v_p_u2082_2212_, 0);
            leanh::lean_inc(v_k_2233_);
            v_v_2234_ = leanh::lean_ctor_get(v_p_u2082_2212_, 1);
            leanh::lean_inc(v_v_2234_);
            v_p_2235_ = leanh::lean_ctor_get(v_p_u2082_2212_, 2);
            leanh::lean_inc_ref(v_p_2235_);
            leanh::lean_dec_ref_known(v_p_u2082_2212_, 3);
            v___x_2236_ = leanh::lean_apply_6(
                v_h__4_2216_,
                v_k_2230_,
                v_v_2231_,
                v_p_2232_,
                v_k_2233_,
                v_v_2234_,
                v_p_2235_,
            );
            return v___x_2236_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___redArg(
    mut v_x_2237_: u8,
    mut v_h__1_2238_: *mut leanh::LeanObject,
    mut v_h__2_2239_: *mut leanh::LeanObject,
    mut v_h__3_2240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match v_x_2237_ {
        0 => {
            let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_2239_);
            leanh::lean_dec(v_h__1_2238_);
            v___x_2241_ = leanh::lean_box(0);
            v___x_2242_ = leanh::lean_apply_1(v_h__3_2240_, v___x_2241_);
            return v___x_2242_;
        }
        1 => {
            let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_2240_);
            leanh::lean_dec(v_h__2_2239_);
            v___x_2243_ = leanh::lean_box(0);
            v___x_2244_ = leanh::lean_apply_1(v_h__1_2238_, v___x_2243_);
            return v___x_2244_;
        }
        _ => {
            let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_2240_);
            leanh::lean_dec(v_h__1_2238_);
            v___x_2245_ = leanh::lean_box(0);
            v___x_2246_ = leanh::lean_apply_1(v_h__2_2239_, v___x_2245_);
            return v___x_2246_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___redArg___boxed(
    mut v_x_2247_: *mut leanh::LeanObject,
    mut v_h__1_2248_: *mut leanh::LeanObject,
    mut v_h__2_2249_: *mut leanh::LeanObject,
    mut v_h__3_2250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_36__boxed_2251_: u8 = 0;
    let mut v_res_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_36__boxed_2251_ = (leanh::lean_unbox(v_x_2247_) as u8);
    v_res_2252_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___redArg(v_x_36__boxed_2251_, v_h__1_2248_, v_h__2_2249_, v_h__3_2250_);
    return v_res_2252_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter(
    mut v_motive_2253_: *mut leanh::LeanObject,
    mut v_x_2254_: u8,
    mut v_h__1_2255_: *mut leanh::LeanObject,
    mut v_h__2_2256_: *mut leanh::LeanObject,
    mut v_h__3_2257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match v_x_2254_ {
        0 => {
            let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_2256_);
            leanh::lean_dec(v_h__1_2255_);
            v___x_2258_ = leanh::lean_box(0);
            v___x_2259_ = leanh::lean_apply_1(v_h__3_2257_, v___x_2258_);
            return v___x_2259_;
        }
        1 => {
            let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_2257_);
            leanh::lean_dec(v_h__2_2256_);
            v___x_2260_ = leanh::lean_box(0);
            v___x_2261_ = leanh::lean_apply_1(v_h__1_2255_, v___x_2260_);
            return v___x_2261_;
        }
        _ => {
            let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_2257_);
            leanh::lean_dec(v_h__1_2255_);
            v___x_2262_ = leanh::lean_box(0);
            v___x_2263_ = leanh::lean_apply_1(v_h__2_2256_, v___x_2262_);
            return v___x_2263_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___boxed(
    mut v_motive_2264_: *mut leanh::LeanObject,
    mut v_x_2265_: *mut leanh::LeanObject,
    mut v_h__1_2266_: *mut leanh::LeanObject,
    mut v_h__2_2267_: *mut leanh::LeanObject,
    mut v_h__3_2268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_51__boxed_2269_: u8 = 0;
    let mut v_res_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_51__boxed_2269_ = (leanh::lean_unbox(v_x_2265_) as u8);
    v_res_2270_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter(v_motive_2264_, v_x_51__boxed_2269_, v_h__1_2266_, v_h__2_2267_, v_h__3_2268_);
    return v_res_2270_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go(
    mut v_p_u2082_2272_: *mut leanh::LeanObject,
    mut v_p_u2081_2273_: *mut leanh::LeanObject,
    mut v_acc_2274_: *mut leanh::LeanObject,
    mut v_a_2275_: *mut leanh::LeanObject,
    mut v_a_2276_: *mut leanh::LeanObject,
    mut v_a_2277_: *mut leanh::LeanObject,
    mut v_a_2278_: *mut leanh::LeanObject,
    mut v_a_2279_: *mut leanh::LeanObject,
    mut v_a_2280_: *mut leanh::LeanObject,
    mut v_a_2281_: *mut leanh::LeanObject,
    mut v_a_2282_: *mut leanh::LeanObject,
    mut v_a_2283_: *mut leanh::LeanObject,
    mut v_a_2284_: *mut leanh::LeanObject,
    mut v_a_2285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2299_: u8 = 0;
    let mut v_cancelTk_x3f_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2301_: u8 = 0;
    let mut v_inheritedTraceOptions_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2324_: u8 = 0;
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2328_: u8 = 0;
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: u8 = 0;
    let mut v___x_2331_: u8 = 0;
    let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_2287_ = leanh::lean_ctor_get(v_a_2284_, 0);
                leanh::lean_inc_ref(v_fileName_2287_);
                v_fileMap_2288_ = leanh::lean_ctor_get(v_a_2284_, 1);
                leanh::lean_inc_ref(v_fileMap_2288_);
                v_options_2289_ = leanh::lean_ctor_get(v_a_2284_, 2);
                leanh::lean_inc_ref(v_options_2289_);
                v_currRecDepth_2290_ = leanh::lean_ctor_get(v_a_2284_, 3);
                leanh::lean_inc(v_currRecDepth_2290_);
                v_maxRecDepth_2291_ = leanh::lean_ctor_get(v_a_2284_, 4);
                leanh::lean_inc(v_maxRecDepth_2291_);
                v_ref_2292_ = leanh::lean_ctor_get(v_a_2284_, 5);
                leanh::lean_inc(v_ref_2292_);
                v_currNamespace_2293_ = leanh::lean_ctor_get(v_a_2284_, 6);
                leanh::lean_inc(v_currNamespace_2293_);
                v_openDecls_2294_ = leanh::lean_ctor_get(v_a_2284_, 7);
                leanh::lean_inc(v_openDecls_2294_);
                v_initHeartbeats_2295_ = leanh::lean_ctor_get(v_a_2284_, 8);
                leanh::lean_inc(v_initHeartbeats_2295_);
                v_maxHeartbeats_2296_ = leanh::lean_ctor_get(v_a_2284_, 9);
                leanh::lean_inc(v_maxHeartbeats_2296_);
                v_quotContext_2297_ = leanh::lean_ctor_get(v_a_2284_, 10);
                leanh::lean_inc(v_quotContext_2297_);
                v_currMacroScope_2298_ = leanh::lean_ctor_get(v_a_2284_, 11);
                leanh::lean_inc(v_currMacroScope_2298_);
                v_diag_2299_ = leanh::lean_ctor_get_uint8(
                    v_a_2284_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_2300_ = leanh::lean_ctor_get(v_a_2284_, 12);
                leanh::lean_inc(v_cancelTk_x3f_2300_);
                v_suppressElabErrors_2301_ = leanh::lean_ctor_get_uint8(
                    v_a_2284_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_2302_ = leanh::lean_ctor_get(v_a_2284_, 13);
                leanh::lean_inc_ref(v_inheritedTraceOptions_2302_);
                leanh::lean_dec_ref(v_a_2284_);
                v___x_2329_ = leanh::lean_unsigned_to_nat(0);
                v___x_2330_ = lean_nat_dec_eq(v_maxRecDepth_2291_, v___x_2329_);
                if v___x_2330_ == 0 {
                    v___x_2331_ = lean_nat_dec_eq(v_currRecDepth_2290_, v_maxRecDepth_2291_);
                    if v___x_2331_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_inheritedTraceOptions_2302_);
                        leanh::lean_dec(v_cancelTk_x3f_2300_);
                        leanh::lean_dec(v_currMacroScope_2298_);
                        leanh::lean_dec(v_quotContext_2297_);
                        leanh::lean_dec(v_maxHeartbeats_2296_);
                        leanh::lean_dec(v_initHeartbeats_2295_);
                        leanh::lean_dec(v_openDecls_2294_);
                        leanh::lean_dec(v_currNamespace_2293_);
                        leanh::lean_dec(v_maxRecDepth_2291_);
                        leanh::lean_dec(v_currRecDepth_2290_);
                        leanh::lean_dec_ref(v_options_2289_);
                        leanh::lean_dec_ref(v_fileMap_2288_);
                        leanh::lean_dec_ref(v_fileName_2287_);
                        leanh::lean_dec_ref(v_acc_2274_);
                        leanh::lean_dec_ref(v_p_u2081_2273_);
                        leanh::lean_dec_ref(v_p_u2082_2272_);
                        v___x_2332_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(v_ref_2292_);
                        return v___x_2332_;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2304_ = leanh::lean_unsigned_to_nat(1);
                v___x_2305_ = lean_nat_add(v_currRecDepth_2290_, v___x_2304_);
                leanh::lean_dec(v_currRecDepth_2290_);
                v___x_2306_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_2306_, 0, v_fileName_2287_);
                leanh::lean_ctor_set(v___x_2306_, 1, v_fileMap_2288_);
                leanh::lean_ctor_set(v___x_2306_, 2, v_options_2289_);
                leanh::lean_ctor_set(v___x_2306_, 3, v___x_2305_);
                leanh::lean_ctor_set(v___x_2306_, 4, v_maxRecDepth_2291_);
                leanh::lean_ctor_set(v___x_2306_, 5, v_ref_2292_);
                leanh::lean_ctor_set(v___x_2306_, 6, v_currNamespace_2293_);
                leanh::lean_ctor_set(v___x_2306_, 7, v_openDecls_2294_);
                leanh::lean_ctor_set(v___x_2306_, 8, v_initHeartbeats_2295_);
                leanh::lean_ctor_set(v___x_2306_, 9, v_maxHeartbeats_2296_);
                leanh::lean_ctor_set(v___x_2306_, 10, v_quotContext_2297_);
                leanh::lean_ctor_set(v___x_2306_, 11, v_currMacroScope_2298_);
                leanh::lean_ctor_set(v___x_2306_, 12, v_cancelTk_x3f_2300_);
                leanh::lean_ctor_set(v___x_2306_, 13, v_inheritedTraceOptions_2302_);
                leanh::lean_ctor_set_uint8(
                    v___x_2306_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v_diag_2299_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2306_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_2301_,
                );
                if leanh::lean_obj_tag(v_p_u2081_2273_) == 0 {
                    v_k_2307_ = leanh::lean_ctor_get(v_p_u2081_2273_, 0);
                    leanh::lean_inc(v_k_2307_);
                    leanh::lean_dec_ref_known(v_p_u2081_2273_, 1);
                    v___x_2308_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v_k_2307_, v_p_u2082_2272_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v___x_2306_, v_a_2285_);
                    leanh::lean_dec(v_k_2307_);
                    if leanh::lean_obj_tag(v___x_2308_) == 0 {
                        v_a_2309_ = leanh::lean_ctor_get(v___x_2308_, 0);
                        leanh::lean_inc(v_a_2309_);
                        leanh::lean_dec_ref_known(v___x_2308_, 1);
                        v___x_2310_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_acc_2274_, v_a_2309_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v___x_2306_, v_a_2285_);
                        return v___x_2310_;
                    } else {
                        leanh::lean_dec_ref_known(v___x_2306_, 14);
                        leanh::lean_dec_ref(v_acc_2274_);
                        return v___x_2308_;
                    }
                } else {
                    v_k_2311_ = leanh::lean_ctor_get(v_p_u2081_2273_, 0);
                    leanh::lean_inc(v_k_2311_);
                    v_v_2312_ = leanh::lean_ctor_get(v_p_u2081_2273_, 1);
                    leanh::lean_inc(v_v_2312_);
                    v_p_2313_ = leanh::lean_ctor_get(v_p_u2081_2273_, 2);
                    leanh::lean_inc_ref(v_p_2313_);
                    leanh::lean_dec_ref_known(v_p_u2081_2273_, 3);
                    v___x_2314_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___closed__0;
                    v___x_2315_ = l_Lean_Core_checkSystem(v___x_2314_, v___x_2306_, v_a_2285_);
                    if leanh::lean_obj_tag(v___x_2315_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2315_, 1);
                        leanh::lean_inc_ref(v_p_u2082_2272_);
                        v___x_2316_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_k_2311_, v_v_2312_, v_p_u2082_2272_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v___x_2306_, v_a_2285_);
                        leanh::lean_dec(v_k_2311_);
                        if leanh::lean_obj_tag(v___x_2316_) == 0 {
                            v_a_2317_ = leanh::lean_ctor_get(v___x_2316_, 0);
                            leanh::lean_inc(v_a_2317_);
                            leanh::lean_dec_ref_known(v___x_2316_, 1);
                            leanh::lean_inc_ref(v___x_2306_);
                            v___x_2318_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_acc_2274_, v_a_2317_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v___x_2306_, v_a_2285_);
                            if leanh::lean_obj_tag(v___x_2318_) == 0 {
                                v_a_2319_ = leanh::lean_ctor_get(v___x_2318_, 0);
                                leanh::lean_inc(v_a_2319_);
                                leanh::lean_dec_ref_known(v___x_2318_, 1);
                                v_p_u2081_2273_ = v_p_2313_;
                                v_acc_2274_ = v_a_2319_;
                                v_a_2284_ = v___x_2306_;
                                state = 0;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_p_2313_);
                                leanh::lean_dec_ref_known(v___x_2306_, 14);
                                leanh::lean_dec_ref(v_p_u2082_2272_);
                                return v___x_2318_;
                            }
                        } else {
                            leanh::lean_dec_ref(v_p_2313_);
                            leanh::lean_dec_ref_known(v___x_2306_, 14);
                            leanh::lean_dec_ref(v_acc_2274_);
                            leanh::lean_dec_ref(v_p_u2082_2272_);
                            return v___x_2316_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_p_2313_);
                        leanh::lean_dec(v_v_2312_);
                        leanh::lean_dec(v_k_2311_);
                        leanh::lean_dec_ref_known(v___x_2306_, 14);
                        leanh::lean_dec_ref(v_acc_2274_);
                        leanh::lean_dec_ref(v_p_u2082_2272_);
                        v_a_2321_ = leanh::lean_ctor_get(v___x_2315_, 0);
                        v_isSharedCheck_2328_ =
                            (!leanh::lean_is_exclusive(v___x_2315_)) as u8;
                        if v_isSharedCheck_2328_ == 0 {
                            v___x_2323_ = v___x_2315_;
                            v_isShared_2324_ = v_isSharedCheck_2328_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2321_);
                            leanh::lean_dec(v___x_2315_);
                            v___x_2323_ = leanh::lean_box(0);
                            v_isShared_2324_ = v_isSharedCheck_2328_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_2324_ == 0 {
                    v___x_2326_ = v___x_2323_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2327_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
                    v___x_2326_ = v_reuseFailAlloc_2327_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2326_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___boxed(
    mut v_p_u2082_2333_: *mut leanh::LeanObject,
    mut v_p_u2081_2334_: *mut leanh::LeanObject,
    mut v_acc_2335_: *mut leanh::LeanObject,
    mut v_a_2336_: *mut leanh::LeanObject,
    mut v_a_2337_: *mut leanh::LeanObject,
    mut v_a_2338_: *mut leanh::LeanObject,
    mut v_a_2339_: *mut leanh::LeanObject,
    mut v_a_2340_: *mut leanh::LeanObject,
    mut v_a_2341_: *mut leanh::LeanObject,
    mut v_a_2342_: *mut leanh::LeanObject,
    mut v_a_2343_: *mut leanh::LeanObject,
    mut v_a_2344_: *mut leanh::LeanObject,
    mut v_a_2345_: *mut leanh::LeanObject,
    mut v_a_2346_: *mut leanh::LeanObject,
    mut v_a_2347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2348_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go(v_p_u2082_2333_, v_p_u2081_2334_, v_acc_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_);
    leanh::lean_dec(v_a_2346_);
    leanh::lean_dec(v_a_2344_);
    leanh::lean_dec_ref(v_a_2343_);
    leanh::lean_dec(v_a_2342_);
    leanh::lean_dec_ref(v_a_2341_);
    leanh::lean_dec(v_a_2340_);
    leanh::lean_dec_ref(v_a_2339_);
    leanh::lean_dec(v_a_2338_);
    leanh::lean_dec(v_a_2337_);
    leanh::lean_dec_ref(v_a_2336_);
    return v_res_2348_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2349_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
    v___x_2350_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2350_, 0, v___x_2349_);
    return v___x_2350_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(
    mut v_p_u2081_2351_: *mut leanh::LeanObject,
    mut v_p_u2082_2352_: *mut leanh::LeanObject,
    mut v_a_2353_: *mut leanh::LeanObject,
    mut v_a_2354_: *mut leanh::LeanObject,
    mut v_a_2355_: *mut leanh::LeanObject,
    mut v_a_2356_: *mut leanh::LeanObject,
    mut v_a_2357_: *mut leanh::LeanObject,
    mut v_a_2358_: *mut leanh::LeanObject,
    mut v_a_2359_: *mut leanh::LeanObject,
    mut v_a_2360_: *mut leanh::LeanObject,
    mut v_a_2361_: *mut leanh::LeanObject,
    mut v_a_2362_: *mut leanh::LeanObject,
    mut v_a_2363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2365_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0);
    leanh::lean_inc_ref(v_a_2362_);
    v___x_2366_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go(v_p_u2082_2352_, v_p_u2081_2351_, v___x_2365_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_);
    return v___x_2366_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___boxed(
    mut v_p_u2081_2367_: *mut leanh::LeanObject,
    mut v_p_u2082_2368_: *mut leanh::LeanObject,
    mut v_a_2369_: *mut leanh::LeanObject,
    mut v_a_2370_: *mut leanh::LeanObject,
    mut v_a_2371_: *mut leanh::LeanObject,
    mut v_a_2372_: *mut leanh::LeanObject,
    mut v_a_2373_: *mut leanh::LeanObject,
    mut v_a_2374_: *mut leanh::LeanObject,
    mut v_a_2375_: *mut leanh::LeanObject,
    mut v_a_2376_: *mut leanh::LeanObject,
    mut v_a_2377_: *mut leanh::LeanObject,
    mut v_a_2378_: *mut leanh::LeanObject,
    mut v_a_2379_: *mut leanh::LeanObject,
    mut v_a_2380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2381_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_p_u2081_2367_, v_p_u2082_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_);
    leanh::lean_dec(v_a_2379_);
    leanh::lean_dec_ref(v_a_2378_);
    leanh::lean_dec(v_a_2377_);
    leanh::lean_dec_ref(v_a_2376_);
    leanh::lean_dec(v_a_2375_);
    leanh::lean_dec_ref(v_a_2374_);
    leanh::lean_dec(v_a_2373_);
    leanh::lean_dec_ref(v_a_2372_);
    leanh::lean_dec(v_a_2371_);
    leanh::lean_dec(v_a_2370_);
    leanh::lean_dec_ref(v_a_2369_);
    return v_res_2381_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2382_ = leanh::lean_unsigned_to_nat(1);
    v___x_2383_ = lean_nat_to_int(v___x_2382_);
    return v___x_2383_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2384_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0);
    v___x_2385_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2385_, 0, v___x_2384_);
    return v___x_2385_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(
    mut v_p_2386_: *mut leanh::LeanObject,
    mut v_k_2387_: *mut leanh::LeanObject,
    mut v_a_2388_: *mut leanh::LeanObject,
    mut v_a_2389_: *mut leanh::LeanObject,
    mut v_a_2390_: *mut leanh::LeanObject,
    mut v_a_2391_: *mut leanh::LeanObject,
    mut v_a_2392_: *mut leanh::LeanObject,
    mut v_a_2393_: *mut leanh::LeanObject,
    mut v_a_2394_: *mut leanh::LeanObject,
    mut v_a_2395_: *mut leanh::LeanObject,
    mut v_a_2396_: *mut leanh::LeanObject,
    mut v_a_2397_: *mut leanh::LeanObject,
    mut v_a_2398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2412_: u8 = 0;
    let mut v_cancelTk_x3f_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2414_: u8 = 0;
    let mut v_inheritedTraceOptions_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2418_: u8 = 0;
    let mut v___x_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2423_: u8 = 0;
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2428_: u8 = 0;
    let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: u8 = 0;
    let mut v___x_2438_: u8 = 0;
    let mut v___x_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_2400_ = leanh::lean_ctor_get(v_a_2397_, 0);
                v_fileMap_2401_ = leanh::lean_ctor_get(v_a_2397_, 1);
                v_options_2402_ = leanh::lean_ctor_get(v_a_2397_, 2);
                v_currRecDepth_2403_ = leanh::lean_ctor_get(v_a_2397_, 3);
                v_maxRecDepth_2404_ = leanh::lean_ctor_get(v_a_2397_, 4);
                v_ref_2405_ = leanh::lean_ctor_get(v_a_2397_, 5);
                v_currNamespace_2406_ = leanh::lean_ctor_get(v_a_2397_, 6);
                v_openDecls_2407_ = leanh::lean_ctor_get(v_a_2397_, 7);
                v_initHeartbeats_2408_ = leanh::lean_ctor_get(v_a_2397_, 8);
                v_maxHeartbeats_2409_ = leanh::lean_ctor_get(v_a_2397_, 9);
                v_quotContext_2410_ = leanh::lean_ctor_get(v_a_2397_, 10);
                v_currMacroScope_2411_ = leanh::lean_ctor_get(v_a_2397_, 11);
                v_diag_2412_ = leanh::lean_ctor_get_uint8(
                    v_a_2397_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_2413_ = leanh::lean_ctor_get(v_a_2397_, 12);
                v_suppressElabErrors_2414_ = leanh::lean_ctor_get_uint8(
                    v_a_2397_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_2415_ = leanh::lean_ctor_get(v_a_2397_, 13);
                v___x_2436_ = leanh::lean_unsigned_to_nat(0);
                v___x_2437_ = lean_nat_dec_eq(v_maxRecDepth_2404_, v___x_2436_);
                if v___x_2437_ == 0 {
                    v___x_2438_ = lean_nat_dec_eq(v_currRecDepth_2403_, v_maxRecDepth_2404_);
                    if v___x_2438_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_p_2386_);
                        leanh::lean_inc(v_ref_2405_);
                        v___x_2439_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(v_ref_2405_);
                        return v___x_2439_;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_zero_2417_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_2418_ = lean_nat_dec_eq(v_k_2387_, v_zero_2417_);
                if v_isZero_2418_ == 1 {
                    leanh::lean_dec_ref(v_p_2386_);
                    v___x_2419_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1);
                    v___x_2420_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2420_, 0, v___x_2419_);
                    return v___x_2420_;
                } else {
                    v_one_2421_ = leanh::lean_unsigned_to_nat(1);
                    v_n_2422_ = lean_nat_sub(v_k_2387_, v_one_2421_);
                    v_isZero_2423_ = lean_nat_dec_eq(v_n_2422_, v_zero_2417_);
                    if v_isZero_2423_ == 1 {
                        leanh::lean_dec(v_n_2422_);
                        v___x_2424_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2424_, 0, v_p_2386_);
                        return v___x_2424_;
                    } else {
                        v_n_2425_ = lean_nat_sub(v_n_2422_, v_one_2421_);
                        leanh::lean_dec(v_n_2422_);
                        v___x_2426_ = lean_nat_add(v_currRecDepth_2403_, v_one_2421_);
                        leanh::lean_inc_ref(v_inheritedTraceOptions_2415_);
                        leanh::lean_inc(v_cancelTk_x3f_2413_);
                        leanh::lean_inc(v_currMacroScope_2411_);
                        leanh::lean_inc(v_quotContext_2410_);
                        leanh::lean_inc(v_maxHeartbeats_2409_);
                        leanh::lean_inc(v_initHeartbeats_2408_);
                        leanh::lean_inc(v_openDecls_2407_);
                        leanh::lean_inc(v_currNamespace_2406_);
                        leanh::lean_inc(v_ref_2405_);
                        leanh::lean_inc(v_maxRecDepth_2404_);
                        leanh::lean_inc_ref(v_options_2402_);
                        leanh::lean_inc_ref(v_fileMap_2401_);
                        leanh::lean_inc_ref(v_fileName_2400_);
                        v___x_2427_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                        leanh::lean_ctor_set(v___x_2427_, 0, v_fileName_2400_);
                        leanh::lean_ctor_set(v___x_2427_, 1, v_fileMap_2401_);
                        leanh::lean_ctor_set(v___x_2427_, 2, v_options_2402_);
                        leanh::lean_ctor_set(v___x_2427_, 3, v___x_2426_);
                        leanh::lean_ctor_set(v___x_2427_, 4, v_maxRecDepth_2404_);
                        leanh::lean_ctor_set(v___x_2427_, 5, v_ref_2405_);
                        leanh::lean_ctor_set(v___x_2427_, 6, v_currNamespace_2406_);
                        leanh::lean_ctor_set(v___x_2427_, 7, v_openDecls_2407_);
                        leanh::lean_ctor_set(v___x_2427_, 8, v_initHeartbeats_2408_);
                        leanh::lean_ctor_set(v___x_2427_, 9, v_maxHeartbeats_2409_);
                        leanh::lean_ctor_set(v___x_2427_, 10, v_quotContext_2410_);
                        leanh::lean_ctor_set(v___x_2427_, 11, v_currMacroScope_2411_);
                        leanh::lean_ctor_set(v___x_2427_, 12, v_cancelTk_x3f_2413_);
                        leanh::lean_ctor_set(v___x_2427_, 13, v_inheritedTraceOptions_2415_);
                        leanh::lean_ctor_set_uint8(
                            v___x_2427_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                            v_diag_2412_,
                        );
                        leanh::lean_ctor_set_uint8(
                            v___x_2427_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                            v_suppressElabErrors_2414_,
                        );
                        v_isZero_2428_ = lean_nat_dec_eq(v_n_2425_, v_zero_2417_);
                        if v_isZero_2428_ == 1 {
                            leanh::lean_dec(v_n_2425_);
                            leanh::lean_inc_ref(v_p_2386_);
                            v___x_2429_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_p_2386_, v_p_2386_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v___x_2427_, v_a_2398_);
                            leanh::lean_dec_ref_known(v___x_2427_, 14);
                            return v___x_2429_;
                        } else {
                            v_n_2430_ = lean_nat_sub(v_n_2425_, v_one_2421_);
                            leanh::lean_dec(v_n_2425_);
                            v___x_2431_ = leanh::lean_unsigned_to_nat(2);
                            v___x_2432_ = lean_nat_add(v_n_2430_, v___x_2431_);
                            leanh::lean_dec(v_n_2430_);
                            leanh::lean_inc_ref(v_p_2386_);
                            v___x_2433_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(v_p_2386_, v___x_2432_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v___x_2427_, v_a_2398_);
                            leanh::lean_dec(v___x_2432_);
                            if leanh::lean_obj_tag(v___x_2433_) == 0 {
                                v_a_2434_ = leanh::lean_ctor_get(v___x_2433_, 0);
                                leanh::lean_inc(v_a_2434_);
                                leanh::lean_dec_ref_known(v___x_2433_, 1);
                                v___x_2435_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_p_2386_, v_a_2434_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v___x_2427_, v_a_2398_);
                                leanh::lean_dec_ref_known(v___x_2427_, 14);
                                return v___x_2435_;
                            } else {
                                leanh::lean_dec_ref_known(v___x_2427_, 14);
                                leanh::lean_dec_ref(v_p_2386_);
                                return v___x_2433_;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___boxed(
    mut v_p_2440_: *mut leanh::LeanObject,
    mut v_k_2441_: *mut leanh::LeanObject,
    mut v_a_2442_: *mut leanh::LeanObject,
    mut v_a_2443_: *mut leanh::LeanObject,
    mut v_a_2444_: *mut leanh::LeanObject,
    mut v_a_2445_: *mut leanh::LeanObject,
    mut v_a_2446_: *mut leanh::LeanObject,
    mut v_a_2447_: *mut leanh::LeanObject,
    mut v_a_2448_: *mut leanh::LeanObject,
    mut v_a_2449_: *mut leanh::LeanObject,
    mut v_a_2450_: *mut leanh::LeanObject,
    mut v_a_2451_: *mut leanh::LeanObject,
    mut v_a_2452_: *mut leanh::LeanObject,
    mut v_a_2453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2454_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(v_p_2440_, v_k_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
    leanh::lean_dec(v_a_2452_);
    leanh::lean_dec_ref(v_a_2451_);
    leanh::lean_dec(v_a_2450_);
    leanh::lean_dec_ref(v_a_2449_);
    leanh::lean_dec(v_a_2448_);
    leanh::lean_dec_ref(v_a_2447_);
    leanh::lean_dec(v_a_2446_);
    leanh::lean_dec_ref(v_a_2445_);
    leanh::lean_dec(v_a_2444_);
    leanh::lean_dec(v_a_2443_);
    leanh::lean_dec_ref(v_a_2442_);
    leanh::lean_dec(v_k_2441_);
    return v_res_2454_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2455_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0);
    v___x_2456_ = lean_int_neg(v___x_2455_);
    return v___x_2456_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2457_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1);
    v___x_2458_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2458_, 0, v___x_2457_);
    return v___x_2458_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(
    mut v_e_2459_: *mut leanh::LeanObject,
    mut v_a_2460_: *mut leanh::LeanObject,
    mut v_a_2461_: *mut leanh::LeanObject,
    mut v_a_2462_: *mut leanh::LeanObject,
    mut v_a_2463_: *mut leanh::LeanObject,
    mut v_a_2464_: *mut leanh::LeanObject,
    mut v_a_2465_: *mut leanh::LeanObject,
    mut v_a_2466_: *mut leanh::LeanObject,
    mut v_a_2467_: *mut leanh::LeanObject,
    mut v_a_2468_: *mut leanh::LeanObject,
    mut v_a_2469_: *mut leanh::LeanObject,
    mut v_a_2470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2489_: u8 = 0;
    let mut v___x_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2495_: u8 = 0;
    let mut v_a_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2499_: u8 = 0;
    let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2503_: u8 = 0;
    let mut v_k_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2507_: u8 = 0;
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2513_: u8 = 0;
    let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2521_: u8 = 0;
    let mut v_a_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2525_: u8 = 0;
    let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2529_: u8 = 0;
    let mut v_isSharedCheck_2530_: u8 = 0;
    let mut v_i_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2534_: u8 = 0;
    let mut v___x_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2540_: u8 = 0;
    let mut v_a_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2547_: u8 = 0;
    let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2553_: u8 = 0;
    let mut v___x_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2560_: u8 = 0;
    let mut v_a_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2564_: u8 = 0;
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2568_: u8 = 0;
    let mut v_isSharedCheck_2569_: u8 = 0;
    let mut v_a_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2580_: u8 = 0;
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2585_: u8 = 0;
    let mut v___x_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2592_: u8 = 0;
    let mut v_a_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2596_: u8 = 0;
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2600_: u8 = 0;
    let mut v_isSharedCheck_2601_: u8 = 0;
    let mut v_a_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2612_: u8 = 0;
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2620_: u8 = 0;
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2627_: u8 = 0;
    let mut v_a_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2631_: u8 = 0;
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2635_: u8 = 0;
    let mut v_a_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2639_: u8 = 0;
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2643_: u8 = 0;
    let mut v_isSharedCheck_2644_: u8 = 0;
    let mut v_a_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2655_: u8 = 0;
    let mut v___x_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2660_: u8 = 0;
    let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2667_: u8 = 0;
    let mut v_a_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2671_: u8 = 0;
    let mut v___x_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2675_: u8 = 0;
    let mut v_isSharedCheck_2676_: u8 = 0;
    let mut v_a_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2681_: u8 = 0;
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: u8 = 0;
    let mut v_k_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2687_: u8 = 0;
    let mut v___x_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2692_: u8 = 0;
    let mut v___x_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2699_: u8 = 0;
    let mut v___x_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2707_: u8 = 0;
    let mut v_a_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2711_: u8 = 0;
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2715_: u8 = 0;
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2720_: u8 = 0;
    let mut v_a_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2724_: u8 = 0;
    let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2728_: u8 = 0;
    let mut v_isSharedCheck_2729_: u8 = 0;
    let mut v_i_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2733_: u8 = 0;
    let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2744_: u8 = 0;
    let mut v___x_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2750_: u8 = 0;
    let mut v___x_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2755_: u8 = 0;
    let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2762_: u8 = 0;
    let mut v_a_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2766_: u8 = 0;
    let mut v___x_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2770_: u8 = 0;
    let mut v_isSharedCheck_2771_: u8 = 0;
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2774_: u8 = 0;
    let mut v_k_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_e_2459_) {
                1 => {
                    v_k_2504_ = leanh::lean_ctor_get(v_e_2459_, 0);
                    v_isSharedCheck_2530_ = (!leanh::lean_is_exclusive(v_e_2459_)) as u8;
                    if v_isSharedCheck_2530_ == 0 {
                        v___x_2506_ = v_e_2459_;
                        v_isShared_2507_ = v_isSharedCheck_2530_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_2504_);
                        leanh::lean_dec(v_e_2459_);
                        v___x_2506_ = leanh::lean_box(0);
                        v_isShared_2507_ = v_isSharedCheck_2530_;
                        state = 6;
                        continue;
                    }
                }
                3 => {
                    v_i_2531_ = leanh::lean_ctor_get(v_e_2459_, 0);
                    v_isSharedCheck_2540_ = (!leanh::lean_is_exclusive(v_e_2459_)) as u8;
                    if v_isSharedCheck_2540_ == 0 {
                        v___x_2533_ = v_e_2459_;
                        v_isShared_2534_ = v_isSharedCheck_2540_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_i_2531_);
                        leanh::lean_dec(v_e_2459_);
                        v___x_2533_ = leanh::lean_box(0);
                        v_isShared_2534_ = v_isSharedCheck_2540_;
                        state = 12;
                        continue;
                    }
                }
                4 => {
                    v_a_2541_ = leanh::lean_ctor_get(v_e_2459_, 0);
                    leanh::lean_inc_ref(v_a_2541_);
                    leanh::lean_dec_ref_known(v_e_2459_, 1);
                    v___x_2542_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_2541_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                    if leanh::lean_obj_tag(v___x_2542_) == 0 {
                        v_a_2543_ = leanh::lean_ctor_get(v___x_2542_, 0);
                        leanh::lean_inc(v_a_2543_);
                        if leanh::lean_obj_tag(v_a_2543_) == 0 {
                            return v___x_2542_;
                        } else {
                            leanh::lean_dec_ref_known(v___x_2542_, 1);
                            v_val_2544_ = leanh::lean_ctor_get(v_a_2543_, 0);
                            v_isSharedCheck_2569_ =
                                (!leanh::lean_is_exclusive(v_a_2543_)) as u8;
                            if v_isSharedCheck_2569_ == 0 {
                                v___x_2546_ = v_a_2543_;
                                v_isShared_2547_ = v_isSharedCheck_2569_;
                                state = 14;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_2544_);
                                leanh::lean_dec(v_a_2543_);
                                v___x_2546_ = leanh::lean_box(0);
                                v_isShared_2547_ = v_isSharedCheck_2569_;
                                state = 14;
                                continue;
                            }
                        }
                    } else {
                        return v___x_2542_;
                    }
                }
                5 => {
                    v_a_2570_ = leanh::lean_ctor_get(v_e_2459_, 0);
                    leanh::lean_inc_ref(v_a_2570_);
                    v_b_2571_ = leanh::lean_ctor_get(v_e_2459_, 1);
                    leanh::lean_inc_ref(v_b_2571_);
                    leanh::lean_dec_ref_known(v_e_2459_, 2);
                    v___x_2572_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_2570_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                    if leanh::lean_obj_tag(v___x_2572_) == 0 {
                        v_a_2573_ = leanh::lean_ctor_get(v___x_2572_, 0);
                        leanh::lean_inc(v_a_2573_);
                        if leanh::lean_obj_tag(v_a_2573_) == 0 {
                            leanh::lean_dec_ref(v_b_2571_);
                            return v___x_2572_;
                        } else {
                            leanh::lean_dec_ref_known(v___x_2572_, 1);
                            v_val_2574_ = leanh::lean_ctor_get(v_a_2573_, 0);
                            leanh::lean_inc(v_val_2574_);
                            leanh::lean_dec_ref_known(v_a_2573_, 1);
                            v___x_2575_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_b_2571_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                            if leanh::lean_obj_tag(v___x_2575_) == 0 {
                                v_a_2576_ = leanh::lean_ctor_get(v___x_2575_, 0);
                                leanh::lean_inc(v_a_2576_);
                                if leanh::lean_obj_tag(v_a_2576_) == 0 {
                                    leanh::lean_dec(v_val_2574_);
                                    return v___x_2575_;
                                } else {
                                    leanh::lean_dec_ref_known(v___x_2575_, 1);
                                    v_val_2577_ = leanh::lean_ctor_get(v_a_2576_, 0);
                                    v_isSharedCheck_2601_ =
                                        (!leanh::lean_is_exclusive(v_a_2576_)) as u8;
                                    if v_isSharedCheck_2601_ == 0 {
                                        v___x_2579_ = v_a_2576_;
                                        v_isShared_2580_ = v_isSharedCheck_2601_;
                                        state = 20;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_val_2577_);
                                        leanh::lean_dec(v_a_2576_);
                                        v___x_2579_ = leanh::lean_box(0);
                                        v_isShared_2580_ = v_isSharedCheck_2601_;
                                        state = 20;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_val_2574_);
                                return v___x_2575_;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_2571_);
                        return v___x_2572_;
                    }
                }
                6 => {
                    v_a_2602_ = leanh::lean_ctor_get(v_e_2459_, 0);
                    leanh::lean_inc_ref(v_a_2602_);
                    v_b_2603_ = leanh::lean_ctor_get(v_e_2459_, 1);
                    leanh::lean_inc_ref(v_b_2603_);
                    leanh::lean_dec_ref_known(v_e_2459_, 2);
                    v___x_2604_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_2602_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                    if leanh::lean_obj_tag(v___x_2604_) == 0 {
                        v_a_2605_ = leanh::lean_ctor_get(v___x_2604_, 0);
                        leanh::lean_inc(v_a_2605_);
                        if leanh::lean_obj_tag(v_a_2605_) == 0 {
                            leanh::lean_dec_ref(v_b_2603_);
                            return v___x_2604_;
                        } else {
                            leanh::lean_dec_ref_known(v___x_2604_, 1);
                            v_val_2606_ = leanh::lean_ctor_get(v_a_2605_, 0);
                            leanh::lean_inc(v_val_2606_);
                            leanh::lean_dec_ref_known(v_a_2605_, 1);
                            v___x_2607_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_b_2603_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                            if leanh::lean_obj_tag(v___x_2607_) == 0 {
                                v_a_2608_ = leanh::lean_ctor_get(v___x_2607_, 0);
                                leanh::lean_inc(v_a_2608_);
                                if leanh::lean_obj_tag(v_a_2608_) == 0 {
                                    leanh::lean_dec(v_val_2606_);
                                    return v___x_2607_;
                                } else {
                                    leanh::lean_dec_ref_known(v___x_2607_, 1);
                                    v_val_2609_ = leanh::lean_ctor_get(v_a_2608_, 0);
                                    v_isSharedCheck_2644_ =
                                        (!leanh::lean_is_exclusive(v_a_2608_)) as u8;
                                    if v_isSharedCheck_2644_ == 0 {
                                        v___x_2611_ = v_a_2608_;
                                        v_isShared_2612_ = v_isSharedCheck_2644_;
                                        state = 26;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_val_2609_);
                                        leanh::lean_dec(v_a_2608_);
                                        v___x_2611_ = leanh::lean_box(0);
                                        v_isShared_2612_ = v_isSharedCheck_2644_;
                                        state = 26;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_val_2606_);
                                return v___x_2607_;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_2603_);
                        return v___x_2604_;
                    }
                }
                7 => {
                    v_a_2645_ = leanh::lean_ctor_get(v_e_2459_, 0);
                    leanh::lean_inc_ref(v_a_2645_);
                    v_b_2646_ = leanh::lean_ctor_get(v_e_2459_, 1);
                    leanh::lean_inc_ref(v_b_2646_);
                    leanh::lean_dec_ref_known(v_e_2459_, 2);
                    v___x_2647_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_2645_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                    if leanh::lean_obj_tag(v___x_2647_) == 0 {
                        v_a_2648_ = leanh::lean_ctor_get(v___x_2647_, 0);
                        leanh::lean_inc(v_a_2648_);
                        if leanh::lean_obj_tag(v_a_2648_) == 0 {
                            leanh::lean_dec_ref(v_b_2646_);
                            return v___x_2647_;
                        } else {
                            leanh::lean_dec_ref_known(v___x_2647_, 1);
                            v_val_2649_ = leanh::lean_ctor_get(v_a_2648_, 0);
                            leanh::lean_inc(v_val_2649_);
                            leanh::lean_dec_ref_known(v_a_2648_, 1);
                            v___x_2650_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_b_2646_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                            if leanh::lean_obj_tag(v___x_2650_) == 0 {
                                v_a_2651_ = leanh::lean_ctor_get(v___x_2650_, 0);
                                leanh::lean_inc(v_a_2651_);
                                if leanh::lean_obj_tag(v_a_2651_) == 0 {
                                    leanh::lean_dec(v_val_2649_);
                                    return v___x_2650_;
                                } else {
                                    leanh::lean_dec_ref_known(v___x_2650_, 1);
                                    v_val_2652_ = leanh::lean_ctor_get(v_a_2651_, 0);
                                    v_isSharedCheck_2676_ =
                                        (!leanh::lean_is_exclusive(v_a_2651_)) as u8;
                                    if v_isSharedCheck_2676_ == 0 {
                                        v___x_2654_ = v_a_2651_;
                                        v_isShared_2655_ = v_isSharedCheck_2676_;
                                        state = 34;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_val_2652_);
                                        leanh::lean_dec(v_a_2651_);
                                        v___x_2654_ = leanh::lean_box(0);
                                        v_isShared_2655_ = v_isSharedCheck_2676_;
                                        state = 34;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_val_2649_);
                                return v___x_2650_;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_2646_);
                        return v___x_2647_;
                    }
                }
                8 => {
                    v_a_2677_ = leanh::lean_ctor_get(v_e_2459_, 0);
                    v_k_2678_ = leanh::lean_ctor_get(v_e_2459_, 1);
                    v_isSharedCheck_2774_ = (!leanh::lean_is_exclusive(v_e_2459_)) as u8;
                    if v_isSharedCheck_2774_ == 0 {
                        v___x_2680_ = v_e_2459_;
                        v_isShared_2681_ = v_isSharedCheck_2774_;
                        state = 40;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_2678_);
                        leanh::lean_inc(v_a_2677_);
                        leanh::lean_dec(v_e_2459_);
                        v___x_2680_ = leanh::lean_box(0);
                        v_isShared_2681_ = v_isSharedCheck_2774_;
                        state = 40;
                        continue;
                    }
                }
                _ => {
                    v_k_2775_ = leanh::lean_ctor_get(v_e_2459_, 0);
                    leanh::lean_inc(v_k_2775_);
                    leanh::lean_dec_ref(v_e_2459_);
                    v_n_2473_ = v_k_2775_;
                    v___y_2474_ = v_a_2460_;
                    v___y_2475_ = v_a_2461_;
                    v___y_2476_ = v_a_2462_;
                    v___y_2477_ = v_a_2463_;
                    v___y_2478_ = v_a_2464_;
                    v___y_2479_ = v_a_2465_;
                    v___y_2480_ = v_a_2466_;
                    v___y_2481_ = v_a_2467_;
                    v___y_2482_ = v_a_2468_;
                    v___y_2483_ = v_a_2469_;
                    v___y_2484_ = v_a_2470_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_2485_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v_n_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
                if leanh::lean_obj_tag(v___x_2485_) == 0 {
                    v_a_2486_ = leanh::lean_ctor_get(v___x_2485_, 0);
                    v_isSharedCheck_2495_ = (!leanh::lean_is_exclusive(v___x_2485_)) as u8;
                    if v_isSharedCheck_2495_ == 0 {
                        v___x_2488_ = v___x_2485_;
                        v_isShared_2489_ = v_isSharedCheck_2495_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2486_);
                        leanh::lean_dec(v___x_2485_);
                        v___x_2488_ = leanh::lean_box(0);
                        v_isShared_2489_ = v_isSharedCheck_2495_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2496_ = leanh::lean_ctor_get(v___x_2485_, 0);
                    v_isSharedCheck_2503_ = (!leanh::lean_is_exclusive(v___x_2485_)) as u8;
                    if v_isSharedCheck_2503_ == 0 {
                        v___x_2498_ = v___x_2485_;
                        v_isShared_2499_ = v_isSharedCheck_2503_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2496_);
                        leanh::lean_dec(v___x_2485_);
                        v___x_2498_ = leanh::lean_box(0);
                        v_isShared_2499_ = v_isSharedCheck_2503_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2490_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2490_, 0, v_a_2486_);
                v___x_2491_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2491_, 0, v___x_2490_);
                if v_isShared_2489_ == 0 {
                    leanh::lean_ctor_set(v___x_2488_, 0, v___x_2491_);
                    v___x_2493_ = v___x_2488_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2494_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2494_, 0, v___x_2491_);
                    v___x_2493_ = v_reuseFailAlloc_2494_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2493_;
            }
            4 => {
                if v_isShared_2499_ == 0 {
                    v___x_2501_ = v___x_2498_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2502_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
                    v___x_2501_ = v_reuseFailAlloc_2502_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2501_;
            }
            6 => {
                v___x_2508_ = lean_nat_to_int(v_k_2504_);
                v___x_2509_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v___x_2508_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                if leanh::lean_obj_tag(v___x_2509_) == 0 {
                    v_a_2510_ = leanh::lean_ctor_get(v___x_2509_, 0);
                    v_isSharedCheck_2521_ = (!leanh::lean_is_exclusive(v___x_2509_)) as u8;
                    if v_isSharedCheck_2521_ == 0 {
                        v___x_2512_ = v___x_2509_;
                        v_isShared_2513_ = v_isSharedCheck_2521_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2510_);
                        leanh::lean_dec(v___x_2509_);
                        v___x_2512_ = leanh::lean_box(0);
                        v_isShared_2513_ = v_isSharedCheck_2521_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2506_);
                    v_a_2522_ = leanh::lean_ctor_get(v___x_2509_, 0);
                    v_isSharedCheck_2529_ = (!leanh::lean_is_exclusive(v___x_2509_)) as u8;
                    if v_isSharedCheck_2529_ == 0 {
                        v___x_2524_ = v___x_2509_;
                        v_isShared_2525_ = v_isSharedCheck_2529_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2522_);
                        leanh::lean_dec(v___x_2509_);
                        v___x_2524_ = leanh::lean_box(0);
                        v_isShared_2525_ = v_isSharedCheck_2529_;
                        state = 10;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_2507_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2506_, 0);
                    leanh::lean_ctor_set(v___x_2506_, 0, v_a_2510_);
                    v___x_2515_ = v___x_2506_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2520_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2510_);
                    v___x_2515_ = v_reuseFailAlloc_2520_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2516_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2516_, 0, v___x_2515_);
                if v_isShared_2513_ == 0 {
                    leanh::lean_ctor_set(v___x_2512_, 0, v___x_2516_);
                    v___x_2518_ = v___x_2512_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2519_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2516_);
                    v___x_2518_ = v_reuseFailAlloc_2519_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2518_;
            }
            10 => {
                if v_isShared_2525_ == 0 {
                    v___x_2527_ = v___x_2524_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2528_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2522_);
                    v___x_2527_ = v_reuseFailAlloc_2528_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2527_;
            }
            12 => {
                v___x_2535_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_2531_);
                if v_isShared_2534_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2533_, 1);
                    leanh::lean_ctor_set(v___x_2533_, 0, v___x_2535_);
                    v___x_2537_ = v___x_2533_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2539_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2535_);
                    v___x_2537_ = v_reuseFailAlloc_2539_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_2538_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2538_, 0, v___x_2537_);
                return v___x_2538_;
            }
            14 => {
                v___x_2548_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0);
                v___x_2549_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v___x_2548_, v_val_2544_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                if leanh::lean_obj_tag(v___x_2549_) == 0 {
                    v_a_2550_ = leanh::lean_ctor_get(v___x_2549_, 0);
                    v_isSharedCheck_2560_ = (!leanh::lean_is_exclusive(v___x_2549_)) as u8;
                    if v_isSharedCheck_2560_ == 0 {
                        v___x_2552_ = v___x_2549_;
                        v_isShared_2553_ = v_isSharedCheck_2560_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2550_);
                        leanh::lean_dec(v___x_2549_);
                        v___x_2552_ = leanh::lean_box(0);
                        v_isShared_2553_ = v_isSharedCheck_2560_;
                        state = 15;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2546_);
                    v_a_2561_ = leanh::lean_ctor_get(v___x_2549_, 0);
                    v_isSharedCheck_2568_ = (!leanh::lean_is_exclusive(v___x_2549_)) as u8;
                    if v_isSharedCheck_2568_ == 0 {
                        v___x_2563_ = v___x_2549_;
                        v_isShared_2564_ = v_isSharedCheck_2568_;
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2561_);
                        leanh::lean_dec(v___x_2549_);
                        v___x_2563_ = leanh::lean_box(0);
                        v_isShared_2564_ = v_isSharedCheck_2568_;
                        state = 18;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_2547_ == 0 {
                    leanh::lean_ctor_set(v___x_2546_, 0, v_a_2550_);
                    v___x_2555_ = v___x_2546_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2559_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2550_);
                    v___x_2555_ = v_reuseFailAlloc_2559_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_2553_ == 0 {
                    leanh::lean_ctor_set(v___x_2552_, 0, v___x_2555_);
                    v___x_2557_ = v___x_2552_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2558_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2555_);
                    v___x_2557_ = v_reuseFailAlloc_2558_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2557_;
            }
            18 => {
                if v_isShared_2564_ == 0 {
                    v___x_2566_ = v___x_2563_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2567_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
                    v___x_2566_ = v_reuseFailAlloc_2567_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2566_;
            }
            20 => {
                leanh::lean_inc_ref(v_a_2469_);
                v___x_2581_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_val_2574_, v_val_2577_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                if leanh::lean_obj_tag(v___x_2581_) == 0 {
                    v_a_2582_ = leanh::lean_ctor_get(v___x_2581_, 0);
                    v_isSharedCheck_2592_ = (!leanh::lean_is_exclusive(v___x_2581_)) as u8;
                    if v_isSharedCheck_2592_ == 0 {
                        v___x_2584_ = v___x_2581_;
                        v_isShared_2585_ = v_isSharedCheck_2592_;
                        state = 21;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2582_);
                        leanh::lean_dec(v___x_2581_);
                        v___x_2584_ = leanh::lean_box(0);
                        v_isShared_2585_ = v_isSharedCheck_2592_;
                        state = 21;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2579_);
                    v_a_2593_ = leanh::lean_ctor_get(v___x_2581_, 0);
                    v_isSharedCheck_2600_ = (!leanh::lean_is_exclusive(v___x_2581_)) as u8;
                    if v_isSharedCheck_2600_ == 0 {
                        v___x_2595_ = v___x_2581_;
                        v_isShared_2596_ = v_isSharedCheck_2600_;
                        state = 24;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2593_);
                        leanh::lean_dec(v___x_2581_);
                        v___x_2595_ = leanh::lean_box(0);
                        v_isShared_2596_ = v_isSharedCheck_2600_;
                        state = 24;
                        continue;
                    }
                }
            }
            21 => {
                if v_isShared_2580_ == 0 {
                    leanh::lean_ctor_set(v___x_2579_, 0, v_a_2582_);
                    v___x_2587_ = v___x_2579_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2591_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2582_);
                    v___x_2587_ = v_reuseFailAlloc_2591_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_2585_ == 0 {
                    leanh::lean_ctor_set(v___x_2584_, 0, v___x_2587_);
                    v___x_2589_ = v___x_2584_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2590_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2587_);
                    v___x_2589_ = v_reuseFailAlloc_2590_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_2589_;
            }
            24 => {
                if v_isShared_2596_ == 0 {
                    v___x_2598_ = v___x_2595_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_2599_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
                    v___x_2598_ = v_reuseFailAlloc_2599_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_2598_;
            }
            26 => {
                v___x_2613_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0);
                v___x_2614_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v___x_2613_, v_val_2609_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                if leanh::lean_obj_tag(v___x_2614_) == 0 {
                    v_a_2615_ = leanh::lean_ctor_get(v___x_2614_, 0);
                    leanh::lean_inc(v_a_2615_);
                    leanh::lean_dec_ref_known(v___x_2614_, 1);
                    leanh::lean_inc_ref(v_a_2469_);
                    v___x_2616_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_val_2606_, v_a_2615_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                    if leanh::lean_obj_tag(v___x_2616_) == 0 {
                        v_a_2617_ = leanh::lean_ctor_get(v___x_2616_, 0);
                        v_isSharedCheck_2627_ =
                            (!leanh::lean_is_exclusive(v___x_2616_)) as u8;
                        if v_isSharedCheck_2627_ == 0 {
                            v___x_2619_ = v___x_2616_;
                            v_isShared_2620_ = v_isSharedCheck_2627_;
                            state = 27;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2617_);
                            leanh::lean_dec(v___x_2616_);
                            v___x_2619_ = leanh::lean_box(0);
                            v_isShared_2620_ = v_isSharedCheck_2627_;
                            state = 27;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2611_);
                        v_a_2628_ = leanh::lean_ctor_get(v___x_2616_, 0);
                        v_isSharedCheck_2635_ =
                            (!leanh::lean_is_exclusive(v___x_2616_)) as u8;
                        if v_isSharedCheck_2635_ == 0 {
                            v___x_2630_ = v___x_2616_;
                            v_isShared_2631_ = v_isSharedCheck_2635_;
                            state = 30;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2628_);
                            leanh::lean_dec(v___x_2616_);
                            v___x_2630_ = leanh::lean_box(0);
                            v_isShared_2631_ = v_isSharedCheck_2635_;
                            state = 30;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_2611_);
                    leanh::lean_dec(v_val_2606_);
                    v_a_2636_ = leanh::lean_ctor_get(v___x_2614_, 0);
                    v_isSharedCheck_2643_ = (!leanh::lean_is_exclusive(v___x_2614_)) as u8;
                    if v_isSharedCheck_2643_ == 0 {
                        v___x_2638_ = v___x_2614_;
                        v_isShared_2639_ = v_isSharedCheck_2643_;
                        state = 32;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2636_);
                        leanh::lean_dec(v___x_2614_);
                        v___x_2638_ = leanh::lean_box(0);
                        v_isShared_2639_ = v_isSharedCheck_2643_;
                        state = 32;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_2612_ == 0 {
                    leanh::lean_ctor_set(v___x_2611_, 0, v_a_2617_);
                    v___x_2622_ = v___x_2611_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2626_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2617_);
                    v___x_2622_ = v_reuseFailAlloc_2626_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_2620_ == 0 {
                    leanh::lean_ctor_set(v___x_2619_, 0, v___x_2622_);
                    v___x_2624_ = v___x_2619_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_2625_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2622_);
                    v___x_2624_ = v_reuseFailAlloc_2625_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_2624_;
            }
            30 => {
                if v_isShared_2631_ == 0 {
                    v___x_2633_ = v___x_2630_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_2634_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_a_2628_);
                    v___x_2633_ = v_reuseFailAlloc_2634_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_2633_;
            }
            32 => {
                if v_isShared_2639_ == 0 {
                    v___x_2641_ = v___x_2638_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2642_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_a_2636_);
                    v___x_2641_ = v_reuseFailAlloc_2642_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_2641_;
            }
            34 => {
                v___x_2656_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_val_2649_, v_val_2652_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                if leanh::lean_obj_tag(v___x_2656_) == 0 {
                    v_a_2657_ = leanh::lean_ctor_get(v___x_2656_, 0);
                    v_isSharedCheck_2667_ = (!leanh::lean_is_exclusive(v___x_2656_)) as u8;
                    if v_isSharedCheck_2667_ == 0 {
                        v___x_2659_ = v___x_2656_;
                        v_isShared_2660_ = v_isSharedCheck_2667_;
                        state = 35;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2657_);
                        leanh::lean_dec(v___x_2656_);
                        v___x_2659_ = leanh::lean_box(0);
                        v_isShared_2660_ = v_isSharedCheck_2667_;
                        state = 35;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2654_);
                    v_a_2668_ = leanh::lean_ctor_get(v___x_2656_, 0);
                    v_isSharedCheck_2675_ = (!leanh::lean_is_exclusive(v___x_2656_)) as u8;
                    if v_isSharedCheck_2675_ == 0 {
                        v___x_2670_ = v___x_2656_;
                        v_isShared_2671_ = v_isSharedCheck_2675_;
                        state = 38;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2668_);
                        leanh::lean_dec(v___x_2656_);
                        v___x_2670_ = leanh::lean_box(0);
                        v_isShared_2671_ = v_isSharedCheck_2675_;
                        state = 38;
                        continue;
                    }
                }
            }
            35 => {
                if v_isShared_2655_ == 0 {
                    leanh::lean_ctor_set(v___x_2654_, 0, v_a_2657_);
                    v___x_2662_ = v___x_2654_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_2666_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2657_);
                    v___x_2662_ = v_reuseFailAlloc_2666_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                if v_isShared_2660_ == 0 {
                    leanh::lean_ctor_set(v___x_2659_, 0, v___x_2662_);
                    v___x_2664_ = v___x_2659_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2665_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2662_);
                    v___x_2664_ = v_reuseFailAlloc_2665_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_2664_;
            }
            38 => {
                if v_isShared_2671_ == 0 {
                    v___x_2673_ = v___x_2670_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_2674_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
                    v___x_2673_ = v_reuseFailAlloc_2674_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_2673_;
            }
            40 => {
                v___x_2682_ = leanh::lean_unsigned_to_nat(0);
                v___x_2683_ = lean_nat_dec_eq(v_k_2678_, v___x_2682_);
                if v___x_2683_ == 0 {
                    match leanh::lean_obj_tag(v_a_2677_) {
                        0 => {
                            leanh::lean_del_object(v___x_2680_);
                            v_k_2684_ = leanh::lean_ctor_get(v_a_2677_, 0);
                            v_isSharedCheck_2729_ =
                                (!leanh::lean_is_exclusive(v_a_2677_)) as u8;
                            if v_isSharedCheck_2729_ == 0 {
                                v___x_2686_ = v_a_2677_;
                                v_isShared_2687_ = v_isSharedCheck_2729_;
                                state = 41;
                                continue;
                            } else {
                                leanh::lean_inc(v_k_2684_);
                                leanh::lean_dec(v_a_2677_);
                                v___x_2686_ = leanh::lean_box(0);
                                v_isShared_2687_ = v_isSharedCheck_2729_;
                                state = 41;
                                continue;
                            }
                        }
                        3 => {
                            v_i_2730_ = leanh::lean_ctor_get(v_a_2677_, 0);
                            v_isSharedCheck_2744_ =
                                (!leanh::lean_is_exclusive(v_a_2677_)) as u8;
                            if v_isSharedCheck_2744_ == 0 {
                                v___x_2732_ = v_a_2677_;
                                v_isShared_2733_ = v_isSharedCheck_2744_;
                                state = 52;
                                continue;
                            } else {
                                leanh::lean_inc(v_i_2730_);
                                leanh::lean_dec(v_a_2677_);
                                v___x_2732_ = leanh::lean_box(0);
                                v_isShared_2733_ = v_isSharedCheck_2744_;
                                state = 52;
                                continue;
                            }
                        }
                        _ => {
                            leanh::lean_del_object(v___x_2680_);
                            v___x_2745_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_2677_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                            if leanh::lean_obj_tag(v___x_2745_) == 0 {
                                v_a_2746_ = leanh::lean_ctor_get(v___x_2745_, 0);
                                leanh::lean_inc(v_a_2746_);
                                if leanh::lean_obj_tag(v_a_2746_) == 0 {
                                    leanh::lean_dec(v_k_2678_);
                                    return v___x_2745_;
                                } else {
                                    leanh::lean_dec_ref_known(v___x_2745_, 1);
                                    v_val_2747_ = leanh::lean_ctor_get(v_a_2746_, 0);
                                    v_isSharedCheck_2771_ =
                                        (!leanh::lean_is_exclusive(v_a_2746_)) as u8;
                                    if v_isSharedCheck_2771_ == 0 {
                                        v___x_2749_ = v_a_2746_;
                                        v_isShared_2750_ = v_isSharedCheck_2771_;
                                        state = 55;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_val_2747_);
                                        leanh::lean_dec(v_a_2746_);
                                        v___x_2749_ = leanh::lean_box(0);
                                        v_isShared_2750_ = v_isSharedCheck_2771_;
                                        state = 55;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_k_2678_);
                                return v___x_2745_;
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_2680_);
                    leanh::lean_dec(v_k_2678_);
                    leanh::lean_dec_ref(v_a_2677_);
                    v___x_2772_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1);
                    v___x_2773_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2773_, 0, v___x_2772_);
                    return v___x_2773_;
                }
            }
            41 => {
                leanh::lean_inc(v_k_2678_);
                v___x_2688_ = l_Lean_Meta_Grind_Arith_checkExp___redArg(
                    v_k_2678_, v_a_2463_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_,
                    v_a_2470_,
                );
                if leanh::lean_obj_tag(v___x_2688_) == 0 {
                    v_a_2689_ = leanh::lean_ctor_get(v___x_2688_, 0);
                    v_isSharedCheck_2720_ = (!leanh::lean_is_exclusive(v___x_2688_)) as u8;
                    if v_isSharedCheck_2720_ == 0 {
                        v___x_2691_ = v___x_2688_;
                        v_isShared_2692_ = v_isSharedCheck_2720_;
                        state = 42;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2689_);
                        leanh::lean_dec(v___x_2688_);
                        v___x_2691_ = leanh::lean_box(0);
                        v_isShared_2692_ = v_isSharedCheck_2720_;
                        state = 42;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2686_);
                    leanh::lean_dec(v_k_2684_);
                    leanh::lean_dec(v_k_2678_);
                    v_a_2721_ = leanh::lean_ctor_get(v___x_2688_, 0);
                    v_isSharedCheck_2728_ = (!leanh::lean_is_exclusive(v___x_2688_)) as u8;
                    if v_isSharedCheck_2728_ == 0 {
                        v___x_2723_ = v___x_2688_;
                        v_isShared_2724_ = v_isSharedCheck_2728_;
                        state = 50;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2721_);
                        leanh::lean_dec(v___x_2688_);
                        v___x_2723_ = leanh::lean_box(0);
                        v_isShared_2724_ = v_isSharedCheck_2728_;
                        state = 50;
                        continue;
                    }
                }
            }
            42 => {
                if leanh::lean_obj_tag(v_a_2689_) == 0 {
                    if v___x_2683_ == 0 {
                        leanh::lean_del_object(v___x_2686_);
                        leanh::lean_dec(v_k_2684_);
                        leanh::lean_dec(v_k_2678_);
                        v___x_2716_ = leanh::lean_box(0);
                        if v_isShared_2692_ == 0 {
                            leanh::lean_ctor_set(v___x_2691_, 0, v___x_2716_);
                            v___x_2718_ = v___x_2691_;
                            state = 49;
                            continue;
                        } else {
                            v_reuseFailAlloc_2719_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2716_);
                            v___x_2718_ = v_reuseFailAlloc_2719_;
                            state = 49;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2691_);
                        state = 43;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_a_2689_, 1);
                    leanh::lean_del_object(v___x_2691_);
                    state = 43;
                    continue;
                }
            }
            43 => {
                v___x_2694_ = l_Int_pow(v_k_2684_, v_k_2678_);
                leanh::lean_dec(v_k_2678_);
                leanh::lean_dec(v_k_2684_);
                v___x_2695_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v___x_2694_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                if leanh::lean_obj_tag(v___x_2695_) == 0 {
                    v_a_2696_ = leanh::lean_ctor_get(v___x_2695_, 0);
                    v_isSharedCheck_2707_ = (!leanh::lean_is_exclusive(v___x_2695_)) as u8;
                    if v_isSharedCheck_2707_ == 0 {
                        v___x_2698_ = v___x_2695_;
                        v_isShared_2699_ = v_isSharedCheck_2707_;
                        state = 44;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2696_);
                        leanh::lean_dec(v___x_2695_);
                        v___x_2698_ = leanh::lean_box(0);
                        v_isShared_2699_ = v_isSharedCheck_2707_;
                        state = 44;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2686_);
                    v_a_2708_ = leanh::lean_ctor_get(v___x_2695_, 0);
                    v_isSharedCheck_2715_ = (!leanh::lean_is_exclusive(v___x_2695_)) as u8;
                    if v_isSharedCheck_2715_ == 0 {
                        v___x_2710_ = v___x_2695_;
                        v_isShared_2711_ = v_isSharedCheck_2715_;
                        state = 47;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2708_);
                        leanh::lean_dec(v___x_2695_);
                        v___x_2710_ = leanh::lean_box(0);
                        v_isShared_2711_ = v_isSharedCheck_2715_;
                        state = 47;
                        continue;
                    }
                }
            }
            44 => {
                if v_isShared_2687_ == 0 {
                    leanh::lean_ctor_set(v___x_2686_, 0, v_a_2696_);
                    v___x_2701_ = v___x_2686_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_2706_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_a_2696_);
                    v___x_2701_ = v_reuseFailAlloc_2706_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                v___x_2702_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2702_, 0, v___x_2701_);
                if v_isShared_2699_ == 0 {
                    leanh::lean_ctor_set(v___x_2698_, 0, v___x_2702_);
                    v___x_2704_ = v___x_2698_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_2705_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2705_, 0, v___x_2702_);
                    v___x_2704_ = v_reuseFailAlloc_2705_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_2704_;
            }
            47 => {
                if v_isShared_2711_ == 0 {
                    v___x_2713_ = v___x_2710_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_2714_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
                    v___x_2713_ = v_reuseFailAlloc_2714_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_2713_;
            }
            49 => {
                return v___x_2718_;
            }
            50 => {
                if v_isShared_2724_ == 0 {
                    v___x_2726_ = v___x_2723_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_2727_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2721_);
                    v___x_2726_ = v_reuseFailAlloc_2727_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                return v___x_2726_;
            }
            52 => {
                if v_isShared_2681_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2680_, 0);
                    leanh::lean_ctor_set(v___x_2680_, 0, v_i_2730_);
                    v___x_2735_ = v___x_2680_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_2743_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_i_2730_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2743_, 1, v_k_2678_);
                    v___x_2735_ = v_reuseFailAlloc_2743_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                v___x_2736_ = leanh::lean_box(0);
                v___x_2737_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2737_, 0, v___x_2735_);
                leanh::lean_ctor_set(v___x_2737_, 1, v___x_2736_);
                v___x_2738_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_2737_);
                if v_isShared_2733_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2732_, 1);
                    leanh::lean_ctor_set(v___x_2732_, 0, v___x_2738_);
                    v___x_2740_ = v___x_2732_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_2742_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2738_);
                    v___x_2740_ = v_reuseFailAlloc_2742_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                v___x_2741_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2741_, 0, v___x_2740_);
                return v___x_2741_;
            }
            55 => {
                v___x_2751_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(v_val_2747_, v_k_2678_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                leanh::lean_dec(v_k_2678_);
                if leanh::lean_obj_tag(v___x_2751_) == 0 {
                    v_a_2752_ = leanh::lean_ctor_get(v___x_2751_, 0);
                    v_isSharedCheck_2762_ = (!leanh::lean_is_exclusive(v___x_2751_)) as u8;
                    if v_isSharedCheck_2762_ == 0 {
                        v___x_2754_ = v___x_2751_;
                        v_isShared_2755_ = v_isSharedCheck_2762_;
                        state = 56;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2752_);
                        leanh::lean_dec(v___x_2751_);
                        v___x_2754_ = leanh::lean_box(0);
                        v_isShared_2755_ = v_isSharedCheck_2762_;
                        state = 56;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2749_);
                    v_a_2763_ = leanh::lean_ctor_get(v___x_2751_, 0);
                    v_isSharedCheck_2770_ = (!leanh::lean_is_exclusive(v___x_2751_)) as u8;
                    if v_isSharedCheck_2770_ == 0 {
                        v___x_2765_ = v___x_2751_;
                        v_isShared_2766_ = v_isSharedCheck_2770_;
                        state = 59;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2763_);
                        leanh::lean_dec(v___x_2751_);
                        v___x_2765_ = leanh::lean_box(0);
                        v_isShared_2766_ = v_isSharedCheck_2770_;
                        state = 59;
                        continue;
                    }
                }
            }
            56 => {
                if v_isShared_2750_ == 0 {
                    leanh::lean_ctor_set(v___x_2749_, 0, v_a_2752_);
                    v___x_2757_ = v___x_2749_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_2761_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2752_);
                    v___x_2757_ = v_reuseFailAlloc_2761_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                if v_isShared_2755_ == 0 {
                    leanh::lean_ctor_set(v___x_2754_, 0, v___x_2757_);
                    v___x_2759_ = v___x_2754_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_2760_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2760_, 0, v___x_2757_);
                    v___x_2759_ = v_reuseFailAlloc_2760_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                return v___x_2759_;
            }
            59 => {
                if v_isShared_2766_ == 0 {
                    v___x_2768_ = v___x_2765_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_2769_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
                    v___x_2768_ = v_reuseFailAlloc_2769_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                return v___x_2768_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___boxed(
    mut v_e_2776_: *mut leanh::LeanObject,
    mut v_a_2777_: *mut leanh::LeanObject,
    mut v_a_2778_: *mut leanh::LeanObject,
    mut v_a_2779_: *mut leanh::LeanObject,
    mut v_a_2780_: *mut leanh::LeanObject,
    mut v_a_2781_: *mut leanh::LeanObject,
    mut v_a_2782_: *mut leanh::LeanObject,
    mut v_a_2783_: *mut leanh::LeanObject,
    mut v_a_2784_: *mut leanh::LeanObject,
    mut v_a_2785_: *mut leanh::LeanObject,
    mut v_a_2786_: *mut leanh::LeanObject,
    mut v_a_2787_: *mut leanh::LeanObject,
    mut v_a_2788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2789_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_e_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_);
    leanh::lean_dec(v_a_2787_);
    leanh::lean_dec_ref(v_a_2786_);
    leanh::lean_dec(v_a_2785_);
    leanh::lean_dec_ref(v_a_2784_);
    leanh::lean_dec(v_a_2783_);
    leanh::lean_dec_ref(v_a_2782_);
    leanh::lean_dec(v_a_2781_);
    leanh::lean_dec_ref(v_a_2780_);
    leanh::lean_dec(v_a_2779_);
    leanh::lean_dec(v_a_2778_);
    leanh::lean_dec_ref(v_a_2777_);
    return v_res_2789_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_toPolyM_x3f(
    mut v_e_2790_: *mut leanh::LeanObject,
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
) -> *mut leanh::LeanObject {
    let mut v___x_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2803_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_e_2790_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_);
    return v___x_2803_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_toPolyM_x3f___boxed(
    mut v_e_2804_: *mut leanh::LeanObject,
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
    mut v_a_2815_: *mut leanh::LeanObject,
    mut v_a_2816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2817_ = l_Lean_Grind_CommRing_Expr_toPolyM_x3f(
        v_e_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_,
        v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_,
    );
    leanh::lean_dec(v_a_2815_);
    leanh::lean_dec_ref(v_a_2814_);
    leanh::lean_dec(v_a_2813_);
    leanh::lean_dec_ref(v_a_2812_);
    leanh::lean_dec(v_a_2811_);
    leanh::lean_dec_ref(v_a_2810_);
    leanh::lean_dec(v_a_2809_);
    leanh::lean_dec_ref(v_a_2808_);
    leanh::lean_dec(v_a_2807_);
    leanh::lean_dec(v_a_2806_);
    leanh::lean_dec_ref(v_a_2805_);
    return v_res_2817_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulConstM(
    mut v_p_2818_: *mut leanh::LeanObject,
    mut v_k_2819_: *mut leanh::LeanObject,
    mut v_a_2820_: *mut leanh::LeanObject,
    mut v_a_2821_: *mut leanh::LeanObject,
    mut v_a_2822_: *mut leanh::LeanObject,
    mut v_a_2823_: *mut leanh::LeanObject,
    mut v_a_2824_: *mut leanh::LeanObject,
    mut v_a_2825_: *mut leanh::LeanObject,
    mut v_a_2826_: *mut leanh::LeanObject,
    mut v_a_2827_: *mut leanh::LeanObject,
    mut v_a_2828_: *mut leanh::LeanObject,
    mut v_a_2829_: *mut leanh::LeanObject,
    mut v_a_2830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2832_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v_k_2819_, v_p_2818_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_);
    return v___x_2832_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulConstM___boxed(
    mut v_p_2833_: *mut leanh::LeanObject,
    mut v_k_2834_: *mut leanh::LeanObject,
    mut v_a_2835_: *mut leanh::LeanObject,
    mut v_a_2836_: *mut leanh::LeanObject,
    mut v_a_2837_: *mut leanh::LeanObject,
    mut v_a_2838_: *mut leanh::LeanObject,
    mut v_a_2839_: *mut leanh::LeanObject,
    mut v_a_2840_: *mut leanh::LeanObject,
    mut v_a_2841_: *mut leanh::LeanObject,
    mut v_a_2842_: *mut leanh::LeanObject,
    mut v_a_2843_: *mut leanh::LeanObject,
    mut v_a_2844_: *mut leanh::LeanObject,
    mut v_a_2845_: *mut leanh::LeanObject,
    mut v_a_2846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2847_ = l_Lean_Grind_CommRing_Poly_mulConstM(
        v_p_2833_, v_k_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_,
        v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_,
    );
    leanh::lean_dec(v_a_2845_);
    leanh::lean_dec_ref(v_a_2844_);
    leanh::lean_dec(v_a_2843_);
    leanh::lean_dec_ref(v_a_2842_);
    leanh::lean_dec(v_a_2841_);
    leanh::lean_dec_ref(v_a_2840_);
    leanh::lean_dec(v_a_2839_);
    leanh::lean_dec_ref(v_a_2838_);
    leanh::lean_dec(v_a_2837_);
    leanh::lean_dec(v_a_2836_);
    leanh::lean_dec_ref(v_a_2835_);
    leanh::lean_dec(v_k_2834_);
    return v_res_2847_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMonM(
    mut v_p_2848_: *mut leanh::LeanObject,
    mut v_k_2849_: *mut leanh::LeanObject,
    mut v_m_2850_: *mut leanh::LeanObject,
    mut v_a_2851_: *mut leanh::LeanObject,
    mut v_a_2852_: *mut leanh::LeanObject,
    mut v_a_2853_: *mut leanh::LeanObject,
    mut v_a_2854_: *mut leanh::LeanObject,
    mut v_a_2855_: *mut leanh::LeanObject,
    mut v_a_2856_: *mut leanh::LeanObject,
    mut v_a_2857_: *mut leanh::LeanObject,
    mut v_a_2858_: *mut leanh::LeanObject,
    mut v_a_2859_: *mut leanh::LeanObject,
    mut v_a_2860_: *mut leanh::LeanObject,
    mut v_a_2861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2863_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_k_2849_, v_m_2850_, v_p_2848_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_);
    return v___x_2863_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMonM___boxed(
    mut v_p_2864_: *mut leanh::LeanObject,
    mut v_k_2865_: *mut leanh::LeanObject,
    mut v_m_2866_: *mut leanh::LeanObject,
    mut v_a_2867_: *mut leanh::LeanObject,
    mut v_a_2868_: *mut leanh::LeanObject,
    mut v_a_2869_: *mut leanh::LeanObject,
    mut v_a_2870_: *mut leanh::LeanObject,
    mut v_a_2871_: *mut leanh::LeanObject,
    mut v_a_2872_: *mut leanh::LeanObject,
    mut v_a_2873_: *mut leanh::LeanObject,
    mut v_a_2874_: *mut leanh::LeanObject,
    mut v_a_2875_: *mut leanh::LeanObject,
    mut v_a_2876_: *mut leanh::LeanObject,
    mut v_a_2877_: *mut leanh::LeanObject,
    mut v_a_2878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2879_ = l_Lean_Grind_CommRing_Poly_mulMonM(
        v_p_2864_, v_k_2865_, v_m_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_,
        v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_,
    );
    leanh::lean_dec(v_a_2877_);
    leanh::lean_dec_ref(v_a_2876_);
    leanh::lean_dec(v_a_2875_);
    leanh::lean_dec_ref(v_a_2874_);
    leanh::lean_dec(v_a_2873_);
    leanh::lean_dec_ref(v_a_2872_);
    leanh::lean_dec(v_a_2871_);
    leanh::lean_dec_ref(v_a_2870_);
    leanh::lean_dec(v_a_2869_);
    leanh::lean_dec(v_a_2868_);
    leanh::lean_dec_ref(v_a_2867_);
    leanh::lean_dec(v_k_2865_);
    return v_res_2879_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulM(
    mut v_p_u2081_2880_: *mut leanh::LeanObject,
    mut v_p_u2082_2881_: *mut leanh::LeanObject,
    mut v_a_2882_: *mut leanh::LeanObject,
    mut v_a_2883_: *mut leanh::LeanObject,
    mut v_a_2884_: *mut leanh::LeanObject,
    mut v_a_2885_: *mut leanh::LeanObject,
    mut v_a_2886_: *mut leanh::LeanObject,
    mut v_a_2887_: *mut leanh::LeanObject,
    mut v_a_2888_: *mut leanh::LeanObject,
    mut v_a_2889_: *mut leanh::LeanObject,
    mut v_a_2890_: *mut leanh::LeanObject,
    mut v_a_2891_: *mut leanh::LeanObject,
    mut v_a_2892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2894_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_p_u2081_2880_, v_p_u2082_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_);
    return v___x_2894_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulM___boxed(
    mut v_p_u2081_2895_: *mut leanh::LeanObject,
    mut v_p_u2082_2896_: *mut leanh::LeanObject,
    mut v_a_2897_: *mut leanh::LeanObject,
    mut v_a_2898_: *mut leanh::LeanObject,
    mut v_a_2899_: *mut leanh::LeanObject,
    mut v_a_2900_: *mut leanh::LeanObject,
    mut v_a_2901_: *mut leanh::LeanObject,
    mut v_a_2902_: *mut leanh::LeanObject,
    mut v_a_2903_: *mut leanh::LeanObject,
    mut v_a_2904_: *mut leanh::LeanObject,
    mut v_a_2905_: *mut leanh::LeanObject,
    mut v_a_2906_: *mut leanh::LeanObject,
    mut v_a_2907_: *mut leanh::LeanObject,
    mut v_a_2908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2909_ = l_Lean_Grind_CommRing_Poly_mulM(
        v_p_u2081_2895_,
        v_p_u2082_2896_,
        v_a_2897_,
        v_a_2898_,
        v_a_2899_,
        v_a_2900_,
        v_a_2901_,
        v_a_2902_,
        v_a_2903_,
        v_a_2904_,
        v_a_2905_,
        v_a_2906_,
        v_a_2907_,
    );
    leanh::lean_dec(v_a_2907_);
    leanh::lean_dec_ref(v_a_2906_);
    leanh::lean_dec(v_a_2905_);
    leanh::lean_dec_ref(v_a_2904_);
    leanh::lean_dec(v_a_2903_);
    leanh::lean_dec_ref(v_a_2902_);
    leanh::lean_dec(v_a_2901_);
    leanh::lean_dec_ref(v_a_2900_);
    leanh::lean_dec(v_a_2899_);
    leanh::lean_dec(v_a_2898_);
    leanh::lean_dec_ref(v_a_2897_);
    return v_res_2909_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_combineM(
    mut v_p_u2081_2910_: *mut leanh::LeanObject,
    mut v_p_u2082_2911_: *mut leanh::LeanObject,
    mut v_a_2912_: *mut leanh::LeanObject,
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
) -> *mut leanh::LeanObject {
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_a_2921_);
    v___x_2924_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_p_u2081_2910_, v_p_u2082_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_);
    return v___x_2924_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_combineM___boxed(
    mut v_p_u2081_2925_: *mut leanh::LeanObject,
    mut v_p_u2082_2926_: *mut leanh::LeanObject,
    mut v_a_2927_: *mut leanh::LeanObject,
    mut v_a_2928_: *mut leanh::LeanObject,
    mut v_a_2929_: *mut leanh::LeanObject,
    mut v_a_2930_: *mut leanh::LeanObject,
    mut v_a_2931_: *mut leanh::LeanObject,
    mut v_a_2932_: *mut leanh::LeanObject,
    mut v_a_2933_: *mut leanh::LeanObject,
    mut v_a_2934_: *mut leanh::LeanObject,
    mut v_a_2935_: *mut leanh::LeanObject,
    mut v_a_2936_: *mut leanh::LeanObject,
    mut v_a_2937_: *mut leanh::LeanObject,
    mut v_a_2938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2939_ = l_Lean_Grind_CommRing_Poly_combineM(
        v_p_u2081_2925_,
        v_p_u2082_2926_,
        v_a_2927_,
        v_a_2928_,
        v_a_2929_,
        v_a_2930_,
        v_a_2931_,
        v_a_2932_,
        v_a_2933_,
        v_a_2934_,
        v_a_2935_,
        v_a_2936_,
        v_a_2937_,
    );
    leanh::lean_dec(v_a_2937_);
    leanh::lean_dec_ref(v_a_2936_);
    leanh::lean_dec(v_a_2935_);
    leanh::lean_dec_ref(v_a_2934_);
    leanh::lean_dec(v_a_2933_);
    leanh::lean_dec_ref(v_a_2932_);
    leanh::lean_dec(v_a_2931_);
    leanh::lean_dec_ref(v_a_2930_);
    leanh::lean_dec(v_a_2929_);
    leanh::lean_dec(v_a_2928_);
    leanh::lean_dec_ref(v_a_2927_);
    return v_res_2939_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_Poly_spolM___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2940_ = leanh::lean_box(0);
    v___x_2941_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
    v___x_2942_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0);
    v___x_2943_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_2943_, 0, v___x_2942_);
    leanh::lean_ctor_set(v___x_2943_, 1, v___x_2941_);
    leanh::lean_ctor_set(v___x_2943_, 2, v___x_2940_);
    leanh::lean_ctor_set(v___x_2943_, 3, v___x_2941_);
    leanh::lean_ctor_set(v___x_2943_, 4, v___x_2940_);
    return v___x_2943_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_spolM(
    mut v_p_u2081_2944_: *mut leanh::LeanObject,
    mut v_p_u2082_2945_: *mut leanh::LeanObject,
    mut v_a_2946_: *mut leanh::LeanObject,
    mut v_a_2947_: *mut leanh::LeanObject,
    mut v_a_2948_: *mut leanh::LeanObject,
    mut v_a_2949_: *mut leanh::LeanObject,
    mut v_a_2950_: *mut leanh::LeanObject,
    mut v_a_2951_: *mut leanh::LeanObject,
    mut v_a_2952_: *mut leanh::LeanObject,
    mut v_a_2953_: *mut leanh::LeanObject,
    mut v_a_2954_: *mut leanh::LeanObject,
    mut v_a_2955_: *mut leanh::LeanObject,
    mut v_a_2956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_u2081_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_g_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_u2081_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_u2082_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_u2082_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2985_: u8 = 0;
    let mut v___x_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2990_: u8 = 0;
    let mut v_a_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2994_: u8 = 0;
    let mut v___x_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2998_: u8 = 0;
    let mut v_a_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3002_: u8 = 0;
    let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3006_: u8 = 0;
    let mut v_a_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3010_: u8 = 0;
    let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3014_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_p_u2081_2944_) == 1 {
                    if leanh::lean_obj_tag(v_p_u2082_2945_) == 1 {
                        v_k_2961_ = leanh::lean_ctor_get(v_p_u2081_2944_, 0);
                        leanh::lean_inc(v_k_2961_);
                        v_v_2962_ = leanh::lean_ctor_get(v_p_u2081_2944_, 1);
                        leanh::lean_inc_n(v_v_2962_, 2);
                        v_p_2963_ = leanh::lean_ctor_get(v_p_u2081_2944_, 2);
                        leanh::lean_inc_ref(v_p_2963_);
                        leanh::lean_dec_ref_known(v_p_u2081_2944_, 3);
                        v_k_2964_ = leanh::lean_ctor_get(v_p_u2082_2945_, 0);
                        leanh::lean_inc(v_k_2964_);
                        v_v_2965_ = leanh::lean_ctor_get(v_p_u2082_2945_, 1);
                        leanh::lean_inc_n(v_v_2965_, 2);
                        v_p_2966_ = leanh::lean_ctor_get(v_p_u2082_2945_, 2);
                        leanh::lean_inc_ref(v_p_2966_);
                        leanh::lean_dec_ref_known(v_p_u2082_2945_, 3);
                        v_m_2967_ = l_Lean_Grind_CommRing_Mon_lcm(v_v_2962_, v_v_2965_);
                        leanh::lean_inc(v_m_2967_);
                        v_m_u2081_2968_ = l_Lean_Grind_CommRing_Mon_div(v_m_2967_, v_v_2962_);
                        v___x_2969_ = lean_nat_abs(v_k_2961_);
                        v___x_2970_ = lean_nat_abs(v_k_2964_);
                        v_g_2971_ = lean_nat_gcd(v___x_2969_, v___x_2970_);
                        leanh::lean_dec(v___x_2970_);
                        leanh::lean_dec(v___x_2969_);
                        v___x_2972_ = lean_nat_to_int(v_g_2971_);
                        v_c_u2081_2973_ = lean_int_ediv(v_k_2964_, v___x_2972_);
                        leanh::lean_dec(v_k_2964_);
                        leanh::lean_inc(v_m_u2081_2968_);
                        v___x_2974_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_c_u2081_2973_, v_m_u2081_2968_, v_p_2963_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_);
                        if leanh::lean_obj_tag(v___x_2974_) == 0 {
                            v_a_2975_ = leanh::lean_ctor_get(v___x_2974_, 0);
                            leanh::lean_inc(v_a_2975_);
                            leanh::lean_dec_ref_known(v___x_2974_, 1);
                            v_m_u2082_2976_ = l_Lean_Grind_CommRing_Mon_div(v_m_2967_, v_v_2965_);
                            v___x_2977_ = lean_int_neg(v_k_2961_);
                            leanh::lean_dec(v_k_2961_);
                            v_c_u2082_2978_ = lean_int_ediv(v___x_2977_, v___x_2972_);
                            leanh::lean_dec(v___x_2972_);
                            leanh::lean_dec(v___x_2977_);
                            leanh::lean_inc(v_m_u2082_2976_);
                            v___x_2979_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_c_u2082_2978_, v_m_u2082_2976_, v_p_2966_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_);
                            if leanh::lean_obj_tag(v___x_2979_) == 0 {
                                v_a_2980_ = leanh::lean_ctor_get(v___x_2979_, 0);
                                leanh::lean_inc(v_a_2980_);
                                leanh::lean_dec_ref_known(v___x_2979_, 1);
                                leanh::lean_inc_ref(v_a_2955_);
                                v___x_2981_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_a_2975_, v_a_2980_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_);
                                if leanh::lean_obj_tag(v___x_2981_) == 0 {
                                    v_a_2982_ = leanh::lean_ctor_get(v___x_2981_, 0);
                                    v_isSharedCheck_2990_ =
                                        (!leanh::lean_is_exclusive(v___x_2981_)) as u8;
                                    if v_isSharedCheck_2990_ == 0 {
                                        v___x_2984_ = v___x_2981_;
                                        v_isShared_2985_ = v_isSharedCheck_2990_;
                                        state = 2;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2982_);
                                        leanh::lean_dec(v___x_2981_);
                                        v___x_2984_ = leanh::lean_box(0);
                                        v_isShared_2985_ = v_isSharedCheck_2990_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_c_u2082_2978_);
                                    leanh::lean_dec(v_m_u2082_2976_);
                                    leanh::lean_dec(v_c_u2081_2973_);
                                    leanh::lean_dec(v_m_u2081_2968_);
                                    v_a_2991_ = leanh::lean_ctor_get(v___x_2981_, 0);
                                    v_isSharedCheck_2998_ =
                                        (!leanh::lean_is_exclusive(v___x_2981_)) as u8;
                                    if v_isSharedCheck_2998_ == 0 {
                                        v___x_2993_ = v___x_2981_;
                                        v_isShared_2994_ = v_isSharedCheck_2998_;
                                        state = 4;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2991_);
                                        leanh::lean_dec(v___x_2981_);
                                        v___x_2993_ = leanh::lean_box(0);
                                        v_isShared_2994_ = v_isSharedCheck_2998_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_c_u2082_2978_);
                                leanh::lean_dec(v_m_u2082_2976_);
                                leanh::lean_dec(v_a_2975_);
                                leanh::lean_dec(v_c_u2081_2973_);
                                leanh::lean_dec(v_m_u2081_2968_);
                                v_a_2999_ = leanh::lean_ctor_get(v___x_2979_, 0);
                                v_isSharedCheck_3006_ =
                                    (!leanh::lean_is_exclusive(v___x_2979_)) as u8;
                                if v_isSharedCheck_3006_ == 0 {
                                    v___x_3001_ = v___x_2979_;
                                    v_isShared_3002_ = v_isSharedCheck_3006_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2999_);
                                    leanh::lean_dec(v___x_2979_);
                                    v___x_3001_ = leanh::lean_box(0);
                                    v_isShared_3002_ = v_isSharedCheck_3006_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_c_u2081_2973_);
                            leanh::lean_dec(v___x_2972_);
                            leanh::lean_dec(v_m_u2081_2968_);
                            leanh::lean_dec(v_m_2967_);
                            leanh::lean_dec_ref(v_p_2966_);
                            leanh::lean_dec(v_v_2965_);
                            leanh::lean_dec(v_k_2961_);
                            v_a_3007_ = leanh::lean_ctor_get(v___x_2974_, 0);
                            v_isSharedCheck_3014_ =
                                (!leanh::lean_is_exclusive(v___x_2974_)) as u8;
                            if v_isSharedCheck_3014_ == 0 {
                                v___x_3009_ = v___x_2974_;
                                v_isShared_3010_ = v_isSharedCheck_3014_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3007_);
                                leanh::lean_dec(v___x_2974_);
                                v___x_3009_ = leanh::lean_box(0);
                                v_isShared_3010_ = v_isSharedCheck_3014_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_p_u2081_2944_, 3);
                        leanh::lean_dec_ref(v_p_u2082_2945_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_p_u2082_2945_);
                    leanh::lean_dec_ref(v_p_u2081_2944_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2959_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_spolM___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_spolM___closed__0_once),
                    _init_l_Lean_Grind_CommRing_Poly_spolM___closed__0,
                );
                v___x_2960_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2960_, 0, v___x_2959_);
                return v___x_2960_;
            }
            2 => {
                v___x_2986_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_2986_, 0, v_a_2982_);
                leanh::lean_ctor_set(v___x_2986_, 1, v_c_u2081_2973_);
                leanh::lean_ctor_set(v___x_2986_, 2, v_m_u2081_2968_);
                leanh::lean_ctor_set(v___x_2986_, 3, v_c_u2082_2978_);
                leanh::lean_ctor_set(v___x_2986_, 4, v_m_u2082_2976_);
                if v_isShared_2985_ == 0 {
                    leanh::lean_ctor_set(v___x_2984_, 0, v___x_2986_);
                    v___x_2988_ = v___x_2984_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2989_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2989_, 0, v___x_2986_);
                    v___x_2988_ = v_reuseFailAlloc_2989_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2988_;
            }
            4 => {
                if v_isShared_2994_ == 0 {
                    v___x_2996_ = v___x_2993_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2997_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2991_);
                    v___x_2996_ = v_reuseFailAlloc_2997_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2996_;
            }
            6 => {
                if v_isShared_3002_ == 0 {
                    v___x_3004_ = v___x_3001_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3005_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
                    v___x_3004_ = v_reuseFailAlloc_3005_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3004_;
            }
            8 => {
                if v_isShared_3010_ == 0 {
                    v___x_3012_ = v___x_3009_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3013_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
                    v___x_3012_ = v_reuseFailAlloc_3013_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3012_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_spolM___boxed(
    mut v_p_u2081_3015_: *mut leanh::LeanObject,
    mut v_p_u2082_3016_: *mut leanh::LeanObject,
    mut v_a_3017_: *mut leanh::LeanObject,
    mut v_a_3018_: *mut leanh::LeanObject,
    mut v_a_3019_: *mut leanh::LeanObject,
    mut v_a_3020_: *mut leanh::LeanObject,
    mut v_a_3021_: *mut leanh::LeanObject,
    mut v_a_3022_: *mut leanh::LeanObject,
    mut v_a_3023_: *mut leanh::LeanObject,
    mut v_a_3024_: *mut leanh::LeanObject,
    mut v_a_3025_: *mut leanh::LeanObject,
    mut v_a_3026_: *mut leanh::LeanObject,
    mut v_a_3027_: *mut leanh::LeanObject,
    mut v_a_3028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3029_ = l_Lean_Grind_CommRing_Poly_spolM(
        v_p_u2081_3015_,
        v_p_u2082_3016_,
        v_a_3017_,
        v_a_3018_,
        v_a_3019_,
        v_a_3020_,
        v_a_3021_,
        v_a_3022_,
        v_a_3023_,
        v_a_3024_,
        v_a_3025_,
        v_a_3026_,
        v_a_3027_,
    );
    leanh::lean_dec(v_a_3027_);
    leanh::lean_dec_ref(v_a_3026_);
    leanh::lean_dec(v_a_3025_);
    leanh::lean_dec_ref(v_a_3024_);
    leanh::lean_dec(v_a_3023_);
    leanh::lean_dec_ref(v_a_3022_);
    leanh::lean_dec(v_a_3021_);
    leanh::lean_dec_ref(v_a_3020_);
    leanh::lean_dec(v_a_3019_);
    leanh::lean_dec(v_a_3018_);
    leanh::lean_dec_ref(v_a_3017_);
    return v_res_3029_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(
    mut v_m_3040_: *mut leanh::LeanObject,
    mut v_a_3041_: *mut leanh::LeanObject,
    mut v_a_3042_: *mut leanh::LeanObject,
    mut v_a_3043_: *mut leanh::LeanObject,
    mut v_a_3044_: *mut leanh::LeanObject,
    mut v_a_3045_: *mut leanh::LeanObject,
    mut v_a_3046_: *mut leanh::LeanObject,
    mut v_a_3047_: *mut leanh::LeanObject,
    mut v_a_3048_: *mut leanh::LeanObject,
    mut v_a_3049_: *mut leanh::LeanObject,
    mut v_a_3050_: *mut leanh::LeanObject,
    mut v_a_3051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toRing_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3064_: u8 = 0;
    let mut v___y_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: u8 = 0;
    let mut v_arg_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: u8 = 0;
    let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: u8 = 0;
    let mut v___x_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: u8 = 0;
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: u8 = 0;
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: u8 = 0;
    let mut v_arg_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: u8 = 0;
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: u8 = 0;
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3099_: u8 = 0;
    let mut v_val_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3103_: u8 = 0;
    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3113_: u8 = 0;
    let mut v_isSharedCheck_3115_: u8 = 0;
    let mut v_a_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3119_: u8 = 0;
    let mut v___x_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3123_: u8 = 0;
    let mut v_size_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: u8 = 0;
    let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3129_: u8 = 0;
    let mut v_unused_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3134_: u8 = 0;
    let mut v___x_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3138_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_m_3040_) == 0 {
                    v___x_3053_ = leanh::lean_box(0);
                    v___x_3054_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3054_, 0, v___x_3053_);
                    return v___x_3054_;
                } else {
                    v_p_3055_ = leanh::lean_ctor_get(v_m_3040_, 0);
                    leanh::lean_inc_ref(v_p_3055_);
                    v_m_3056_ = leanh::lean_ctor_get(v_m_3040_, 1);
                    leanh::lean_inc(v_m_3056_);
                    leanh::lean_dec_ref_known(v_m_3040_, 2);
                    v___x_3057_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                        v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_,
                        v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_,
                    );
                    if leanh::lean_obj_tag(v___x_3057_) == 0 {
                        v_a_3058_ = leanh::lean_ctor_get(v___x_3057_, 0);
                        leanh::lean_inc(v_a_3058_);
                        leanh::lean_dec_ref_known(v___x_3057_, 1);
                        v_toRing_3059_ = leanh::lean_ctor_get(v_a_3058_, 0);
                        leanh::lean_inc_ref(v_toRing_3059_);
                        leanh::lean_dec(v_a_3058_);
                        v_vars_3060_ = leanh::lean_ctor_get(v_toRing_3059_, 14);
                        leanh::lean_inc_ref(v_vars_3060_);
                        leanh::lean_dec_ref(v_toRing_3059_);
                        v_x_3061_ = leanh::lean_ctor_get(v_p_3055_, 0);
                        v_isSharedCheck_3129_ = (!leanh::lean_is_exclusive(v_p_3055_)) as u8;
                        if v_isSharedCheck_3129_ == 0 {
                            v_unused_3130_ = leanh::lean_ctor_get(v_p_3055_, 1);
                            leanh::lean_dec(v_unused_3130_);
                            v___x_3063_ = v_p_3055_;
                            v_isShared_3064_ = v_isSharedCheck_3129_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_x_3061_);
                            leanh::lean_dec(v_p_3055_);
                            v___x_3063_ = leanh::lean_box(0);
                            v_isShared_3064_ = v_isSharedCheck_3129_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_m_3056_);
                        leanh::lean_dec_ref(v_p_3055_);
                        v_a_3131_ = leanh::lean_ctor_get(v___x_3057_, 0);
                        v_isSharedCheck_3138_ =
                            (!leanh::lean_is_exclusive(v___x_3057_)) as u8;
                        if v_isSharedCheck_3138_ == 0 {
                            v___x_3133_ = v___x_3057_;
                            v_isShared_3134_ = v_isSharedCheck_3138_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3131_);
                            leanh::lean_dec(v___x_3057_);
                            v___x_3133_ = leanh::lean_box(0);
                            v_isShared_3134_ = v_isSharedCheck_3138_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_size_3124_ = leanh::lean_ctor_get(v_vars_3060_, 2);
                v___x_3125_ = l_Lean_instInhabitedExpr;
                v___x_3126_ = lean_nat_dec_lt(v_x_3061_, v_size_3124_);
                if v___x_3126_ == 0 {
                    leanh::lean_dec_ref(v_vars_3060_);
                    v___x_3127_ = l_outOfBounds___redArg(v___x_3125_);
                    v___y_3066_ = v___x_3127_;
                    state = 2;
                    continue;
                } else {
                    v___x_3128_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_3125_,
                        v_vars_3060_,
                        v_x_3061_,
                    );
                    leanh::lean_dec_ref(v_vars_3060_);
                    v___y_3066_ = v___x_3128_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3067_ = l_Lean_Expr_cleanupAnnotations(v___y_3066_);
                v___x_3068_ = l_Lean_Expr_isApp(v___x_3067_);
                if v___x_3068_ == 0 {
                    leanh::lean_dec_ref(v___x_3067_);
                    leanh::lean_del_object(v___x_3063_);
                    leanh::lean_dec(v_x_3061_);
                    v_m_3040_ = v_m_3056_;
                    state = 0;
                    continue;
                } else {
                    v_arg_3070_ = leanh::lean_ctor_get(v___x_3067_, 1);
                    leanh::lean_inc_ref(v_arg_3070_);
                    v___x_3071_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3067_);
                    v___x_3072_ = l_Lean_Expr_isApp(v___x_3071_);
                    if v___x_3072_ == 0 {
                        leanh::lean_dec_ref(v___x_3071_);
                        leanh::lean_dec_ref(v_arg_3070_);
                        leanh::lean_del_object(v___x_3063_);
                        leanh::lean_dec(v_x_3061_);
                        v_m_3040_ = v_m_3056_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3074_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3071_);
                        v___x_3075_ = l_Lean_Expr_isApp(v___x_3074_);
                        if v___x_3075_ == 0 {
                            leanh::lean_dec_ref(v___x_3074_);
                            leanh::lean_dec_ref(v_arg_3070_);
                            leanh::lean_del_object(v___x_3063_);
                            leanh::lean_dec(v_x_3061_);
                            v_m_3040_ = v_m_3056_;
                            state = 0;
                            continue;
                        } else {
                            v___x_3077_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3074_);
                            v___x_3078_ =
                                l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__2;
                            v___x_3079_ = l_Lean_Expr_isConstOf(v___x_3077_, v___x_3078_);
                            leanh::lean_dec_ref(v___x_3077_);
                            if v___x_3079_ == 0 {
                                leanh::lean_dec_ref(v_arg_3070_);
                                leanh::lean_del_object(v___x_3063_);
                                leanh::lean_dec(v_x_3061_);
                                v_m_3040_ = v_m_3056_;
                                state = 0;
                                continue;
                            } else {
                                v___x_3081_ = l_Lean_Expr_cleanupAnnotations(v_arg_3070_);
                                v___x_3082_ = l_Lean_Expr_isApp(v___x_3081_);
                                if v___x_3082_ == 0 {
                                    leanh::lean_dec_ref(v___x_3081_);
                                    leanh::lean_del_object(v___x_3063_);
                                    leanh::lean_dec(v_x_3061_);
                                    v_m_3040_ = v_m_3056_;
                                    state = 0;
                                    continue;
                                } else {
                                    v___x_3084_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3081_);
                                    v___x_3085_ = l_Lean_Expr_isApp(v___x_3084_);
                                    if v___x_3085_ == 0 {
                                        leanh::lean_dec_ref(v___x_3084_);
                                        leanh::lean_del_object(v___x_3063_);
                                        leanh::lean_dec(v_x_3061_);
                                        v_m_3040_ = v_m_3056_;
                                        state = 0;
                                        continue;
                                    } else {
                                        v_arg_3087_ = leanh::lean_ctor_get(v___x_3084_, 1);
                                        leanh::lean_inc_ref(v_arg_3087_);
                                        v___x_3088_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_3084_);
                                        v___x_3089_ = l_Lean_Expr_isApp(v___x_3088_);
                                        if v___x_3089_ == 0 {
                                            leanh::lean_dec_ref(v___x_3088_);
                                            leanh::lean_dec_ref(v_arg_3087_);
                                            leanh::lean_del_object(v___x_3063_);
                                            leanh::lean_dec(v_x_3061_);
                                            v_m_3040_ = v_m_3056_;
                                            state = 0;
                                            continue;
                                        } else {
                                            v___x_3091_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_3088_);
                                            v___x_3092_ = l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__5;
                                            v___x_3093_ =
                                                l_Lean_Expr_isConstOf(v___x_3091_, v___x_3092_);
                                            leanh::lean_dec_ref(v___x_3091_);
                                            if v___x_3093_ == 0 {
                                                leanh::lean_dec_ref(v_arg_3087_);
                                                leanh::lean_del_object(v___x_3063_);
                                                leanh::lean_dec(v_x_3061_);
                                                v_m_3040_ = v_m_3056_;
                                                state = 0;
                                                continue;
                                            } else {
                                                v___x_3095_ = l_Lean_Meta_getNatValue_x3f(
                                                    v_arg_3087_,
                                                    v_a_3048_,
                                                    v_a_3049_,
                                                    v_a_3050_,
                                                    v_a_3051_,
                                                );
                                                leanh::lean_dec_ref(v_arg_3087_);
                                                if leanh::lean_obj_tag(v___x_3095_) == 0 {
                                                    v_a_3096_ =
                                                        leanh::lean_ctor_get(v___x_3095_, 0);
                                                    v_isSharedCheck_3115_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_3095_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_3115_ == 0 {
                                                        v___x_3098_ = v___x_3095_;
                                                        v_isShared_3099_ = v_isSharedCheck_3115_;
                                                        state = 3;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_a_3096_);
                                                        leanh::lean_dec(v___x_3095_);
                                                        v___x_3098_ = leanh::lean_box(0);
                                                        v_isShared_3099_ = v_isSharedCheck_3115_;
                                                        state = 3;
                                                        continue;
                                                    }
                                                } else {
                                                    leanh::lean_del_object(v___x_3063_);
                                                    leanh::lean_dec(v_x_3061_);
                                                    leanh::lean_dec(v_m_3056_);
                                                    v_a_3116_ =
                                                        leanh::lean_ctor_get(v___x_3095_, 0);
                                                    v_isSharedCheck_3123_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_3095_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_3123_ == 0 {
                                                        v___x_3118_ = v___x_3095_;
                                                        v_isShared_3119_ = v_isSharedCheck_3123_;
                                                        state = 8;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_a_3116_);
                                                        leanh::lean_dec(v___x_3095_);
                                                        v___x_3118_ = leanh::lean_box(0);
                                                        v_isShared_3119_ = v_isSharedCheck_3123_;
                                                        state = 8;
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
            }
            3 => {
                if leanh::lean_obj_tag(v_a_3096_) == 1 {
                    leanh::lean_dec(v_m_3056_);
                    v_val_3100_ = leanh::lean_ctor_get(v_a_3096_, 0);
                    v_isSharedCheck_3113_ = (!leanh::lean_is_exclusive(v_a_3096_)) as u8;
                    if v_isSharedCheck_3113_ == 0 {
                        v___x_3102_ = v_a_3096_;
                        v_isShared_3103_ = v_isSharedCheck_3113_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3100_);
                        leanh::lean_dec(v_a_3096_);
                        v___x_3102_ = leanh::lean_box(0);
                        v_isShared_3103_ = v_isSharedCheck_3113_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3098_);
                    leanh::lean_dec(v_a_3096_);
                    leanh::lean_del_object(v___x_3063_);
                    leanh::lean_dec(v_x_3061_);
                    v_m_3040_ = v_m_3056_;
                    state = 0;
                    continue;
                }
            }
            4 => {
                if v_isShared_3064_ == 0 {
                    leanh::lean_ctor_set(v___x_3063_, 1, v_x_3061_);
                    leanh::lean_ctor_set(v___x_3063_, 0, v_val_3100_);
                    v___x_3105_ = v___x_3063_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3112_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_val_3100_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3112_, 1, v_x_3061_);
                    v___x_3105_ = v_reuseFailAlloc_3112_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3103_ == 0 {
                    leanh::lean_ctor_set(v___x_3102_, 0, v___x_3105_);
                    v___x_3107_ = v___x_3102_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3111_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3105_);
                    v___x_3107_ = v_reuseFailAlloc_3111_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3099_ == 0 {
                    leanh::lean_ctor_set(v___x_3098_, 0, v___x_3107_);
                    v___x_3109_ = v___x_3098_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3110_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3107_);
                    v___x_3109_ = v_reuseFailAlloc_3110_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3109_;
            }
            8 => {
                if v_isShared_3119_ == 0 {
                    v___x_3121_ = v___x_3118_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3122_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3116_);
                    v___x_3121_ = v_reuseFailAlloc_3122_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3121_;
            }
            10 => {
                if v_isShared_3134_ == 0 {
                    v___x_3136_ = v___x_3133_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3137_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
                    v___x_3136_ = v_reuseFailAlloc_3137_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3136_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___boxed(
    mut v_m_3139_: *mut leanh::LeanObject,
    mut v_a_3140_: *mut leanh::LeanObject,
    mut v_a_3141_: *mut leanh::LeanObject,
    mut v_a_3142_: *mut leanh::LeanObject,
    mut v_a_3143_: *mut leanh::LeanObject,
    mut v_a_3144_: *mut leanh::LeanObject,
    mut v_a_3145_: *mut leanh::LeanObject,
    mut v_a_3146_: *mut leanh::LeanObject,
    mut v_a_3147_: *mut leanh::LeanObject,
    mut v_a_3148_: *mut leanh::LeanObject,
    mut v_a_3149_: *mut leanh::LeanObject,
    mut v_a_3150_: *mut leanh::LeanObject,
    mut v_a_3151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3152_ = l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(
        v_m_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_,
        v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_,
    );
    leanh::lean_dec(v_a_3150_);
    leanh::lean_dec_ref(v_a_3149_);
    leanh::lean_dec(v_a_3148_);
    leanh::lean_dec_ref(v_a_3147_);
    leanh::lean_dec(v_a_3146_);
    leanh::lean_dec_ref(v_a_3145_);
    leanh::lean_dec(v_a_3144_);
    leanh::lean_dec_ref(v_a_3143_);
    leanh::lean_dec(v_a_3142_);
    leanh::lean_dec(v_a_3141_);
    leanh::lean_dec_ref(v_a_3140_);
    return v_res_3152_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f(
    mut v_p_3153_: *mut leanh::LeanObject,
    mut v_a_3154_: *mut leanh::LeanObject,
    mut v_a_3155_: *mut leanh::LeanObject,
    mut v_a_3156_: *mut leanh::LeanObject,
    mut v_a_3157_: *mut leanh::LeanObject,
    mut v_a_3158_: *mut leanh::LeanObject,
    mut v_a_3159_: *mut leanh::LeanObject,
    mut v_a_3160_: *mut leanh::LeanObject,
    mut v_a_3161_: *mut leanh::LeanObject,
    mut v_a_3162_: *mut leanh::LeanObject,
    mut v_a_3163_: *mut leanh::LeanObject,
    mut v_a_3164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3168_: u8 = 0;
    let mut v___x_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3173_: u8 = 0;
    let mut v_unused_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_p_3153_) == 0 {
                    v_isSharedCheck_3173_ = (!leanh::lean_is_exclusive(v_p_3153_)) as u8;
                    if v_isSharedCheck_3173_ == 0 {
                        v_unused_3174_ = leanh::lean_ctor_get(v_p_3153_, 0);
                        leanh::lean_dec(v_unused_3174_);
                        v___x_3167_ = v_p_3153_;
                        v_isShared_3168_ = v_isSharedCheck_3173_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_p_3153_);
                        v___x_3167_ = leanh::lean_box(0);
                        v_isShared_3168_ = v_isSharedCheck_3173_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_v_3175_ = leanh::lean_ctor_get(v_p_3153_, 1);
                    leanh::lean_inc(v_v_3175_);
                    v_p_3176_ = leanh::lean_ctor_get(v_p_3153_, 2);
                    leanh::lean_inc_ref(v_p_3176_);
                    leanh::lean_dec_ref_known(v_p_3153_, 3);
                    v___x_3177_ = l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(
                        v_v_3175_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_,
                        v_a_3159_, v_a_3160_, v_a_3161_, v_a_3162_, v_a_3163_, v_a_3164_,
                    );
                    if leanh::lean_obj_tag(v___x_3177_) == 0 {
                        v_a_3178_ = leanh::lean_ctor_get(v___x_3177_, 0);
                        leanh::lean_inc(v_a_3178_);
                        if leanh::lean_obj_tag(v_a_3178_) == 1 {
                            leanh::lean_dec_ref_known(v_a_3178_, 1);
                            leanh::lean_dec_ref(v_p_3176_);
                            return v___x_3177_;
                        } else {
                            leanh::lean_dec_ref_known(v___x_3177_, 1);
                            leanh::lean_dec(v_a_3178_);
                            v_p_3153_ = v_p_3176_;
                            state = 0;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_p_3176_);
                        return v___x_3177_;
                    }
                }
            }
            1 => {
                v___x_3169_ = leanh::lean_box(0);
                if v_isShared_3168_ == 0 {
                    leanh::lean_ctor_set(v___x_3167_, 0, v___x_3169_);
                    v___x_3171_ = v___x_3167_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3172_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_3169_);
                    v___x_3171_ = v_reuseFailAlloc_3172_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3171_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f___boxed(
    mut v_p_3180_: *mut leanh::LeanObject,
    mut v_a_3181_: *mut leanh::LeanObject,
    mut v_a_3182_: *mut leanh::LeanObject,
    mut v_a_3183_: *mut leanh::LeanObject,
    mut v_a_3184_: *mut leanh::LeanObject,
    mut v_a_3185_: *mut leanh::LeanObject,
    mut v_a_3186_: *mut leanh::LeanObject,
    mut v_a_3187_: *mut leanh::LeanObject,
    mut v_a_3188_: *mut leanh::LeanObject,
    mut v_a_3189_: *mut leanh::LeanObject,
    mut v_a_3190_: *mut leanh::LeanObject,
    mut v_a_3191_: *mut leanh::LeanObject,
    mut v_a_3192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3193_ = l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f(
        v_p_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_,
        v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_,
    );
    leanh::lean_dec(v_a_3191_);
    leanh::lean_dec_ref(v_a_3190_);
    leanh::lean_dec(v_a_3189_);
    leanh::lean_dec_ref(v_a_3188_);
    leanh::lean_dec(v_a_3187_);
    leanh::lean_dec_ref(v_a_3186_);
    leanh::lean_dec(v_a_3185_);
    leanh::lean_dec_ref(v_a_3184_);
    leanh::lean_dec(v_a_3183_);
    leanh::lean_dec(v_a_3182_);
    leanh::lean_dec_ref(v_a_3181_);
    return v_res_3193_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(
    mut v_k_u2082_x27_3194_: *mut leanh::LeanObject,
    mut v_m_u2082_3195_: *mut leanh::LeanObject,
    mut v_p_u2082_3196_: *mut leanh::LeanObject,
    mut v_p_u2081_3197_: *mut leanh::LeanObject,
    mut v_a_3198_: *mut leanh::LeanObject,
    mut v_a_3199_: *mut leanh::LeanObject,
    mut v_a_3200_: *mut leanh::LeanObject,
    mut v_a_3201_: *mut leanh::LeanObject,
    mut v_a_3202_: *mut leanh::LeanObject,
    mut v_a_3203_: *mut leanh::LeanObject,
    mut v_a_3204_: *mut leanh::LeanObject,
    mut v_a_3205_: *mut leanh::LeanObject,
    mut v_a_3206_: *mut leanh::LeanObject,
    mut v_a_3207_: *mut leanh::LeanObject,
    mut v_a_3208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3217_: u8 = 0;
    let mut v___x_3218_: u8 = 0;
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3223_: u8 = 0;
    let mut v_val_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3229_: u8 = 0;
    let mut v_val_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3233_: u8 = 0;
    let mut v_p_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_u2081_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_u2082_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_u2082_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3240_: u8 = 0;
    let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: u8 = 0;
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3261_: u8 = 0;
    let mut v_isSharedCheck_3262_: u8 = 0;
    let mut v___x_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3265_: u8 = 0;
    let mut v_p_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_u2081_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_u2082_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_u2082_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3272_: u8 = 0;
    let mut v___x_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3286_: u8 = 0;
    let mut v_isSharedCheck_3287_: u8 = 0;
    let mut v_unused_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3289_: u8 = 0;
    let mut v_a_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3293_: u8 = 0;
    let mut v___x_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3297_: u8 = 0;
    let mut v___x_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3302_: u8 = 0;
    let mut v_m_u2082_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_g_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_u2082_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_u2081_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3319_: u8 = 0;
    let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3325_: u8 = 0;
    let mut v_a_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3329_: u8 = 0;
    let mut v___x_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3333_: u8 = 0;
    let mut v_a_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3337_: u8 = 0;
    let mut v___x_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3341_: u8 = 0;
    let mut v_a_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3345_: u8 = 0;
    let mut v___x_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3349_: u8 = 0;
    let mut v_isSharedCheck_3350_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_p_u2081_3197_) == 0 {
                    leanh::lean_dec_ref_known(v_p_u2081_3197_, 1);
                    leanh::lean_dec_ref(v_p_u2082_3196_);
                    leanh::lean_dec(v_m_u2082_3195_);
                    v___x_3210_ = leanh::lean_box(0);
                    v___x_3211_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3211_, 0, v___x_3210_);
                    return v___x_3211_;
                } else {
                    v_k_3212_ = leanh::lean_ctor_get(v_p_u2081_3197_, 0);
                    v_v_3213_ = leanh::lean_ctor_get(v_p_u2081_3197_, 1);
                    v_p_3214_ = leanh::lean_ctor_get(v_p_u2081_3197_, 2);
                    v_isSharedCheck_3350_ =
                        (!leanh::lean_is_exclusive(v_p_u2081_3197_)) as u8;
                    if v_isSharedCheck_3350_ == 0 {
                        v___x_3216_ = v_p_u2081_3197_;
                        v_isShared_3217_ = v_isSharedCheck_3350_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_p_3214_);
                        leanh::lean_inc(v_v_3213_);
                        leanh::lean_inc(v_k_3212_);
                        leanh::lean_dec(v_p_u2081_3197_);
                        v___x_3216_ = leanh::lean_box(0);
                        v_isShared_3217_ = v_isSharedCheck_3350_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3218_ = l_Lean_Grind_CommRing_Mon_divides(v_m_u2082_3195_, v_v_3213_);
                if v___x_3218_ == 0 {
                    v___x_3219_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(v_k_u2082_x27_3194_, v_m_u2082_3195_, v_p_u2082_3196_, v_p_3214_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_);
                    if leanh::lean_obj_tag(v___x_3219_) == 0 {
                        v_a_3220_ = leanh::lean_ctor_get(v___x_3219_, 0);
                        v_isSharedCheck_3302_ =
                            (!leanh::lean_is_exclusive(v___x_3219_)) as u8;
                        if v_isSharedCheck_3302_ == 0 {
                            v___x_3222_ = v___x_3219_;
                            v_isShared_3223_ = v_isSharedCheck_3302_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3220_);
                            leanh::lean_dec(v___x_3219_);
                            v___x_3222_ = leanh::lean_box(0);
                            v_isShared_3223_ = v_isSharedCheck_3302_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_3216_);
                        leanh::lean_dec(v_v_3213_);
                        leanh::lean_dec(v_k_3212_);
                        return v___x_3219_;
                    }
                } else {
                    leanh::lean_del_object(v___x_3216_);
                    v_m_u2082_3303_ = l_Lean_Grind_CommRing_Mon_div(v_v_3213_, v_m_u2082_3195_);
                    v___x_3304_ = lean_nat_abs(v_k_3212_);
                    v___x_3305_ = lean_nat_abs(v_k_u2082_x27_3194_);
                    v_g_3306_ = lean_nat_gcd(v___x_3304_, v___x_3305_);
                    leanh::lean_dec(v___x_3305_);
                    leanh::lean_dec(v___x_3304_);
                    v___x_3307_ = lean_nat_to_int(v_g_3306_);
                    v___x_3308_ = lean_int_neg(v_k_3212_);
                    leanh::lean_dec(v_k_3212_);
                    v_k_u2082_3309_ = lean_int_ediv(v___x_3308_, v___x_3307_);
                    leanh::lean_dec(v___x_3308_);
                    leanh::lean_inc(v_m_u2082_3303_);
                    v___x_3310_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_k_u2082_3309_, v_m_u2082_3303_, v_p_u2082_3196_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_);
                    if leanh::lean_obj_tag(v___x_3310_) == 0 {
                        v_a_3311_ = leanh::lean_ctor_get(v___x_3310_, 0);
                        leanh::lean_inc(v_a_3311_);
                        leanh::lean_dec_ref_known(v___x_3310_, 1);
                        v_k_u2081_3312_ = lean_int_ediv(v_k_u2082_x27_3194_, v___x_3307_);
                        leanh::lean_dec(v___x_3307_);
                        v___x_3313_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v_k_u2081_3312_, v_p_3214_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_);
                        if leanh::lean_obj_tag(v___x_3313_) == 0 {
                            v_a_3314_ = leanh::lean_ctor_get(v___x_3313_, 0);
                            leanh::lean_inc(v_a_3314_);
                            leanh::lean_dec_ref_known(v___x_3313_, 1);
                            leanh::lean_inc_ref(v_a_3207_);
                            v___x_3315_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_a_3311_, v_a_3314_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_);
                            if leanh::lean_obj_tag(v___x_3315_) == 0 {
                                v_a_3316_ = leanh::lean_ctor_get(v___x_3315_, 0);
                                v_isSharedCheck_3325_ =
                                    (!leanh::lean_is_exclusive(v___x_3315_)) as u8;
                                if v_isSharedCheck_3325_ == 0 {
                                    v___x_3318_ = v___x_3315_;
                                    v_isShared_3319_ = v_isSharedCheck_3325_;
                                    state = 20;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3316_);
                                    leanh::lean_dec(v___x_3315_);
                                    v___x_3318_ = leanh::lean_box(0);
                                    v_isShared_3319_ = v_isSharedCheck_3325_;
                                    state = 20;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_k_u2081_3312_);
                                leanh::lean_dec(v_k_u2082_3309_);
                                leanh::lean_dec(v_m_u2082_3303_);
                                v_a_3326_ = leanh::lean_ctor_get(v___x_3315_, 0);
                                v_isSharedCheck_3333_ =
                                    (!leanh::lean_is_exclusive(v___x_3315_)) as u8;
                                if v_isSharedCheck_3333_ == 0 {
                                    v___x_3328_ = v___x_3315_;
                                    v_isShared_3329_ = v_isSharedCheck_3333_;
                                    state = 22;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3326_);
                                    leanh::lean_dec(v___x_3315_);
                                    v___x_3328_ = leanh::lean_box(0);
                                    v_isShared_3329_ = v_isSharedCheck_3333_;
                                    state = 22;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_k_u2081_3312_);
                            leanh::lean_dec(v_a_3311_);
                            leanh::lean_dec(v_k_u2082_3309_);
                            leanh::lean_dec(v_m_u2082_3303_);
                            v_a_3334_ = leanh::lean_ctor_get(v___x_3313_, 0);
                            v_isSharedCheck_3341_ =
                                (!leanh::lean_is_exclusive(v___x_3313_)) as u8;
                            if v_isSharedCheck_3341_ == 0 {
                                v___x_3336_ = v___x_3313_;
                                v_isShared_3337_ = v_isSharedCheck_3341_;
                                state = 24;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3334_);
                                leanh::lean_dec(v___x_3313_);
                                v___x_3336_ = leanh::lean_box(0);
                                v_isShared_3337_ = v_isSharedCheck_3341_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_k_u2082_3309_);
                        leanh::lean_dec(v___x_3307_);
                        leanh::lean_dec(v_m_u2082_3303_);
                        leanh::lean_dec_ref(v_p_3214_);
                        v_a_3342_ = leanh::lean_ctor_get(v___x_3310_, 0);
                        v_isSharedCheck_3349_ =
                            (!leanh::lean_is_exclusive(v___x_3310_)) as u8;
                        if v_isSharedCheck_3349_ == 0 {
                            v___x_3344_ = v___x_3310_;
                            v_isShared_3345_ = v_isSharedCheck_3349_;
                            state = 26;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3342_);
                            leanh::lean_dec(v___x_3310_);
                            v___x_3344_ = leanh::lean_box(0);
                            v_isShared_3345_ = v_isSharedCheck_3349_;
                            state = 26;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_3220_) == 1 {
                    leanh::lean_del_object(v___x_3222_);
                    v_val_3224_ = leanh::lean_ctor_get(v_a_3220_, 0);
                    leanh::lean_inc(v_val_3224_);
                    v___x_3225_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_);
                    if leanh::lean_obj_tag(v___x_3225_) == 0 {
                        v_a_3226_ = leanh::lean_ctor_get(v___x_3225_, 0);
                        v_isSharedCheck_3289_ =
                            (!leanh::lean_is_exclusive(v___x_3225_)) as u8;
                        if v_isSharedCheck_3289_ == 0 {
                            v___x_3228_ = v___x_3225_;
                            v_isShared_3229_ = v_isSharedCheck_3289_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3226_);
                            leanh::lean_dec(v___x_3225_);
                            v___x_3228_ = leanh::lean_box(0);
                            v_isShared_3229_ = v_isSharedCheck_3289_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_a_3220_, 1);
                        leanh::lean_dec(v_val_3224_);
                        leanh::lean_del_object(v___x_3216_);
                        leanh::lean_dec(v_v_3213_);
                        leanh::lean_dec(v_k_3212_);
                        v_a_3290_ = leanh::lean_ctor_get(v___x_3225_, 0);
                        v_isSharedCheck_3297_ =
                            (!leanh::lean_is_exclusive(v___x_3225_)) as u8;
                        if v_isSharedCheck_3297_ == 0 {
                            v___x_3292_ = v___x_3225_;
                            v_isShared_3293_ = v_isSharedCheck_3297_;
                            state = 17;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3290_);
                            leanh::lean_dec(v___x_3225_);
                            v___x_3292_ = leanh::lean_box(0);
                            v_isShared_3293_ = v_isSharedCheck_3297_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_3220_);
                    leanh::lean_del_object(v___x_3216_);
                    leanh::lean_dec(v_v_3213_);
                    leanh::lean_dec(v_k_3212_);
                    v___x_3298_ = leanh::lean_box(0);
                    if v_isShared_3223_ == 0 {
                        leanh::lean_ctor_set(v___x_3222_, 0, v___x_3298_);
                        v___x_3300_ = v___x_3222_;
                        state = 19;
                        continue;
                    } else {
                        v_reuseFailAlloc_3301_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3298_);
                        v___x_3300_ = v_reuseFailAlloc_3301_;
                        state = 19;
                        continue;
                    }
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_a_3226_) == 1 {
                    v_val_3230_ = leanh::lean_ctor_get(v_a_3226_, 0);
                    v_isSharedCheck_3262_ = (!leanh::lean_is_exclusive(v_a_3226_)) as u8;
                    if v_isSharedCheck_3262_ == 0 {
                        v___x_3232_ = v_a_3226_;
                        v_isShared_3233_ = v_isSharedCheck_3262_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3230_);
                        leanh::lean_dec(v_a_3226_);
                        v___x_3232_ = leanh::lean_box(0);
                        v_isShared_3233_ = v_isSharedCheck_3262_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3226_);
                    v_isSharedCheck_3287_ = (!leanh::lean_is_exclusive(v_a_3220_)) as u8;
                    if v_isSharedCheck_3287_ == 0 {
                        v_unused_3288_ = leanh::lean_ctor_get(v_a_3220_, 0);
                        leanh::lean_dec(v_unused_3288_);
                        v___x_3264_ = v_a_3220_;
                        v_isShared_3265_ = v_isSharedCheck_3287_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_3220_);
                        v___x_3264_ = leanh::lean_box(0);
                        v_isShared_3265_ = v_isSharedCheck_3287_;
                        state = 11;
                        continue;
                    }
                }
            }
            4 => {
                v_p_3234_ = leanh::lean_ctor_get(v_val_3224_, 0);
                v_k_u2081_3235_ = leanh::lean_ctor_get(v_val_3224_, 1);
                v_k_u2082_3236_ = leanh::lean_ctor_get(v_val_3224_, 2);
                v_m_u2082_3237_ = leanh::lean_ctor_get(v_val_3224_, 3);
                v_isSharedCheck_3261_ = (!leanh::lean_is_exclusive(v_val_3224_)) as u8;
                if v_isSharedCheck_3261_ == 0 {
                    v___x_3239_ = v_val_3224_;
                    v_isShared_3240_ = v_isSharedCheck_3261_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_m_u2082_3237_);
                    leanh::lean_inc(v_k_u2082_3236_);
                    leanh::lean_inc(v_k_u2081_3235_);
                    leanh::lean_inc(v_p_3234_);
                    leanh::lean_dec(v_val_3224_);
                    v___x_3239_ = leanh::lean_box(0);
                    v_isShared_3240_ = v_isSharedCheck_3261_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3241_ = lean_int_mul(v_k_3212_, v_k_u2081_3235_);
                leanh::lean_dec(v_k_3212_);
                v___x_3242_ = lean_nat_to_int(v_val_3230_);
                v___x_3243_ = lean_int_emod(v___x_3241_, v___x_3242_);
                leanh::lean_dec(v___x_3242_);
                leanh::lean_dec(v___x_3241_);
                v___x_3244_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
                v___x_3245_ = lean_int_dec_eq(v___x_3243_, v___x_3244_);
                if v___x_3245_ == 0 {
                    leanh::lean_dec_ref_known(v_a_3220_, 1);
                    if v_isShared_3217_ == 0 {
                        leanh::lean_ctor_set(v___x_3216_, 2, v_p_3234_);
                        leanh::lean_ctor_set(v___x_3216_, 0, v___x_3243_);
                        v___x_3247_ = v___x_3216_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3257_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3257_, 0, v___x_3243_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3257_, 1, v_v_3213_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3257_, 2, v_p_3234_);
                        v___x_3247_ = v_reuseFailAlloc_3257_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3243_);
                    leanh::lean_del_object(v___x_3239_);
                    leanh::lean_dec(v_m_u2082_3237_);
                    leanh::lean_dec(v_k_u2082_3236_);
                    leanh::lean_dec(v_k_u2081_3235_);
                    leanh::lean_dec_ref(v_p_3234_);
                    leanh::lean_del_object(v___x_3232_);
                    leanh::lean_del_object(v___x_3216_);
                    leanh::lean_dec(v_v_3213_);
                    if v_isShared_3229_ == 0 {
                        leanh::lean_ctor_set(v___x_3228_, 0, v_a_3220_);
                        v___x_3259_ = v___x_3228_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3260_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_a_3220_);
                        v___x_3259_ = v_reuseFailAlloc_3260_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_3240_ == 0 {
                    leanh::lean_ctor_set(v___x_3239_, 0, v___x_3247_);
                    v___x_3249_ = v___x_3239_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3256_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3247_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3256_, 1, v_k_u2081_3235_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3256_, 2, v_k_u2082_3236_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3256_, 3, v_m_u2082_3237_);
                    v___x_3249_ = v_reuseFailAlloc_3256_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3233_ == 0 {
                    leanh::lean_ctor_set(v___x_3232_, 0, v___x_3249_);
                    v___x_3251_ = v___x_3232_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3255_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3255_, 0, v___x_3249_);
                    v___x_3251_ = v_reuseFailAlloc_3255_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_3229_ == 0 {
                    leanh::lean_ctor_set(v___x_3228_, 0, v___x_3251_);
                    v___x_3253_ = v___x_3228_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3254_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3254_, 0, v___x_3251_);
                    v___x_3253_ = v_reuseFailAlloc_3254_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3253_;
            }
            10 => {
                return v___x_3259_;
            }
            11 => {
                v_p_3266_ = leanh::lean_ctor_get(v_val_3224_, 0);
                v_k_u2081_3267_ = leanh::lean_ctor_get(v_val_3224_, 1);
                v_k_u2082_3268_ = leanh::lean_ctor_get(v_val_3224_, 2);
                v_m_u2082_3269_ = leanh::lean_ctor_get(v_val_3224_, 3);
                v_isSharedCheck_3286_ = (!leanh::lean_is_exclusive(v_val_3224_)) as u8;
                if v_isSharedCheck_3286_ == 0 {
                    v___x_3271_ = v_val_3224_;
                    v_isShared_3272_ = v_isSharedCheck_3286_;
                    state = 12;
                    continue;
                } else {
                    leanh::lean_inc(v_m_u2082_3269_);
                    leanh::lean_inc(v_k_u2082_3268_);
                    leanh::lean_inc(v_k_u2081_3267_);
                    leanh::lean_inc(v_p_3266_);
                    leanh::lean_dec(v_val_3224_);
                    v___x_3271_ = leanh::lean_box(0);
                    v_isShared_3272_ = v_isSharedCheck_3286_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_3273_ = lean_int_mul(v_k_3212_, v_k_u2081_3267_);
                leanh::lean_dec(v_k_3212_);
                if v_isShared_3217_ == 0 {
                    leanh::lean_ctor_set(v___x_3216_, 2, v_p_3266_);
                    leanh::lean_ctor_set(v___x_3216_, 0, v___x_3273_);
                    v___x_3275_ = v___x_3216_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3285_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3285_, 0, v___x_3273_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3285_, 1, v_v_3213_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3285_, 2, v_p_3266_);
                    v___x_3275_ = v_reuseFailAlloc_3285_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_3272_ == 0 {
                    leanh::lean_ctor_set(v___x_3271_, 0, v___x_3275_);
                    v___x_3277_ = v___x_3271_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3284_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 0, v___x_3275_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 1, v_k_u2081_3267_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 2, v_k_u2082_3268_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 3, v_m_u2082_3269_);
                    v___x_3277_ = v_reuseFailAlloc_3284_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_3265_ == 0 {
                    leanh::lean_ctor_set(v___x_3264_, 0, v___x_3277_);
                    v___x_3279_ = v___x_3264_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3283_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3283_, 0, v___x_3277_);
                    v___x_3279_ = v_reuseFailAlloc_3283_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_3229_ == 0 {
                    leanh::lean_ctor_set(v___x_3228_, 0, v___x_3279_);
                    v___x_3281_ = v___x_3228_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3282_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3282_, 0, v___x_3279_);
                    v___x_3281_ = v_reuseFailAlloc_3282_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3281_;
            }
            17 => {
                if v_isShared_3293_ == 0 {
                    v___x_3295_ = v___x_3292_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3296_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_a_3290_);
                    v___x_3295_ = v_reuseFailAlloc_3296_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3295_;
            }
            19 => {
                return v___x_3300_;
            }
            20 => {
                v___x_3320_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3320_, 0, v_a_3316_);
                leanh::lean_ctor_set(v___x_3320_, 1, v_k_u2081_3312_);
                leanh::lean_ctor_set(v___x_3320_, 2, v_k_u2082_3309_);
                leanh::lean_ctor_set(v___x_3320_, 3, v_m_u2082_3303_);
                v___x_3321_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3321_, 0, v___x_3320_);
                if v_isShared_3319_ == 0 {
                    leanh::lean_ctor_set(v___x_3318_, 0, v___x_3321_);
                    v___x_3323_ = v___x_3318_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3324_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3324_, 0, v___x_3321_);
                    v___x_3323_ = v_reuseFailAlloc_3324_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_3323_;
            }
            22 => {
                if v_isShared_3329_ == 0 {
                    v___x_3331_ = v___x_3328_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3332_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_a_3326_);
                    v___x_3331_ = v_reuseFailAlloc_3332_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_3331_;
            }
            24 => {
                if v_isShared_3337_ == 0 {
                    v___x_3339_ = v___x_3336_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3340_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_a_3334_);
                    v___x_3339_ = v_reuseFailAlloc_3340_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_3339_;
            }
            26 => {
                if v_isShared_3345_ == 0 {
                    v___x_3347_ = v___x_3344_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3348_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_a_3342_);
                    v___x_3347_ = v_reuseFailAlloc_3348_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_3347_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f___boxed(
    mut v_k_u2082_x27_3351_: *mut leanh::LeanObject,
    mut v_m_u2082_3352_: *mut leanh::LeanObject,
    mut v_p_u2082_3353_: *mut leanh::LeanObject,
    mut v_p_u2081_3354_: *mut leanh::LeanObject,
    mut v_a_3355_: *mut leanh::LeanObject,
    mut v_a_3356_: *mut leanh::LeanObject,
    mut v_a_3357_: *mut leanh::LeanObject,
    mut v_a_3358_: *mut leanh::LeanObject,
    mut v_a_3359_: *mut leanh::LeanObject,
    mut v_a_3360_: *mut leanh::LeanObject,
    mut v_a_3361_: *mut leanh::LeanObject,
    mut v_a_3362_: *mut leanh::LeanObject,
    mut v_a_3363_: *mut leanh::LeanObject,
    mut v_a_3364_: *mut leanh::LeanObject,
    mut v_a_3365_: *mut leanh::LeanObject,
    mut v_a_3366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3367_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(v_k_u2082_x27_3351_, v_m_u2082_3352_, v_p_u2082_3353_, v_p_u2081_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_);
    leanh::lean_dec(v_a_3365_);
    leanh::lean_dec_ref(v_a_3364_);
    leanh::lean_dec(v_a_3363_);
    leanh::lean_dec_ref(v_a_3362_);
    leanh::lean_dec(v_a_3361_);
    leanh::lean_dec_ref(v_a_3360_);
    leanh::lean_dec(v_a_3359_);
    leanh::lean_dec_ref(v_a_3358_);
    leanh::lean_dec(v_a_3357_);
    leanh::lean_dec(v_a_3356_);
    leanh::lean_dec_ref(v_a_3355_);
    leanh::lean_dec(v_k_u2082_x27_3351_);
    return v_res_3367_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_simpM_x3f(
    mut v_p_u2081_3368_: *mut leanh::LeanObject,
    mut v_p_u2082_3369_: *mut leanh::LeanObject,
    mut v_a_3370_: *mut leanh::LeanObject,
    mut v_a_3371_: *mut leanh::LeanObject,
    mut v_a_3372_: *mut leanh::LeanObject,
    mut v_a_3373_: *mut leanh::LeanObject,
    mut v_a_3374_: *mut leanh::LeanObject,
    mut v_a_3375_: *mut leanh::LeanObject,
    mut v_a_3376_: *mut leanh::LeanObject,
    mut v_a_3377_: *mut leanh::LeanObject,
    mut v_a_3378_: *mut leanh::LeanObject,
    mut v_a_3379_: *mut leanh::LeanObject,
    mut v_a_3380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_p_u2082_3369_) == 1 {
        let mut v_k_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_k_3382_ = leanh::lean_ctor_get(v_p_u2082_3369_, 0);
        leanh::lean_inc(v_k_3382_);
        v_v_3383_ = leanh::lean_ctor_get(v_p_u2082_3369_, 1);
        leanh::lean_inc(v_v_3383_);
        v_p_3384_ = leanh::lean_ctor_get(v_p_u2082_3369_, 2);
        leanh::lean_inc_ref(v_p_3384_);
        leanh::lean_dec_ref_known(v_p_u2082_3369_, 3);
        v___x_3385_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(v_k_3382_, v_v_3383_, v_p_3384_, v_p_u2081_3368_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_);
        leanh::lean_dec(v_k_3382_);
        return v___x_3385_;
    } else {
        let mut v___x_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_p_u2082_3369_);
        leanh::lean_dec_ref(v_p_u2081_3368_);
        v___x_3386_ = leanh::lean_box(0);
        v___x_3387_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3387_, 0, v___x_3386_);
        return v___x_3387_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_simpM_x3f___boxed(
    mut v_p_u2081_3388_: *mut leanh::LeanObject,
    mut v_p_u2082_3389_: *mut leanh::LeanObject,
    mut v_a_3390_: *mut leanh::LeanObject,
    mut v_a_3391_: *mut leanh::LeanObject,
    mut v_a_3392_: *mut leanh::LeanObject,
    mut v_a_3393_: *mut leanh::LeanObject,
    mut v_a_3394_: *mut leanh::LeanObject,
    mut v_a_3395_: *mut leanh::LeanObject,
    mut v_a_3396_: *mut leanh::LeanObject,
    mut v_a_3397_: *mut leanh::LeanObject,
    mut v_a_3398_: *mut leanh::LeanObject,
    mut v_a_3399_: *mut leanh::LeanObject,
    mut v_a_3400_: *mut leanh::LeanObject,
    mut v_a_3401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3402_ = l_Lean_Grind_CommRing_Poly_simpM_x3f(
        v_p_u2081_3388_,
        v_p_u2082_3389_,
        v_a_3390_,
        v_a_3391_,
        v_a_3392_,
        v_a_3393_,
        v_a_3394_,
        v_a_3395_,
        v_a_3396_,
        v_a_3397_,
        v_a_3398_,
        v_a_3399_,
        v_a_3400_,
    );
    leanh::lean_dec(v_a_3400_);
    leanh::lean_dec_ref(v_a_3399_);
    leanh::lean_dec(v_a_3398_);
    leanh::lean_dec_ref(v_a_3397_);
    leanh::lean_dec(v_a_3396_);
    leanh::lean_dec_ref(v_a_3395_);
    leanh::lean_dec(v_a_3394_);
    leanh::lean_dec_ref(v_a_3393_);
    leanh::lean_dec(v_a_3392_);
    leanh::lean_dec(v_a_3391_);
    leanh::lean_dec_ref(v_a_3390_);
    return v_res_3402_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(
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
    res = runtime_initialize_Lean_Meta_Sym_Arith_Poly(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(
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
    res = initialize_Lean_Meta_Sym_Arith_Poly(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(builtin);
}