// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.SafePoly
// Imports: Lean.Meta.Tactic.Grind.Arith.CommRing.RingM Lean.Meta.Sym.Arith.Poly Lean.Meta.Tactic.Grind.Arith.EvalNum Init.Data.Nat.Linear
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
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr2, l_Lean_maxRecDepthErrorMessage};
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
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_eq, lean_int_mul, lean_int_neg, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::{lean_int_ediv, lean_int_emod};
use crate::lean_imports_rs::Init::Data::Nat::Gcd::lean_nat_gcd;
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_2, lean_apply_4,
    lean_apply_6, lean_box, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__1_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__1_value) as *mut LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__0_value) as *mut LeanObject,7310567555909517314 as *mut LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__1_value) as *mut LeanObject,273128857561458264 as *mut LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [103, 114, 105, 110, 100, 32, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommRing_Poly_spolM___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommRing_Poly_spolM___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__0_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__1_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__1_value)
        as *mut LeanObject;
static l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__2_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__0_value)
                as *mut LeanObject,
            1412621069384631438 as *mut LeanObject,
        ],
    };
pub static l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__2_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__1_value)
                as *mut LeanObject,
            10171450186735820607 as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__3_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__4_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__4_value)
        as *mut LeanObject;
static l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__5_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__3_value)
                as *mut LeanObject,
            17636616155771105671 as *mut LeanObject,
        ],
    };
pub static l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__5_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__4_value)
                as *mut LeanObject,
            15578568367168711682 as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__5_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(
    mut v___y_1702_: *mut LeanObject,
    mut v___y_1703_: *mut LeanObject,
    mut v___y_1704_: *mut LeanObject,
    mut v___y_1705_: *mut LeanObject,
    mut v___y_1706_: *mut LeanObject,
    mut v___y_1707_: *mut LeanObject,
    mut v___y_1708_: *mut LeanObject,
    mut v___y_1709_: *mut LeanObject,
    mut v___y_1710_: *mut LeanObject,
    mut v___y_1711_: *mut LeanObject,
    mut v___y_1712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1718_: u8 = 0;
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toRing_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1729_: u8 = 0;
    let mut v_snd_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: u8 = 0;
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1737_: u8 = 0;
    let mut v_isSharedCheck_1738_: u8 = 0;
    let mut v_a_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1742_: u8 = 0;
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1745_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_1714_) == 0 {
                    v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
                    v_isSharedCheck_1738_ = (!lean_is_exclusive(v___x_1714_)) as u8;
                    if v_isSharedCheck_1738_ == 0 {
                        v___x_1717_ = v___x_1714_;
                        v_isShared_1718_ = v_isSharedCheck_1738_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1715_);
                        lean_dec(v___x_1714_);
                        v___x_1717_ = lean_box(0);
                        v_isShared_1718_ = v_isSharedCheck_1738_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1739_ = lean_ctor_get(v___x_1714_, 0);
                    v_isSharedCheck_1746_ = (!lean_is_exclusive(v___x_1714_)) as u8;
                    if v_isSharedCheck_1746_ == 0 {
                        v___x_1741_ = v___x_1714_;
                        v_isShared_1742_ = v_isSharedCheck_1746_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_1739_);
                        lean_dec(v___x_1714_);
                        v___x_1741_ = lean_box(0);
                        v_isShared_1742_ = v_isSharedCheck_1746_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_toRing_1724_ = lean_ctor_get(v_a_1715_, 0);
                lean_inc_ref(v_toRing_1724_);
                lean_dec(v_a_1715_);
                v_charInst_x3f_1725_ = lean_ctor_get(v_toRing_1724_, 5);
                lean_inc(v_charInst_x3f_1725_);
                lean_dec_ref(v_toRing_1724_);
                if lean_obj_tag(v_charInst_x3f_1725_) == 1 {
                    v_val_1726_ = lean_ctor_get(v_charInst_x3f_1725_, 0);
                    v_isSharedCheck_1737_ = (!lean_is_exclusive(v_charInst_x3f_1725_)) as u8;
                    if v_isSharedCheck_1737_ == 0 {
                        v___x_1728_ = v_charInst_x3f_1725_;
                        v_isShared_1729_ = v_isSharedCheck_1737_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_val_1726_);
                        lean_dec(v_charInst_x3f_1725_);
                        v___x_1728_ = lean_box(0);
                        v_isShared_1729_ = v_isSharedCheck_1737_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_charInst_x3f_1725_);
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1720_ = lean_box(0);
                if v_isShared_1718_ == 0 {
                    lean_ctor_set(v___x_1717_, 0, v___x_1720_);
                    v___x_1722_ = v___x_1717_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1720_);
                    v___x_1722_ = v_reuseFailAlloc_1723_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1722_;
            }
            4 => {
                v_snd_1730_ = lean_ctor_get(v_val_1726_, 1);
                lean_inc(v_snd_1730_);
                lean_dec(v_val_1726_);
                v___x_1731_ = lean_unsigned_to_nat(0);
                v___x_1732_ = lean_nat_dec_eq(v_snd_1730_, v___x_1731_);
                if v___x_1732_ == 0 {
                    lean_del_object(v___x_1717_);
                    if v_isShared_1729_ == 0 {
                        lean_ctor_set(v___x_1728_, 0, v_snd_1730_);
                        v___x_1734_ = v___x_1728_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_snd_1730_);
                        v___x_1734_ = v_reuseFailAlloc_1736_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v_snd_1730_);
                    lean_del_object(v___x_1728_);
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_1735_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1735_, 0, v___x_1734_);
                return v___x_1735_;
            }
            6 => {
                if v_isShared_1742_ == 0 {
                    v___x_1744_ = v___x_1741_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
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
    mut v___y_1747_: *mut LeanObject,
    mut v___y_1748_: *mut LeanObject,
    mut v___y_1749_: *mut LeanObject,
    mut v___y_1750_: *mut LeanObject,
    mut v___y_1751_: *mut LeanObject,
    mut v___y_1752_: *mut LeanObject,
    mut v___y_1753_: *mut LeanObject,
    mut v___y_1754_: *mut LeanObject,
    mut v___y_1755_: *mut LeanObject,
    mut v___y_1756_: *mut LeanObject,
    mut v___y_1757_: *mut LeanObject,
    mut v___y_1758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1759_: *mut LeanObject = core::ptr::null_mut();
    v_res_1759_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
    lean_dec(v___y_1757_);
    lean_dec_ref(v___y_1756_);
    lean_dec(v___y_1755_);
    lean_dec_ref(v___y_1754_);
    lean_dec(v___y_1753_);
    lean_dec_ref(v___y_1752_);
    lean_dec(v___y_1751_);
    lean_dec_ref(v___y_1750_);
    lean_dec(v___y_1749_);
    lean_dec(v___y_1748_);
    lean_dec_ref(v___y_1747_);
    return v_res_1759_;
}
pub unsafe fn l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__1(
    mut v_a_1760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    v___x_1761_ = lean_nat_to_int(v_a_1760_);
    return v___x_1761_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(
    mut v_a_1762_: *mut LeanObject,
    mut v_a_1763_: *mut LeanObject,
    mut v_a_1764_: *mut LeanObject,
    mut v_a_1765_: *mut LeanObject,
    mut v_a_1766_: *mut LeanObject,
    mut v_a_1767_: *mut LeanObject,
    mut v_a_1768_: *mut LeanObject,
    mut v_a_1769_: *mut LeanObject,
    mut v_a_1770_: *mut LeanObject,
    mut v_a_1771_: *mut LeanObject,
    mut v_a_1772_: *mut LeanObject,
    mut v_a_1773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1779_: u8 = 0;
    let mut v_val_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1789_: u8 = 0;
    let mut v_a_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1793_: u8 = 0;
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1797_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1775_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_);
                if lean_obj_tag(v___x_1775_) == 0 {
                    v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
                    v_isSharedCheck_1789_ = (!lean_is_exclusive(v___x_1775_)) as u8;
                    if v_isSharedCheck_1789_ == 0 {
                        v___x_1778_ = v___x_1775_;
                        v_isShared_1779_ = v_isSharedCheck_1789_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1776_);
                        lean_dec(v___x_1775_);
                        v___x_1778_ = lean_box(0);
                        v_isShared_1779_ = v_isSharedCheck_1789_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1762_);
                    v_a_1790_ = lean_ctor_get(v___x_1775_, 0);
                    v_isSharedCheck_1797_ = (!lean_is_exclusive(v___x_1775_)) as u8;
                    if v_isSharedCheck_1797_ == 0 {
                        v___x_1792_ = v___x_1775_;
                        v_isShared_1793_ = v_isSharedCheck_1797_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1790_);
                        lean_dec(v___x_1775_);
                        v___x_1792_ = lean_box(0);
                        v_isShared_1793_ = v_isSharedCheck_1797_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1776_) == 1 {
                    v_val_1780_ = lean_ctor_get(v_a_1776_, 0);
                    lean_inc(v_val_1780_);
                    lean_dec_ref_known(v_a_1776_, 1);
                    v___x_1781_ = lean_nat_to_int(v_val_1780_);
                    v___x_1782_ = lean_int_emod(v_a_1762_, v___x_1781_);
                    lean_dec(v___x_1781_);
                    lean_dec(v_a_1762_);
                    if v_isShared_1779_ == 0 {
                        lean_ctor_set(v___x_1778_, 0, v___x_1782_);
                        v___x_1784_ = v___x_1778_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
                        v___x_1784_ = v_reuseFailAlloc_1785_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1776_);
                    if v_isShared_1779_ == 0 {
                        lean_ctor_set(v___x_1778_, 0, v_a_1762_);
                        v___x_1787_ = v___x_1778_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1762_);
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
                    v_reuseFailAlloc_1796_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1790_);
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
    mut v_a_1798_: *mut LeanObject,
    mut v_a_1799_: *mut LeanObject,
    mut v_a_1800_: *mut LeanObject,
    mut v_a_1801_: *mut LeanObject,
    mut v_a_1802_: *mut LeanObject,
    mut v_a_1803_: *mut LeanObject,
    mut v_a_1804_: *mut LeanObject,
    mut v_a_1805_: *mut LeanObject,
    mut v_a_1806_: *mut LeanObject,
    mut v_a_1807_: *mut LeanObject,
    mut v_a_1808_: *mut LeanObject,
    mut v_a_1809_: *mut LeanObject,
    mut v_a_1810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1811_: *mut LeanObject = core::ptr::null_mut();
    v_res_1811_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
    lean_dec(v_a_1809_);
    lean_dec_ref(v_a_1808_);
    lean_dec(v_a_1807_);
    lean_dec_ref(v_a_1806_);
    lean_dec(v_a_1805_);
    lean_dec_ref(v_a_1804_);
    lean_dec(v_a_1803_);
    lean_dec_ref(v_a_1802_);
    lean_dec(v_a_1801_);
    lean_dec(v_a_1800_);
    lean_dec_ref(v_a_1799_);
    return v_res_1811_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(
    mut v_p_1812_: *mut LeanObject,
    mut v_k_1813_: *mut LeanObject,
    mut v_a_1814_: *mut LeanObject,
    mut v_a_1815_: *mut LeanObject,
    mut v_a_1816_: *mut LeanObject,
    mut v_a_1817_: *mut LeanObject,
    mut v_a_1818_: *mut LeanObject,
    mut v_a_1819_: *mut LeanObject,
    mut v_a_1820_: *mut LeanObject,
    mut v_a_1821_: *mut LeanObject,
    mut v_a_1822_: *mut LeanObject,
    mut v_a_1823_: *mut LeanObject,
    mut v_a_1824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1830_: u8 = 0;
    let mut v_val_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1840_: u8 = 0;
    let mut v_a_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1844_: u8 = 0;
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1848_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1826_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_);
                if lean_obj_tag(v___x_1826_) == 0 {
                    v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
                    v_isSharedCheck_1840_ = (!lean_is_exclusive(v___x_1826_)) as u8;
                    if v_isSharedCheck_1840_ == 0 {
                        v___x_1829_ = v___x_1826_;
                        v_isShared_1830_ = v_isSharedCheck_1840_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1827_);
                        lean_dec(v___x_1826_);
                        v___x_1829_ = lean_box(0);
                        v_isShared_1830_ = v_isSharedCheck_1840_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_p_1812_);
                    v_a_1841_ = lean_ctor_get(v___x_1826_, 0);
                    v_isSharedCheck_1848_ = (!lean_is_exclusive(v___x_1826_)) as u8;
                    if v_isSharedCheck_1848_ == 0 {
                        v___x_1843_ = v___x_1826_;
                        v_isShared_1844_ = v_isSharedCheck_1848_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1841_);
                        lean_dec(v___x_1826_);
                        v___x_1843_ = lean_box(0);
                        v_isShared_1844_ = v_isSharedCheck_1848_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1827_) == 1 {
                    v_val_1831_ = lean_ctor_get(v_a_1827_, 0);
                    lean_inc(v_val_1831_);
                    lean_dec_ref_known(v_a_1827_, 1);
                    v___x_1832_ =
                        l_Lean_Grind_CommRing_Poly_addConstC(v_p_1812_, v_k_1813_, v_val_1831_);
                    if v_isShared_1830_ == 0 {
                        lean_ctor_set(v___x_1829_, 0, v___x_1832_);
                        v___x_1834_ = v___x_1829_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1832_);
                        v___x_1834_ = v_reuseFailAlloc_1835_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1827_);
                    v___x_1836_ = l_Lean_Grind_CommRing_Poly_addConst(v_p_1812_, v_k_1813_);
                    if v_isShared_1830_ == 0 {
                        lean_ctor_set(v___x_1829_, 0, v___x_1836_);
                        v___x_1838_ = v___x_1829_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
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
                    v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
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
    mut v_p_1849_: *mut LeanObject,
    mut v_k_1850_: *mut LeanObject,
    mut v_a_1851_: *mut LeanObject,
    mut v_a_1852_: *mut LeanObject,
    mut v_a_1853_: *mut LeanObject,
    mut v_a_1854_: *mut LeanObject,
    mut v_a_1855_: *mut LeanObject,
    mut v_a_1856_: *mut LeanObject,
    mut v_a_1857_: *mut LeanObject,
    mut v_a_1858_: *mut LeanObject,
    mut v_a_1859_: *mut LeanObject,
    mut v_a_1860_: *mut LeanObject,
    mut v_a_1861_: *mut LeanObject,
    mut v_a_1862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1863_: *mut LeanObject = core::ptr::null_mut();
    v_res_1863_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(v_p_1849_, v_k_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
    lean_dec(v_a_1861_);
    lean_dec_ref(v_a_1860_);
    lean_dec(v_a_1859_);
    lean_dec_ref(v_a_1858_);
    lean_dec(v_a_1857_);
    lean_dec_ref(v_a_1856_);
    lean_dec(v_a_1855_);
    lean_dec_ref(v_a_1854_);
    lean_dec(v_a_1853_);
    lean_dec(v_a_1852_);
    lean_dec_ref(v_a_1851_);
    lean_dec(v_k_1850_);
    return v_res_1863_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(
    mut v_k_1864_: *mut LeanObject,
    mut v_p_1865_: *mut LeanObject,
    mut v_a_1866_: *mut LeanObject,
    mut v_a_1867_: *mut LeanObject,
    mut v_a_1868_: *mut LeanObject,
    mut v_a_1869_: *mut LeanObject,
    mut v_a_1870_: *mut LeanObject,
    mut v_a_1871_: *mut LeanObject,
    mut v_a_1872_: *mut LeanObject,
    mut v_a_1873_: *mut LeanObject,
    mut v_a_1874_: *mut LeanObject,
    mut v_a_1875_: *mut LeanObject,
    mut v_a_1876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1882_: u8 = 0;
    let mut v_val_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1892_: u8 = 0;
    let mut v_a_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1896_: u8 = 0;
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1900_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1878_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_);
                if lean_obj_tag(v___x_1878_) == 0 {
                    v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
                    v_isSharedCheck_1892_ = (!lean_is_exclusive(v___x_1878_)) as u8;
                    if v_isSharedCheck_1892_ == 0 {
                        v___x_1881_ = v___x_1878_;
                        v_isShared_1882_ = v_isSharedCheck_1892_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1879_);
                        lean_dec(v___x_1878_);
                        v___x_1881_ = lean_box(0);
                        v_isShared_1882_ = v_isSharedCheck_1892_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_p_1865_);
                    v_a_1893_ = lean_ctor_get(v___x_1878_, 0);
                    v_isSharedCheck_1900_ = (!lean_is_exclusive(v___x_1878_)) as u8;
                    if v_isSharedCheck_1900_ == 0 {
                        v___x_1895_ = v___x_1878_;
                        v_isShared_1896_ = v_isSharedCheck_1900_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1893_);
                        lean_dec(v___x_1878_);
                        v___x_1895_ = lean_box(0);
                        v_isShared_1896_ = v_isSharedCheck_1900_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1879_) == 1 {
                    v_val_1883_ = lean_ctor_get(v_a_1879_, 0);
                    lean_inc(v_val_1883_);
                    lean_dec_ref_known(v_a_1879_, 1);
                    v___x_1884_ =
                        l_Lean_Grind_CommRing_Poly_mulConstC(v_k_1864_, v_p_1865_, v_val_1883_);
                    if v_isShared_1882_ == 0 {
                        lean_ctor_set(v___x_1881_, 0, v___x_1884_);
                        v___x_1886_ = v___x_1881_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1887_, 0, v___x_1884_);
                        v___x_1886_ = v_reuseFailAlloc_1887_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1879_);
                    v___x_1888_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_1864_, v_p_1865_);
                    if v_isShared_1882_ == 0 {
                        lean_ctor_set(v___x_1881_, 0, v___x_1888_);
                        v___x_1890_ = v___x_1881_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1888_);
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
                    v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
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
    mut v_k_1901_: *mut LeanObject,
    mut v_p_1902_: *mut LeanObject,
    mut v_a_1903_: *mut LeanObject,
    mut v_a_1904_: *mut LeanObject,
    mut v_a_1905_: *mut LeanObject,
    mut v_a_1906_: *mut LeanObject,
    mut v_a_1907_: *mut LeanObject,
    mut v_a_1908_: *mut LeanObject,
    mut v_a_1909_: *mut LeanObject,
    mut v_a_1910_: *mut LeanObject,
    mut v_a_1911_: *mut LeanObject,
    mut v_a_1912_: *mut LeanObject,
    mut v_a_1913_: *mut LeanObject,
    mut v_a_1914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1915_: *mut LeanObject = core::ptr::null_mut();
    v_res_1915_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v_k_1901_, v_p_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_);
    lean_dec(v_a_1913_);
    lean_dec_ref(v_a_1912_);
    lean_dec(v_a_1911_);
    lean_dec_ref(v_a_1910_);
    lean_dec(v_a_1909_);
    lean_dec_ref(v_a_1908_);
    lean_dec(v_a_1907_);
    lean_dec_ref(v_a_1906_);
    lean_dec(v_a_1905_);
    lean_dec(v_a_1904_);
    lean_dec_ref(v_a_1903_);
    lean_dec(v_k_1901_);
    return v_res_1915_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(
    mut v_k_1916_: *mut LeanObject,
    mut v_m_1917_: *mut LeanObject,
    mut v_p_1918_: *mut LeanObject,
    mut v_a_1919_: *mut LeanObject,
    mut v_a_1920_: *mut LeanObject,
    mut v_a_1921_: *mut LeanObject,
    mut v_a_1922_: *mut LeanObject,
    mut v_a_1923_: *mut LeanObject,
    mut v_a_1924_: *mut LeanObject,
    mut v_a_1925_: *mut LeanObject,
    mut v_a_1926_: *mut LeanObject,
    mut v_a_1927_: *mut LeanObject,
    mut v_a_1928_: *mut LeanObject,
    mut v_a_1929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1935_: u8 = 0;
    let mut v_val_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1945_: u8 = 0;
    let mut v_a_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1949_: u8 = 0;
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1953_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1931_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_);
                if lean_obj_tag(v___x_1931_) == 0 {
                    v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
                    v_isSharedCheck_1945_ = (!lean_is_exclusive(v___x_1931_)) as u8;
                    if v_isSharedCheck_1945_ == 0 {
                        v___x_1934_ = v___x_1931_;
                        v_isShared_1935_ = v_isSharedCheck_1945_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1932_);
                        lean_dec(v___x_1931_);
                        v___x_1934_ = lean_box(0);
                        v_isShared_1935_ = v_isSharedCheck_1945_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_p_1918_);
                    lean_dec(v_m_1917_);
                    v_a_1946_ = lean_ctor_get(v___x_1931_, 0);
                    v_isSharedCheck_1953_ = (!lean_is_exclusive(v___x_1931_)) as u8;
                    if v_isSharedCheck_1953_ == 0 {
                        v___x_1948_ = v___x_1931_;
                        v_isShared_1949_ = v_isSharedCheck_1953_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1946_);
                        lean_dec(v___x_1931_);
                        v___x_1948_ = lean_box(0);
                        v_isShared_1949_ = v_isSharedCheck_1953_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1932_) == 1 {
                    v_val_1936_ = lean_ctor_get(v_a_1932_, 0);
                    lean_inc(v_val_1936_);
                    lean_dec_ref_known(v_a_1932_, 1);
                    v___x_1937_ = l_Lean_Grind_CommRing_Poly_mulMonC(
                        v_k_1916_,
                        v_m_1917_,
                        v_p_1918_,
                        v_val_1936_,
                    );
                    if v_isShared_1935_ == 0 {
                        lean_ctor_set(v___x_1934_, 0, v___x_1937_);
                        v___x_1939_ = v___x_1934_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1937_);
                        v___x_1939_ = v_reuseFailAlloc_1940_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1932_);
                    v___x_1941_ =
                        l_Lean_Grind_CommRing_Poly_mulMon(v_k_1916_, v_m_1917_, v_p_1918_);
                    if v_isShared_1935_ == 0 {
                        lean_ctor_set(v___x_1934_, 0, v___x_1941_);
                        v___x_1943_ = v___x_1934_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1941_);
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
                    v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
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
    mut v_k_1954_: *mut LeanObject,
    mut v_m_1955_: *mut LeanObject,
    mut v_p_1956_: *mut LeanObject,
    mut v_a_1957_: *mut LeanObject,
    mut v_a_1958_: *mut LeanObject,
    mut v_a_1959_: *mut LeanObject,
    mut v_a_1960_: *mut LeanObject,
    mut v_a_1961_: *mut LeanObject,
    mut v_a_1962_: *mut LeanObject,
    mut v_a_1963_: *mut LeanObject,
    mut v_a_1964_: *mut LeanObject,
    mut v_a_1965_: *mut LeanObject,
    mut v_a_1966_: *mut LeanObject,
    mut v_a_1967_: *mut LeanObject,
    mut v_a_1968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1969_: *mut LeanObject = core::ptr::null_mut();
    v_res_1969_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_k_1954_, v_m_1955_, v_p_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_);
    lean_dec(v_a_1967_);
    lean_dec_ref(v_a_1966_);
    lean_dec(v_a_1965_);
    lean_dec_ref(v_a_1964_);
    lean_dec(v_a_1963_);
    lean_dec_ref(v_a_1962_);
    lean_dec(v_a_1961_);
    lean_dec_ref(v_a_1960_);
    lean_dec(v_a_1959_);
    lean_dec(v_a_1958_);
    lean_dec_ref(v_a_1957_);
    lean_dec(v_k_1954_);
    return v_res_1969_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    v___x_1975_ = l_Lean_maxRecDepthErrorMessage;
    v___x_1976_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1976_, 0, v___x_1975_);
    return v___x_1976_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    v___x_1977_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__3);
    v___x_1978_ = l_Lean_MessageData_ofFormat(v___x_1977_);
    return v___x_1978_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    v___x_1979_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__4);
    v___x_1980_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__2;
    v___x_1981_ = lean_alloc_ctor(8, 2, (0) as u32);
    lean_ctor_set(v___x_1981_, 0, v___x_1980_);
    lean_ctor_set(v___x_1981_, 1, v___x_1979_);
    return v___x_1981_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(
    mut v_ref_1982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    v___x_1984_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___closed__5);
    v___x_1985_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1985_, 0, v_ref_1982_);
    lean_ctor_set(v___x_1985_, 1, v___x_1984_);
    v___x_1986_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1986_, 0, v___x_1985_);
    return v___x_1986_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg___boxed(
    mut v_ref_1987_: *mut LeanObject,
    mut v___y_1988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1989_: *mut LeanObject = core::ptr::null_mut();
    v_res_1989_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(v_ref_1987_);
    return v_res_1989_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0(
    mut v_00_u03b1_1990_: *mut LeanObject,
    mut v_ref_1991_: *mut LeanObject,
    mut v___y_1992_: *mut LeanObject,
    mut v___y_1993_: *mut LeanObject,
    mut v___y_1994_: *mut LeanObject,
    mut v___y_1995_: *mut LeanObject,
    mut v___y_1996_: *mut LeanObject,
    mut v___y_1997_: *mut LeanObject,
    mut v___y_1998_: *mut LeanObject,
    mut v___y_1999_: *mut LeanObject,
    mut v___y_2000_: *mut LeanObject,
    mut v___y_2001_: *mut LeanObject,
    mut v___y_2002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    v___x_2004_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(v_ref_1991_);
    return v___x_2004_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___boxed(
    mut v_00_u03b1_2005_: *mut LeanObject,
    mut v_ref_2006_: *mut LeanObject,
    mut v___y_2007_: *mut LeanObject,
    mut v___y_2008_: *mut LeanObject,
    mut v___y_2009_: *mut LeanObject,
    mut v___y_2010_: *mut LeanObject,
    mut v___y_2011_: *mut LeanObject,
    mut v___y_2012_: *mut LeanObject,
    mut v___y_2013_: *mut LeanObject,
    mut v___y_2014_: *mut LeanObject,
    mut v___y_2015_: *mut LeanObject,
    mut v___y_2016_: *mut LeanObject,
    mut v___y_2017_: *mut LeanObject,
    mut v___y_2018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2019_: *mut LeanObject = core::ptr::null_mut();
    v_res_2019_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0(v_00_u03b1_2005_, v_ref_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
    lean_dec(v___y_2017_);
    lean_dec_ref(v___y_2016_);
    lean_dec(v___y_2015_);
    lean_dec_ref(v___y_2014_);
    lean_dec(v___y_2013_);
    lean_dec_ref(v___y_2012_);
    lean_dec(v___y_2011_);
    lean_dec_ref(v___y_2010_);
    lean_dec(v___y_2009_);
    lean_dec(v___y_2008_);
    lean_dec_ref(v___y_2007_);
    return v_res_2019_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0()
-> *mut LeanObject {
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    v___x_2020_ = lean_unsigned_to_nat(0);
    v___x_2021_ = lean_nat_to_int(v___x_2020_);
    return v___x_2021_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(
    mut v_p_u2081_2022_: *mut LeanObject,
    mut v_p_u2082_2023_: *mut LeanObject,
    mut v_a_2024_: *mut LeanObject,
    mut v_a_2025_: *mut LeanObject,
    mut v_a_2026_: *mut LeanObject,
    mut v_a_2027_: *mut LeanObject,
    mut v_a_2028_: *mut LeanObject,
    mut v_a_2029_: *mut LeanObject,
    mut v_a_2030_: *mut LeanObject,
    mut v_a_2031_: *mut LeanObject,
    mut v_a_2032_: *mut LeanObject,
    mut v_a_2033_: *mut LeanObject,
    mut v_a_2034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2048_: u8 = 0;
    let mut v_cancelTk_x3f_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2050_: u8 = 0;
    let mut v_inheritedTraceOptions_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2060_: u8 = 0;
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2066_: u8 = 0;
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2073_: u8 = 0;
    let mut v_a_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2077_: u8 = 0;
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2081_: u8 = 0;
    let mut v_isSharedCheck_2082_: u8 = 0;
    let mut v_k_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: u8 = 0;
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2096_: u8 = 0;
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2101_: u8 = 0;
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2108_: u8 = 0;
    let mut v_isSharedCheck_2109_: u8 = 0;
    let mut v_unused_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2115_: u8 = 0;
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: u8 = 0;
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2125_: u8 = 0;
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2132_: u8 = 0;
    let mut v_a_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2137_: u8 = 0;
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2141_: u8 = 0;
    let mut v_isSharedCheck_2142_: u8 = 0;
    let mut v_unused_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2148_: u8 = 0;
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2153_: u8 = 0;
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2160_: u8 = 0;
    let mut v_isSharedCheck_2161_: u8 = 0;
    let mut v_unused_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: u8 = 0;
    let mut v___x_2167_: u8 = 0;
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_2036_ = lean_ctor_get(v_a_2033_, 0);
                lean_inc_ref(v_fileName_2036_);
                v_fileMap_2037_ = lean_ctor_get(v_a_2033_, 1);
                lean_inc_ref(v_fileMap_2037_);
                v_options_2038_ = lean_ctor_get(v_a_2033_, 2);
                lean_inc_ref(v_options_2038_);
                v_currRecDepth_2039_ = lean_ctor_get(v_a_2033_, 3);
                lean_inc(v_currRecDepth_2039_);
                v_maxRecDepth_2040_ = lean_ctor_get(v_a_2033_, 4);
                lean_inc(v_maxRecDepth_2040_);
                v_ref_2041_ = lean_ctor_get(v_a_2033_, 5);
                lean_inc(v_ref_2041_);
                v_currNamespace_2042_ = lean_ctor_get(v_a_2033_, 6);
                lean_inc(v_currNamespace_2042_);
                v_openDecls_2043_ = lean_ctor_get(v_a_2033_, 7);
                lean_inc(v_openDecls_2043_);
                v_initHeartbeats_2044_ = lean_ctor_get(v_a_2033_, 8);
                lean_inc(v_initHeartbeats_2044_);
                v_maxHeartbeats_2045_ = lean_ctor_get(v_a_2033_, 9);
                lean_inc(v_maxHeartbeats_2045_);
                v_quotContext_2046_ = lean_ctor_get(v_a_2033_, 10);
                lean_inc(v_quotContext_2046_);
                v_currMacroScope_2047_ = lean_ctor_get(v_a_2033_, 11);
                lean_inc(v_currMacroScope_2047_);
                v_diag_2048_ = lean_ctor_get_uint8(
                    v_a_2033_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_2049_ = lean_ctor_get(v_a_2033_, 12);
                lean_inc(v_cancelTk_x3f_2049_);
                v_suppressElabErrors_2050_ = lean_ctor_get_uint8(
                    v_a_2033_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_2051_ = lean_ctor_get(v_a_2033_, 13);
                lean_inc_ref(v_inheritedTraceOptions_2051_);
                lean_dec_ref(v_a_2033_);
                v___x_2165_ = lean_unsigned_to_nat(0);
                v___x_2166_ = lean_nat_dec_eq(v_maxRecDepth_2040_, v___x_2165_);
                if v___x_2166_ == 0 {
                    v___x_2167_ = lean_nat_dec_eq(v_currRecDepth_2039_, v_maxRecDepth_2040_);
                    if v___x_2167_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_inheritedTraceOptions_2051_);
                        lean_dec(v_cancelTk_x3f_2049_);
                        lean_dec(v_currMacroScope_2047_);
                        lean_dec(v_quotContext_2046_);
                        lean_dec(v_maxHeartbeats_2045_);
                        lean_dec(v_initHeartbeats_2044_);
                        lean_dec(v_openDecls_2043_);
                        lean_dec(v_currNamespace_2042_);
                        lean_dec(v_maxRecDepth_2040_);
                        lean_dec(v_currRecDepth_2039_);
                        lean_dec_ref(v_options_2038_);
                        lean_dec_ref(v_fileMap_2037_);
                        lean_dec_ref(v_fileName_2036_);
                        lean_dec_ref(v_p_u2082_2023_);
                        lean_dec_ref(v_p_u2081_2022_);
                        v___x_2168_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(v_ref_2041_);
                        return v___x_2168_;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2053_ = lean_unsigned_to_nat(1);
                v___x_2054_ = lean_nat_add(v_currRecDepth_2039_, v___x_2053_);
                lean_dec(v_currRecDepth_2039_);
                v___x_2055_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_2055_, 0, v_fileName_2036_);
                lean_ctor_set(v___x_2055_, 1, v_fileMap_2037_);
                lean_ctor_set(v___x_2055_, 2, v_options_2038_);
                lean_ctor_set(v___x_2055_, 3, v___x_2054_);
                lean_ctor_set(v___x_2055_, 4, v_maxRecDepth_2040_);
                lean_ctor_set(v___x_2055_, 5, v_ref_2041_);
                lean_ctor_set(v___x_2055_, 6, v_currNamespace_2042_);
                lean_ctor_set(v___x_2055_, 7, v_openDecls_2043_);
                lean_ctor_set(v___x_2055_, 8, v_initHeartbeats_2044_);
                lean_ctor_set(v___x_2055_, 9, v_maxHeartbeats_2045_);
                lean_ctor_set(v___x_2055_, 10, v_quotContext_2046_);
                lean_ctor_set(v___x_2055_, 11, v_currMacroScope_2047_);
                lean_ctor_set(v___x_2055_, 12, v_cancelTk_x3f_2049_);
                lean_ctor_set(v___x_2055_, 13, v_inheritedTraceOptions_2051_);
                lean_ctor_set_uint8(
                    v___x_2055_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_2048_,
                );
                lean_ctor_set_uint8(
                    v___x_2055_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_2050_,
                );
                if lean_obj_tag(v_p_u2081_2022_) == 0 {
                    if lean_obj_tag(v_p_u2082_2023_) == 0 {
                        v_k_2056_ = lean_ctor_get(v_p_u2081_2022_, 0);
                        lean_inc(v_k_2056_);
                        lean_dec_ref_known(v_p_u2081_2022_, 1);
                        v_k_2057_ = lean_ctor_get(v_p_u2082_2023_, 0);
                        v_isSharedCheck_2082_ = (!lean_is_exclusive(v_p_u2082_2023_)) as u8;
                        if v_isSharedCheck_2082_ == 0 {
                            v___x_2059_ = v_p_u2082_2023_;
                            v_isShared_2060_ = v_isSharedCheck_2082_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_k_2057_);
                            lean_dec(v_p_u2082_2023_);
                            v___x_2059_ = lean_box(0);
                            v_isShared_2060_ = v_isSharedCheck_2082_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_k_2083_ = lean_ctor_get(v_p_u2081_2022_, 0);
                        lean_inc(v_k_2083_);
                        lean_dec_ref_known(v_p_u2081_2022_, 1);
                        v___x_2084_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(v_p_u2082_2023_, v_k_2083_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v___x_2055_, v_a_2034_);
                        lean_dec_ref_known(v___x_2055_, 14);
                        lean_dec(v_k_2083_);
                        return v___x_2084_;
                    }
                } else {
                    if lean_obj_tag(v_p_u2082_2023_) == 0 {
                        v_k_2085_ = lean_ctor_get(v_p_u2082_2023_, 0);
                        lean_inc(v_k_2085_);
                        lean_dec_ref_known(v_p_u2082_2023_, 1);
                        v___x_2086_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_addConst(v_p_u2081_2022_, v_k_2085_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v___x_2055_, v_a_2034_);
                        lean_dec_ref_known(v___x_2055_, 14);
                        lean_dec(v_k_2085_);
                        return v___x_2086_;
                    } else {
                        v_k_2087_ = lean_ctor_get(v_p_u2081_2022_, 0);
                        v_v_2088_ = lean_ctor_get(v_p_u2081_2022_, 1);
                        v_p_2089_ = lean_ctor_get(v_p_u2081_2022_, 2);
                        v_k_2090_ = lean_ctor_get(v_p_u2082_2023_, 0);
                        v_v_2091_ = lean_ctor_get(v_p_u2082_2023_, 1);
                        v_p_2092_ = lean_ctor_get(v_p_u2082_2023_, 2);
                        v___x_2093_ = l_Lean_Grind_CommRing_Mon_grevlex(v_v_2088_, v_v_2091_);
                        match v___x_2093_ {
                            0 => {
                                lean_inc_ref(v_p_2092_);
                                lean_inc(v_v_2091_);
                                lean_inc(v_k_2090_);
                                v_isSharedCheck_2109_ = (!lean_is_exclusive(v_p_u2082_2023_)) as u8;
                                if v_isSharedCheck_2109_ == 0 {
                                    v_unused_2110_ = lean_ctor_get(v_p_u2082_2023_, 2);
                                    lean_dec(v_unused_2110_);
                                    v_unused_2111_ = lean_ctor_get(v_p_u2082_2023_, 1);
                                    lean_dec(v_unused_2111_);
                                    v_unused_2112_ = lean_ctor_get(v_p_u2082_2023_, 0);
                                    lean_dec(v_unused_2112_);
                                    v___x_2095_ = v_p_u2082_2023_;
                                    v_isShared_2096_ = v_isSharedCheck_2109_;
                                    state = 8;
                                    continue;
                                } else {
                                    lean_dec(v_p_u2082_2023_);
                                    v___x_2095_ = lean_box(0);
                                    v_isShared_2096_ = v_isSharedCheck_2109_;
                                    state = 8;
                                    continue;
                                }
                            }
                            1 => {
                                lean_inc_ref(v_p_2092_);
                                lean_inc(v_k_2090_);
                                lean_inc_ref(v_p_2089_);
                                lean_inc(v_v_2088_);
                                lean_inc(v_k_2087_);
                                lean_dec_ref_known(v_p_u2081_2022_, 3);
                                v_isSharedCheck_2142_ = (!lean_is_exclusive(v_p_u2082_2023_)) as u8;
                                if v_isSharedCheck_2142_ == 0 {
                                    v_unused_2143_ = lean_ctor_get(v_p_u2082_2023_, 2);
                                    lean_dec(v_unused_2143_);
                                    v_unused_2144_ = lean_ctor_get(v_p_u2082_2023_, 1);
                                    lean_dec(v_unused_2144_);
                                    v_unused_2145_ = lean_ctor_get(v_p_u2082_2023_, 0);
                                    lean_dec(v_unused_2145_);
                                    v___x_2114_ = v_p_u2082_2023_;
                                    v_isShared_2115_ = v_isSharedCheck_2142_;
                                    state = 12;
                                    continue;
                                } else {
                                    lean_dec(v_p_u2082_2023_);
                                    v___x_2114_ = lean_box(0);
                                    v_isShared_2115_ = v_isSharedCheck_2142_;
                                    state = 12;
                                    continue;
                                }
                            }
                            _ => {
                                lean_inc_ref(v_p_2089_);
                                lean_inc(v_v_2088_);
                                lean_inc(v_k_2087_);
                                v_isSharedCheck_2161_ = (!lean_is_exclusive(v_p_u2081_2022_)) as u8;
                                if v_isSharedCheck_2161_ == 0 {
                                    v_unused_2162_ = lean_ctor_get(v_p_u2081_2022_, 2);
                                    lean_dec(v_unused_2162_);
                                    v_unused_2163_ = lean_ctor_get(v_p_u2081_2022_, 1);
                                    lean_dec(v_unused_2163_);
                                    v_unused_2164_ = lean_ctor_get(v_p_u2081_2022_, 0);
                                    lean_dec(v_unused_2164_);
                                    v___x_2147_ = v_p_u2081_2022_;
                                    v_isShared_2148_ = v_isSharedCheck_2161_;
                                    state = 18;
                                    continue;
                                } else {
                                    lean_dec(v_p_u2081_2022_);
                                    v___x_2147_ = lean_box(0);
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
                lean_dec(v_k_2057_);
                lean_dec(v_k_2056_);
                v___x_2062_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v___x_2061_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v___x_2055_, v_a_2034_);
                lean_dec_ref_known(v___x_2055_, 14);
                if lean_obj_tag(v___x_2062_) == 0 {
                    v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
                    v_isSharedCheck_2073_ = (!lean_is_exclusive(v___x_2062_)) as u8;
                    if v_isSharedCheck_2073_ == 0 {
                        v___x_2065_ = v___x_2062_;
                        v_isShared_2066_ = v_isSharedCheck_2073_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2063_);
                        lean_dec(v___x_2062_);
                        v___x_2065_ = lean_box(0);
                        v_isShared_2066_ = v_isSharedCheck_2073_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2059_);
                    v_a_2074_ = lean_ctor_get(v___x_2062_, 0);
                    v_isSharedCheck_2081_ = (!lean_is_exclusive(v___x_2062_)) as u8;
                    if v_isSharedCheck_2081_ == 0 {
                        v___x_2076_ = v___x_2062_;
                        v_isShared_2077_ = v_isSharedCheck_2081_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_2074_);
                        lean_dec(v___x_2062_);
                        v___x_2076_ = lean_box(0);
                        v_isShared_2077_ = v_isSharedCheck_2081_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2060_ == 0 {
                    lean_ctor_set(v___x_2059_, 0, v_a_2063_);
                    v___x_2068_ = v___x_2059_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2063_);
                    v___x_2068_ = v_reuseFailAlloc_2072_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2066_ == 0 {
                    lean_ctor_set(v___x_2065_, 0, v___x_2068_);
                    v___x_2070_ = v___x_2065_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2068_);
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
                    v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
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
                if lean_obj_tag(v___x_2097_) == 0 {
                    v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
                    v_isSharedCheck_2108_ = (!lean_is_exclusive(v___x_2097_)) as u8;
                    if v_isSharedCheck_2108_ == 0 {
                        v___x_2100_ = v___x_2097_;
                        v_isShared_2101_ = v_isSharedCheck_2108_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_2098_);
                        lean_dec(v___x_2097_);
                        v___x_2100_ = lean_box(0);
                        v_isShared_2101_ = v_isSharedCheck_2108_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2095_);
                    lean_dec(v_v_2091_);
                    lean_dec(v_k_2090_);
                    return v___x_2097_;
                }
            }
            9 => {
                if v_isShared_2096_ == 0 {
                    lean_ctor_set(v___x_2095_, 2, v_a_2098_);
                    v___x_2103_ = v___x_2095_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_k_2090_);
                    lean_ctor_set(v_reuseFailAlloc_2107_, 1, v_v_2091_);
                    lean_ctor_set(v_reuseFailAlloc_2107_, 2, v_a_2098_);
                    v___x_2103_ = v_reuseFailAlloc_2107_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_2101_ == 0 {
                    lean_ctor_set(v___x_2100_, 0, v___x_2103_);
                    v___x_2105_ = v___x_2100_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2103_);
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
                lean_dec(v_k_2090_);
                lean_dec(v_k_2087_);
                v___x_2117_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v___x_2116_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v___x_2055_, v_a_2034_);
                if lean_obj_tag(v___x_2117_) == 0 {
                    v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
                    lean_inc(v_a_2118_);
                    lean_dec_ref_known(v___x_2117_, 1);
                    v___x_2119_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
                    v___x_2120_ = lean_int_dec_eq(v_a_2118_, v___x_2119_);
                    if v___x_2120_ == 0 {
                        v___x_2121_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_p_2089_, v_p_2092_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v___x_2055_, v_a_2034_);
                        if lean_obj_tag(v___x_2121_) == 0 {
                            v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
                            v_isSharedCheck_2132_ = (!lean_is_exclusive(v___x_2121_)) as u8;
                            if v_isSharedCheck_2132_ == 0 {
                                v___x_2124_ = v___x_2121_;
                                v_isShared_2125_ = v_isSharedCheck_2132_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_a_2122_);
                                lean_dec(v___x_2121_);
                                v___x_2124_ = lean_box(0);
                                v_isShared_2125_ = v_isSharedCheck_2132_;
                                state = 13;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_2118_);
                            lean_del_object(v___x_2114_);
                            lean_dec(v_v_2088_);
                            return v___x_2121_;
                        }
                    } else {
                        lean_dec(v_a_2118_);
                        lean_del_object(v___x_2114_);
                        lean_dec(v_v_2088_);
                        v_p_u2081_2022_ = v_p_2089_;
                        v_p_u2082_2023_ = v_p_2092_;
                        v_a_2033_ = v___x_2055_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2114_);
                    lean_dec_ref(v_p_2092_);
                    lean_dec_ref(v_p_2089_);
                    lean_dec(v_v_2088_);
                    lean_dec_ref_known(v___x_2055_, 14);
                    v_a_2134_ = lean_ctor_get(v___x_2117_, 0);
                    v_isSharedCheck_2141_ = (!lean_is_exclusive(v___x_2117_)) as u8;
                    if v_isSharedCheck_2141_ == 0 {
                        v___x_2136_ = v___x_2117_;
                        v_isShared_2137_ = v_isSharedCheck_2141_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_2134_);
                        lean_dec(v___x_2117_);
                        v___x_2136_ = lean_box(0);
                        v_isShared_2137_ = v_isSharedCheck_2141_;
                        state = 16;
                        continue;
                    }
                }
            }
            13 => {
                if v_isShared_2115_ == 0 {
                    lean_ctor_set(v___x_2114_, 2, v_a_2122_);
                    lean_ctor_set(v___x_2114_, 1, v_v_2088_);
                    lean_ctor_set(v___x_2114_, 0, v_a_2118_);
                    v___x_2127_ = v___x_2114_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2118_);
                    lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_v_2088_);
                    lean_ctor_set(v_reuseFailAlloc_2131_, 2, v_a_2122_);
                    v___x_2127_ = v_reuseFailAlloc_2131_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_2125_ == 0 {
                    lean_ctor_set(v___x_2124_, 0, v___x_2127_);
                    v___x_2129_ = v___x_2124_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2127_);
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
                    v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
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
                if lean_obj_tag(v___x_2149_) == 0 {
                    v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
                    v_isSharedCheck_2160_ = (!lean_is_exclusive(v___x_2149_)) as u8;
                    if v_isSharedCheck_2160_ == 0 {
                        v___x_2152_ = v___x_2149_;
                        v_isShared_2153_ = v_isSharedCheck_2160_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_2150_);
                        lean_dec(v___x_2149_);
                        v___x_2152_ = lean_box(0);
                        v_isShared_2153_ = v_isSharedCheck_2160_;
                        state = 19;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2147_);
                    lean_dec(v_v_2088_);
                    lean_dec(v_k_2087_);
                    return v___x_2149_;
                }
            }
            19 => {
                if v_isShared_2148_ == 0 {
                    lean_ctor_set(v___x_2147_, 2, v_a_2150_);
                    v___x_2155_ = v___x_2147_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_k_2087_);
                    lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_v_2088_);
                    lean_ctor_set(v_reuseFailAlloc_2159_, 2, v_a_2150_);
                    v___x_2155_ = v_reuseFailAlloc_2159_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_2153_ == 0 {
                    lean_ctor_set(v___x_2152_, 0, v___x_2155_);
                    v___x_2157_ = v___x_2152_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2155_);
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
    mut v_p_u2081_2169_: *mut LeanObject,
    mut v_p_u2082_2170_: *mut LeanObject,
    mut v_a_2171_: *mut LeanObject,
    mut v_a_2172_: *mut LeanObject,
    mut v_a_2173_: *mut LeanObject,
    mut v_a_2174_: *mut LeanObject,
    mut v_a_2175_: *mut LeanObject,
    mut v_a_2176_: *mut LeanObject,
    mut v_a_2177_: *mut LeanObject,
    mut v_a_2178_: *mut LeanObject,
    mut v_a_2179_: *mut LeanObject,
    mut v_a_2180_: *mut LeanObject,
    mut v_a_2181_: *mut LeanObject,
    mut v_a_2182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2183_: *mut LeanObject = core::ptr::null_mut();
    v_res_2183_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_p_u2081_2169_, v_p_u2082_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_);
    lean_dec(v_a_2181_);
    lean_dec(v_a_2179_);
    lean_dec_ref(v_a_2178_);
    lean_dec(v_a_2177_);
    lean_dec_ref(v_a_2176_);
    lean_dec(v_a_2175_);
    lean_dec_ref(v_a_2174_);
    lean_dec(v_a_2173_);
    lean_dec(v_a_2172_);
    lean_dec_ref(v_a_2171_);
    return v_res_2183_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__3_splitter___redArg(
    mut v_p_u2081_2184_: *mut LeanObject,
    mut v_p_u2082_2185_: *mut LeanObject,
    mut v_h__1_2186_: *mut LeanObject,
    mut v_h__2_2187_: *mut LeanObject,
    mut v_h__3_2188_: *mut LeanObject,
    mut v_h__4_2189_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_u2081_2184_) == 0 {
        lean_dec(v_h__4_2189_);
        lean_dec(v_h__3_2188_);
        if lean_obj_tag(v_p_u2082_2185_) == 0 {
            let mut v_k_2190_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_2191_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_2187_);
            v_k_2190_ = lean_ctor_get(v_p_u2081_2184_, 0);
            lean_inc(v_k_2190_);
            lean_dec_ref_known(v_p_u2081_2184_, 1);
            v_k_2191_ = lean_ctor_get(v_p_u2082_2185_, 0);
            lean_inc(v_k_2191_);
            lean_dec_ref_known(v_p_u2082_2185_, 1);
            v___x_2192_ = lean_apply_2(v_h__1_2186_, v_k_2190_, v_k_2191_);
            return v___x_2192_;
        } else {
            let mut v_k_2193_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_2194_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_2195_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_2196_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_2186_);
            v_k_2193_ = lean_ctor_get(v_p_u2081_2184_, 0);
            lean_inc(v_k_2193_);
            lean_dec_ref_known(v_p_u2081_2184_, 1);
            v_k_2194_ = lean_ctor_get(v_p_u2082_2185_, 0);
            lean_inc(v_k_2194_);
            v_v_2195_ = lean_ctor_get(v_p_u2082_2185_, 1);
            lean_inc(v_v_2195_);
            v_p_2196_ = lean_ctor_get(v_p_u2082_2185_, 2);
            lean_inc_ref(v_p_2196_);
            lean_dec_ref_known(v_p_u2082_2185_, 3);
            v___x_2197_ = lean_apply_4(v_h__2_2187_, v_k_2193_, v_k_2194_, v_v_2195_, v_p_2196_);
            return v___x_2197_;
        }
    } else {
        lean_dec(v_h__2_2187_);
        lean_dec(v_h__1_2186_);
        if lean_obj_tag(v_p_u2082_2185_) == 0 {
            let mut v_k_2198_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_2199_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_2200_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_2201_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_2189_);
            v_k_2198_ = lean_ctor_get(v_p_u2081_2184_, 0);
            lean_inc(v_k_2198_);
            v_v_2199_ = lean_ctor_get(v_p_u2081_2184_, 1);
            lean_inc(v_v_2199_);
            v_p_2200_ = lean_ctor_get(v_p_u2081_2184_, 2);
            lean_inc_ref(v_p_2200_);
            lean_dec_ref_known(v_p_u2081_2184_, 3);
            v_k_2201_ = lean_ctor_get(v_p_u2082_2185_, 0);
            lean_inc(v_k_2201_);
            lean_dec_ref_known(v_p_u2082_2185_, 1);
            v___x_2202_ = lean_apply_4(v_h__3_2188_, v_k_2198_, v_v_2199_, v_p_2200_, v_k_2201_);
            return v___x_2202_;
        } else {
            let mut v_k_2203_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_2204_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_2205_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_2206_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_2207_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_2208_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_2188_);
            v_k_2203_ = lean_ctor_get(v_p_u2081_2184_, 0);
            lean_inc(v_k_2203_);
            v_v_2204_ = lean_ctor_get(v_p_u2081_2184_, 1);
            lean_inc(v_v_2204_);
            v_p_2205_ = lean_ctor_get(v_p_u2081_2184_, 2);
            lean_inc_ref(v_p_2205_);
            lean_dec_ref_known(v_p_u2081_2184_, 3);
            v_k_2206_ = lean_ctor_get(v_p_u2082_2185_, 0);
            lean_inc(v_k_2206_);
            v_v_2207_ = lean_ctor_get(v_p_u2082_2185_, 1);
            lean_inc(v_v_2207_);
            v_p_2208_ = lean_ctor_get(v_p_u2082_2185_, 2);
            lean_inc_ref(v_p_2208_);
            lean_dec_ref_known(v_p_u2082_2185_, 3);
            v___x_2209_ = lean_apply_6(
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
    mut v_motive_2210_: *mut LeanObject,
    mut v_p_u2081_2211_: *mut LeanObject,
    mut v_p_u2082_2212_: *mut LeanObject,
    mut v_h__1_2213_: *mut LeanObject,
    mut v_h__2_2214_: *mut LeanObject,
    mut v_h__3_2215_: *mut LeanObject,
    mut v_h__4_2216_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_u2081_2211_) == 0 {
        lean_dec(v_h__4_2216_);
        lean_dec(v_h__3_2215_);
        if lean_obj_tag(v_p_u2082_2212_) == 0 {
            let mut v_k_2217_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_2218_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_2214_);
            v_k_2217_ = lean_ctor_get(v_p_u2081_2211_, 0);
            lean_inc(v_k_2217_);
            lean_dec_ref_known(v_p_u2081_2211_, 1);
            v_k_2218_ = lean_ctor_get(v_p_u2082_2212_, 0);
            lean_inc(v_k_2218_);
            lean_dec_ref_known(v_p_u2082_2212_, 1);
            v___x_2219_ = lean_apply_2(v_h__1_2213_, v_k_2217_, v_k_2218_);
            return v___x_2219_;
        } else {
            let mut v_k_2220_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_2221_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_2222_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_2223_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_2213_);
            v_k_2220_ = lean_ctor_get(v_p_u2081_2211_, 0);
            lean_inc(v_k_2220_);
            lean_dec_ref_known(v_p_u2081_2211_, 1);
            v_k_2221_ = lean_ctor_get(v_p_u2082_2212_, 0);
            lean_inc(v_k_2221_);
            v_v_2222_ = lean_ctor_get(v_p_u2082_2212_, 1);
            lean_inc(v_v_2222_);
            v_p_2223_ = lean_ctor_get(v_p_u2082_2212_, 2);
            lean_inc_ref(v_p_2223_);
            lean_dec_ref_known(v_p_u2082_2212_, 3);
            v___x_2224_ = lean_apply_4(v_h__2_2214_, v_k_2220_, v_k_2221_, v_v_2222_, v_p_2223_);
            return v___x_2224_;
        }
    } else {
        lean_dec(v_h__2_2214_);
        lean_dec(v_h__1_2213_);
        if lean_obj_tag(v_p_u2082_2212_) == 0 {
            let mut v_k_2225_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_2226_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_2227_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_2228_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_2216_);
            v_k_2225_ = lean_ctor_get(v_p_u2081_2211_, 0);
            lean_inc(v_k_2225_);
            v_v_2226_ = lean_ctor_get(v_p_u2081_2211_, 1);
            lean_inc(v_v_2226_);
            v_p_2227_ = lean_ctor_get(v_p_u2081_2211_, 2);
            lean_inc_ref(v_p_2227_);
            lean_dec_ref_known(v_p_u2081_2211_, 3);
            v_k_2228_ = lean_ctor_get(v_p_u2082_2212_, 0);
            lean_inc(v_k_2228_);
            lean_dec_ref_known(v_p_u2082_2212_, 1);
            v___x_2229_ = lean_apply_4(v_h__3_2215_, v_k_2225_, v_v_2226_, v_p_2227_, v_k_2228_);
            return v___x_2229_;
        } else {
            let mut v_k_2230_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_2231_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_2232_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_2233_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_2234_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_2235_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_2215_);
            v_k_2230_ = lean_ctor_get(v_p_u2081_2211_, 0);
            lean_inc(v_k_2230_);
            v_v_2231_ = lean_ctor_get(v_p_u2081_2211_, 1);
            lean_inc(v_v_2231_);
            v_p_2232_ = lean_ctor_get(v_p_u2081_2211_, 2);
            lean_inc_ref(v_p_2232_);
            lean_dec_ref_known(v_p_u2081_2211_, 3);
            v_k_2233_ = lean_ctor_get(v_p_u2082_2212_, 0);
            lean_inc(v_k_2233_);
            v_v_2234_ = lean_ctor_get(v_p_u2082_2212_, 1);
            lean_inc(v_v_2234_);
            v_p_2235_ = lean_ctor_get(v_p_u2082_2212_, 2);
            lean_inc_ref(v_p_2235_);
            lean_dec_ref_known(v_p_u2082_2212_, 3);
            v___x_2236_ = lean_apply_6(
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
    mut v_h__1_2238_: *mut LeanObject,
    mut v_h__2_2239_: *mut LeanObject,
    mut v_h__3_2240_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_2237_ {
        0 => {
            let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_2239_);
            lean_dec(v_h__1_2238_);
            v___x_2241_ = lean_box(0);
            v___x_2242_ = lean_apply_1(v_h__3_2240_, v___x_2241_);
            return v___x_2242_;
        }
        1 => {
            let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_2240_);
            lean_dec(v_h__2_2239_);
            v___x_2243_ = lean_box(0);
            v___x_2244_ = lean_apply_1(v_h__1_2238_, v___x_2243_);
            return v___x_2244_;
        }
        _ => {
            let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_2240_);
            lean_dec(v_h__1_2238_);
            v___x_2245_ = lean_box(0);
            v___x_2246_ = lean_apply_1(v_h__2_2239_, v___x_2245_);
            return v___x_2246_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___redArg___boxed(
    mut v_x_2247_: *mut LeanObject,
    mut v_h__1_2248_: *mut LeanObject,
    mut v_h__2_2249_: *mut LeanObject,
    mut v_h__3_2250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_36__boxed_2251_: u8 = 0;
    let mut v_res_2252_: *mut LeanObject = core::ptr::null_mut();
    v_x_36__boxed_2251_ = (lean_unbox(v_x_2247_) as u8);
    v_res_2252_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___redArg(v_x_36__boxed_2251_, v_h__1_2248_, v_h__2_2249_, v_h__3_2250_);
    return v_res_2252_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter(
    mut v_motive_2253_: *mut LeanObject,
    mut v_x_2254_: u8,
    mut v_h__1_2255_: *mut LeanObject,
    mut v_h__2_2256_: *mut LeanObject,
    mut v_h__3_2257_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_2254_ {
        0 => {
            let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_2256_);
            lean_dec(v_h__1_2255_);
            v___x_2258_ = lean_box(0);
            v___x_2259_ = lean_apply_1(v_h__3_2257_, v___x_2258_);
            return v___x_2259_;
        }
        1 => {
            let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_2257_);
            lean_dec(v_h__2_2256_);
            v___x_2260_ = lean_box(0);
            v___x_2261_ = lean_apply_1(v_h__1_2255_, v___x_2260_);
            return v___x_2261_;
        }
        _ => {
            let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_2257_);
            lean_dec(v_h__1_2255_);
            v___x_2262_ = lean_box(0);
            v___x_2263_ = lean_apply_1(v_h__2_2256_, v___x_2262_);
            return v___x_2263_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter___boxed(
    mut v_motive_2264_: *mut LeanObject,
    mut v_x_2265_: *mut LeanObject,
    mut v_h__1_2266_: *mut LeanObject,
    mut v_h__2_2267_: *mut LeanObject,
    mut v_h__3_2268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_51__boxed_2269_: u8 = 0;
    let mut v_res_2270_: *mut LeanObject = core::ptr::null_mut();
    v_x_51__boxed_2269_ = (lean_unbox(v_x_2265_) as u8);
    v_res_2270_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_match__1_splitter(v_motive_2264_, v_x_51__boxed_2269_, v_h__1_2266_, v_h__2_2267_, v_h__3_2268_);
    return v_res_2270_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go(
    mut v_p_u2082_2272_: *mut LeanObject,
    mut v_p_u2081_2273_: *mut LeanObject,
    mut v_acc_2274_: *mut LeanObject,
    mut v_a_2275_: *mut LeanObject,
    mut v_a_2276_: *mut LeanObject,
    mut v_a_2277_: *mut LeanObject,
    mut v_a_2278_: *mut LeanObject,
    mut v_a_2279_: *mut LeanObject,
    mut v_a_2280_: *mut LeanObject,
    mut v_a_2281_: *mut LeanObject,
    mut v_a_2282_: *mut LeanObject,
    mut v_a_2283_: *mut LeanObject,
    mut v_a_2284_: *mut LeanObject,
    mut v_a_2285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2299_: u8 = 0;
    let mut v_cancelTk_x3f_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2301_: u8 = 0;
    let mut v_inheritedTraceOptions_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2324_: u8 = 0;
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2328_: u8 = 0;
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: u8 = 0;
    let mut v___x_2331_: u8 = 0;
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_2287_ = lean_ctor_get(v_a_2284_, 0);
                lean_inc_ref(v_fileName_2287_);
                v_fileMap_2288_ = lean_ctor_get(v_a_2284_, 1);
                lean_inc_ref(v_fileMap_2288_);
                v_options_2289_ = lean_ctor_get(v_a_2284_, 2);
                lean_inc_ref(v_options_2289_);
                v_currRecDepth_2290_ = lean_ctor_get(v_a_2284_, 3);
                lean_inc(v_currRecDepth_2290_);
                v_maxRecDepth_2291_ = lean_ctor_get(v_a_2284_, 4);
                lean_inc(v_maxRecDepth_2291_);
                v_ref_2292_ = lean_ctor_get(v_a_2284_, 5);
                lean_inc(v_ref_2292_);
                v_currNamespace_2293_ = lean_ctor_get(v_a_2284_, 6);
                lean_inc(v_currNamespace_2293_);
                v_openDecls_2294_ = lean_ctor_get(v_a_2284_, 7);
                lean_inc(v_openDecls_2294_);
                v_initHeartbeats_2295_ = lean_ctor_get(v_a_2284_, 8);
                lean_inc(v_initHeartbeats_2295_);
                v_maxHeartbeats_2296_ = lean_ctor_get(v_a_2284_, 9);
                lean_inc(v_maxHeartbeats_2296_);
                v_quotContext_2297_ = lean_ctor_get(v_a_2284_, 10);
                lean_inc(v_quotContext_2297_);
                v_currMacroScope_2298_ = lean_ctor_get(v_a_2284_, 11);
                lean_inc(v_currMacroScope_2298_);
                v_diag_2299_ = lean_ctor_get_uint8(
                    v_a_2284_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_2300_ = lean_ctor_get(v_a_2284_, 12);
                lean_inc(v_cancelTk_x3f_2300_);
                v_suppressElabErrors_2301_ = lean_ctor_get_uint8(
                    v_a_2284_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_2302_ = lean_ctor_get(v_a_2284_, 13);
                lean_inc_ref(v_inheritedTraceOptions_2302_);
                lean_dec_ref(v_a_2284_);
                v___x_2329_ = lean_unsigned_to_nat(0);
                v___x_2330_ = lean_nat_dec_eq(v_maxRecDepth_2291_, v___x_2329_);
                if v___x_2330_ == 0 {
                    v___x_2331_ = lean_nat_dec_eq(v_currRecDepth_2290_, v_maxRecDepth_2291_);
                    if v___x_2331_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_inheritedTraceOptions_2302_);
                        lean_dec(v_cancelTk_x3f_2300_);
                        lean_dec(v_currMacroScope_2298_);
                        lean_dec(v_quotContext_2297_);
                        lean_dec(v_maxHeartbeats_2296_);
                        lean_dec(v_initHeartbeats_2295_);
                        lean_dec(v_openDecls_2294_);
                        lean_dec(v_currNamespace_2293_);
                        lean_dec(v_maxRecDepth_2291_);
                        lean_dec(v_currRecDepth_2290_);
                        lean_dec_ref(v_options_2289_);
                        lean_dec_ref(v_fileMap_2288_);
                        lean_dec_ref(v_fileName_2287_);
                        lean_dec_ref(v_acc_2274_);
                        lean_dec_ref(v_p_u2081_2273_);
                        lean_dec_ref(v_p_u2082_2272_);
                        v___x_2332_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(v_ref_2292_);
                        return v___x_2332_;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2304_ = lean_unsigned_to_nat(1);
                v___x_2305_ = lean_nat_add(v_currRecDepth_2290_, v___x_2304_);
                lean_dec(v_currRecDepth_2290_);
                v___x_2306_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_2306_, 0, v_fileName_2287_);
                lean_ctor_set(v___x_2306_, 1, v_fileMap_2288_);
                lean_ctor_set(v___x_2306_, 2, v_options_2289_);
                lean_ctor_set(v___x_2306_, 3, v___x_2305_);
                lean_ctor_set(v___x_2306_, 4, v_maxRecDepth_2291_);
                lean_ctor_set(v___x_2306_, 5, v_ref_2292_);
                lean_ctor_set(v___x_2306_, 6, v_currNamespace_2293_);
                lean_ctor_set(v___x_2306_, 7, v_openDecls_2294_);
                lean_ctor_set(v___x_2306_, 8, v_initHeartbeats_2295_);
                lean_ctor_set(v___x_2306_, 9, v_maxHeartbeats_2296_);
                lean_ctor_set(v___x_2306_, 10, v_quotContext_2297_);
                lean_ctor_set(v___x_2306_, 11, v_currMacroScope_2298_);
                lean_ctor_set(v___x_2306_, 12, v_cancelTk_x3f_2300_);
                lean_ctor_set(v___x_2306_, 13, v_inheritedTraceOptions_2302_);
                lean_ctor_set_uint8(
                    v___x_2306_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_2299_,
                );
                lean_ctor_set_uint8(
                    v___x_2306_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_2301_,
                );
                if lean_obj_tag(v_p_u2081_2273_) == 0 {
                    v_k_2307_ = lean_ctor_get(v_p_u2081_2273_, 0);
                    lean_inc(v_k_2307_);
                    lean_dec_ref_known(v_p_u2081_2273_, 1);
                    v___x_2308_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v_k_2307_, v_p_u2082_2272_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v___x_2306_, v_a_2285_);
                    lean_dec(v_k_2307_);
                    if lean_obj_tag(v___x_2308_) == 0 {
                        v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
                        lean_inc(v_a_2309_);
                        lean_dec_ref_known(v___x_2308_, 1);
                        v___x_2310_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_acc_2274_, v_a_2309_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v___x_2306_, v_a_2285_);
                        return v___x_2310_;
                    } else {
                        lean_dec_ref_known(v___x_2306_, 14);
                        lean_dec_ref(v_acc_2274_);
                        return v___x_2308_;
                    }
                } else {
                    v_k_2311_ = lean_ctor_get(v_p_u2081_2273_, 0);
                    lean_inc(v_k_2311_);
                    v_v_2312_ = lean_ctor_get(v_p_u2081_2273_, 1);
                    lean_inc(v_v_2312_);
                    v_p_2313_ = lean_ctor_get(v_p_u2081_2273_, 2);
                    lean_inc_ref(v_p_2313_);
                    lean_dec_ref_known(v_p_u2081_2273_, 3);
                    v___x_2314_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go___closed__0;
                    v___x_2315_ = l_Lean_Core_checkSystem(v___x_2314_, v___x_2306_, v_a_2285_);
                    if lean_obj_tag(v___x_2315_) == 0 {
                        lean_dec_ref_known(v___x_2315_, 1);
                        lean_inc_ref(v_p_u2082_2272_);
                        v___x_2316_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_k_2311_, v_v_2312_, v_p_u2082_2272_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v___x_2306_, v_a_2285_);
                        lean_dec(v_k_2311_);
                        if lean_obj_tag(v___x_2316_) == 0 {
                            v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
                            lean_inc(v_a_2317_);
                            lean_dec_ref_known(v___x_2316_, 1);
                            lean_inc_ref(v___x_2306_);
                            v___x_2318_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_acc_2274_, v_a_2317_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v___x_2306_, v_a_2285_);
                            if lean_obj_tag(v___x_2318_) == 0 {
                                v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
                                lean_inc(v_a_2319_);
                                lean_dec_ref_known(v___x_2318_, 1);
                                v_p_u2081_2273_ = v_p_2313_;
                                v_acc_2274_ = v_a_2319_;
                                v_a_2284_ = v___x_2306_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec_ref(v_p_2313_);
                                lean_dec_ref_known(v___x_2306_, 14);
                                lean_dec_ref(v_p_u2082_2272_);
                                return v___x_2318_;
                            }
                        } else {
                            lean_dec_ref(v_p_2313_);
                            lean_dec_ref_known(v___x_2306_, 14);
                            lean_dec_ref(v_acc_2274_);
                            lean_dec_ref(v_p_u2082_2272_);
                            return v___x_2316_;
                        }
                    } else {
                        lean_dec_ref(v_p_2313_);
                        lean_dec(v_v_2312_);
                        lean_dec(v_k_2311_);
                        lean_dec_ref_known(v___x_2306_, 14);
                        lean_dec_ref(v_acc_2274_);
                        lean_dec_ref(v_p_u2082_2272_);
                        v_a_2321_ = lean_ctor_get(v___x_2315_, 0);
                        v_isSharedCheck_2328_ = (!lean_is_exclusive(v___x_2315_)) as u8;
                        if v_isSharedCheck_2328_ == 0 {
                            v___x_2323_ = v___x_2315_;
                            v_isShared_2324_ = v_isSharedCheck_2328_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2321_);
                            lean_dec(v___x_2315_);
                            v___x_2323_ = lean_box(0);
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
                    v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
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
    mut v_p_u2082_2333_: *mut LeanObject,
    mut v_p_u2081_2334_: *mut LeanObject,
    mut v_acc_2335_: *mut LeanObject,
    mut v_a_2336_: *mut LeanObject,
    mut v_a_2337_: *mut LeanObject,
    mut v_a_2338_: *mut LeanObject,
    mut v_a_2339_: *mut LeanObject,
    mut v_a_2340_: *mut LeanObject,
    mut v_a_2341_: *mut LeanObject,
    mut v_a_2342_: *mut LeanObject,
    mut v_a_2343_: *mut LeanObject,
    mut v_a_2344_: *mut LeanObject,
    mut v_a_2345_: *mut LeanObject,
    mut v_a_2346_: *mut LeanObject,
    mut v_a_2347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2348_: *mut LeanObject = core::ptr::null_mut();
    v_res_2348_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go(v_p_u2082_2333_, v_p_u2081_2334_, v_acc_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_);
    lean_dec(v_a_2346_);
    lean_dec(v_a_2344_);
    lean_dec_ref(v_a_2343_);
    lean_dec(v_a_2342_);
    lean_dec_ref(v_a_2341_);
    lean_dec(v_a_2340_);
    lean_dec_ref(v_a_2339_);
    lean_dec(v_a_2338_);
    lean_dec(v_a_2337_);
    lean_dec_ref(v_a_2336_);
    return v_res_2348_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0()
-> *mut LeanObject {
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    v___x_2349_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
    v___x_2350_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2350_, 0, v___x_2349_);
    return v___x_2350_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(
    mut v_p_u2081_2351_: *mut LeanObject,
    mut v_p_u2082_2352_: *mut LeanObject,
    mut v_a_2353_: *mut LeanObject,
    mut v_a_2354_: *mut LeanObject,
    mut v_a_2355_: *mut LeanObject,
    mut v_a_2356_: *mut LeanObject,
    mut v_a_2357_: *mut LeanObject,
    mut v_a_2358_: *mut LeanObject,
    mut v_a_2359_: *mut LeanObject,
    mut v_a_2360_: *mut LeanObject,
    mut v_a_2361_: *mut LeanObject,
    mut v_a_2362_: *mut LeanObject,
    mut v_a_2363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    v___x_2365_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0);
    lean_inc_ref(v_a_2362_);
    v___x_2366_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul_go(v_p_u2082_2352_, v_p_u2081_2351_, v___x_2365_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_);
    return v___x_2366_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___boxed(
    mut v_p_u2081_2367_: *mut LeanObject,
    mut v_p_u2082_2368_: *mut LeanObject,
    mut v_a_2369_: *mut LeanObject,
    mut v_a_2370_: *mut LeanObject,
    mut v_a_2371_: *mut LeanObject,
    mut v_a_2372_: *mut LeanObject,
    mut v_a_2373_: *mut LeanObject,
    mut v_a_2374_: *mut LeanObject,
    mut v_a_2375_: *mut LeanObject,
    mut v_a_2376_: *mut LeanObject,
    mut v_a_2377_: *mut LeanObject,
    mut v_a_2378_: *mut LeanObject,
    mut v_a_2379_: *mut LeanObject,
    mut v_a_2380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2381_: *mut LeanObject = core::ptr::null_mut();
    v_res_2381_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_p_u2081_2367_, v_p_u2082_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_);
    lean_dec(v_a_2379_);
    lean_dec_ref(v_a_2378_);
    lean_dec(v_a_2377_);
    lean_dec_ref(v_a_2376_);
    lean_dec(v_a_2375_);
    lean_dec_ref(v_a_2374_);
    lean_dec(v_a_2373_);
    lean_dec_ref(v_a_2372_);
    lean_dec(v_a_2371_);
    lean_dec(v_a_2370_);
    lean_dec_ref(v_a_2369_);
    return v_res_2381_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0()
-> *mut LeanObject {
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    v___x_2382_ = lean_unsigned_to_nat(1);
    v___x_2383_ = lean_nat_to_int(v___x_2382_);
    return v___x_2383_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1()
-> *mut LeanObject {
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    v___x_2384_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0);
    v___x_2385_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2385_, 0, v___x_2384_);
    return v___x_2385_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(
    mut v_p_2386_: *mut LeanObject,
    mut v_k_2387_: *mut LeanObject,
    mut v_a_2388_: *mut LeanObject,
    mut v_a_2389_: *mut LeanObject,
    mut v_a_2390_: *mut LeanObject,
    mut v_a_2391_: *mut LeanObject,
    mut v_a_2392_: *mut LeanObject,
    mut v_a_2393_: *mut LeanObject,
    mut v_a_2394_: *mut LeanObject,
    mut v_a_2395_: *mut LeanObject,
    mut v_a_2396_: *mut LeanObject,
    mut v_a_2397_: *mut LeanObject,
    mut v_a_2398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2412_: u8 = 0;
    let mut v_cancelTk_x3f_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2414_: u8 = 0;
    let mut v_inheritedTraceOptions_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_2418_: u8 = 0;
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_2423_: u8 = 0;
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_2428_: u8 = 0;
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: u8 = 0;
    let mut v___x_2438_: u8 = 0;
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_2400_ = lean_ctor_get(v_a_2397_, 0);
                v_fileMap_2401_ = lean_ctor_get(v_a_2397_, 1);
                v_options_2402_ = lean_ctor_get(v_a_2397_, 2);
                v_currRecDepth_2403_ = lean_ctor_get(v_a_2397_, 3);
                v_maxRecDepth_2404_ = lean_ctor_get(v_a_2397_, 4);
                v_ref_2405_ = lean_ctor_get(v_a_2397_, 5);
                v_currNamespace_2406_ = lean_ctor_get(v_a_2397_, 6);
                v_openDecls_2407_ = lean_ctor_get(v_a_2397_, 7);
                v_initHeartbeats_2408_ = lean_ctor_get(v_a_2397_, 8);
                v_maxHeartbeats_2409_ = lean_ctor_get(v_a_2397_, 9);
                v_quotContext_2410_ = lean_ctor_get(v_a_2397_, 10);
                v_currMacroScope_2411_ = lean_ctor_get(v_a_2397_, 11);
                v_diag_2412_ = lean_ctor_get_uint8(
                    v_a_2397_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_2413_ = lean_ctor_get(v_a_2397_, 12);
                v_suppressElabErrors_2414_ = lean_ctor_get_uint8(
                    v_a_2397_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_2415_ = lean_ctor_get(v_a_2397_, 13);
                v___x_2436_ = lean_unsigned_to_nat(0);
                v___x_2437_ = lean_nat_dec_eq(v_maxRecDepth_2404_, v___x_2436_);
                if v___x_2437_ == 0 {
                    v___x_2438_ = lean_nat_dec_eq(v_currRecDepth_2403_, v_maxRecDepth_2404_);
                    if v___x_2438_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_p_2386_);
                        lean_inc(v_ref_2405_);
                        v___x_2439_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine_spec__0___redArg(v_ref_2405_);
                        return v___x_2439_;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_zero_2417_ = lean_unsigned_to_nat(0);
                v_isZero_2418_ = lean_nat_dec_eq(v_k_2387_, v_zero_2417_);
                if v_isZero_2418_ == 1 {
                    lean_dec_ref(v_p_2386_);
                    v___x_2419_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1);
                    v___x_2420_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2420_, 0, v___x_2419_);
                    return v___x_2420_;
                } else {
                    v_one_2421_ = lean_unsigned_to_nat(1);
                    v_n_2422_ = lean_nat_sub(v_k_2387_, v_one_2421_);
                    v_isZero_2423_ = lean_nat_dec_eq(v_n_2422_, v_zero_2417_);
                    if v_isZero_2423_ == 1 {
                        lean_dec(v_n_2422_);
                        v___x_2424_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2424_, 0, v_p_2386_);
                        return v___x_2424_;
                    } else {
                        v_n_2425_ = lean_nat_sub(v_n_2422_, v_one_2421_);
                        lean_dec(v_n_2422_);
                        v___x_2426_ = lean_nat_add(v_currRecDepth_2403_, v_one_2421_);
                        lean_inc_ref(v_inheritedTraceOptions_2415_);
                        lean_inc(v_cancelTk_x3f_2413_);
                        lean_inc(v_currMacroScope_2411_);
                        lean_inc(v_quotContext_2410_);
                        lean_inc(v_maxHeartbeats_2409_);
                        lean_inc(v_initHeartbeats_2408_);
                        lean_inc(v_openDecls_2407_);
                        lean_inc(v_currNamespace_2406_);
                        lean_inc(v_ref_2405_);
                        lean_inc(v_maxRecDepth_2404_);
                        lean_inc_ref(v_options_2402_);
                        lean_inc_ref(v_fileMap_2401_);
                        lean_inc_ref(v_fileName_2400_);
                        v___x_2427_ = lean_alloc_ctor(0, 14, (2) as u32);
                        lean_ctor_set(v___x_2427_, 0, v_fileName_2400_);
                        lean_ctor_set(v___x_2427_, 1, v_fileMap_2401_);
                        lean_ctor_set(v___x_2427_, 2, v_options_2402_);
                        lean_ctor_set(v___x_2427_, 3, v___x_2426_);
                        lean_ctor_set(v___x_2427_, 4, v_maxRecDepth_2404_);
                        lean_ctor_set(v___x_2427_, 5, v_ref_2405_);
                        lean_ctor_set(v___x_2427_, 6, v_currNamespace_2406_);
                        lean_ctor_set(v___x_2427_, 7, v_openDecls_2407_);
                        lean_ctor_set(v___x_2427_, 8, v_initHeartbeats_2408_);
                        lean_ctor_set(v___x_2427_, 9, v_maxHeartbeats_2409_);
                        lean_ctor_set(v___x_2427_, 10, v_quotContext_2410_);
                        lean_ctor_set(v___x_2427_, 11, v_currMacroScope_2411_);
                        lean_ctor_set(v___x_2427_, 12, v_cancelTk_x3f_2413_);
                        lean_ctor_set(v___x_2427_, 13, v_inheritedTraceOptions_2415_);
                        lean_ctor_set_uint8(
                            v___x_2427_,
                            (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                            v_diag_2412_,
                        );
                        lean_ctor_set_uint8(
                            v___x_2427_,
                            (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                            v_suppressElabErrors_2414_,
                        );
                        v_isZero_2428_ = lean_nat_dec_eq(v_n_2425_, v_zero_2417_);
                        if v_isZero_2428_ == 1 {
                            lean_dec(v_n_2425_);
                            lean_inc_ref(v_p_2386_);
                            v___x_2429_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_p_2386_, v_p_2386_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v___x_2427_, v_a_2398_);
                            lean_dec_ref_known(v___x_2427_, 14);
                            return v___x_2429_;
                        } else {
                            v_n_2430_ = lean_nat_sub(v_n_2425_, v_one_2421_);
                            lean_dec(v_n_2425_);
                            v___x_2431_ = lean_unsigned_to_nat(2);
                            v___x_2432_ = lean_nat_add(v_n_2430_, v___x_2431_);
                            lean_dec(v_n_2430_);
                            lean_inc_ref(v_p_2386_);
                            v___x_2433_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(v_p_2386_, v___x_2432_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v___x_2427_, v_a_2398_);
                            lean_dec(v___x_2432_);
                            if lean_obj_tag(v___x_2433_) == 0 {
                                v_a_2434_ = lean_ctor_get(v___x_2433_, 0);
                                lean_inc(v_a_2434_);
                                lean_dec_ref_known(v___x_2433_, 1);
                                v___x_2435_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_p_2386_, v_a_2434_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v___x_2427_, v_a_2398_);
                                lean_dec_ref_known(v___x_2427_, 14);
                                return v___x_2435_;
                            } else {
                                lean_dec_ref_known(v___x_2427_, 14);
                                lean_dec_ref(v_p_2386_);
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
    mut v_p_2440_: *mut LeanObject,
    mut v_k_2441_: *mut LeanObject,
    mut v_a_2442_: *mut LeanObject,
    mut v_a_2443_: *mut LeanObject,
    mut v_a_2444_: *mut LeanObject,
    mut v_a_2445_: *mut LeanObject,
    mut v_a_2446_: *mut LeanObject,
    mut v_a_2447_: *mut LeanObject,
    mut v_a_2448_: *mut LeanObject,
    mut v_a_2449_: *mut LeanObject,
    mut v_a_2450_: *mut LeanObject,
    mut v_a_2451_: *mut LeanObject,
    mut v_a_2452_: *mut LeanObject,
    mut v_a_2453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2454_: *mut LeanObject = core::ptr::null_mut();
    v_res_2454_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(v_p_2440_, v_k_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_);
    lean_dec(v_a_2452_);
    lean_dec_ref(v_a_2451_);
    lean_dec(v_a_2450_);
    lean_dec_ref(v_a_2449_);
    lean_dec(v_a_2448_);
    lean_dec_ref(v_a_2447_);
    lean_dec(v_a_2446_);
    lean_dec_ref(v_a_2445_);
    lean_dec(v_a_2444_);
    lean_dec(v_a_2443_);
    lean_dec_ref(v_a_2442_);
    lean_dec(v_k_2441_);
    return v_res_2454_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0()
-> *mut LeanObject {
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    v___x_2455_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__0);
    v___x_2456_ = lean_int_neg(v___x_2455_);
    return v___x_2456_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1()
-> *mut LeanObject {
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    v___x_2457_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow___closed__1);
    v___x_2458_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2458_, 0, v___x_2457_);
    return v___x_2458_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(
    mut v_e_2459_: *mut LeanObject,
    mut v_a_2460_: *mut LeanObject,
    mut v_a_2461_: *mut LeanObject,
    mut v_a_2462_: *mut LeanObject,
    mut v_a_2463_: *mut LeanObject,
    mut v_a_2464_: *mut LeanObject,
    mut v_a_2465_: *mut LeanObject,
    mut v_a_2466_: *mut LeanObject,
    mut v_a_2467_: *mut LeanObject,
    mut v_a_2468_: *mut LeanObject,
    mut v_a_2469_: *mut LeanObject,
    mut v_a_2470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_n_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2489_: u8 = 0;
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2495_: u8 = 0;
    let mut v_a_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2499_: u8 = 0;
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2503_: u8 = 0;
    let mut v_k_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2507_: u8 = 0;
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2513_: u8 = 0;
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2521_: u8 = 0;
    let mut v_a_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2525_: u8 = 0;
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2529_: u8 = 0;
    let mut v_isSharedCheck_2530_: u8 = 0;
    let mut v_i_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2534_: u8 = 0;
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2540_: u8 = 0;
    let mut v_a_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2547_: u8 = 0;
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2553_: u8 = 0;
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2560_: u8 = 0;
    let mut v_a_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2564_: u8 = 0;
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2568_: u8 = 0;
    let mut v_isSharedCheck_2569_: u8 = 0;
    let mut v_a_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2580_: u8 = 0;
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2585_: u8 = 0;
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2592_: u8 = 0;
    let mut v_a_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2596_: u8 = 0;
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2600_: u8 = 0;
    let mut v_isSharedCheck_2601_: u8 = 0;
    let mut v_a_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2612_: u8 = 0;
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2620_: u8 = 0;
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2627_: u8 = 0;
    let mut v_a_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2631_: u8 = 0;
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2635_: u8 = 0;
    let mut v_a_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2639_: u8 = 0;
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2643_: u8 = 0;
    let mut v_isSharedCheck_2644_: u8 = 0;
    let mut v_a_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2655_: u8 = 0;
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2660_: u8 = 0;
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2667_: u8 = 0;
    let mut v_a_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2671_: u8 = 0;
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2675_: u8 = 0;
    let mut v_isSharedCheck_2676_: u8 = 0;
    let mut v_a_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2681_: u8 = 0;
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: u8 = 0;
    let mut v_k_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2687_: u8 = 0;
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2692_: u8 = 0;
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2699_: u8 = 0;
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2707_: u8 = 0;
    let mut v_a_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2711_: u8 = 0;
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2715_: u8 = 0;
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2720_: u8 = 0;
    let mut v_a_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2724_: u8 = 0;
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2728_: u8 = 0;
    let mut v_isSharedCheck_2729_: u8 = 0;
    let mut v_i_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2733_: u8 = 0;
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2744_: u8 = 0;
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2750_: u8 = 0;
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2755_: u8 = 0;
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2762_: u8 = 0;
    let mut v_a_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2766_: u8 = 0;
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2770_: u8 = 0;
    let mut v_isSharedCheck_2771_: u8 = 0;
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2774_: u8 = 0;
    let mut v_k_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_2459_) {
                1 => {
                    v_k_2504_ = lean_ctor_get(v_e_2459_, 0);
                    v_isSharedCheck_2530_ = (!lean_is_exclusive(v_e_2459_)) as u8;
                    if v_isSharedCheck_2530_ == 0 {
                        v___x_2506_ = v_e_2459_;
                        v_isShared_2507_ = v_isSharedCheck_2530_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_k_2504_);
                        lean_dec(v_e_2459_);
                        v___x_2506_ = lean_box(0);
                        v_isShared_2507_ = v_isSharedCheck_2530_;
                        state = 6;
                        continue;
                    }
                }
                3 => {
                    v_i_2531_ = lean_ctor_get(v_e_2459_, 0);
                    v_isSharedCheck_2540_ = (!lean_is_exclusive(v_e_2459_)) as u8;
                    if v_isSharedCheck_2540_ == 0 {
                        v___x_2533_ = v_e_2459_;
                        v_isShared_2534_ = v_isSharedCheck_2540_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_i_2531_);
                        lean_dec(v_e_2459_);
                        v___x_2533_ = lean_box(0);
                        v_isShared_2534_ = v_isSharedCheck_2540_;
                        state = 12;
                        continue;
                    }
                }
                4 => {
                    v_a_2541_ = lean_ctor_get(v_e_2459_, 0);
                    lean_inc_ref(v_a_2541_);
                    lean_dec_ref_known(v_e_2459_, 1);
                    v___x_2542_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_2541_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                    if lean_obj_tag(v___x_2542_) == 0 {
                        v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
                        lean_inc(v_a_2543_);
                        if lean_obj_tag(v_a_2543_) == 0 {
                            return v___x_2542_;
                        } else {
                            lean_dec_ref_known(v___x_2542_, 1);
                            v_val_2544_ = lean_ctor_get(v_a_2543_, 0);
                            v_isSharedCheck_2569_ = (!lean_is_exclusive(v_a_2543_)) as u8;
                            if v_isSharedCheck_2569_ == 0 {
                                v___x_2546_ = v_a_2543_;
                                v_isShared_2547_ = v_isSharedCheck_2569_;
                                state = 14;
                                continue;
                            } else {
                                lean_inc(v_val_2544_);
                                lean_dec(v_a_2543_);
                                v___x_2546_ = lean_box(0);
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
                    v_a_2570_ = lean_ctor_get(v_e_2459_, 0);
                    lean_inc_ref(v_a_2570_);
                    v_b_2571_ = lean_ctor_get(v_e_2459_, 1);
                    lean_inc_ref(v_b_2571_);
                    lean_dec_ref_known(v_e_2459_, 2);
                    v___x_2572_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_2570_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                    if lean_obj_tag(v___x_2572_) == 0 {
                        v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
                        lean_inc(v_a_2573_);
                        if lean_obj_tag(v_a_2573_) == 0 {
                            lean_dec_ref(v_b_2571_);
                            return v___x_2572_;
                        } else {
                            lean_dec_ref_known(v___x_2572_, 1);
                            v_val_2574_ = lean_ctor_get(v_a_2573_, 0);
                            lean_inc(v_val_2574_);
                            lean_dec_ref_known(v_a_2573_, 1);
                            v___x_2575_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_b_2571_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                            if lean_obj_tag(v___x_2575_) == 0 {
                                v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
                                lean_inc(v_a_2576_);
                                if lean_obj_tag(v_a_2576_) == 0 {
                                    lean_dec(v_val_2574_);
                                    return v___x_2575_;
                                } else {
                                    lean_dec_ref_known(v___x_2575_, 1);
                                    v_val_2577_ = lean_ctor_get(v_a_2576_, 0);
                                    v_isSharedCheck_2601_ = (!lean_is_exclusive(v_a_2576_)) as u8;
                                    if v_isSharedCheck_2601_ == 0 {
                                        v___x_2579_ = v_a_2576_;
                                        v_isShared_2580_ = v_isSharedCheck_2601_;
                                        state = 20;
                                        continue;
                                    } else {
                                        lean_inc(v_val_2577_);
                                        lean_dec(v_a_2576_);
                                        v___x_2579_ = lean_box(0);
                                        v_isShared_2580_ = v_isSharedCheck_2601_;
                                        state = 20;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_val_2574_);
                                return v___x_2575_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_b_2571_);
                        return v___x_2572_;
                    }
                }
                6 => {
                    v_a_2602_ = lean_ctor_get(v_e_2459_, 0);
                    lean_inc_ref(v_a_2602_);
                    v_b_2603_ = lean_ctor_get(v_e_2459_, 1);
                    lean_inc_ref(v_b_2603_);
                    lean_dec_ref_known(v_e_2459_, 2);
                    v___x_2604_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_2602_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                    if lean_obj_tag(v___x_2604_) == 0 {
                        v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
                        lean_inc(v_a_2605_);
                        if lean_obj_tag(v_a_2605_) == 0 {
                            lean_dec_ref(v_b_2603_);
                            return v___x_2604_;
                        } else {
                            lean_dec_ref_known(v___x_2604_, 1);
                            v_val_2606_ = lean_ctor_get(v_a_2605_, 0);
                            lean_inc(v_val_2606_);
                            lean_dec_ref_known(v_a_2605_, 1);
                            v___x_2607_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_b_2603_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                            if lean_obj_tag(v___x_2607_) == 0 {
                                v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
                                lean_inc(v_a_2608_);
                                if lean_obj_tag(v_a_2608_) == 0 {
                                    lean_dec(v_val_2606_);
                                    return v___x_2607_;
                                } else {
                                    lean_dec_ref_known(v___x_2607_, 1);
                                    v_val_2609_ = lean_ctor_get(v_a_2608_, 0);
                                    v_isSharedCheck_2644_ = (!lean_is_exclusive(v_a_2608_)) as u8;
                                    if v_isSharedCheck_2644_ == 0 {
                                        v___x_2611_ = v_a_2608_;
                                        v_isShared_2612_ = v_isSharedCheck_2644_;
                                        state = 26;
                                        continue;
                                    } else {
                                        lean_inc(v_val_2609_);
                                        lean_dec(v_a_2608_);
                                        v___x_2611_ = lean_box(0);
                                        v_isShared_2612_ = v_isSharedCheck_2644_;
                                        state = 26;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_val_2606_);
                                return v___x_2607_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_b_2603_);
                        return v___x_2604_;
                    }
                }
                7 => {
                    v_a_2645_ = lean_ctor_get(v_e_2459_, 0);
                    lean_inc_ref(v_a_2645_);
                    v_b_2646_ = lean_ctor_get(v_e_2459_, 1);
                    lean_inc_ref(v_b_2646_);
                    lean_dec_ref_known(v_e_2459_, 2);
                    v___x_2647_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_2645_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                    if lean_obj_tag(v___x_2647_) == 0 {
                        v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
                        lean_inc(v_a_2648_);
                        if lean_obj_tag(v_a_2648_) == 0 {
                            lean_dec_ref(v_b_2646_);
                            return v___x_2647_;
                        } else {
                            lean_dec_ref_known(v___x_2647_, 1);
                            v_val_2649_ = lean_ctor_get(v_a_2648_, 0);
                            lean_inc(v_val_2649_);
                            lean_dec_ref_known(v_a_2648_, 1);
                            v___x_2650_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_b_2646_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                            if lean_obj_tag(v___x_2650_) == 0 {
                                v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
                                lean_inc(v_a_2651_);
                                if lean_obj_tag(v_a_2651_) == 0 {
                                    lean_dec(v_val_2649_);
                                    return v___x_2650_;
                                } else {
                                    lean_dec_ref_known(v___x_2650_, 1);
                                    v_val_2652_ = lean_ctor_get(v_a_2651_, 0);
                                    v_isSharedCheck_2676_ = (!lean_is_exclusive(v_a_2651_)) as u8;
                                    if v_isSharedCheck_2676_ == 0 {
                                        v___x_2654_ = v_a_2651_;
                                        v_isShared_2655_ = v_isSharedCheck_2676_;
                                        state = 34;
                                        continue;
                                    } else {
                                        lean_inc(v_val_2652_);
                                        lean_dec(v_a_2651_);
                                        v___x_2654_ = lean_box(0);
                                        v_isShared_2655_ = v_isSharedCheck_2676_;
                                        state = 34;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_val_2649_);
                                return v___x_2650_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_b_2646_);
                        return v___x_2647_;
                    }
                }
                8 => {
                    v_a_2677_ = lean_ctor_get(v_e_2459_, 0);
                    v_k_2678_ = lean_ctor_get(v_e_2459_, 1);
                    v_isSharedCheck_2774_ = (!lean_is_exclusive(v_e_2459_)) as u8;
                    if v_isSharedCheck_2774_ == 0 {
                        v___x_2680_ = v_e_2459_;
                        v_isShared_2681_ = v_isSharedCheck_2774_;
                        state = 40;
                        continue;
                    } else {
                        lean_inc(v_k_2678_);
                        lean_inc(v_a_2677_);
                        lean_dec(v_e_2459_);
                        v___x_2680_ = lean_box(0);
                        v_isShared_2681_ = v_isSharedCheck_2774_;
                        state = 40;
                        continue;
                    }
                }
                _ => {
                    v_k_2775_ = lean_ctor_get(v_e_2459_, 0);
                    lean_inc(v_k_2775_);
                    lean_dec_ref(v_e_2459_);
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
                if lean_obj_tag(v___x_2485_) == 0 {
                    v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
                    v_isSharedCheck_2495_ = (!lean_is_exclusive(v___x_2485_)) as u8;
                    if v_isSharedCheck_2495_ == 0 {
                        v___x_2488_ = v___x_2485_;
                        v_isShared_2489_ = v_isSharedCheck_2495_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2486_);
                        lean_dec(v___x_2485_);
                        v___x_2488_ = lean_box(0);
                        v_isShared_2489_ = v_isSharedCheck_2495_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2496_ = lean_ctor_get(v___x_2485_, 0);
                    v_isSharedCheck_2503_ = (!lean_is_exclusive(v___x_2485_)) as u8;
                    if v_isSharedCheck_2503_ == 0 {
                        v___x_2498_ = v___x_2485_;
                        v_isShared_2499_ = v_isSharedCheck_2503_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2496_);
                        lean_dec(v___x_2485_);
                        v___x_2498_ = lean_box(0);
                        v_isShared_2499_ = v_isSharedCheck_2503_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2490_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2490_, 0, v_a_2486_);
                v___x_2491_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2491_, 0, v___x_2490_);
                if v_isShared_2489_ == 0 {
                    lean_ctor_set(v___x_2488_, 0, v___x_2491_);
                    v___x_2493_ = v___x_2488_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2494_, 0, v___x_2491_);
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
                    v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
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
                if lean_obj_tag(v___x_2509_) == 0 {
                    v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
                    v_isSharedCheck_2521_ = (!lean_is_exclusive(v___x_2509_)) as u8;
                    if v_isSharedCheck_2521_ == 0 {
                        v___x_2512_ = v___x_2509_;
                        v_isShared_2513_ = v_isSharedCheck_2521_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2510_);
                        lean_dec(v___x_2509_);
                        v___x_2512_ = lean_box(0);
                        v_isShared_2513_ = v_isSharedCheck_2521_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2506_);
                    v_a_2522_ = lean_ctor_get(v___x_2509_, 0);
                    v_isSharedCheck_2529_ = (!lean_is_exclusive(v___x_2509_)) as u8;
                    if v_isSharedCheck_2529_ == 0 {
                        v___x_2524_ = v___x_2509_;
                        v_isShared_2525_ = v_isSharedCheck_2529_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_2522_);
                        lean_dec(v___x_2509_);
                        v___x_2524_ = lean_box(0);
                        v_isShared_2525_ = v_isSharedCheck_2529_;
                        state = 10;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_2507_ == 0 {
                    lean_ctor_set_tag(v___x_2506_, 0);
                    lean_ctor_set(v___x_2506_, 0, v_a_2510_);
                    v___x_2515_ = v___x_2506_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2510_);
                    v___x_2515_ = v_reuseFailAlloc_2520_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2516_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2516_, 0, v___x_2515_);
                if v_isShared_2513_ == 0 {
                    lean_ctor_set(v___x_2512_, 0, v___x_2516_);
                    v___x_2518_ = v___x_2512_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2516_);
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
                    v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2522_);
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
                    lean_ctor_set_tag(v___x_2533_, 1);
                    lean_ctor_set(v___x_2533_, 0, v___x_2535_);
                    v___x_2537_ = v___x_2533_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2535_);
                    v___x_2537_ = v_reuseFailAlloc_2539_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_2538_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2538_, 0, v___x_2537_);
                return v___x_2538_;
            }
            14 => {
                v___x_2548_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0);
                v___x_2549_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v___x_2548_, v_val_2544_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                if lean_obj_tag(v___x_2549_) == 0 {
                    v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
                    v_isSharedCheck_2560_ = (!lean_is_exclusive(v___x_2549_)) as u8;
                    if v_isSharedCheck_2560_ == 0 {
                        v___x_2552_ = v___x_2549_;
                        v_isShared_2553_ = v_isSharedCheck_2560_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_2550_);
                        lean_dec(v___x_2549_);
                        v___x_2552_ = lean_box(0);
                        v_isShared_2553_ = v_isSharedCheck_2560_;
                        state = 15;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2546_);
                    v_a_2561_ = lean_ctor_get(v___x_2549_, 0);
                    v_isSharedCheck_2568_ = (!lean_is_exclusive(v___x_2549_)) as u8;
                    if v_isSharedCheck_2568_ == 0 {
                        v___x_2563_ = v___x_2549_;
                        v_isShared_2564_ = v_isSharedCheck_2568_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_a_2561_);
                        lean_dec(v___x_2549_);
                        v___x_2563_ = lean_box(0);
                        v_isShared_2564_ = v_isSharedCheck_2568_;
                        state = 18;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_2547_ == 0 {
                    lean_ctor_set(v___x_2546_, 0, v_a_2550_);
                    v___x_2555_ = v___x_2546_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2550_);
                    v___x_2555_ = v_reuseFailAlloc_2559_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_2553_ == 0 {
                    lean_ctor_set(v___x_2552_, 0, v___x_2555_);
                    v___x_2557_ = v___x_2552_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2555_);
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
                    v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
                    v___x_2566_ = v_reuseFailAlloc_2567_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2566_;
            }
            20 => {
                lean_inc_ref(v_a_2469_);
                v___x_2581_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_val_2574_, v_val_2577_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                if lean_obj_tag(v___x_2581_) == 0 {
                    v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
                    v_isSharedCheck_2592_ = (!lean_is_exclusive(v___x_2581_)) as u8;
                    if v_isSharedCheck_2592_ == 0 {
                        v___x_2584_ = v___x_2581_;
                        v_isShared_2585_ = v_isSharedCheck_2592_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_a_2582_);
                        lean_dec(v___x_2581_);
                        v___x_2584_ = lean_box(0);
                        v_isShared_2585_ = v_isSharedCheck_2592_;
                        state = 21;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2579_);
                    v_a_2593_ = lean_ctor_get(v___x_2581_, 0);
                    v_isSharedCheck_2600_ = (!lean_is_exclusive(v___x_2581_)) as u8;
                    if v_isSharedCheck_2600_ == 0 {
                        v___x_2595_ = v___x_2581_;
                        v_isShared_2596_ = v_isSharedCheck_2600_;
                        state = 24;
                        continue;
                    } else {
                        lean_inc(v_a_2593_);
                        lean_dec(v___x_2581_);
                        v___x_2595_ = lean_box(0);
                        v_isShared_2596_ = v_isSharedCheck_2600_;
                        state = 24;
                        continue;
                    }
                }
            }
            21 => {
                if v_isShared_2580_ == 0 {
                    lean_ctor_set(v___x_2579_, 0, v_a_2582_);
                    v___x_2587_ = v___x_2579_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2582_);
                    v___x_2587_ = v_reuseFailAlloc_2591_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_2585_ == 0 {
                    lean_ctor_set(v___x_2584_, 0, v___x_2587_);
                    v___x_2589_ = v___x_2584_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2587_);
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
                    v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
                    v___x_2598_ = v_reuseFailAlloc_2599_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_2598_;
            }
            26 => {
                v___x_2613_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__0);
                v___x_2614_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v___x_2613_, v_val_2609_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                if lean_obj_tag(v___x_2614_) == 0 {
                    v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
                    lean_inc(v_a_2615_);
                    lean_dec_ref_known(v___x_2614_, 1);
                    lean_inc_ref(v_a_2469_);
                    v___x_2616_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_val_2606_, v_a_2615_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                    if lean_obj_tag(v___x_2616_) == 0 {
                        v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
                        v_isSharedCheck_2627_ = (!lean_is_exclusive(v___x_2616_)) as u8;
                        if v_isSharedCheck_2627_ == 0 {
                            v___x_2619_ = v___x_2616_;
                            v_isShared_2620_ = v_isSharedCheck_2627_;
                            state = 27;
                            continue;
                        } else {
                            lean_inc(v_a_2617_);
                            lean_dec(v___x_2616_);
                            v___x_2619_ = lean_box(0);
                            v_isShared_2620_ = v_isSharedCheck_2627_;
                            state = 27;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_2611_);
                        v_a_2628_ = lean_ctor_get(v___x_2616_, 0);
                        v_isSharedCheck_2635_ = (!lean_is_exclusive(v___x_2616_)) as u8;
                        if v_isSharedCheck_2635_ == 0 {
                            v___x_2630_ = v___x_2616_;
                            v_isShared_2631_ = v_isSharedCheck_2635_;
                            state = 30;
                            continue;
                        } else {
                            lean_inc(v_a_2628_);
                            lean_dec(v___x_2616_);
                            v___x_2630_ = lean_box(0);
                            v_isShared_2631_ = v_isSharedCheck_2635_;
                            state = 30;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2611_);
                    lean_dec(v_val_2606_);
                    v_a_2636_ = lean_ctor_get(v___x_2614_, 0);
                    v_isSharedCheck_2643_ = (!lean_is_exclusive(v___x_2614_)) as u8;
                    if v_isSharedCheck_2643_ == 0 {
                        v___x_2638_ = v___x_2614_;
                        v_isShared_2639_ = v_isSharedCheck_2643_;
                        state = 32;
                        continue;
                    } else {
                        lean_inc(v_a_2636_);
                        lean_dec(v___x_2614_);
                        v___x_2638_ = lean_box(0);
                        v_isShared_2639_ = v_isSharedCheck_2643_;
                        state = 32;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_2612_ == 0 {
                    lean_ctor_set(v___x_2611_, 0, v_a_2617_);
                    v___x_2622_ = v___x_2611_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2617_);
                    v___x_2622_ = v_reuseFailAlloc_2626_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_2620_ == 0 {
                    lean_ctor_set(v___x_2619_, 0, v___x_2622_);
                    v___x_2624_ = v___x_2619_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2622_);
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
                    v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_a_2628_);
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
                    v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_a_2636_);
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
                if lean_obj_tag(v___x_2656_) == 0 {
                    v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
                    v_isSharedCheck_2667_ = (!lean_is_exclusive(v___x_2656_)) as u8;
                    if v_isSharedCheck_2667_ == 0 {
                        v___x_2659_ = v___x_2656_;
                        v_isShared_2660_ = v_isSharedCheck_2667_;
                        state = 35;
                        continue;
                    } else {
                        lean_inc(v_a_2657_);
                        lean_dec(v___x_2656_);
                        v___x_2659_ = lean_box(0);
                        v_isShared_2660_ = v_isSharedCheck_2667_;
                        state = 35;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2654_);
                    v_a_2668_ = lean_ctor_get(v___x_2656_, 0);
                    v_isSharedCheck_2675_ = (!lean_is_exclusive(v___x_2656_)) as u8;
                    if v_isSharedCheck_2675_ == 0 {
                        v___x_2670_ = v___x_2656_;
                        v_isShared_2671_ = v_isSharedCheck_2675_;
                        state = 38;
                        continue;
                    } else {
                        lean_inc(v_a_2668_);
                        lean_dec(v___x_2656_);
                        v___x_2670_ = lean_box(0);
                        v_isShared_2671_ = v_isSharedCheck_2675_;
                        state = 38;
                        continue;
                    }
                }
            }
            35 => {
                if v_isShared_2655_ == 0 {
                    lean_ctor_set(v___x_2654_, 0, v_a_2657_);
                    v___x_2662_ = v___x_2654_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2657_);
                    v___x_2662_ = v_reuseFailAlloc_2666_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                if v_isShared_2660_ == 0 {
                    lean_ctor_set(v___x_2659_, 0, v___x_2662_);
                    v___x_2664_ = v___x_2659_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2665_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2662_);
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
                    v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
                    v___x_2673_ = v_reuseFailAlloc_2674_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_2673_;
            }
            40 => {
                v___x_2682_ = lean_unsigned_to_nat(0);
                v___x_2683_ = lean_nat_dec_eq(v_k_2678_, v___x_2682_);
                if v___x_2683_ == 0 {
                    match lean_obj_tag(v_a_2677_) {
                        0 => {
                            lean_del_object(v___x_2680_);
                            v_k_2684_ = lean_ctor_get(v_a_2677_, 0);
                            v_isSharedCheck_2729_ = (!lean_is_exclusive(v_a_2677_)) as u8;
                            if v_isSharedCheck_2729_ == 0 {
                                v___x_2686_ = v_a_2677_;
                                v_isShared_2687_ = v_isSharedCheck_2729_;
                                state = 41;
                                continue;
                            } else {
                                lean_inc(v_k_2684_);
                                lean_dec(v_a_2677_);
                                v___x_2686_ = lean_box(0);
                                v_isShared_2687_ = v_isSharedCheck_2729_;
                                state = 41;
                                continue;
                            }
                        }
                        3 => {
                            v_i_2730_ = lean_ctor_get(v_a_2677_, 0);
                            v_isSharedCheck_2744_ = (!lean_is_exclusive(v_a_2677_)) as u8;
                            if v_isSharedCheck_2744_ == 0 {
                                v___x_2732_ = v_a_2677_;
                                v_isShared_2733_ = v_isSharedCheck_2744_;
                                state = 52;
                                continue;
                            } else {
                                lean_inc(v_i_2730_);
                                lean_dec(v_a_2677_);
                                v___x_2732_ = lean_box(0);
                                v_isShared_2733_ = v_isSharedCheck_2744_;
                                state = 52;
                                continue;
                            }
                        }
                        _ => {
                            lean_del_object(v___x_2680_);
                            v___x_2745_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_a_2677_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                            if lean_obj_tag(v___x_2745_) == 0 {
                                v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
                                lean_inc(v_a_2746_);
                                if lean_obj_tag(v_a_2746_) == 0 {
                                    lean_dec(v_k_2678_);
                                    return v___x_2745_;
                                } else {
                                    lean_dec_ref_known(v___x_2745_, 1);
                                    v_val_2747_ = lean_ctor_get(v_a_2746_, 0);
                                    v_isSharedCheck_2771_ = (!lean_is_exclusive(v_a_2746_)) as u8;
                                    if v_isSharedCheck_2771_ == 0 {
                                        v___x_2749_ = v_a_2746_;
                                        v_isShared_2750_ = v_isSharedCheck_2771_;
                                        state = 55;
                                        continue;
                                    } else {
                                        lean_inc(v_val_2747_);
                                        lean_dec(v_a_2746_);
                                        v___x_2749_ = lean_box(0);
                                        v_isShared_2750_ = v_isSharedCheck_2771_;
                                        state = 55;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_k_2678_);
                                return v___x_2745_;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_2680_);
                    lean_dec(v_k_2678_);
                    lean_dec_ref(v_a_2677_);
                    v___x_2772_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly___closed__1);
                    v___x_2773_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2773_, 0, v___x_2772_);
                    return v___x_2773_;
                }
            }
            41 => {
                lean_inc(v_k_2678_);
                v___x_2688_ = l_Lean_Meta_Grind_Arith_checkExp___redArg(
                    v_k_2678_, v_a_2463_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_,
                    v_a_2470_,
                );
                if lean_obj_tag(v___x_2688_) == 0 {
                    v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
                    v_isSharedCheck_2720_ = (!lean_is_exclusive(v___x_2688_)) as u8;
                    if v_isSharedCheck_2720_ == 0 {
                        v___x_2691_ = v___x_2688_;
                        v_isShared_2692_ = v_isSharedCheck_2720_;
                        state = 42;
                        continue;
                    } else {
                        lean_inc(v_a_2689_);
                        lean_dec(v___x_2688_);
                        v___x_2691_ = lean_box(0);
                        v_isShared_2692_ = v_isSharedCheck_2720_;
                        state = 42;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2686_);
                    lean_dec(v_k_2684_);
                    lean_dec(v_k_2678_);
                    v_a_2721_ = lean_ctor_get(v___x_2688_, 0);
                    v_isSharedCheck_2728_ = (!lean_is_exclusive(v___x_2688_)) as u8;
                    if v_isSharedCheck_2728_ == 0 {
                        v___x_2723_ = v___x_2688_;
                        v_isShared_2724_ = v_isSharedCheck_2728_;
                        state = 50;
                        continue;
                    } else {
                        lean_inc(v_a_2721_);
                        lean_dec(v___x_2688_);
                        v___x_2723_ = lean_box(0);
                        v_isShared_2724_ = v_isSharedCheck_2728_;
                        state = 50;
                        continue;
                    }
                }
            }
            42 => {
                if lean_obj_tag(v_a_2689_) == 0 {
                    if v___x_2683_ == 0 {
                        lean_del_object(v___x_2686_);
                        lean_dec(v_k_2684_);
                        lean_dec(v_k_2678_);
                        v___x_2716_ = lean_box(0);
                        if v_isShared_2692_ == 0 {
                            lean_ctor_set(v___x_2691_, 0, v___x_2716_);
                            v___x_2718_ = v___x_2691_;
                            state = 49;
                            continue;
                        } else {
                            v_reuseFailAlloc_2719_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2716_);
                            v___x_2718_ = v_reuseFailAlloc_2719_;
                            state = 49;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_2691_);
                        state = 43;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_a_2689_, 1);
                    lean_del_object(v___x_2691_);
                    state = 43;
                    continue;
                }
            }
            43 => {
                v___x_2694_ = l_Int_pow(v_k_2684_, v_k_2678_);
                lean_dec(v_k_2678_);
                lean_dec(v_k_2684_);
                v___x_2695_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar(v___x_2694_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                if lean_obj_tag(v___x_2695_) == 0 {
                    v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
                    v_isSharedCheck_2707_ = (!lean_is_exclusive(v___x_2695_)) as u8;
                    if v_isSharedCheck_2707_ == 0 {
                        v___x_2698_ = v___x_2695_;
                        v_isShared_2699_ = v_isSharedCheck_2707_;
                        state = 44;
                        continue;
                    } else {
                        lean_inc(v_a_2696_);
                        lean_dec(v___x_2695_);
                        v___x_2698_ = lean_box(0);
                        v_isShared_2699_ = v_isSharedCheck_2707_;
                        state = 44;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2686_);
                    v_a_2708_ = lean_ctor_get(v___x_2695_, 0);
                    v_isSharedCheck_2715_ = (!lean_is_exclusive(v___x_2695_)) as u8;
                    if v_isSharedCheck_2715_ == 0 {
                        v___x_2710_ = v___x_2695_;
                        v_isShared_2711_ = v_isSharedCheck_2715_;
                        state = 47;
                        continue;
                    } else {
                        lean_inc(v_a_2708_);
                        lean_dec(v___x_2695_);
                        v___x_2710_ = lean_box(0);
                        v_isShared_2711_ = v_isSharedCheck_2715_;
                        state = 47;
                        continue;
                    }
                }
            }
            44 => {
                if v_isShared_2687_ == 0 {
                    lean_ctor_set(v___x_2686_, 0, v_a_2696_);
                    v___x_2701_ = v___x_2686_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_a_2696_);
                    v___x_2701_ = v_reuseFailAlloc_2706_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                v___x_2702_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2702_, 0, v___x_2701_);
                if v_isShared_2699_ == 0 {
                    lean_ctor_set(v___x_2698_, 0, v___x_2702_);
                    v___x_2704_ = v___x_2698_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2705_, 0, v___x_2702_);
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
                    v_reuseFailAlloc_2714_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
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
                    v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2721_);
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
                    lean_ctor_set_tag(v___x_2680_, 0);
                    lean_ctor_set(v___x_2680_, 0, v_i_2730_);
                    v___x_2735_ = v___x_2680_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_i_2730_);
                    lean_ctor_set(v_reuseFailAlloc_2743_, 1, v_k_2678_);
                    v___x_2735_ = v_reuseFailAlloc_2743_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                v___x_2736_ = lean_box(0);
                v___x_2737_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2737_, 0, v___x_2735_);
                lean_ctor_set(v___x_2737_, 1, v___x_2736_);
                v___x_2738_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_2737_);
                if v_isShared_2733_ == 0 {
                    lean_ctor_set_tag(v___x_2732_, 1);
                    lean_ctor_set(v___x_2732_, 0, v___x_2738_);
                    v___x_2740_ = v___x_2732_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_2742_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2738_);
                    v___x_2740_ = v_reuseFailAlloc_2742_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                v___x_2741_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2741_, 0, v___x_2740_);
                return v___x_2741_;
            }
            55 => {
                v___x_2751_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_pow(v_val_2747_, v_k_2678_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
                lean_dec(v_k_2678_);
                if lean_obj_tag(v___x_2751_) == 0 {
                    v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
                    v_isSharedCheck_2762_ = (!lean_is_exclusive(v___x_2751_)) as u8;
                    if v_isSharedCheck_2762_ == 0 {
                        v___x_2754_ = v___x_2751_;
                        v_isShared_2755_ = v_isSharedCheck_2762_;
                        state = 56;
                        continue;
                    } else {
                        lean_inc(v_a_2752_);
                        lean_dec(v___x_2751_);
                        v___x_2754_ = lean_box(0);
                        v_isShared_2755_ = v_isSharedCheck_2762_;
                        state = 56;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2749_);
                    v_a_2763_ = lean_ctor_get(v___x_2751_, 0);
                    v_isSharedCheck_2770_ = (!lean_is_exclusive(v___x_2751_)) as u8;
                    if v_isSharedCheck_2770_ == 0 {
                        v___x_2765_ = v___x_2751_;
                        v_isShared_2766_ = v_isSharedCheck_2770_;
                        state = 59;
                        continue;
                    } else {
                        lean_inc(v_a_2763_);
                        lean_dec(v___x_2751_);
                        v___x_2765_ = lean_box(0);
                        v_isShared_2766_ = v_isSharedCheck_2770_;
                        state = 59;
                        continue;
                    }
                }
            }
            56 => {
                if v_isShared_2750_ == 0 {
                    lean_ctor_set(v___x_2749_, 0, v_a_2752_);
                    v___x_2757_ = v___x_2749_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2752_);
                    v___x_2757_ = v_reuseFailAlloc_2761_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                if v_isShared_2755_ == 0 {
                    lean_ctor_set(v___x_2754_, 0, v___x_2757_);
                    v___x_2759_ = v___x_2754_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2760_, 0, v___x_2757_);
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
                    v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
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
    mut v_e_2776_: *mut LeanObject,
    mut v_a_2777_: *mut LeanObject,
    mut v_a_2778_: *mut LeanObject,
    mut v_a_2779_: *mut LeanObject,
    mut v_a_2780_: *mut LeanObject,
    mut v_a_2781_: *mut LeanObject,
    mut v_a_2782_: *mut LeanObject,
    mut v_a_2783_: *mut LeanObject,
    mut v_a_2784_: *mut LeanObject,
    mut v_a_2785_: *mut LeanObject,
    mut v_a_2786_: *mut LeanObject,
    mut v_a_2787_: *mut LeanObject,
    mut v_a_2788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2789_: *mut LeanObject = core::ptr::null_mut();
    v_res_2789_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_e_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_);
    lean_dec(v_a_2787_);
    lean_dec_ref(v_a_2786_);
    lean_dec(v_a_2785_);
    lean_dec_ref(v_a_2784_);
    lean_dec(v_a_2783_);
    lean_dec_ref(v_a_2782_);
    lean_dec(v_a_2781_);
    lean_dec_ref(v_a_2780_);
    lean_dec(v_a_2779_);
    lean_dec(v_a_2778_);
    lean_dec_ref(v_a_2777_);
    return v_res_2789_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_toPolyM_x3f(
    mut v_e_2790_: *mut LeanObject,
    mut v_a_2791_: *mut LeanObject,
    mut v_a_2792_: *mut LeanObject,
    mut v_a_2793_: *mut LeanObject,
    mut v_a_2794_: *mut LeanObject,
    mut v_a_2795_: *mut LeanObject,
    mut v_a_2796_: *mut LeanObject,
    mut v_a_2797_: *mut LeanObject,
    mut v_a_2798_: *mut LeanObject,
    mut v_a_2799_: *mut LeanObject,
    mut v_a_2800_: *mut LeanObject,
    mut v_a_2801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    v___x_2803_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_toPoly(v_e_2790_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_);
    return v___x_2803_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_toPolyM_x3f___boxed(
    mut v_e_2804_: *mut LeanObject,
    mut v_a_2805_: *mut LeanObject,
    mut v_a_2806_: *mut LeanObject,
    mut v_a_2807_: *mut LeanObject,
    mut v_a_2808_: *mut LeanObject,
    mut v_a_2809_: *mut LeanObject,
    mut v_a_2810_: *mut LeanObject,
    mut v_a_2811_: *mut LeanObject,
    mut v_a_2812_: *mut LeanObject,
    mut v_a_2813_: *mut LeanObject,
    mut v_a_2814_: *mut LeanObject,
    mut v_a_2815_: *mut LeanObject,
    mut v_a_2816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2817_: *mut LeanObject = core::ptr::null_mut();
    v_res_2817_ = l_Lean_Grind_CommRing_Expr_toPolyM_x3f(
        v_e_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_,
        v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_,
    );
    lean_dec(v_a_2815_);
    lean_dec_ref(v_a_2814_);
    lean_dec(v_a_2813_);
    lean_dec_ref(v_a_2812_);
    lean_dec(v_a_2811_);
    lean_dec_ref(v_a_2810_);
    lean_dec(v_a_2809_);
    lean_dec_ref(v_a_2808_);
    lean_dec(v_a_2807_);
    lean_dec(v_a_2806_);
    lean_dec_ref(v_a_2805_);
    return v_res_2817_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulConstM(
    mut v_p_2818_: *mut LeanObject,
    mut v_k_2819_: *mut LeanObject,
    mut v_a_2820_: *mut LeanObject,
    mut v_a_2821_: *mut LeanObject,
    mut v_a_2822_: *mut LeanObject,
    mut v_a_2823_: *mut LeanObject,
    mut v_a_2824_: *mut LeanObject,
    mut v_a_2825_: *mut LeanObject,
    mut v_a_2826_: *mut LeanObject,
    mut v_a_2827_: *mut LeanObject,
    mut v_a_2828_: *mut LeanObject,
    mut v_a_2829_: *mut LeanObject,
    mut v_a_2830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    v___x_2832_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v_k_2819_, v_p_2818_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_);
    return v___x_2832_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulConstM___boxed(
    mut v_p_2833_: *mut LeanObject,
    mut v_k_2834_: *mut LeanObject,
    mut v_a_2835_: *mut LeanObject,
    mut v_a_2836_: *mut LeanObject,
    mut v_a_2837_: *mut LeanObject,
    mut v_a_2838_: *mut LeanObject,
    mut v_a_2839_: *mut LeanObject,
    mut v_a_2840_: *mut LeanObject,
    mut v_a_2841_: *mut LeanObject,
    mut v_a_2842_: *mut LeanObject,
    mut v_a_2843_: *mut LeanObject,
    mut v_a_2844_: *mut LeanObject,
    mut v_a_2845_: *mut LeanObject,
    mut v_a_2846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2847_: *mut LeanObject = core::ptr::null_mut();
    v_res_2847_ = l_Lean_Grind_CommRing_Poly_mulConstM(
        v_p_2833_, v_k_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_,
        v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_,
    );
    lean_dec(v_a_2845_);
    lean_dec_ref(v_a_2844_);
    lean_dec(v_a_2843_);
    lean_dec_ref(v_a_2842_);
    lean_dec(v_a_2841_);
    lean_dec_ref(v_a_2840_);
    lean_dec(v_a_2839_);
    lean_dec_ref(v_a_2838_);
    lean_dec(v_a_2837_);
    lean_dec(v_a_2836_);
    lean_dec_ref(v_a_2835_);
    lean_dec(v_k_2834_);
    return v_res_2847_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMonM(
    mut v_p_2848_: *mut LeanObject,
    mut v_k_2849_: *mut LeanObject,
    mut v_m_2850_: *mut LeanObject,
    mut v_a_2851_: *mut LeanObject,
    mut v_a_2852_: *mut LeanObject,
    mut v_a_2853_: *mut LeanObject,
    mut v_a_2854_: *mut LeanObject,
    mut v_a_2855_: *mut LeanObject,
    mut v_a_2856_: *mut LeanObject,
    mut v_a_2857_: *mut LeanObject,
    mut v_a_2858_: *mut LeanObject,
    mut v_a_2859_: *mut LeanObject,
    mut v_a_2860_: *mut LeanObject,
    mut v_a_2861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    v___x_2863_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_k_2849_, v_m_2850_, v_p_2848_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_);
    return v___x_2863_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMonM___boxed(
    mut v_p_2864_: *mut LeanObject,
    mut v_k_2865_: *mut LeanObject,
    mut v_m_2866_: *mut LeanObject,
    mut v_a_2867_: *mut LeanObject,
    mut v_a_2868_: *mut LeanObject,
    mut v_a_2869_: *mut LeanObject,
    mut v_a_2870_: *mut LeanObject,
    mut v_a_2871_: *mut LeanObject,
    mut v_a_2872_: *mut LeanObject,
    mut v_a_2873_: *mut LeanObject,
    mut v_a_2874_: *mut LeanObject,
    mut v_a_2875_: *mut LeanObject,
    mut v_a_2876_: *mut LeanObject,
    mut v_a_2877_: *mut LeanObject,
    mut v_a_2878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2879_: *mut LeanObject = core::ptr::null_mut();
    v_res_2879_ = l_Lean_Grind_CommRing_Poly_mulMonM(
        v_p_2864_, v_k_2865_, v_m_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_,
        v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_,
    );
    lean_dec(v_a_2877_);
    lean_dec_ref(v_a_2876_);
    lean_dec(v_a_2875_);
    lean_dec_ref(v_a_2874_);
    lean_dec(v_a_2873_);
    lean_dec_ref(v_a_2872_);
    lean_dec(v_a_2871_);
    lean_dec_ref(v_a_2870_);
    lean_dec(v_a_2869_);
    lean_dec(v_a_2868_);
    lean_dec_ref(v_a_2867_);
    lean_dec(v_k_2865_);
    return v_res_2879_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulM(
    mut v_p_u2081_2880_: *mut LeanObject,
    mut v_p_u2082_2881_: *mut LeanObject,
    mut v_a_2882_: *mut LeanObject,
    mut v_a_2883_: *mut LeanObject,
    mut v_a_2884_: *mut LeanObject,
    mut v_a_2885_: *mut LeanObject,
    mut v_a_2886_: *mut LeanObject,
    mut v_a_2887_: *mut LeanObject,
    mut v_a_2888_: *mut LeanObject,
    mut v_a_2889_: *mut LeanObject,
    mut v_a_2890_: *mut LeanObject,
    mut v_a_2891_: *mut LeanObject,
    mut v_a_2892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    v___x_2894_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul(v_p_u2081_2880_, v_p_u2082_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_);
    return v___x_2894_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulM___boxed(
    mut v_p_u2081_2895_: *mut LeanObject,
    mut v_p_u2082_2896_: *mut LeanObject,
    mut v_a_2897_: *mut LeanObject,
    mut v_a_2898_: *mut LeanObject,
    mut v_a_2899_: *mut LeanObject,
    mut v_a_2900_: *mut LeanObject,
    mut v_a_2901_: *mut LeanObject,
    mut v_a_2902_: *mut LeanObject,
    mut v_a_2903_: *mut LeanObject,
    mut v_a_2904_: *mut LeanObject,
    mut v_a_2905_: *mut LeanObject,
    mut v_a_2906_: *mut LeanObject,
    mut v_a_2907_: *mut LeanObject,
    mut v_a_2908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2909_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2907_);
    lean_dec_ref(v_a_2906_);
    lean_dec(v_a_2905_);
    lean_dec_ref(v_a_2904_);
    lean_dec(v_a_2903_);
    lean_dec_ref(v_a_2902_);
    lean_dec(v_a_2901_);
    lean_dec_ref(v_a_2900_);
    lean_dec(v_a_2899_);
    lean_dec(v_a_2898_);
    lean_dec_ref(v_a_2897_);
    return v_res_2909_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_combineM(
    mut v_p_u2081_2910_: *mut LeanObject,
    mut v_p_u2082_2911_: *mut LeanObject,
    mut v_a_2912_: *mut LeanObject,
    mut v_a_2913_: *mut LeanObject,
    mut v_a_2914_: *mut LeanObject,
    mut v_a_2915_: *mut LeanObject,
    mut v_a_2916_: *mut LeanObject,
    mut v_a_2917_: *mut LeanObject,
    mut v_a_2918_: *mut LeanObject,
    mut v_a_2919_: *mut LeanObject,
    mut v_a_2920_: *mut LeanObject,
    mut v_a_2921_: *mut LeanObject,
    mut v_a_2922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_a_2921_);
    v___x_2924_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_p_u2081_2910_, v_p_u2082_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_);
    return v___x_2924_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_combineM___boxed(
    mut v_p_u2081_2925_: *mut LeanObject,
    mut v_p_u2082_2926_: *mut LeanObject,
    mut v_a_2927_: *mut LeanObject,
    mut v_a_2928_: *mut LeanObject,
    mut v_a_2929_: *mut LeanObject,
    mut v_a_2930_: *mut LeanObject,
    mut v_a_2931_: *mut LeanObject,
    mut v_a_2932_: *mut LeanObject,
    mut v_a_2933_: *mut LeanObject,
    mut v_a_2934_: *mut LeanObject,
    mut v_a_2935_: *mut LeanObject,
    mut v_a_2936_: *mut LeanObject,
    mut v_a_2937_: *mut LeanObject,
    mut v_a_2938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2939_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2937_);
    lean_dec_ref(v_a_2936_);
    lean_dec(v_a_2935_);
    lean_dec_ref(v_a_2934_);
    lean_dec(v_a_2933_);
    lean_dec_ref(v_a_2932_);
    lean_dec(v_a_2931_);
    lean_dec_ref(v_a_2930_);
    lean_dec(v_a_2929_);
    lean_dec(v_a_2928_);
    lean_dec_ref(v_a_2927_);
    return v_res_2939_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_Poly_spolM___closed__0() -> *mut LeanObject {
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    v___x_2940_ = lean_box(0);
    v___x_2941_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
    v___x_2942_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mul___closed__0);
    v___x_2943_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_2943_, 0, v___x_2942_);
    lean_ctor_set(v___x_2943_, 1, v___x_2941_);
    lean_ctor_set(v___x_2943_, 2, v___x_2940_);
    lean_ctor_set(v___x_2943_, 3, v___x_2941_);
    lean_ctor_set(v___x_2943_, 4, v___x_2940_);
    return v___x_2943_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_spolM(
    mut v_p_u2081_2944_: *mut LeanObject,
    mut v_p_u2082_2945_: *mut LeanObject,
    mut v_a_2946_: *mut LeanObject,
    mut v_a_2947_: *mut LeanObject,
    mut v_a_2948_: *mut LeanObject,
    mut v_a_2949_: *mut LeanObject,
    mut v_a_2950_: *mut LeanObject,
    mut v_a_2951_: *mut LeanObject,
    mut v_a_2952_: *mut LeanObject,
    mut v_a_2953_: *mut LeanObject,
    mut v_a_2954_: *mut LeanObject,
    mut v_a_2955_: *mut LeanObject,
    mut v_a_2956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_u2081_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_g_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_u2081_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_u2082_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_u2082_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2985_: u8 = 0;
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2990_: u8 = 0;
    let mut v_a_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2994_: u8 = 0;
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2998_: u8 = 0;
    let mut v_a_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3002_: u8 = 0;
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3006_: u8 = 0;
    let mut v_a_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3010_: u8 = 0;
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3014_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_u2081_2944_) == 1 {
                    if lean_obj_tag(v_p_u2082_2945_) == 1 {
                        v_k_2961_ = lean_ctor_get(v_p_u2081_2944_, 0);
                        lean_inc(v_k_2961_);
                        v_v_2962_ = lean_ctor_get(v_p_u2081_2944_, 1);
                        lean_inc_n(v_v_2962_, 2);
                        v_p_2963_ = lean_ctor_get(v_p_u2081_2944_, 2);
                        lean_inc_ref(v_p_2963_);
                        lean_dec_ref_known(v_p_u2081_2944_, 3);
                        v_k_2964_ = lean_ctor_get(v_p_u2082_2945_, 0);
                        lean_inc(v_k_2964_);
                        v_v_2965_ = lean_ctor_get(v_p_u2082_2945_, 1);
                        lean_inc_n(v_v_2965_, 2);
                        v_p_2966_ = lean_ctor_get(v_p_u2082_2945_, 2);
                        lean_inc_ref(v_p_2966_);
                        lean_dec_ref_known(v_p_u2082_2945_, 3);
                        v_m_2967_ = l_Lean_Grind_CommRing_Mon_lcm(v_v_2962_, v_v_2965_);
                        lean_inc(v_m_2967_);
                        v_m_u2081_2968_ = l_Lean_Grind_CommRing_Mon_div(v_m_2967_, v_v_2962_);
                        v___x_2969_ = lean_nat_abs(v_k_2961_);
                        v___x_2970_ = lean_nat_abs(v_k_2964_);
                        v_g_2971_ = lean_nat_gcd(v___x_2969_, v___x_2970_);
                        lean_dec(v___x_2970_);
                        lean_dec(v___x_2969_);
                        v___x_2972_ = lean_nat_to_int(v_g_2971_);
                        v_c_u2081_2973_ = lean_int_ediv(v_k_2964_, v___x_2972_);
                        lean_dec(v_k_2964_);
                        lean_inc(v_m_u2081_2968_);
                        v___x_2974_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_c_u2081_2973_, v_m_u2081_2968_, v_p_2963_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_);
                        if lean_obj_tag(v___x_2974_) == 0 {
                            v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
                            lean_inc(v_a_2975_);
                            lean_dec_ref_known(v___x_2974_, 1);
                            v_m_u2082_2976_ = l_Lean_Grind_CommRing_Mon_div(v_m_2967_, v_v_2965_);
                            v___x_2977_ = lean_int_neg(v_k_2961_);
                            lean_dec(v_k_2961_);
                            v_c_u2082_2978_ = lean_int_ediv(v___x_2977_, v___x_2972_);
                            lean_dec(v___x_2972_);
                            lean_dec(v___x_2977_);
                            lean_inc(v_m_u2082_2976_);
                            v___x_2979_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_c_u2082_2978_, v_m_u2082_2976_, v_p_2966_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_);
                            if lean_obj_tag(v___x_2979_) == 0 {
                                v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
                                lean_inc(v_a_2980_);
                                lean_dec_ref_known(v___x_2979_, 1);
                                lean_inc_ref(v_a_2955_);
                                v___x_2981_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_a_2975_, v_a_2980_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_);
                                if lean_obj_tag(v___x_2981_) == 0 {
                                    v_a_2982_ = lean_ctor_get(v___x_2981_, 0);
                                    v_isSharedCheck_2990_ = (!lean_is_exclusive(v___x_2981_)) as u8;
                                    if v_isSharedCheck_2990_ == 0 {
                                        v___x_2984_ = v___x_2981_;
                                        v_isShared_2985_ = v_isSharedCheck_2990_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2982_);
                                        lean_dec(v___x_2981_);
                                        v___x_2984_ = lean_box(0);
                                        v_isShared_2985_ = v_isSharedCheck_2990_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_c_u2082_2978_);
                                    lean_dec(v_m_u2082_2976_);
                                    lean_dec(v_c_u2081_2973_);
                                    lean_dec(v_m_u2081_2968_);
                                    v_a_2991_ = lean_ctor_get(v___x_2981_, 0);
                                    v_isSharedCheck_2998_ = (!lean_is_exclusive(v___x_2981_)) as u8;
                                    if v_isSharedCheck_2998_ == 0 {
                                        v___x_2993_ = v___x_2981_;
                                        v_isShared_2994_ = v_isSharedCheck_2998_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2991_);
                                        lean_dec(v___x_2981_);
                                        v___x_2993_ = lean_box(0);
                                        v_isShared_2994_ = v_isSharedCheck_2998_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_c_u2082_2978_);
                                lean_dec(v_m_u2082_2976_);
                                lean_dec(v_a_2975_);
                                lean_dec(v_c_u2081_2973_);
                                lean_dec(v_m_u2081_2968_);
                                v_a_2999_ = lean_ctor_get(v___x_2979_, 0);
                                v_isSharedCheck_3006_ = (!lean_is_exclusive(v___x_2979_)) as u8;
                                if v_isSharedCheck_3006_ == 0 {
                                    v___x_3001_ = v___x_2979_;
                                    v_isShared_3002_ = v_isSharedCheck_3006_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_2999_);
                                    lean_dec(v___x_2979_);
                                    v___x_3001_ = lean_box(0);
                                    v_isShared_3002_ = v_isSharedCheck_3006_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_c_u2081_2973_);
                            lean_dec(v___x_2972_);
                            lean_dec(v_m_u2081_2968_);
                            lean_dec(v_m_2967_);
                            lean_dec_ref(v_p_2966_);
                            lean_dec(v_v_2965_);
                            lean_dec(v_k_2961_);
                            v_a_3007_ = lean_ctor_get(v___x_2974_, 0);
                            v_isSharedCheck_3014_ = (!lean_is_exclusive(v___x_2974_)) as u8;
                            if v_isSharedCheck_3014_ == 0 {
                                v___x_3009_ = v___x_2974_;
                                v_isShared_3010_ = v_isSharedCheck_3014_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_3007_);
                                lean_dec(v___x_2974_);
                                v___x_3009_ = lean_box(0);
                                v_isShared_3010_ = v_isSharedCheck_3014_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_p_u2081_2944_, 3);
                        lean_dec_ref(v_p_u2082_2945_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_p_u2082_2945_);
                    lean_dec_ref(v_p_u2081_2944_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2959_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_spolM___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_spolM___closed__0_once),
                    _init_l_Lean_Grind_CommRing_Poly_spolM___closed__0,
                );
                v___x_2960_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2960_, 0, v___x_2959_);
                return v___x_2960_;
            }
            2 => {
                v___x_2986_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_2986_, 0, v_a_2982_);
                lean_ctor_set(v___x_2986_, 1, v_c_u2081_2973_);
                lean_ctor_set(v___x_2986_, 2, v_m_u2081_2968_);
                lean_ctor_set(v___x_2986_, 3, v_c_u2082_2978_);
                lean_ctor_set(v___x_2986_, 4, v_m_u2082_2976_);
                if v_isShared_2985_ == 0 {
                    lean_ctor_set(v___x_2984_, 0, v___x_2986_);
                    v___x_2988_ = v___x_2984_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2989_, 0, v___x_2986_);
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
                    v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2991_);
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
                    v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
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
                    v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
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
    mut v_p_u2081_3015_: *mut LeanObject,
    mut v_p_u2082_3016_: *mut LeanObject,
    mut v_a_3017_: *mut LeanObject,
    mut v_a_3018_: *mut LeanObject,
    mut v_a_3019_: *mut LeanObject,
    mut v_a_3020_: *mut LeanObject,
    mut v_a_3021_: *mut LeanObject,
    mut v_a_3022_: *mut LeanObject,
    mut v_a_3023_: *mut LeanObject,
    mut v_a_3024_: *mut LeanObject,
    mut v_a_3025_: *mut LeanObject,
    mut v_a_3026_: *mut LeanObject,
    mut v_a_3027_: *mut LeanObject,
    mut v_a_3028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3029_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3027_);
    lean_dec_ref(v_a_3026_);
    lean_dec(v_a_3025_);
    lean_dec_ref(v_a_3024_);
    lean_dec(v_a_3023_);
    lean_dec_ref(v_a_3022_);
    lean_dec(v_a_3021_);
    lean_dec_ref(v_a_3020_);
    lean_dec(v_a_3019_);
    lean_dec(v_a_3018_);
    lean_dec_ref(v_a_3017_);
    return v_res_3029_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(
    mut v_m_3040_: *mut LeanObject,
    mut v_a_3041_: *mut LeanObject,
    mut v_a_3042_: *mut LeanObject,
    mut v_a_3043_: *mut LeanObject,
    mut v_a_3044_: *mut LeanObject,
    mut v_a_3045_: *mut LeanObject,
    mut v_a_3046_: *mut LeanObject,
    mut v_a_3047_: *mut LeanObject,
    mut v_a_3048_: *mut LeanObject,
    mut v_a_3049_: *mut LeanObject,
    mut v_a_3050_: *mut LeanObject,
    mut v_a_3051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toRing_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3064_: u8 = 0;
    let mut v___y_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: u8 = 0;
    let mut v_arg_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: u8 = 0;
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: u8 = 0;
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: u8 = 0;
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: u8 = 0;
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: u8 = 0;
    let mut v_arg_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: u8 = 0;
    let mut v___x_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: u8 = 0;
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3099_: u8 = 0;
    let mut v_val_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3103_: u8 = 0;
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3113_: u8 = 0;
    let mut v_isSharedCheck_3115_: u8 = 0;
    let mut v_a_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3119_: u8 = 0;
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3123_: u8 = 0;
    let mut v_size_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: u8 = 0;
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3129_: u8 = 0;
    let mut v_unused_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3134_: u8 = 0;
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3138_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_m_3040_) == 0 {
                    v___x_3053_ = lean_box(0);
                    v___x_3054_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3054_, 0, v___x_3053_);
                    return v___x_3054_;
                } else {
                    v_p_3055_ = lean_ctor_get(v_m_3040_, 0);
                    lean_inc_ref(v_p_3055_);
                    v_m_3056_ = lean_ctor_get(v_m_3040_, 1);
                    lean_inc(v_m_3056_);
                    lean_dec_ref_known(v_m_3040_, 2);
                    v___x_3057_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                        v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_,
                        v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_,
                    );
                    if lean_obj_tag(v___x_3057_) == 0 {
                        v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
                        lean_inc(v_a_3058_);
                        lean_dec_ref_known(v___x_3057_, 1);
                        v_toRing_3059_ = lean_ctor_get(v_a_3058_, 0);
                        lean_inc_ref(v_toRing_3059_);
                        lean_dec(v_a_3058_);
                        v_vars_3060_ = lean_ctor_get(v_toRing_3059_, 14);
                        lean_inc_ref(v_vars_3060_);
                        lean_dec_ref(v_toRing_3059_);
                        v_x_3061_ = lean_ctor_get(v_p_3055_, 0);
                        v_isSharedCheck_3129_ = (!lean_is_exclusive(v_p_3055_)) as u8;
                        if v_isSharedCheck_3129_ == 0 {
                            v_unused_3130_ = lean_ctor_get(v_p_3055_, 1);
                            lean_dec(v_unused_3130_);
                            v___x_3063_ = v_p_3055_;
                            v_isShared_3064_ = v_isSharedCheck_3129_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_x_3061_);
                            lean_dec(v_p_3055_);
                            v___x_3063_ = lean_box(0);
                            v_isShared_3064_ = v_isSharedCheck_3129_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_m_3056_);
                        lean_dec_ref(v_p_3055_);
                        v_a_3131_ = lean_ctor_get(v___x_3057_, 0);
                        v_isSharedCheck_3138_ = (!lean_is_exclusive(v___x_3057_)) as u8;
                        if v_isSharedCheck_3138_ == 0 {
                            v___x_3133_ = v___x_3057_;
                            v_isShared_3134_ = v_isSharedCheck_3138_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_3131_);
                            lean_dec(v___x_3057_);
                            v___x_3133_ = lean_box(0);
                            v_isShared_3134_ = v_isSharedCheck_3138_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_size_3124_ = lean_ctor_get(v_vars_3060_, 2);
                v___x_3125_ = l_Lean_instInhabitedExpr;
                v___x_3126_ = lean_nat_dec_lt(v_x_3061_, v_size_3124_);
                if v___x_3126_ == 0 {
                    lean_dec_ref(v_vars_3060_);
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
                    lean_dec_ref(v_vars_3060_);
                    v___y_3066_ = v___x_3128_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3067_ = l_Lean_Expr_cleanupAnnotations(v___y_3066_);
                v___x_3068_ = l_Lean_Expr_isApp(v___x_3067_);
                if v___x_3068_ == 0 {
                    lean_dec_ref(v___x_3067_);
                    lean_del_object(v___x_3063_);
                    lean_dec(v_x_3061_);
                    v_m_3040_ = v_m_3056_;
                    state = 0;
                    continue;
                } else {
                    v_arg_3070_ = lean_ctor_get(v___x_3067_, 1);
                    lean_inc_ref(v_arg_3070_);
                    v___x_3071_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3067_);
                    v___x_3072_ = l_Lean_Expr_isApp(v___x_3071_);
                    if v___x_3072_ == 0 {
                        lean_dec_ref(v___x_3071_);
                        lean_dec_ref(v_arg_3070_);
                        lean_del_object(v___x_3063_);
                        lean_dec(v_x_3061_);
                        v_m_3040_ = v_m_3056_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3074_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3071_);
                        v___x_3075_ = l_Lean_Expr_isApp(v___x_3074_);
                        if v___x_3075_ == 0 {
                            lean_dec_ref(v___x_3074_);
                            lean_dec_ref(v_arg_3070_);
                            lean_del_object(v___x_3063_);
                            lean_dec(v_x_3061_);
                            v_m_3040_ = v_m_3056_;
                            state = 0;
                            continue;
                        } else {
                            v___x_3077_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3074_);
                            v___x_3078_ =
                                l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__2;
                            v___x_3079_ = l_Lean_Expr_isConstOf(v___x_3077_, v___x_3078_);
                            lean_dec_ref(v___x_3077_);
                            if v___x_3079_ == 0 {
                                lean_dec_ref(v_arg_3070_);
                                lean_del_object(v___x_3063_);
                                lean_dec(v_x_3061_);
                                v_m_3040_ = v_m_3056_;
                                state = 0;
                                continue;
                            } else {
                                v___x_3081_ = l_Lean_Expr_cleanupAnnotations(v_arg_3070_);
                                v___x_3082_ = l_Lean_Expr_isApp(v___x_3081_);
                                if v___x_3082_ == 0 {
                                    lean_dec_ref(v___x_3081_);
                                    lean_del_object(v___x_3063_);
                                    lean_dec(v_x_3061_);
                                    v_m_3040_ = v_m_3056_;
                                    state = 0;
                                    continue;
                                } else {
                                    v___x_3084_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3081_);
                                    v___x_3085_ = l_Lean_Expr_isApp(v___x_3084_);
                                    if v___x_3085_ == 0 {
                                        lean_dec_ref(v___x_3084_);
                                        lean_del_object(v___x_3063_);
                                        lean_dec(v_x_3061_);
                                        v_m_3040_ = v_m_3056_;
                                        state = 0;
                                        continue;
                                    } else {
                                        v_arg_3087_ = lean_ctor_get(v___x_3084_, 1);
                                        lean_inc_ref(v_arg_3087_);
                                        v___x_3088_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_3084_);
                                        v___x_3089_ = l_Lean_Expr_isApp(v___x_3088_);
                                        if v___x_3089_ == 0 {
                                            lean_dec_ref(v___x_3088_);
                                            lean_dec_ref(v_arg_3087_);
                                            lean_del_object(v___x_3063_);
                                            lean_dec(v_x_3061_);
                                            v_m_3040_ = v_m_3056_;
                                            state = 0;
                                            continue;
                                        } else {
                                            v___x_3091_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_3088_);
                                            v___x_3092_ = l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f___closed__5;
                                            v___x_3093_ =
                                                l_Lean_Expr_isConstOf(v___x_3091_, v___x_3092_);
                                            lean_dec_ref(v___x_3091_);
                                            if v___x_3093_ == 0 {
                                                lean_dec_ref(v_arg_3087_);
                                                lean_del_object(v___x_3063_);
                                                lean_dec(v_x_3061_);
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
                                                lean_dec_ref(v_arg_3087_);
                                                if lean_obj_tag(v___x_3095_) == 0 {
                                                    v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
                                                    v_isSharedCheck_3115_ =
                                                        (!lean_is_exclusive(v___x_3095_)) as u8;
                                                    if v_isSharedCheck_3115_ == 0 {
                                                        v___x_3098_ = v___x_3095_;
                                                        v_isShared_3099_ = v_isSharedCheck_3115_;
                                                        state = 3;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_3096_);
                                                        lean_dec(v___x_3095_);
                                                        v___x_3098_ = lean_box(0);
                                                        v_isShared_3099_ = v_isSharedCheck_3115_;
                                                        state = 3;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_del_object(v___x_3063_);
                                                    lean_dec(v_x_3061_);
                                                    lean_dec(v_m_3056_);
                                                    v_a_3116_ = lean_ctor_get(v___x_3095_, 0);
                                                    v_isSharedCheck_3123_ =
                                                        (!lean_is_exclusive(v___x_3095_)) as u8;
                                                    if v_isSharedCheck_3123_ == 0 {
                                                        v___x_3118_ = v___x_3095_;
                                                        v_isShared_3119_ = v_isSharedCheck_3123_;
                                                        state = 8;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_3116_);
                                                        lean_dec(v___x_3095_);
                                                        v___x_3118_ = lean_box(0);
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
                if lean_obj_tag(v_a_3096_) == 1 {
                    lean_dec(v_m_3056_);
                    v_val_3100_ = lean_ctor_get(v_a_3096_, 0);
                    v_isSharedCheck_3113_ = (!lean_is_exclusive(v_a_3096_)) as u8;
                    if v_isSharedCheck_3113_ == 0 {
                        v___x_3102_ = v_a_3096_;
                        v_isShared_3103_ = v_isSharedCheck_3113_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_val_3100_);
                        lean_dec(v_a_3096_);
                        v___x_3102_ = lean_box(0);
                        v_isShared_3103_ = v_isSharedCheck_3113_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3098_);
                    lean_dec(v_a_3096_);
                    lean_del_object(v___x_3063_);
                    lean_dec(v_x_3061_);
                    v_m_3040_ = v_m_3056_;
                    state = 0;
                    continue;
                }
            }
            4 => {
                if v_isShared_3064_ == 0 {
                    lean_ctor_set(v___x_3063_, 1, v_x_3061_);
                    lean_ctor_set(v___x_3063_, 0, v_val_3100_);
                    v___x_3105_ = v___x_3063_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_val_3100_);
                    lean_ctor_set(v_reuseFailAlloc_3112_, 1, v_x_3061_);
                    v___x_3105_ = v_reuseFailAlloc_3112_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3103_ == 0 {
                    lean_ctor_set(v___x_3102_, 0, v___x_3105_);
                    v___x_3107_ = v___x_3102_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3105_);
                    v___x_3107_ = v_reuseFailAlloc_3111_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3099_ == 0 {
                    lean_ctor_set(v___x_3098_, 0, v___x_3107_);
                    v___x_3109_ = v___x_3098_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3107_);
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
                    v_reuseFailAlloc_3122_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3116_);
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
                    v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
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
    mut v_m_3139_: *mut LeanObject,
    mut v_a_3140_: *mut LeanObject,
    mut v_a_3141_: *mut LeanObject,
    mut v_a_3142_: *mut LeanObject,
    mut v_a_3143_: *mut LeanObject,
    mut v_a_3144_: *mut LeanObject,
    mut v_a_3145_: *mut LeanObject,
    mut v_a_3146_: *mut LeanObject,
    mut v_a_3147_: *mut LeanObject,
    mut v_a_3148_: *mut LeanObject,
    mut v_a_3149_: *mut LeanObject,
    mut v_a_3150_: *mut LeanObject,
    mut v_a_3151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3152_: *mut LeanObject = core::ptr::null_mut();
    v_res_3152_ = l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(
        v_m_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_,
        v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_,
    );
    lean_dec(v_a_3150_);
    lean_dec_ref(v_a_3149_);
    lean_dec(v_a_3148_);
    lean_dec_ref(v_a_3147_);
    lean_dec(v_a_3146_);
    lean_dec_ref(v_a_3145_);
    lean_dec(v_a_3144_);
    lean_dec_ref(v_a_3143_);
    lean_dec(v_a_3142_);
    lean_dec(v_a_3141_);
    lean_dec_ref(v_a_3140_);
    return v_res_3152_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f(
    mut v_p_3153_: *mut LeanObject,
    mut v_a_3154_: *mut LeanObject,
    mut v_a_3155_: *mut LeanObject,
    mut v_a_3156_: *mut LeanObject,
    mut v_a_3157_: *mut LeanObject,
    mut v_a_3158_: *mut LeanObject,
    mut v_a_3159_: *mut LeanObject,
    mut v_a_3160_: *mut LeanObject,
    mut v_a_3161_: *mut LeanObject,
    mut v_a_3162_: *mut LeanObject,
    mut v_a_3163_: *mut LeanObject,
    mut v_a_3164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3168_: u8 = 0;
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3173_: u8 = 0;
    let mut v_unused_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_3153_) == 0 {
                    v_isSharedCheck_3173_ = (!lean_is_exclusive(v_p_3153_)) as u8;
                    if v_isSharedCheck_3173_ == 0 {
                        v_unused_3174_ = lean_ctor_get(v_p_3153_, 0);
                        lean_dec(v_unused_3174_);
                        v___x_3167_ = v_p_3153_;
                        v_isShared_3168_ = v_isSharedCheck_3173_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_p_3153_);
                        v___x_3167_ = lean_box(0);
                        v_isShared_3168_ = v_isSharedCheck_3173_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_v_3175_ = lean_ctor_get(v_p_3153_, 1);
                    lean_inc(v_v_3175_);
                    v_p_3176_ = lean_ctor_get(v_p_3153_, 2);
                    lean_inc_ref(v_p_3176_);
                    lean_dec_ref_known(v_p_3153_, 3);
                    v___x_3177_ = l_Lean_Grind_CommRing_Mon_findInvNumeralVar_x3f(
                        v_v_3175_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_,
                        v_a_3159_, v_a_3160_, v_a_3161_, v_a_3162_, v_a_3163_, v_a_3164_,
                    );
                    if lean_obj_tag(v___x_3177_) == 0 {
                        v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
                        lean_inc(v_a_3178_);
                        if lean_obj_tag(v_a_3178_) == 1 {
                            lean_dec_ref_known(v_a_3178_, 1);
                            lean_dec_ref(v_p_3176_);
                            return v___x_3177_;
                        } else {
                            lean_dec_ref_known(v___x_3177_, 1);
                            lean_dec(v_a_3178_);
                            v_p_3153_ = v_p_3176_;
                            state = 0;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_p_3176_);
                        return v___x_3177_;
                    }
                }
            }
            1 => {
                v___x_3169_ = lean_box(0);
                if v_isShared_3168_ == 0 {
                    lean_ctor_set(v___x_3167_, 0, v___x_3169_);
                    v___x_3171_ = v___x_3167_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_3169_);
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
    mut v_p_3180_: *mut LeanObject,
    mut v_a_3181_: *mut LeanObject,
    mut v_a_3182_: *mut LeanObject,
    mut v_a_3183_: *mut LeanObject,
    mut v_a_3184_: *mut LeanObject,
    mut v_a_3185_: *mut LeanObject,
    mut v_a_3186_: *mut LeanObject,
    mut v_a_3187_: *mut LeanObject,
    mut v_a_3188_: *mut LeanObject,
    mut v_a_3189_: *mut LeanObject,
    mut v_a_3190_: *mut LeanObject,
    mut v_a_3191_: *mut LeanObject,
    mut v_a_3192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3193_: *mut LeanObject = core::ptr::null_mut();
    v_res_3193_ = l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f(
        v_p_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_,
        v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_,
    );
    lean_dec(v_a_3191_);
    lean_dec_ref(v_a_3190_);
    lean_dec(v_a_3189_);
    lean_dec_ref(v_a_3188_);
    lean_dec(v_a_3187_);
    lean_dec_ref(v_a_3186_);
    lean_dec(v_a_3185_);
    lean_dec_ref(v_a_3184_);
    lean_dec(v_a_3183_);
    lean_dec(v_a_3182_);
    lean_dec_ref(v_a_3181_);
    return v_res_3193_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(
    mut v_k_u2082_x27_3194_: *mut LeanObject,
    mut v_m_u2082_3195_: *mut LeanObject,
    mut v_p_u2082_3196_: *mut LeanObject,
    mut v_p_u2081_3197_: *mut LeanObject,
    mut v_a_3198_: *mut LeanObject,
    mut v_a_3199_: *mut LeanObject,
    mut v_a_3200_: *mut LeanObject,
    mut v_a_3201_: *mut LeanObject,
    mut v_a_3202_: *mut LeanObject,
    mut v_a_3203_: *mut LeanObject,
    mut v_a_3204_: *mut LeanObject,
    mut v_a_3205_: *mut LeanObject,
    mut v_a_3206_: *mut LeanObject,
    mut v_a_3207_: *mut LeanObject,
    mut v_a_3208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3217_: u8 = 0;
    let mut v___x_3218_: u8 = 0;
    let mut v___x_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3223_: u8 = 0;
    let mut v_val_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3229_: u8 = 0;
    let mut v_val_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3233_: u8 = 0;
    let mut v_p_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_u2081_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_u2082_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_u2082_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3240_: u8 = 0;
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: u8 = 0;
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3261_: u8 = 0;
    let mut v_isSharedCheck_3262_: u8 = 0;
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3265_: u8 = 0;
    let mut v_p_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_u2081_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_u2082_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_u2082_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3272_: u8 = 0;
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3286_: u8 = 0;
    let mut v_isSharedCheck_3287_: u8 = 0;
    let mut v_unused_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3289_: u8 = 0;
    let mut v_a_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3293_: u8 = 0;
    let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3297_: u8 = 0;
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3302_: u8 = 0;
    let mut v_m_u2082_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_g_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_u2082_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_u2081_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3319_: u8 = 0;
    let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3325_: u8 = 0;
    let mut v_a_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3329_: u8 = 0;
    let mut v___x_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3333_: u8 = 0;
    let mut v_a_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3337_: u8 = 0;
    let mut v___x_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3341_: u8 = 0;
    let mut v_a_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3345_: u8 = 0;
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3349_: u8 = 0;
    let mut v_isSharedCheck_3350_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_u2081_3197_) == 0 {
                    lean_dec_ref_known(v_p_u2081_3197_, 1);
                    lean_dec_ref(v_p_u2082_3196_);
                    lean_dec(v_m_u2082_3195_);
                    v___x_3210_ = lean_box(0);
                    v___x_3211_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3211_, 0, v___x_3210_);
                    return v___x_3211_;
                } else {
                    v_k_3212_ = lean_ctor_get(v_p_u2081_3197_, 0);
                    v_v_3213_ = lean_ctor_get(v_p_u2081_3197_, 1);
                    v_p_3214_ = lean_ctor_get(v_p_u2081_3197_, 2);
                    v_isSharedCheck_3350_ = (!lean_is_exclusive(v_p_u2081_3197_)) as u8;
                    if v_isSharedCheck_3350_ == 0 {
                        v___x_3216_ = v_p_u2081_3197_;
                        v_isShared_3217_ = v_isSharedCheck_3350_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_p_3214_);
                        lean_inc(v_v_3213_);
                        lean_inc(v_k_3212_);
                        lean_dec(v_p_u2081_3197_);
                        v___x_3216_ = lean_box(0);
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
                    if lean_obj_tag(v___x_3219_) == 0 {
                        v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
                        v_isSharedCheck_3302_ = (!lean_is_exclusive(v___x_3219_)) as u8;
                        if v_isSharedCheck_3302_ == 0 {
                            v___x_3222_ = v___x_3219_;
                            v_isShared_3223_ = v_isSharedCheck_3302_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_3220_);
                            lean_dec(v___x_3219_);
                            v___x_3222_ = lean_box(0);
                            v_isShared_3223_ = v_isSharedCheck_3302_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_3216_);
                        lean_dec(v_v_3213_);
                        lean_dec(v_k_3212_);
                        return v___x_3219_;
                    }
                } else {
                    lean_del_object(v___x_3216_);
                    v_m_u2082_3303_ = l_Lean_Grind_CommRing_Mon_div(v_v_3213_, v_m_u2082_3195_);
                    v___x_3304_ = lean_nat_abs(v_k_3212_);
                    v___x_3305_ = lean_nat_abs(v_k_u2082_x27_3194_);
                    v_g_3306_ = lean_nat_gcd(v___x_3304_, v___x_3305_);
                    lean_dec(v___x_3305_);
                    lean_dec(v___x_3304_);
                    v___x_3307_ = lean_nat_to_int(v_g_3306_);
                    v___x_3308_ = lean_int_neg(v_k_3212_);
                    lean_dec(v_k_3212_);
                    v_k_u2082_3309_ = lean_int_ediv(v___x_3308_, v___x_3307_);
                    lean_dec(v___x_3308_);
                    lean_inc(v_m_u2082_3303_);
                    v___x_3310_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulMon(v_k_u2082_3309_, v_m_u2082_3303_, v_p_u2082_3196_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_);
                    if lean_obj_tag(v___x_3310_) == 0 {
                        v_a_3311_ = lean_ctor_get(v___x_3310_, 0);
                        lean_inc(v_a_3311_);
                        lean_dec_ref_known(v___x_3310_, 1);
                        v_k_u2081_3312_ = lean_int_ediv(v_k_u2082_x27_3194_, v___x_3307_);
                        lean_dec(v___x_3307_);
                        v___x_3313_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_mulConst(v_k_u2081_3312_, v_p_3214_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_);
                        if lean_obj_tag(v___x_3313_) == 0 {
                            v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
                            lean_inc(v_a_3314_);
                            lean_dec_ref_known(v___x_3313_, 1);
                            lean_inc_ref(v_a_3207_);
                            v___x_3315_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine(v_a_3311_, v_a_3314_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_);
                            if lean_obj_tag(v___x_3315_) == 0 {
                                v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
                                v_isSharedCheck_3325_ = (!lean_is_exclusive(v___x_3315_)) as u8;
                                if v_isSharedCheck_3325_ == 0 {
                                    v___x_3318_ = v___x_3315_;
                                    v_isShared_3319_ = v_isSharedCheck_3325_;
                                    state = 20;
                                    continue;
                                } else {
                                    lean_inc(v_a_3316_);
                                    lean_dec(v___x_3315_);
                                    v___x_3318_ = lean_box(0);
                                    v_isShared_3319_ = v_isSharedCheck_3325_;
                                    state = 20;
                                    continue;
                                }
                            } else {
                                lean_dec(v_k_u2081_3312_);
                                lean_dec(v_k_u2082_3309_);
                                lean_dec(v_m_u2082_3303_);
                                v_a_3326_ = lean_ctor_get(v___x_3315_, 0);
                                v_isSharedCheck_3333_ = (!lean_is_exclusive(v___x_3315_)) as u8;
                                if v_isSharedCheck_3333_ == 0 {
                                    v___x_3328_ = v___x_3315_;
                                    v_isShared_3329_ = v_isSharedCheck_3333_;
                                    state = 22;
                                    continue;
                                } else {
                                    lean_inc(v_a_3326_);
                                    lean_dec(v___x_3315_);
                                    v___x_3328_ = lean_box(0);
                                    v_isShared_3329_ = v_isSharedCheck_3333_;
                                    state = 22;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_k_u2081_3312_);
                            lean_dec(v_a_3311_);
                            lean_dec(v_k_u2082_3309_);
                            lean_dec(v_m_u2082_3303_);
                            v_a_3334_ = lean_ctor_get(v___x_3313_, 0);
                            v_isSharedCheck_3341_ = (!lean_is_exclusive(v___x_3313_)) as u8;
                            if v_isSharedCheck_3341_ == 0 {
                                v___x_3336_ = v___x_3313_;
                                v_isShared_3337_ = v_isSharedCheck_3341_;
                                state = 24;
                                continue;
                            } else {
                                lean_inc(v_a_3334_);
                                lean_dec(v___x_3313_);
                                v___x_3336_ = lean_box(0);
                                v_isShared_3337_ = v_isSharedCheck_3341_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_k_u2082_3309_);
                        lean_dec(v___x_3307_);
                        lean_dec(v_m_u2082_3303_);
                        lean_dec_ref(v_p_3214_);
                        v_a_3342_ = lean_ctor_get(v___x_3310_, 0);
                        v_isSharedCheck_3349_ = (!lean_is_exclusive(v___x_3310_)) as u8;
                        if v_isSharedCheck_3349_ == 0 {
                            v___x_3344_ = v___x_3310_;
                            v_isShared_3345_ = v_isSharedCheck_3349_;
                            state = 26;
                            continue;
                        } else {
                            lean_inc(v_a_3342_);
                            lean_dec(v___x_3310_);
                            v___x_3344_ = lean_box(0);
                            v_isShared_3345_ = v_isSharedCheck_3349_;
                            state = 26;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_3220_) == 1 {
                    lean_del_object(v___x_3222_);
                    v_val_3224_ = lean_ctor_get(v_a_3220_, 0);
                    lean_inc(v_val_3224_);
                    v___x_3225_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_applyChar_spec__0(v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_);
                    if lean_obj_tag(v___x_3225_) == 0 {
                        v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
                        v_isSharedCheck_3289_ = (!lean_is_exclusive(v___x_3225_)) as u8;
                        if v_isSharedCheck_3289_ == 0 {
                            v___x_3228_ = v___x_3225_;
                            v_isShared_3229_ = v_isSharedCheck_3289_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3226_);
                            lean_dec(v___x_3225_);
                            v___x_3228_ = lean_box(0);
                            v_isShared_3229_ = v_isSharedCheck_3289_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_a_3220_, 1);
                        lean_dec(v_val_3224_);
                        lean_del_object(v___x_3216_);
                        lean_dec(v_v_3213_);
                        lean_dec(v_k_3212_);
                        v_a_3290_ = lean_ctor_get(v___x_3225_, 0);
                        v_isSharedCheck_3297_ = (!lean_is_exclusive(v___x_3225_)) as u8;
                        if v_isSharedCheck_3297_ == 0 {
                            v___x_3292_ = v___x_3225_;
                            v_isShared_3293_ = v_isSharedCheck_3297_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_3290_);
                            lean_dec(v___x_3225_);
                            v___x_3292_ = lean_box(0);
                            v_isShared_3293_ = v_isSharedCheck_3297_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_3220_);
                    lean_del_object(v___x_3216_);
                    lean_dec(v_v_3213_);
                    lean_dec(v_k_3212_);
                    v___x_3298_ = lean_box(0);
                    if v_isShared_3223_ == 0 {
                        lean_ctor_set(v___x_3222_, 0, v___x_3298_);
                        v___x_3300_ = v___x_3222_;
                        state = 19;
                        continue;
                    } else {
                        v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3298_);
                        v___x_3300_ = v_reuseFailAlloc_3301_;
                        state = 19;
                        continue;
                    }
                }
            }
            3 => {
                if lean_obj_tag(v_a_3226_) == 1 {
                    v_val_3230_ = lean_ctor_get(v_a_3226_, 0);
                    v_isSharedCheck_3262_ = (!lean_is_exclusive(v_a_3226_)) as u8;
                    if v_isSharedCheck_3262_ == 0 {
                        v___x_3232_ = v_a_3226_;
                        v_isShared_3233_ = v_isSharedCheck_3262_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_val_3230_);
                        lean_dec(v_a_3226_);
                        v___x_3232_ = lean_box(0);
                        v_isShared_3233_ = v_isSharedCheck_3262_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3226_);
                    v_isSharedCheck_3287_ = (!lean_is_exclusive(v_a_3220_)) as u8;
                    if v_isSharedCheck_3287_ == 0 {
                        v_unused_3288_ = lean_ctor_get(v_a_3220_, 0);
                        lean_dec(v_unused_3288_);
                        v___x_3264_ = v_a_3220_;
                        v_isShared_3265_ = v_isSharedCheck_3287_;
                        state = 11;
                        continue;
                    } else {
                        lean_dec(v_a_3220_);
                        v___x_3264_ = lean_box(0);
                        v_isShared_3265_ = v_isSharedCheck_3287_;
                        state = 11;
                        continue;
                    }
                }
            }
            4 => {
                v_p_3234_ = lean_ctor_get(v_val_3224_, 0);
                v_k_u2081_3235_ = lean_ctor_get(v_val_3224_, 1);
                v_k_u2082_3236_ = lean_ctor_get(v_val_3224_, 2);
                v_m_u2082_3237_ = lean_ctor_get(v_val_3224_, 3);
                v_isSharedCheck_3261_ = (!lean_is_exclusive(v_val_3224_)) as u8;
                if v_isSharedCheck_3261_ == 0 {
                    v___x_3239_ = v_val_3224_;
                    v_isShared_3240_ = v_isSharedCheck_3261_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_m_u2082_3237_);
                    lean_inc(v_k_u2082_3236_);
                    lean_inc(v_k_u2081_3235_);
                    lean_inc(v_p_3234_);
                    lean_dec(v_val_3224_);
                    v___x_3239_ = lean_box(0);
                    v_isShared_3240_ = v_isSharedCheck_3261_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3241_ = lean_int_mul(v_k_3212_, v_k_u2081_3235_);
                lean_dec(v_k_3212_);
                v___x_3242_ = lean_nat_to_int(v_val_3230_);
                v___x_3243_ = lean_int_emod(v___x_3241_, v___x_3242_);
                lean_dec(v___x_3242_);
                lean_dec(v___x_3241_);
                v___x_3244_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Meta_Grind_Arith_CommRing_combine___closed__0);
                v___x_3245_ = lean_int_dec_eq(v___x_3243_, v___x_3244_);
                if v___x_3245_ == 0 {
                    lean_dec_ref_known(v_a_3220_, 1);
                    if v_isShared_3217_ == 0 {
                        lean_ctor_set(v___x_3216_, 2, v_p_3234_);
                        lean_ctor_set(v___x_3216_, 0, v___x_3243_);
                        v___x_3247_ = v___x_3216_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3257_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3257_, 0, v___x_3243_);
                        lean_ctor_set(v_reuseFailAlloc_3257_, 1, v_v_3213_);
                        lean_ctor_set(v_reuseFailAlloc_3257_, 2, v_p_3234_);
                        v___x_3247_ = v_reuseFailAlloc_3257_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3243_);
                    lean_del_object(v___x_3239_);
                    lean_dec(v_m_u2082_3237_);
                    lean_dec(v_k_u2082_3236_);
                    lean_dec(v_k_u2081_3235_);
                    lean_dec_ref(v_p_3234_);
                    lean_del_object(v___x_3232_);
                    lean_del_object(v___x_3216_);
                    lean_dec(v_v_3213_);
                    if v_isShared_3229_ == 0 {
                        lean_ctor_set(v___x_3228_, 0, v_a_3220_);
                        v___x_3259_ = v___x_3228_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3260_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_a_3220_);
                        v___x_3259_ = v_reuseFailAlloc_3260_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_3240_ == 0 {
                    lean_ctor_set(v___x_3239_, 0, v___x_3247_);
                    v___x_3249_ = v___x_3239_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3247_);
                    lean_ctor_set(v_reuseFailAlloc_3256_, 1, v_k_u2081_3235_);
                    lean_ctor_set(v_reuseFailAlloc_3256_, 2, v_k_u2082_3236_);
                    lean_ctor_set(v_reuseFailAlloc_3256_, 3, v_m_u2082_3237_);
                    v___x_3249_ = v_reuseFailAlloc_3256_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3233_ == 0 {
                    lean_ctor_set(v___x_3232_, 0, v___x_3249_);
                    v___x_3251_ = v___x_3232_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3255_, 0, v___x_3249_);
                    v___x_3251_ = v_reuseFailAlloc_3255_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_3229_ == 0 {
                    lean_ctor_set(v___x_3228_, 0, v___x_3251_);
                    v___x_3253_ = v___x_3228_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3254_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3254_, 0, v___x_3251_);
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
                v_p_3266_ = lean_ctor_get(v_val_3224_, 0);
                v_k_u2081_3267_ = lean_ctor_get(v_val_3224_, 1);
                v_k_u2082_3268_ = lean_ctor_get(v_val_3224_, 2);
                v_m_u2082_3269_ = lean_ctor_get(v_val_3224_, 3);
                v_isSharedCheck_3286_ = (!lean_is_exclusive(v_val_3224_)) as u8;
                if v_isSharedCheck_3286_ == 0 {
                    v___x_3271_ = v_val_3224_;
                    v_isShared_3272_ = v_isSharedCheck_3286_;
                    state = 12;
                    continue;
                } else {
                    lean_inc(v_m_u2082_3269_);
                    lean_inc(v_k_u2082_3268_);
                    lean_inc(v_k_u2081_3267_);
                    lean_inc(v_p_3266_);
                    lean_dec(v_val_3224_);
                    v___x_3271_ = lean_box(0);
                    v_isShared_3272_ = v_isSharedCheck_3286_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_3273_ = lean_int_mul(v_k_3212_, v_k_u2081_3267_);
                lean_dec(v_k_3212_);
                if v_isShared_3217_ == 0 {
                    lean_ctor_set(v___x_3216_, 2, v_p_3266_);
                    lean_ctor_set(v___x_3216_, 0, v___x_3273_);
                    v___x_3275_ = v___x_3216_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3285_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3285_, 0, v___x_3273_);
                    lean_ctor_set(v_reuseFailAlloc_3285_, 1, v_v_3213_);
                    lean_ctor_set(v_reuseFailAlloc_3285_, 2, v_p_3266_);
                    v___x_3275_ = v_reuseFailAlloc_3285_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_3272_ == 0 {
                    lean_ctor_set(v___x_3271_, 0, v___x_3275_);
                    v___x_3277_ = v___x_3271_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3284_, 0, v___x_3275_);
                    lean_ctor_set(v_reuseFailAlloc_3284_, 1, v_k_u2081_3267_);
                    lean_ctor_set(v_reuseFailAlloc_3284_, 2, v_k_u2082_3268_);
                    lean_ctor_set(v_reuseFailAlloc_3284_, 3, v_m_u2082_3269_);
                    v___x_3277_ = v_reuseFailAlloc_3284_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_3265_ == 0 {
                    lean_ctor_set(v___x_3264_, 0, v___x_3277_);
                    v___x_3279_ = v___x_3264_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3283_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3283_, 0, v___x_3277_);
                    v___x_3279_ = v_reuseFailAlloc_3283_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_3229_ == 0 {
                    lean_ctor_set(v___x_3228_, 0, v___x_3279_);
                    v___x_3281_ = v___x_3228_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3282_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3282_, 0, v___x_3279_);
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
                    v_reuseFailAlloc_3296_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_a_3290_);
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
                v___x_3320_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_3320_, 0, v_a_3316_);
                lean_ctor_set(v___x_3320_, 1, v_k_u2081_3312_);
                lean_ctor_set(v___x_3320_, 2, v_k_u2082_3309_);
                lean_ctor_set(v___x_3320_, 3, v_m_u2082_3303_);
                v___x_3321_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3321_, 0, v___x_3320_);
                if v_isShared_3319_ == 0 {
                    lean_ctor_set(v___x_3318_, 0, v___x_3321_);
                    v___x_3323_ = v___x_3318_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3324_, 0, v___x_3321_);
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
                    v_reuseFailAlloc_3332_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_a_3326_);
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
                    v_reuseFailAlloc_3340_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_a_3334_);
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
                    v_reuseFailAlloc_3348_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_a_3342_);
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
    mut v_k_u2082_x27_3351_: *mut LeanObject,
    mut v_m_u2082_3352_: *mut LeanObject,
    mut v_p_u2082_3353_: *mut LeanObject,
    mut v_p_u2081_3354_: *mut LeanObject,
    mut v_a_3355_: *mut LeanObject,
    mut v_a_3356_: *mut LeanObject,
    mut v_a_3357_: *mut LeanObject,
    mut v_a_3358_: *mut LeanObject,
    mut v_a_3359_: *mut LeanObject,
    mut v_a_3360_: *mut LeanObject,
    mut v_a_3361_: *mut LeanObject,
    mut v_a_3362_: *mut LeanObject,
    mut v_a_3363_: *mut LeanObject,
    mut v_a_3364_: *mut LeanObject,
    mut v_a_3365_: *mut LeanObject,
    mut v_a_3366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3367_: *mut LeanObject = core::ptr::null_mut();
    v_res_3367_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(v_k_u2082_x27_3351_, v_m_u2082_3352_, v_p_u2082_3353_, v_p_u2081_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_);
    lean_dec(v_a_3365_);
    lean_dec_ref(v_a_3364_);
    lean_dec(v_a_3363_);
    lean_dec_ref(v_a_3362_);
    lean_dec(v_a_3361_);
    lean_dec_ref(v_a_3360_);
    lean_dec(v_a_3359_);
    lean_dec_ref(v_a_3358_);
    lean_dec(v_a_3357_);
    lean_dec(v_a_3356_);
    lean_dec_ref(v_a_3355_);
    lean_dec(v_k_u2082_x27_3351_);
    return v_res_3367_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_simpM_x3f(
    mut v_p_u2081_3368_: *mut LeanObject,
    mut v_p_u2082_3369_: *mut LeanObject,
    mut v_a_3370_: *mut LeanObject,
    mut v_a_3371_: *mut LeanObject,
    mut v_a_3372_: *mut LeanObject,
    mut v_a_3373_: *mut LeanObject,
    mut v_a_3374_: *mut LeanObject,
    mut v_a_3375_: *mut LeanObject,
    mut v_a_3376_: *mut LeanObject,
    mut v_a_3377_: *mut LeanObject,
    mut v_a_3378_: *mut LeanObject,
    mut v_a_3379_: *mut LeanObject,
    mut v_a_3380_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_u2082_3369_) == 1 {
        let mut v_k_3382_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_3383_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_3384_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
        v_k_3382_ = lean_ctor_get(v_p_u2082_3369_, 0);
        lean_inc(v_k_3382_);
        v_v_3383_ = lean_ctor_get(v_p_u2082_3369_, 1);
        lean_inc(v_v_3383_);
        v_p_3384_ = lean_ctor_get(v_p_u2082_3369_, 2);
        lean_inc_ref(v_p_3384_);
        lean_dec_ref_known(v_p_u2082_3369_, 3);
        v___x_3385_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly_0__Lean_Grind_CommRing_Poly_simpM_x3f_go_x3f(v_k_3382_, v_v_3383_, v_p_3384_, v_p_u2081_3368_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_);
        lean_dec(v_k_3382_);
        return v___x_3385_;
    } else {
        let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_p_u2082_3369_);
        lean_dec_ref(v_p_u2081_3368_);
        v___x_3386_ = lean_box(0);
        v___x_3387_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3387_, 0, v___x_3386_);
        return v___x_3387_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_simpM_x3f___boxed(
    mut v_p_u2081_3388_: *mut LeanObject,
    mut v_p_u2082_3389_: *mut LeanObject,
    mut v_a_3390_: *mut LeanObject,
    mut v_a_3391_: *mut LeanObject,
    mut v_a_3392_: *mut LeanObject,
    mut v_a_3393_: *mut LeanObject,
    mut v_a_3394_: *mut LeanObject,
    mut v_a_3395_: *mut LeanObject,
    mut v_a_3396_: *mut LeanObject,
    mut v_a_3397_: *mut LeanObject,
    mut v_a_3398_: *mut LeanObject,
    mut v_a_3399_: *mut LeanObject,
    mut v_a_3400_: *mut LeanObject,
    mut v_a_3401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3402_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3400_);
    lean_dec_ref(v_a_3399_);
    lean_dec(v_a_3398_);
    lean_dec_ref(v_a_3397_);
    lean_dec(v_a_3396_);
    lean_dec_ref(v_a_3395_);
    lean_dec(v_a_3394_);
    lean_dec_ref(v_a_3393_);
    lean_dec(v_a_3392_);
    lean_dec(v_a_3391_);
    lean_dec_ref(v_a_3390_);
    return v_res_3402_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_Poly(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Arith_Poly(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(builtin);
}
