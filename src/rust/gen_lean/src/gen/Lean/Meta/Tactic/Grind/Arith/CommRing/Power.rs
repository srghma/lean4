// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.Power
// Imports: Init.Grind Lean.Meta.Tactic.Grind.Arith.Simproc Lean.Meta.NatInstTesters Lean.Meta.Tactic.Grind.PropagatorAttr
use crate::r#gen::Init::Grind::{initialize_Init_Grind, runtime_initialize_Init_Grind};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFn_x21, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_isApp, l_Lean_Expr_isConstOf, l_Lean_mkApp7, l_Lean_mkAppB,
};
use crate::r#gen::Lean::Meta::AppBuilder::l_Lean_Meta_mkMul;
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_instantiateMVarsIfMVarApp___redArg;
use crate::r#gen::Lean::Meta::NatInstTesters::{
    initialize_Lean_Meta_NatInstTesters, l_Lean_Meta_Structural_isInstHAddNat___redArg,
    runtime_initialize_Lean_Meta_NatInstTesters,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Simproc::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Simproc, l_Lean_Meta_Grind_Arith_mkSemiringThm,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Simproc,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::PropagatorAttr::{
    initialize_Lean_Meta_Tactic_Grind_PropagatorAttr,
    l_Lean_Meta_Grind_registerBuiltinUpwardPropagator,
    runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l_Lean_Meta_Grind_Goal_getENode, l_Lean_Meta_Grind_getGeneration___redArg,
    l_Lean_Meta_Grind_pushEqCore___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::l_Lean_Meta_Simp_Result_getProof;
use crate::ffi::lean_st_ref_get;
use crate::ffi::{
    lean_grind_internalize, lean_grind_mk_eq_proof, lean_grind_preprocess,
};
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__2_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__3_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__4_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 111, 119, 95, 97, 100, 100, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject,12050285396929189622 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject,1576265659481040706 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__6_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__7_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 100, 100, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__6_value) as *mut crate::leanh::LeanObject,10393083817453678557 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__7_value) as *mut crate::leanh::LeanObject,10680564408669940870 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__0_value:
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
    m_data: [72, 80, 111, 119, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__1_value:
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
    m_data: [104, 80, 111, 119, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__0_value)
            as *mut crate::leanh::LeanObject,
        12847922472053947547 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__1_value)
            as *mut crate::leanh::LeanObject,
        10422657989269798688 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__3_value:
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
static mut l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__3_value)
            as *mut crate::leanh::LeanObject,
        11442535297760353691 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(
    mut v_x_391_: *mut crate::leanh::LeanObject,
    mut v___y_392_: *mut crate::leanh::LeanObject,
    mut v___y_393_: *mut crate::leanh::LeanObject,
    mut v___y_394_: *mut crate::leanh::LeanObject,
    mut v___y_395_: *mut crate::leanh::LeanObject,
    mut v___y_396_: *mut crate::leanh::LeanObject,
    mut v___y_397_: *mut crate::leanh::LeanObject,
    mut v___y_398_: *mut crate::leanh::LeanObject,
    mut v___y_399_: *mut crate::leanh::LeanObject,
    mut v___y_400_: *mut crate::leanh::LeanObject,
    mut v___y_401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_403_ = crate::leanh::lean_box(0);
    v___x_404_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_404_, 0, v___x_403_);
    return v___x_404_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0___boxed(
    mut v_x_405_: *mut crate::leanh::LeanObject,
    mut v___y_406_: *mut crate::leanh::LeanObject,
    mut v___y_407_: *mut crate::leanh::LeanObject,
    mut v___y_408_: *mut crate::leanh::LeanObject,
    mut v___y_409_: *mut crate::leanh::LeanObject,
    mut v___y_410_: *mut crate::leanh::LeanObject,
    mut v___y_411_: *mut crate::leanh::LeanObject,
    mut v___y_412_: *mut crate::leanh::LeanObject,
    mut v___y_413_: *mut crate::leanh::LeanObject,
    mut v___y_414_: *mut crate::leanh::LeanObject,
    mut v___y_415_: *mut crate::leanh::LeanObject,
    mut v___y_416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_417_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v_x_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_);
    crate::leanh::lean_dec(v___y_415_);
    crate::leanh::lean_dec_ref(v___y_414_);
    crate::leanh::lean_dec(v___y_413_);
    crate::leanh::lean_dec_ref(v___y_412_);
    crate::leanh::lean_dec(v___y_411_);
    crate::leanh::lean_dec_ref(v___y_410_);
    crate::leanh::lean_dec(v___y_409_);
    crate::leanh::lean_dec_ref(v___y_408_);
    crate::leanh::lean_dec(v___y_407_);
    crate::leanh::lean_dec(v___y_406_);
    return v_res_417_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg(
    mut v_a_434_: *mut crate::leanh::LeanObject,
    mut v_a_435_: *mut crate::leanh::LeanObject,
    mut v_e_436_: *mut crate::leanh::LeanObject,
    mut v_a_437_: *mut crate::leanh::LeanObject,
    mut v_a_438_: *mut crate::leanh::LeanObject,
    mut v_a_439_: *mut crate::leanh::LeanObject,
    mut v___y_440_: *mut crate::leanh::LeanObject,
    mut v___y_441_: *mut crate::leanh::LeanObject,
    mut v___y_442_: *mut crate::leanh::LeanObject,
    mut v___y_443_: *mut crate::leanh::LeanObject,
    mut v___y_444_: *mut crate::leanh::LeanObject,
    mut v___y_445_: *mut crate::leanh::LeanObject,
    mut v___y_446_: *mut crate::leanh::LeanObject,
    mut v___y_447_: *mut crate::leanh::LeanObject,
    mut v___y_448_: *mut crate::leanh::LeanObject,
    mut v___y_449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_455_: u8 = 0;
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_self_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_next_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_464_: u8 = 0;
    let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: u8 = 0;
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_484_: u8 = 0;
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_488_: u8 = 0;
    let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: u8 = 0;
    let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_495_: u8 = 0;
    let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: u8 = 0;
    let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: u8 = 0;
    let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_510_: u8 = 0;
    let mut v___x_511_: u8 = 0;
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: u8 = 0;
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: u8 = 0;
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_541_: u8 = 0;
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_545_: u8 = 0;
    let mut v_a_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_549_: u8 = 0;
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_553_: u8 = 0;
    let mut v_a_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_557_: u8 = 0;
    let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_561_: u8 = 0;
    let mut v_a_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_565_: u8 = 0;
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_569_: u8 = 0;
    let mut v_a_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_573_: u8 = 0;
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_577_: u8 = 0;
    let mut v_a_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_581_: u8 = 0;
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_585_: u8 = 0;
    let mut v_a_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_589_: u8 = 0;
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_593_: u8 = 0;
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: u8 = 0;
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_600_: u8 = 0;
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: u8 = 0;
    let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: u8 = 0;
    let mut v___x_610_: u8 = 0;
    let mut v_isSharedCheck_611_: u8 = 0;
    let mut v_a_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_615_: u8 = 0;
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_619_: u8 = 0;
    let mut v_a_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_623_: u8 = 0;
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_627_: u8 = 0;
    let mut v_isSharedCheck_628_: u8 = 0;
    let mut v_unused_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_451_ = lean_st_ref_get(v___y_440_);
                v_snd_452_ = crate::leanh::lean_ctor_get(v_a_439_, 1);
                v_isSharedCheck_628_ = (!crate::leanh::lean_is_exclusive(v_a_439_)) as u8;
                if v_isSharedCheck_628_ == 0 {
                    v_unused_629_ = crate::leanh::lean_ctor_get(v_a_439_, 0);
                    crate::leanh::lean_dec(v_unused_629_);
                    v___x_454_ = v_a_439_;
                    v_isShared_455_ = v_isSharedCheck_628_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_452_);
                    crate::leanh::lean_dec(v_a_439_);
                    v___x_454_ = crate::leanh::lean_box(0);
                    v_isShared_455_ = v_isSharedCheck_628_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_snd_452_);
                v___x_456_ = l_Lean_Meta_Grind_Goal_getENode(
                    v___x_451_, v_snd_452_, v___y_446_, v___y_447_, v___y_448_, v___y_449_,
                );
                crate::leanh::lean_dec(v___x_451_);
                if crate::leanh::lean_obj_tag(v___x_456_) == 0 {
                    v_a_457_ = crate::leanh::lean_ctor_get(v___x_456_, 0);
                    crate::leanh::lean_inc(v_a_457_);
                    crate::leanh::lean_dec_ref_known(v___x_456_, 1);
                    v_self_458_ = crate::leanh::lean_ctor_get(v_a_457_, 0);
                    crate::leanh::lean_inc_ref_n(v_self_458_, 2);
                    v_next_459_ = crate::leanh::lean_ctor_get(v_a_457_, 1);
                    crate::leanh::lean_inc_ref(v_next_459_);
                    crate::leanh::lean_dec(v_a_457_);
                    v___x_460_ =
                        l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_self_458_, v___y_447_);
                    if crate::leanh::lean_obj_tag(v___x_460_) == 0 {
                        v_a_461_ = crate::leanh::lean_ctor_get(v___x_460_, 0);
                        v_isSharedCheck_611_ = (!crate::leanh::lean_is_exclusive(v___x_460_)) as u8;
                        if v_isSharedCheck_611_ == 0 {
                            v___x_463_ = v___x_460_;
                            v_isShared_464_ = v_isSharedCheck_611_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_461_);
                            crate::leanh::lean_dec(v___x_460_);
                            v___x_463_ = crate::leanh::lean_box(0);
                            v_isShared_464_ = v_isSharedCheck_611_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_next_459_);
                        crate::leanh::lean_dec_ref(v_self_458_);
                        crate::leanh::lean_del_object(v___x_454_);
                        crate::leanh::lean_dec(v_snd_452_);
                        crate::leanh::lean_dec_ref(v_a_438_);
                        crate::leanh::lean_dec_ref(v_a_437_);
                        crate::leanh::lean_dec_ref(v_e_436_);
                        crate::leanh::lean_dec_ref(v_a_434_);
                        v_a_612_ = crate::leanh::lean_ctor_get(v___x_460_, 0);
                        v_isSharedCheck_619_ = (!crate::leanh::lean_is_exclusive(v___x_460_)) as u8;
                        if v_isSharedCheck_619_ == 0 {
                            v___x_614_ = v___x_460_;
                            v_isShared_615_ = v_isSharedCheck_619_;
                            state = 25;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_612_);
                            crate::leanh::lean_dec(v___x_460_);
                            v___x_614_ = crate::leanh::lean_box(0);
                            v_isShared_615_ = v_isSharedCheck_619_;
                            state = 25;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_454_);
                    crate::leanh::lean_dec(v_snd_452_);
                    crate::leanh::lean_dec_ref(v_a_438_);
                    crate::leanh::lean_dec_ref(v_a_437_);
                    crate::leanh::lean_dec_ref(v_e_436_);
                    crate::leanh::lean_dec_ref(v_a_434_);
                    v_a_620_ = crate::leanh::lean_ctor_get(v___x_456_, 0);
                    v_isSharedCheck_627_ = (!crate::leanh::lean_is_exclusive(v___x_456_)) as u8;
                    if v_isSharedCheck_627_ == 0 {
                        v___x_622_ = v___x_456_;
                        v_isShared_623_ = v_isSharedCheck_627_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_620_);
                        crate::leanh::lean_dec(v___x_456_);
                        v___x_622_ = crate::leanh::lean_box(0);
                        v_isShared_623_ = v_isSharedCheck_627_;
                        state = 27;
                        continue;
                    }
                }
            }
            2 => {
                v___x_465_ = crate::leanh::lean_box(0);
                v___x_489_ = l_Lean_Expr_cleanupAnnotations(v_a_461_);
                v___x_490_ = l_Lean_Expr_isApp(v___x_489_);
                if v___x_490_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_489_);
                    crate::leanh::lean_dec_ref(v_self_458_);
                    v___x_491_ = crate::leanh::lean_box(0);
                    v___x_492_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_491_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
                    v___y_480_ = v___x_492_;
                    state = 7;
                    continue;
                } else {
                    v_arg_493_ = crate::leanh::lean_ctor_get(v___x_489_, 1);
                    crate::leanh::lean_inc_ref(v_arg_493_);
                    v___x_494_ = l_Lean_Expr_appFnCleanup___redArg(v___x_489_);
                    v___x_495_ = l_Lean_Expr_isApp(v___x_494_);
                    if v___x_495_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_494_);
                        crate::leanh::lean_dec_ref(v_arg_493_);
                        crate::leanh::lean_dec_ref(v_self_458_);
                        v___x_496_ = crate::leanh::lean_box(0);
                        v___x_497_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_496_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
                        v___y_480_ = v___x_497_;
                        state = 7;
                        continue;
                    } else {
                        v_arg_498_ = crate::leanh::lean_ctor_get(v___x_494_, 1);
                        crate::leanh::lean_inc_ref(v_arg_498_);
                        v___x_499_ = l_Lean_Expr_appFnCleanup___redArg(v___x_494_);
                        v___x_500_ = l_Lean_Expr_isApp(v___x_499_);
                        if v___x_500_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_499_);
                            crate::leanh::lean_dec_ref(v_arg_498_);
                            crate::leanh::lean_dec_ref(v_arg_493_);
                            crate::leanh::lean_dec_ref(v_self_458_);
                            v___x_501_ = crate::leanh::lean_box(0);
                            v___x_502_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_501_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
                            v___y_480_ = v___x_502_;
                            state = 7;
                            continue;
                        } else {
                            v_arg_503_ = crate::leanh::lean_ctor_get(v___x_499_, 1);
                            crate::leanh::lean_inc_ref(v_arg_503_);
                            v___x_504_ = l_Lean_Expr_appFnCleanup___redArg(v___x_499_);
                            v___x_505_ = l_Lean_Expr_isApp(v___x_504_);
                            if v___x_505_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_504_);
                                crate::leanh::lean_dec_ref(v_arg_503_);
                                crate::leanh::lean_dec_ref(v_arg_498_);
                                crate::leanh::lean_dec_ref(v_arg_493_);
                                crate::leanh::lean_dec_ref(v_self_458_);
                                v___x_506_ = crate::leanh::lean_box(0);
                                v___x_507_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_506_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
                                v___y_480_ = v___x_507_;
                                state = 7;
                                continue;
                            } else {
                                v_arg_508_ = crate::leanh::lean_ctor_get(v___x_504_, 1);
                                crate::leanh::lean_inc_ref(v_arg_508_);
                                v___x_594_ = l_Lean_Expr_appFnCleanup___redArg(v___x_504_);
                                v___x_595_ = l_Lean_Expr_isApp(v___x_594_);
                                if v___x_595_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_594_);
                                    crate::leanh::lean_dec_ref(v_arg_508_);
                                    crate::leanh::lean_dec_ref(v_arg_503_);
                                    crate::leanh::lean_dec_ref(v_arg_498_);
                                    crate::leanh::lean_dec_ref(v_arg_493_);
                                    crate::leanh::lean_dec_ref(v_self_458_);
                                    v___x_596_ = crate::leanh::lean_box(0);
                                    v___x_597_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_596_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
                                    v___y_480_ = v___x_597_;
                                    state = 7;
                                    continue;
                                } else {
                                    v_arg_598_ = crate::leanh::lean_ctor_get(v___x_594_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_598_);
                                    v___x_599_ = l_Lean_Expr_appFnCleanup___redArg(v___x_594_);
                                    v___x_600_ = l_Lean_Expr_isApp(v___x_599_);
                                    if v___x_600_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_599_);
                                        crate::leanh::lean_dec_ref(v_arg_598_);
                                        crate::leanh::lean_dec_ref(v_arg_508_);
                                        crate::leanh::lean_dec_ref(v_arg_503_);
                                        crate::leanh::lean_dec_ref(v_arg_498_);
                                        crate::leanh::lean_dec_ref(v_arg_493_);
                                        crate::leanh::lean_dec_ref(v_self_458_);
                                        v___x_601_ = crate::leanh::lean_box(0);
                                        v___x_602_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_601_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
                                        v___y_480_ = v___x_602_;
                                        state = 7;
                                        continue;
                                    } else {
                                        v_arg_603_ = crate::leanh::lean_ctor_get(v___x_599_, 1);
                                        crate::leanh::lean_inc_ref(v_arg_603_);
                                        v___x_604_ = l_Lean_Expr_appFnCleanup___redArg(v___x_599_);
                                        v___x_605_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__8;
                                        v___x_606_ = l_Lean_Expr_isConstOf(v___x_604_, v___x_605_);
                                        crate::leanh::lean_dec_ref(v___x_604_);
                                        if v___x_606_ == 0 {
                                            crate::leanh::lean_dec_ref(v_arg_603_);
                                            crate::leanh::lean_dec_ref(v_arg_598_);
                                            crate::leanh::lean_dec_ref(v_arg_508_);
                                            crate::leanh::lean_dec_ref(v_arg_503_);
                                            crate::leanh::lean_dec_ref(v_arg_498_);
                                            crate::leanh::lean_dec_ref(v_arg_493_);
                                            crate::leanh::lean_dec_ref(v_self_458_);
                                            v___x_607_ = crate::leanh::lean_box(0);
                                            v___x_608_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_607_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
                                            v___y_480_ = v___x_608_;
                                            state = 7;
                                            continue;
                                        } else {
                                            v___x_609_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_435_, v_arg_603_);
                                            crate::leanh::lean_dec_ref(v_arg_603_);
                                            if v___x_609_ == 0 {
                                                crate::leanh::lean_dec_ref(v_arg_598_);
                                                v___y_510_ = v___x_609_;
                                                state = 10;
                                                continue;
                                            } else {
                                                v___x_610_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_435_, v_arg_598_);
                                                crate::leanh::lean_dec_ref(v_arg_598_);
                                                v___y_510_ = v___x_610_;
                                                state = 10;
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
            3 => {
                v___x_467_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_next_459_,
                        v_a_434_,
                    );
                if v___x_467_ == 0 {
                    crate::leanh::lean_del_object(v___x_463_);
                    crate::leanh::lean_dec(v_snd_452_);
                    if v_isShared_455_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_454_, 1, v_next_459_);
                        crate::leanh::lean_ctor_set(v___x_454_, 0, v___x_465_);
                        v___x_469_ = v___x_454_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_471_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_465_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_471_, 1, v_next_459_);
                        v___x_469_ = v_reuseFailAlloc_471_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_next_459_);
                    crate::leanh::lean_dec_ref(v_a_438_);
                    crate::leanh::lean_dec_ref(v_a_437_);
                    crate::leanh::lean_dec_ref(v_e_436_);
                    crate::leanh::lean_dec_ref(v_a_434_);
                    v___x_472_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__0;
                    if v_isShared_455_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_454_, 0, v___x_472_);
                        v___x_474_ = v___x_454_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_478_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_472_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_478_, 1, v_snd_452_);
                        v___x_474_ = v_reuseFailAlloc_478_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v_a_439_ = v___x_469_;
                state = 0;
                continue;
            }
            5 => {
                if v_isShared_464_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_463_, 0, v___x_474_);
                    v___x_476_ = v___x_463_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_477_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_474_);
                    v___x_476_ = v_reuseFailAlloc_477_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_476_;
            }
            7 => {
                if crate::leanh::lean_obj_tag(v___y_480_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_480_, 1);
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_del_object(v___x_463_);
                    crate::leanh::lean_dec_ref(v_next_459_);
                    crate::leanh::lean_del_object(v___x_454_);
                    crate::leanh::lean_dec(v_snd_452_);
                    crate::leanh::lean_dec_ref(v_a_438_);
                    crate::leanh::lean_dec_ref(v_a_437_);
                    crate::leanh::lean_dec_ref(v_e_436_);
                    crate::leanh::lean_dec_ref(v_a_434_);
                    v_a_481_ = crate::leanh::lean_ctor_get(v___y_480_, 0);
                    v_isSharedCheck_488_ = (!crate::leanh::lean_is_exclusive(v___y_480_)) as u8;
                    if v_isSharedCheck_488_ == 0 {
                        v___x_483_ = v___y_480_;
                        v_isShared_484_ = v_isSharedCheck_488_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_481_);
                        crate::leanh::lean_dec(v___y_480_);
                        v___x_483_ = crate::leanh::lean_box(0);
                        v_isShared_484_ = v_isSharedCheck_488_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_484_ == 0 {
                    v___x_486_ = v___x_483_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_487_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
                    v___x_486_ = v_reuseFailAlloc_487_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_486_;
            }
            10 => {
                if v___y_510_ == 0 {
                    crate::leanh::lean_dec_ref(v_arg_508_);
                    crate::leanh::lean_dec_ref(v_arg_503_);
                    crate::leanh::lean_dec_ref(v_arg_498_);
                    crate::leanh::lean_dec_ref(v_arg_493_);
                    crate::leanh::lean_dec_ref(v_self_458_);
                    state = 3;
                    continue;
                } else {
                    v___x_511_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_a_435_, v_arg_508_,
                        );
                    crate::leanh::lean_dec_ref(v_arg_508_);
                    if v___x_511_ == 0 {
                        crate::leanh::lean_dec_ref(v_arg_503_);
                        crate::leanh::lean_dec_ref(v_arg_498_);
                        crate::leanh::lean_dec_ref(v_arg_493_);
                        crate::leanh::lean_dec_ref(v_self_458_);
                        state = 3;
                        continue;
                    } else {
                        v___x_512_ =
                            l_Lean_Meta_Structural_isInstHAddNat___redArg(v_arg_503_, v___y_447_);
                        if crate::leanh::lean_obj_tag(v___x_512_) == 0 {
                            v_a_513_ = crate::leanh::lean_ctor_get(v___x_512_, 0);
                            crate::leanh::lean_inc(v_a_513_);
                            crate::leanh::lean_dec_ref_known(v___x_512_, 1);
                            v___x_514_ = (crate::leanh::lean_unbox(v_a_513_) as u8);
                            crate::leanh::lean_dec(v_a_513_);
                            if v___x_514_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_498_);
                                crate::leanh::lean_dec_ref(v_arg_493_);
                                crate::leanh::lean_dec_ref(v_self_458_);
                                state = 3;
                                continue;
                            } else {
                                v___x_515_ = l_Lean_Expr_appFn_x21(v_e_436_);
                                v___x_516_ = l_Lean_Expr_appFn_x21(v___x_515_);
                                crate::leanh::lean_dec_ref(v___x_515_);
                                crate::leanh::lean_inc_ref(v_arg_498_);
                                crate::leanh::lean_inc_ref_n(v_a_437_, 2);
                                crate::leanh::lean_inc_ref(v___x_516_);
                                v___x_517_ = l_Lean_mkAppB(v___x_516_, v_a_437_, v_arg_498_);
                                crate::leanh::lean_inc_ref(v_arg_493_);
                                v___x_518_ = l_Lean_mkAppB(v___x_516_, v_a_437_, v_arg_493_);
                                v___x_519_ = l_Lean_Meta_mkMul(
                                    v___x_517_, v___x_518_, v___y_446_, v___y_447_, v___y_448_,
                                    v___y_449_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_519_) == 0 {
                                    v_a_520_ = crate::leanh::lean_ctor_get(v___x_519_, 0);
                                    crate::leanh::lean_inc(v_a_520_);
                                    crate::leanh::lean_dec_ref_known(v___x_519_, 1);
                                    crate::leanh::lean_inc(v___y_449_);
                                    crate::leanh::lean_inc_ref(v___y_448_);
                                    crate::leanh::lean_inc(v___y_447_);
                                    crate::leanh::lean_inc_ref(v___y_446_);
                                    crate::leanh::lean_inc(v___y_445_);
                                    crate::leanh::lean_inc_ref(v___y_444_);
                                    crate::leanh::lean_inc(v___y_443_);
                                    crate::leanh::lean_inc_ref(v___y_442_);
                                    crate::leanh::lean_inc(v___y_441_);
                                    crate::leanh::lean_inc(v___y_440_);
                                    v___x_521_ = lean_grind_preprocess(
                                        v_a_520_, v___y_440_, v___y_441_, v___y_442_, v___y_443_,
                                        v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_,
                                        v___y_449_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_521_) == 0 {
                                        v_a_522_ = crate::leanh::lean_ctor_get(v___x_521_, 0);
                                        crate::leanh::lean_inc(v_a_522_);
                                        crate::leanh::lean_dec_ref_known(v___x_521_, 1);
                                        v___x_523_ = l_Lean_Meta_Grind_getGeneration___redArg(
                                            v_e_436_, v___y_440_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_523_) == 0 {
                                            v_a_524_ = crate::leanh::lean_ctor_get(v___x_523_, 0);
                                            crate::leanh::lean_inc(v_a_524_);
                                            crate::leanh::lean_dec_ref_known(v___x_523_, 1);
                                            v_expr_525_ = crate::leanh::lean_ctor_get(v_a_522_, 0);
                                            crate::leanh::lean_inc_ref_n(v_expr_525_, 2);
                                            crate::leanh::lean_inc(v___y_449_);
                                            crate::leanh::lean_inc_ref(v___y_448_);
                                            crate::leanh::lean_inc(v___y_447_);
                                            crate::leanh::lean_inc_ref(v___y_446_);
                                            crate::leanh::lean_inc(v___y_445_);
                                            crate::leanh::lean_inc_ref(v___y_444_);
                                            crate::leanh::lean_inc(v___y_443_);
                                            crate::leanh::lean_inc_ref(v___y_442_);
                                            crate::leanh::lean_inc(v___y_441_);
                                            crate::leanh::lean_inc(v___y_440_);
                                            v___x_526_ = lean_grind_internalize(
                                                v_expr_525_,
                                                v_a_524_,
                                                v___x_465_,
                                                v___y_440_,
                                                v___y_441_,
                                                v___y_442_,
                                                v___y_443_,
                                                v___y_444_,
                                                v___y_445_,
                                                v___y_446_,
                                                v___y_447_,
                                                v___y_448_,
                                                v___y_449_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_526_) == 0 {
                                                crate::leanh::lean_dec_ref_known(v___x_526_, 1);
                                                v___x_527_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__5;
                                                crate::leanh::lean_inc_ref(v_a_438_);
                                                v___x_528_ = l_Lean_Meta_Grind_Arith_mkSemiringThm(
                                                    v___x_527_, v_a_438_, v___y_446_, v___y_447_,
                                                    v___y_448_, v___y_449_,
                                                );
                                                if crate::leanh::lean_obj_tag(v___x_528_) == 0 {
                                                    v_a_529_ =
                                                        crate::leanh::lean_ctor_get(v___x_528_, 0);
                                                    crate::leanh::lean_inc(v_a_529_);
                                                    crate::leanh::lean_dec_ref_known(v___x_528_, 1);
                                                    if crate::leanh::lean_obj_tag(v_a_529_) == 1 {
                                                        v_val_530_ = crate::leanh::lean_ctor_get(
                                                            v_a_529_, 0,
                                                        );
                                                        crate::leanh::lean_inc(v_val_530_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v_a_529_, 1,
                                                        );
                                                        crate::leanh::lean_inc(v___y_449_);
                                                        crate::leanh::lean_inc_ref(v___y_448_);
                                                        crate::leanh::lean_inc(v___y_447_);
                                                        crate::leanh::lean_inc_ref(v___y_446_);
                                                        crate::leanh::lean_inc(v___y_445_);
                                                        crate::leanh::lean_inc_ref(v___y_444_);
                                                        crate::leanh::lean_inc(v___y_443_);
                                                        crate::leanh::lean_inc_ref(v___y_442_);
                                                        crate::leanh::lean_inc(v___y_441_);
                                                        crate::leanh::lean_inc(v___y_440_);
                                                        crate::leanh::lean_inc_ref(v_a_434_);
                                                        v___x_531_ = lean_grind_mk_eq_proof(
                                                            v_a_434_,
                                                            v_self_458_,
                                                            v___y_440_,
                                                            v___y_441_,
                                                            v___y_442_,
                                                            v___y_443_,
                                                            v___y_444_,
                                                            v___y_445_,
                                                            v___y_446_,
                                                            v___y_447_,
                                                            v___y_448_,
                                                            v___y_449_,
                                                        );
                                                        if crate::leanh::lean_obj_tag(v___x_531_)
                                                            == 0
                                                        {
                                                            v_a_532_ = crate::leanh::lean_ctor_get(
                                                                v___x_531_, 0,
                                                            );
                                                            crate::leanh::lean_inc(v_a_532_);
                                                            crate::leanh::lean_dec_ref_known(
                                                                v___x_531_, 1,
                                                            );
                                                            v___x_533_ =
                                                                l_Lean_Meta_Simp_Result_getProof(
                                                                    v_a_522_, v___y_446_,
                                                                    v___y_447_, v___y_448_,
                                                                    v___y_449_,
                                                                );
                                                            if crate::leanh::lean_obj_tag(
                                                                v___x_533_,
                                                            ) == 0
                                                            {
                                                                v_a_534_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_533_, 0,
                                                                    );
                                                                crate::leanh::lean_inc(v_a_534_);
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v___x_533_, 1,
                                                                );
                                                                crate::leanh::lean_inc_ref(
                                                                    v_a_434_,
                                                                );
                                                                crate::leanh::lean_inc_ref(
                                                                    v_expr_525_,
                                                                );
                                                                crate::leanh::lean_inc_ref(
                                                                    v_a_437_,
                                                                );
                                                                v___x_535_ = l_Lean_mkApp7(
                                                                    v_val_530_,
                                                                    v_a_437_,
                                                                    v_expr_525_,
                                                                    v_a_434_,
                                                                    v_arg_498_,
                                                                    v_arg_493_,
                                                                    v_a_532_,
                                                                    v_a_534_,
                                                                );
                                                                v___x_536_ = 0;
                                                                crate::leanh::lean_inc_ref(
                                                                    v_e_436_,
                                                                );
                                                                v___x_537_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_436_, v_expr_525_, v___x_535_, v___x_536_, v___y_440_, v___y_442_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
                                                                v___y_480_ = v___x_537_;
                                                                state = 7;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_dec(v_a_532_);
                                                                crate::leanh::lean_dec(v_val_530_);
                                                                crate::leanh::lean_dec_ref(
                                                                    v_expr_525_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_498_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_493_,
                                                                );
                                                                crate::leanh::lean_del_object(
                                                                    v___x_463_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_next_459_,
                                                                );
                                                                crate::leanh::lean_del_object(
                                                                    v___x_454_,
                                                                );
                                                                crate::leanh::lean_dec(v_snd_452_);
                                                                crate::leanh::lean_dec_ref(
                                                                    v_a_438_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_a_437_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_e_436_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_a_434_,
                                                                );
                                                                v_a_538_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_533_, 0,
                                                                    );
                                                                v_isSharedCheck_545_ = (!crate::leanh::lean_is_exclusive(v___x_533_)) as u8;
                                                                if v_isSharedCheck_545_ == 0 {
                                                                    v___x_540_ = v___x_533_;
                                                                    v_isShared_541_ =
                                                                        v_isSharedCheck_545_;
                                                                    state = 11;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_inc(
                                                                        v_a_538_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_533_,
                                                                    );
                                                                    v___x_540_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v_isShared_541_ =
                                                                        v_isSharedCheck_545_;
                                                                    state = 11;
                                                                    continue;
                                                                }
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec(v_val_530_);
                                                            crate::leanh::lean_dec_ref(v_expr_525_);
                                                            crate::leanh::lean_dec(v_a_522_);
                                                            crate::leanh::lean_dec_ref(v_arg_498_);
                                                            crate::leanh::lean_dec_ref(v_arg_493_);
                                                            crate::leanh::lean_del_object(
                                                                v___x_463_,
                                                            );
                                                            crate::leanh::lean_dec_ref(v_next_459_);
                                                            crate::leanh::lean_del_object(
                                                                v___x_454_,
                                                            );
                                                            crate::leanh::lean_dec(v_snd_452_);
                                                            crate::leanh::lean_dec_ref(v_a_438_);
                                                            crate::leanh::lean_dec_ref(v_a_437_);
                                                            crate::leanh::lean_dec_ref(v_e_436_);
                                                            crate::leanh::lean_dec_ref(v_a_434_);
                                                            v_a_546_ = crate::leanh::lean_ctor_get(
                                                                v___x_531_, 0,
                                                            );
                                                            v_isSharedCheck_553_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_531_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_553_ == 0 {
                                                                v___x_548_ = v___x_531_;
                                                                v_isShared_549_ =
                                                                    v_isSharedCheck_553_;
                                                                state = 13;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_546_);
                                                                crate::leanh::lean_dec(v___x_531_);
                                                                v___x_548_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_549_ =
                                                                    v_isSharedCheck_553_;
                                                                state = 13;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec(v_a_529_);
                                                        crate::leanh::lean_dec_ref(v_expr_525_);
                                                        crate::leanh::lean_dec(v_a_522_);
                                                        crate::leanh::lean_dec_ref(v_arg_498_);
                                                        crate::leanh::lean_dec_ref(v_arg_493_);
                                                        crate::leanh::lean_dec_ref(v_self_458_);
                                                        state = 3;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v_expr_525_);
                                                    crate::leanh::lean_dec(v_a_522_);
                                                    crate::leanh::lean_dec_ref(v_arg_498_);
                                                    crate::leanh::lean_dec_ref(v_arg_493_);
                                                    crate::leanh::lean_del_object(v___x_463_);
                                                    crate::leanh::lean_dec_ref(v_next_459_);
                                                    crate::leanh::lean_dec_ref(v_self_458_);
                                                    crate::leanh::lean_del_object(v___x_454_);
                                                    crate::leanh::lean_dec(v_snd_452_);
                                                    crate::leanh::lean_dec_ref(v_a_438_);
                                                    crate::leanh::lean_dec_ref(v_a_437_);
                                                    crate::leanh::lean_dec_ref(v_e_436_);
                                                    crate::leanh::lean_dec_ref(v_a_434_);
                                                    v_a_554_ =
                                                        crate::leanh::lean_ctor_get(v___x_528_, 0);
                                                    v_isSharedCheck_561_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_528_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_561_ == 0 {
                                                        v___x_556_ = v___x_528_;
                                                        v_isShared_557_ = v_isSharedCheck_561_;
                                                        state = 15;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_554_);
                                                        crate::leanh::lean_dec(v___x_528_);
                                                        v___x_556_ = crate::leanh::lean_box(0);
                                                        v_isShared_557_ = v_isSharedCheck_561_;
                                                        state = 15;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v_expr_525_);
                                                crate::leanh::lean_dec(v_a_522_);
                                                crate::leanh::lean_dec_ref(v_arg_498_);
                                                crate::leanh::lean_dec_ref(v_arg_493_);
                                                crate::leanh::lean_dec_ref(v_self_458_);
                                                v___y_480_ = v___x_526_;
                                                state = 7;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_a_522_);
                                            crate::leanh::lean_dec_ref(v_arg_498_);
                                            crate::leanh::lean_dec_ref(v_arg_493_);
                                            crate::leanh::lean_del_object(v___x_463_);
                                            crate::leanh::lean_dec_ref(v_next_459_);
                                            crate::leanh::lean_dec_ref(v_self_458_);
                                            crate::leanh::lean_del_object(v___x_454_);
                                            crate::leanh::lean_dec(v_snd_452_);
                                            crate::leanh::lean_dec_ref(v_a_438_);
                                            crate::leanh::lean_dec_ref(v_a_437_);
                                            crate::leanh::lean_dec_ref(v_e_436_);
                                            crate::leanh::lean_dec_ref(v_a_434_);
                                            v_a_562_ = crate::leanh::lean_ctor_get(v___x_523_, 0);
                                            v_isSharedCheck_569_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_523_))
                                                    as u8;
                                            if v_isSharedCheck_569_ == 0 {
                                                v___x_564_ = v___x_523_;
                                                v_isShared_565_ = v_isSharedCheck_569_;
                                                state = 17;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_562_);
                                                crate::leanh::lean_dec(v___x_523_);
                                                v___x_564_ = crate::leanh::lean_box(0);
                                                v_isShared_565_ = v_isSharedCheck_569_;
                                                state = 17;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_arg_498_);
                                        crate::leanh::lean_dec_ref(v_arg_493_);
                                        crate::leanh::lean_del_object(v___x_463_);
                                        crate::leanh::lean_dec_ref(v_next_459_);
                                        crate::leanh::lean_dec_ref(v_self_458_);
                                        crate::leanh::lean_del_object(v___x_454_);
                                        crate::leanh::lean_dec(v_snd_452_);
                                        crate::leanh::lean_dec_ref(v_a_438_);
                                        crate::leanh::lean_dec_ref(v_a_437_);
                                        crate::leanh::lean_dec_ref(v_e_436_);
                                        crate::leanh::lean_dec_ref(v_a_434_);
                                        v_a_570_ = crate::leanh::lean_ctor_get(v___x_521_, 0);
                                        v_isSharedCheck_577_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_521_)) as u8;
                                        if v_isSharedCheck_577_ == 0 {
                                            v___x_572_ = v___x_521_;
                                            v_isShared_573_ = v_isSharedCheck_577_;
                                            state = 19;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_570_);
                                            crate::leanh::lean_dec(v___x_521_);
                                            v___x_572_ = crate::leanh::lean_box(0);
                                            v_isShared_573_ = v_isSharedCheck_577_;
                                            state = 19;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_arg_498_);
                                    crate::leanh::lean_dec_ref(v_arg_493_);
                                    crate::leanh::lean_del_object(v___x_463_);
                                    crate::leanh::lean_dec_ref(v_next_459_);
                                    crate::leanh::lean_dec_ref(v_self_458_);
                                    crate::leanh::lean_del_object(v___x_454_);
                                    crate::leanh::lean_dec(v_snd_452_);
                                    crate::leanh::lean_dec_ref(v_a_438_);
                                    crate::leanh::lean_dec_ref(v_a_437_);
                                    crate::leanh::lean_dec_ref(v_e_436_);
                                    crate::leanh::lean_dec_ref(v_a_434_);
                                    v_a_578_ = crate::leanh::lean_ctor_get(v___x_519_, 0);
                                    v_isSharedCheck_585_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_519_)) as u8;
                                    if v_isSharedCheck_585_ == 0 {
                                        v___x_580_ = v___x_519_;
                                        v_isShared_581_ = v_isSharedCheck_585_;
                                        state = 21;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_578_);
                                        crate::leanh::lean_dec(v___x_519_);
                                        v___x_580_ = crate::leanh::lean_box(0);
                                        v_isShared_581_ = v_isSharedCheck_585_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_arg_498_);
                            crate::leanh::lean_dec_ref(v_arg_493_);
                            crate::leanh::lean_del_object(v___x_463_);
                            crate::leanh::lean_dec_ref(v_next_459_);
                            crate::leanh::lean_dec_ref(v_self_458_);
                            crate::leanh::lean_del_object(v___x_454_);
                            crate::leanh::lean_dec(v_snd_452_);
                            crate::leanh::lean_dec_ref(v_a_438_);
                            crate::leanh::lean_dec_ref(v_a_437_);
                            crate::leanh::lean_dec_ref(v_e_436_);
                            crate::leanh::lean_dec_ref(v_a_434_);
                            v_a_586_ = crate::leanh::lean_ctor_get(v___x_512_, 0);
                            v_isSharedCheck_593_ =
                                (!crate::leanh::lean_is_exclusive(v___x_512_)) as u8;
                            if v_isSharedCheck_593_ == 0 {
                                v___x_588_ = v___x_512_;
                                v_isShared_589_ = v_isSharedCheck_593_;
                                state = 23;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_586_);
                                crate::leanh::lean_dec(v___x_512_);
                                v___x_588_ = crate::leanh::lean_box(0);
                                v_isShared_589_ = v_isSharedCheck_593_;
                                state = 23;
                                continue;
                            }
                        }
                    }
                }
            }
            11 => {
                if v_isShared_541_ == 0 {
                    v___x_543_ = v___x_540_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_544_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
                    v___x_543_ = v_reuseFailAlloc_544_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_543_;
            }
            13 => {
                if v_isShared_549_ == 0 {
                    v___x_551_ = v___x_548_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_552_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_546_);
                    v___x_551_ = v_reuseFailAlloc_552_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_551_;
            }
            15 => {
                if v_isShared_557_ == 0 {
                    v___x_559_ = v___x_556_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_560_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
                    v___x_559_ = v_reuseFailAlloc_560_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_559_;
            }
            17 => {
                if v_isShared_565_ == 0 {
                    v___x_567_ = v___x_564_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_568_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_562_);
                    v___x_567_ = v_reuseFailAlloc_568_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_567_;
            }
            19 => {
                if v_isShared_573_ == 0 {
                    v___x_575_ = v___x_572_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_576_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
                    v___x_575_ = v_reuseFailAlloc_576_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_575_;
            }
            21 => {
                if v_isShared_581_ == 0 {
                    v___x_583_ = v___x_580_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_584_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
                    v___x_583_ = v_reuseFailAlloc_584_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_583_;
            }
            23 => {
                if v_isShared_589_ == 0 {
                    v___x_591_ = v___x_588_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_592_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
                    v___x_591_ = v_reuseFailAlloc_592_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_591_;
            }
            25 => {
                if v_isShared_615_ == 0 {
                    v___x_617_ = v___x_614_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_618_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
                    v___x_617_ = v_reuseFailAlloc_618_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_617_;
            }
            27 => {
                if v_isShared_623_ == 0 {
                    v___x_625_ = v___x_622_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_626_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
                    v___x_625_ = v_reuseFailAlloc_626_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_625_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_630_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_a_631_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_e_632_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_a_633_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_a_634_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_a_635_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_636_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_637_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_638_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_639_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_640_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_641_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_642_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_643_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_644_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_645_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_646_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_647_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg(v_a_630_, v_a_631_, v_e_632_, v_a_633_, v_a_634_, v_a_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
    crate::leanh::lean_dec(v___y_645_);
    crate::leanh::lean_dec_ref(v___y_644_);
    crate::leanh::lean_dec(v___y_643_);
    crate::leanh::lean_dec_ref(v___y_642_);
    crate::leanh::lean_dec(v___y_641_);
    crate::leanh::lean_dec_ref(v___y_640_);
    crate::leanh::lean_dec(v___y_639_);
    crate::leanh::lean_dec_ref(v___y_638_);
    crate::leanh::lean_dec(v___y_637_);
    crate::leanh::lean_dec(v___y_636_);
    crate::leanh::lean_dec_ref(v_a_631_);
    return v_res_647_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_propagatePower(
    mut v_e_656_: *mut crate::leanh::LeanObject,
    mut v_a_657_: *mut crate::leanh::LeanObject,
    mut v_a_658_: *mut crate::leanh::LeanObject,
    mut v_a_659_: *mut crate::leanh::LeanObject,
    mut v_a_660_: *mut crate::leanh::LeanObject,
    mut v_a_661_: *mut crate::leanh::LeanObject,
    mut v_a_662_: *mut crate::leanh::LeanObject,
    mut v_a_663_: *mut crate::leanh::LeanObject,
    mut v_a_664_: *mut crate::leanh::LeanObject,
    mut v_a_665_: *mut crate::leanh::LeanObject,
    mut v_a_666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: u8 = 0;
    let mut v_arg_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: u8 = 0;
    let mut v_arg_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: u8 = 0;
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: u8 = 0;
    let mut v_arg_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: u8 = 0;
    let mut v_arg_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: u8 = 0;
    let mut v_arg_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: u8 = 0;
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: u8 = 0;
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: u8 = 0;
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_705_: u8 = 0;
    let mut v_fst_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_715_: u8 = 0;
    let mut v_a_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_719_: u8 = 0;
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_723_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_656_);
                v___x_671_ = l_Lean_Expr_cleanupAnnotations(v_e_656_);
                v___x_672_ = l_Lean_Expr_isApp(v___x_671_);
                if v___x_672_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_671_);
                    crate::leanh::lean_dec_ref(v_e_656_);
                    state = 1;
                    continue;
                } else {
                    v_arg_673_ = crate::leanh::lean_ctor_get(v___x_671_, 1);
                    crate::leanh::lean_inc_ref(v_arg_673_);
                    v___x_674_ = l_Lean_Expr_appFnCleanup___redArg(v___x_671_);
                    v___x_675_ = l_Lean_Expr_isApp(v___x_674_);
                    if v___x_675_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_674_);
                        crate::leanh::lean_dec_ref(v_arg_673_);
                        crate::leanh::lean_dec_ref(v_e_656_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_676_ = crate::leanh::lean_ctor_get(v___x_674_, 1);
                        crate::leanh::lean_inc_ref(v_arg_676_);
                        v___x_677_ = l_Lean_Expr_appFnCleanup___redArg(v___x_674_);
                        v___x_678_ = l_Lean_Expr_isApp(v___x_677_);
                        if v___x_678_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_677_);
                            crate::leanh::lean_dec_ref(v_arg_676_);
                            crate::leanh::lean_dec_ref(v_arg_673_);
                            crate::leanh::lean_dec_ref(v_e_656_);
                            state = 1;
                            continue;
                        } else {
                            v___x_679_ = l_Lean_Expr_appFnCleanup___redArg(v___x_677_);
                            v___x_680_ = l_Lean_Expr_isApp(v___x_679_);
                            if v___x_680_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_679_);
                                crate::leanh::lean_dec_ref(v_arg_676_);
                                crate::leanh::lean_dec_ref(v_arg_673_);
                                crate::leanh::lean_dec_ref(v_e_656_);
                                state = 1;
                                continue;
                            } else {
                                v_arg_681_ = crate::leanh::lean_ctor_get(v___x_679_, 1);
                                crate::leanh::lean_inc_ref(v_arg_681_);
                                v___x_682_ = l_Lean_Expr_appFnCleanup___redArg(v___x_679_);
                                v___x_683_ = l_Lean_Expr_isApp(v___x_682_);
                                if v___x_683_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_682_);
                                    crate::leanh::lean_dec_ref(v_arg_681_);
                                    crate::leanh::lean_dec_ref(v_arg_676_);
                                    crate::leanh::lean_dec_ref(v_arg_673_);
                                    crate::leanh::lean_dec_ref(v_e_656_);
                                    state = 1;
                                    continue;
                                } else {
                                    v_arg_684_ = crate::leanh::lean_ctor_get(v___x_682_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_684_);
                                    v___x_685_ = l_Lean_Expr_appFnCleanup___redArg(v___x_682_);
                                    v___x_686_ = l_Lean_Expr_isApp(v___x_685_);
                                    if v___x_686_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_685_);
                                        crate::leanh::lean_dec_ref(v_arg_684_);
                                        crate::leanh::lean_dec_ref(v_arg_681_);
                                        crate::leanh::lean_dec_ref(v_arg_676_);
                                        crate::leanh::lean_dec_ref(v_arg_673_);
                                        crate::leanh::lean_dec_ref(v_e_656_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v_arg_687_ = crate::leanh::lean_ctor_get(v___x_685_, 1);
                                        crate::leanh::lean_inc_ref(v_arg_687_);
                                        v___x_688_ = l_Lean_Expr_appFnCleanup___redArg(v___x_685_);
                                        v___x_689_ = l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2;
                                        v___x_690_ = l_Lean_Expr_isConstOf(v___x_688_, v___x_689_);
                                        crate::leanh::lean_dec_ref(v___x_688_);
                                        if v___x_690_ == 0 {
                                            crate::leanh::lean_dec_ref(v_arg_687_);
                                            crate::leanh::lean_dec_ref(v_arg_684_);
                                            crate::leanh::lean_dec_ref(v_arg_681_);
                                            crate::leanh::lean_dec_ref(v_arg_676_);
                                            crate::leanh::lean_dec_ref(v_arg_673_);
                                            crate::leanh::lean_dec_ref(v_e_656_);
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc_ref(v_arg_684_);
                                            v___x_691_ = l_Lean_Expr_cleanupAnnotations(v_arg_684_);
                                            v___x_692_ = l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__4;
                                            v___x_693_ =
                                                l_Lean_Expr_isConstOf(v___x_691_, v___x_692_);
                                            crate::leanh::lean_dec_ref(v___x_691_);
                                            if v___x_693_ == 0 {
                                                crate::leanh::lean_dec_ref(v_arg_687_);
                                                crate::leanh::lean_dec_ref(v_arg_684_);
                                                crate::leanh::lean_dec_ref(v_arg_681_);
                                                crate::leanh::lean_dec_ref(v_arg_676_);
                                                crate::leanh::lean_dec_ref(v_arg_673_);
                                                crate::leanh::lean_dec_ref(v_e_656_);
                                                v___x_694_ = crate::leanh::lean_box(0);
                                                v___x_695_ =
                                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_695_, 0, v___x_694_,
                                                );
                                                return v___x_695_;
                                            } else {
                                                v___x_696_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_687_, v_arg_681_);
                                                crate::leanh::lean_dec_ref(v_arg_681_);
                                                if v___x_696_ == 0 {
                                                    crate::leanh::lean_dec_ref(v_arg_687_);
                                                    crate::leanh::lean_dec_ref(v_arg_684_);
                                                    crate::leanh::lean_dec_ref(v_arg_676_);
                                                    crate::leanh::lean_dec_ref(v_arg_673_);
                                                    crate::leanh::lean_dec_ref(v_e_656_);
                                                    v___x_697_ = crate::leanh::lean_box(0);
                                                    v___x_698_ = crate::leanh::lean_alloc_ctor(
                                                        0,
                                                        1,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_698_, 0, v___x_697_,
                                                    );
                                                    return v___x_698_;
                                                } else {
                                                    v___x_699_ = crate::leanh::lean_box(0);
                                                    crate::leanh::lean_inc_ref(v_arg_673_);
                                                    v___x_700_ = crate::leanh::lean_alloc_ctor(
                                                        0,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_700_, 0, v___x_699_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_700_, 1, v_arg_673_,
                                                    );
                                                    v___x_701_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg(v_arg_673_, v_arg_684_, v_e_656_, v_arg_676_, v_arg_687_, v___x_700_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_);
                                                    crate::leanh::lean_dec_ref(v_arg_684_);
                                                    if crate::leanh::lean_obj_tag(v___x_701_) == 0 {
                                                        v_a_702_ = crate::leanh::lean_ctor_get(
                                                            v___x_701_, 0,
                                                        );
                                                        v_isSharedCheck_715_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_701_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_715_ == 0 {
                                                            v___x_704_ = v___x_701_;
                                                            v_isShared_705_ = v_isSharedCheck_715_;
                                                            state = 2;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_702_);
                                                            crate::leanh::lean_dec(v___x_701_);
                                                            v___x_704_ = crate::leanh::lean_box(0);
                                                            v_isShared_705_ = v_isSharedCheck_715_;
                                                            state = 2;
                                                            continue;
                                                        }
                                                    } else {
                                                        v_a_716_ = crate::leanh::lean_ctor_get(
                                                            v___x_701_, 0,
                                                        );
                                                        v_isSharedCheck_723_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_701_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_723_ == 0 {
                                                            v___x_718_ = v___x_701_;
                                                            v_isShared_719_ = v_isSharedCheck_723_;
                                                            state = 5;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_716_);
                                                            crate::leanh::lean_dec(v___x_701_);
                                                            v___x_718_ = crate::leanh::lean_box(0);
                                                            v_isShared_719_ = v_isSharedCheck_723_;
                                                            state = 5;
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
            }
            1 => {
                v___x_669_ = crate::leanh::lean_box(0);
                v___x_670_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_670_, 0, v___x_669_);
                return v___x_670_;
            }
            2 => {
                v_fst_706_ = crate::leanh::lean_ctor_get(v_a_702_, 0);
                crate::leanh::lean_inc(v_fst_706_);
                crate::leanh::lean_dec(v_a_702_);
                if crate::leanh::lean_obj_tag(v_fst_706_) == 0 {
                    v___x_707_ = crate::leanh::lean_box(0);
                    if v_isShared_705_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_704_, 0, v___x_707_);
                        v___x_709_ = v___x_704_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_710_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
                        v___x_709_ = v_reuseFailAlloc_710_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_val_711_ = crate::leanh::lean_ctor_get(v_fst_706_, 0);
                    crate::leanh::lean_inc(v_val_711_);
                    crate::leanh::lean_dec_ref_known(v_fst_706_, 1);
                    if v_isShared_705_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_704_, 0, v_val_711_);
                        v___x_713_ = v___x_704_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_714_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_714_, 0, v_val_711_);
                        v___x_713_ = v_reuseFailAlloc_714_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_709_;
            }
            4 => {
                return v___x_713_;
            }
            5 => {
                if v_isShared_719_ == 0 {
                    v___x_721_ = v___x_718_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_722_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_716_);
                    v___x_721_ = v_reuseFailAlloc_722_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_721_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_propagatePower___boxed(
    mut v_e_724_: *mut crate::leanh::LeanObject,
    mut v_a_725_: *mut crate::leanh::LeanObject,
    mut v_a_726_: *mut crate::leanh::LeanObject,
    mut v_a_727_: *mut crate::leanh::LeanObject,
    mut v_a_728_: *mut crate::leanh::LeanObject,
    mut v_a_729_: *mut crate::leanh::LeanObject,
    mut v_a_730_: *mut crate::leanh::LeanObject,
    mut v_a_731_: *mut crate::leanh::LeanObject,
    mut v_a_732_: *mut crate::leanh::LeanObject,
    mut v_a_733_: *mut crate::leanh::LeanObject,
    mut v_a_734_: *mut crate::leanh::LeanObject,
    mut v_a_735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_736_ = l_Lean_Meta_Grind_Arith_CommRing_propagatePower(
        v_e_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_,
        v_a_733_, v_a_734_,
    );
    crate::leanh::lean_dec(v_a_734_);
    crate::leanh::lean_dec_ref(v_a_733_);
    crate::leanh::lean_dec(v_a_732_);
    crate::leanh::lean_dec_ref(v_a_731_);
    crate::leanh::lean_dec(v_a_730_);
    crate::leanh::lean_dec_ref(v_a_729_);
    crate::leanh::lean_dec(v_a_728_);
    crate::leanh::lean_dec_ref(v_a_727_);
    crate::leanh::lean_dec(v_a_726_);
    crate::leanh::lean_dec(v_a_725_);
    return v_res_736_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0(
    mut v_a_737_: *mut crate::leanh::LeanObject,
    mut v_a_738_: *mut crate::leanh::LeanObject,
    mut v_e_739_: *mut crate::leanh::LeanObject,
    mut v_a_740_: *mut crate::leanh::LeanObject,
    mut v_a_741_: *mut crate::leanh::LeanObject,
    mut v_inst_742_: *mut crate::leanh::LeanObject,
    mut v_a_743_: *mut crate::leanh::LeanObject,
    mut v___y_744_: *mut crate::leanh::LeanObject,
    mut v___y_745_: *mut crate::leanh::LeanObject,
    mut v___y_746_: *mut crate::leanh::LeanObject,
    mut v___y_747_: *mut crate::leanh::LeanObject,
    mut v___y_748_: *mut crate::leanh::LeanObject,
    mut v___y_749_: *mut crate::leanh::LeanObject,
    mut v___y_750_: *mut crate::leanh::LeanObject,
    mut v___y_751_: *mut crate::leanh::LeanObject,
    mut v___y_752_: *mut crate::leanh::LeanObject,
    mut v___y_753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_755_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg(v_a_737_, v_a_738_, v_e_739_, v_a_740_, v_a_741_, v_a_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
    return v___x_755_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_756_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_a_757_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_e_758_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_a_759_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_a_760_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_inst_761_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_a_762_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_763_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_764_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_765_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_766_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_767_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_768_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_769_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_770_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_771_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_772_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_773_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_res_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_774_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0(v_a_756_, v_a_757_, v_e_758_, v_a_759_, v_a_760_, v_inst_761_, v_a_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
    crate::leanh::lean_dec(v___y_772_);
    crate::leanh::lean_dec_ref(v___y_771_);
    crate::leanh::lean_dec(v___y_770_);
    crate::leanh::lean_dec_ref(v___y_769_);
    crate::leanh::lean_dec(v___y_768_);
    crate::leanh::lean_dec_ref(v___y_767_);
    crate::leanh::lean_dec(v___y_766_);
    crate::leanh::lean_dec_ref(v___y_765_);
    crate::leanh::lean_dec(v___y_764_);
    crate::leanh::lean_dec(v___y_763_);
    crate::leanh::lean_dec_ref(v_a_757_);
    return v_res_774_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_0__Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_14_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_776_ = l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2;
    v___x_777_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_propagatePower___boxed as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_778_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_776_, v___x_777_);
    return v___x_778_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_0__Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_14____boxed(
    mut v_a_779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_780_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_0__Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_14_();
    return v_res_780_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(
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
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(builtin);
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
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_0__Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_14_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(
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
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(builtin);
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
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(builtin);
}
