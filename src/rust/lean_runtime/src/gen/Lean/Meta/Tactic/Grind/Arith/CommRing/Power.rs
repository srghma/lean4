// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.Power
// Imports: Init.Grind Lean.Meta.Tactic.Grind.Arith.Simproc Lean.Meta.NatInstTesters Lean.Meta.Tactic.Grind.PropagatorAttr
use crate::r#gen::Init::Grind::{initialize_Init_Grind, runtime_initialize_Init_Grind};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4};
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
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Meta::Tactic::Grind::Types::{
    lean_grind_internalize, lean_grind_mk_eq_proof, lean_grind_preprocess,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_tag, lean_unbox,
};
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__2_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__3_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__3_value) as *mut LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__4_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 111, 119, 95, 97, 100, 100, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__4_value) as *mut LeanObject;
static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__2_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__3_value) as *mut LeanObject,12050285396929189622 as *mut LeanObject] };
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__4_value) as *mut LeanObject,1576265659481040706 as *mut LeanObject] };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__5_value) as *mut LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__6_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__6_value) as *mut LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__7_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 100, 100, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__7_value) as *mut LeanObject;
static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__6_value) as *mut LeanObject,10393083817453678557 as *mut LeanObject] };
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__7_value) as *mut LeanObject,10680564408669940870 as *mut LeanObject] };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__8_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__1_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__1_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__0_value)
                as *mut LeanObject,
            12847922472053947547 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__1_value)
                as *mut LeanObject,
            10422657989269798688 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__3_value: LeanStringObject<4> =
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
        m_data: [78, 97, 116, 0],
    };
static mut l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__3_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__4_value)
        as *mut LeanObject;
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(
    mut v_x_391_: *mut LeanObject,
    mut v___y_392_: *mut LeanObject,
    mut v___y_393_: *mut LeanObject,
    mut v___y_394_: *mut LeanObject,
    mut v___y_395_: *mut LeanObject,
    mut v___y_396_: *mut LeanObject,
    mut v___y_397_: *mut LeanObject,
    mut v___y_398_: *mut LeanObject,
    mut v___y_399_: *mut LeanObject,
    mut v___y_400_: *mut LeanObject,
    mut v___y_401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut LeanObject = core::ptr::null_mut();
    v___x_403_ = lean_box(0);
    v___x_404_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_404_, 0, v___x_403_);
    return v___x_404_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0___boxed(
    mut v_x_405_: *mut LeanObject,
    mut v___y_406_: *mut LeanObject,
    mut v___y_407_: *mut LeanObject,
    mut v___y_408_: *mut LeanObject,
    mut v___y_409_: *mut LeanObject,
    mut v___y_410_: *mut LeanObject,
    mut v___y_411_: *mut LeanObject,
    mut v___y_412_: *mut LeanObject,
    mut v___y_413_: *mut LeanObject,
    mut v___y_414_: *mut LeanObject,
    mut v___y_415_: *mut LeanObject,
    mut v___y_416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_417_: *mut LeanObject = core::ptr::null_mut();
    v_res_417_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v_x_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_);
    lean_dec(v___y_415_);
    lean_dec_ref(v___y_414_);
    lean_dec(v___y_413_);
    lean_dec_ref(v___y_412_);
    lean_dec(v___y_411_);
    lean_dec_ref(v___y_410_);
    lean_dec(v___y_409_);
    lean_dec_ref(v___y_408_);
    lean_dec(v___y_407_);
    lean_dec(v___y_406_);
    return v_res_417_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg(
    mut v_a_434_: *mut LeanObject,
    mut v_a_435_: *mut LeanObject,
    mut v_e_436_: *mut LeanObject,
    mut v_a_437_: *mut LeanObject,
    mut v_a_438_: *mut LeanObject,
    mut v_a_439_: *mut LeanObject,
    mut v___y_440_: *mut LeanObject,
    mut v___y_441_: *mut LeanObject,
    mut v___y_442_: *mut LeanObject,
    mut v___y_443_: *mut LeanObject,
    mut v___y_444_: *mut LeanObject,
    mut v___y_445_: *mut LeanObject,
    mut v___y_446_: *mut LeanObject,
    mut v___y_447_: *mut LeanObject,
    mut v___y_448_: *mut LeanObject,
    mut v___y_449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_455_: u8 = 0;
    let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_self_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_next_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_464_: u8 = 0;
    let mut v___x_465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_467_: u8 = 0;
    let mut v___x_469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_484_: u8 = 0;
    let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_488_: u8 = 0;
    let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_490_: u8 = 0;
    let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_495_: u8 = 0;
    let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_500_: u8 = 0;
    let mut v___x_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_505_: u8 = 0;
    let mut v___x_506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_510_: u8 = 0;
    let mut v___x_511_: u8 = 0;
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_514_: u8 = 0;
    let mut v___x_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_536_: u8 = 0;
    let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_541_: u8 = 0;
    let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_545_: u8 = 0;
    let mut v_a_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_549_: u8 = 0;
    let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_553_: u8 = 0;
    let mut v_a_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_557_: u8 = 0;
    let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_561_: u8 = 0;
    let mut v_a_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_565_: u8 = 0;
    let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_569_: u8 = 0;
    let mut v_a_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_573_: u8 = 0;
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_577_: u8 = 0;
    let mut v_a_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_581_: u8 = 0;
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_585_: u8 = 0;
    let mut v_a_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_589_: u8 = 0;
    let mut v___x_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_593_: u8 = 0;
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_595_: u8 = 0;
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_600_: u8 = 0;
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: u8 = 0;
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_609_: u8 = 0;
    let mut v___x_610_: u8 = 0;
    let mut v_isSharedCheck_611_: u8 = 0;
    let mut v_a_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_615_: u8 = 0;
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_619_: u8 = 0;
    let mut v_a_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_623_: u8 = 0;
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_627_: u8 = 0;
    let mut v_isSharedCheck_628_: u8 = 0;
    let mut v_unused_629_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_451_ = lean_st_ref_get(v___y_440_);
                v_snd_452_ = lean_ctor_get(v_a_439_, 1);
                v_isSharedCheck_628_ = (!lean_is_exclusive(v_a_439_)) as u8;
                if v_isSharedCheck_628_ == 0 {
                    v_unused_629_ = lean_ctor_get(v_a_439_, 0);
                    lean_dec(v_unused_629_);
                    v___x_454_ = v_a_439_;
                    v_isShared_455_ = v_isSharedCheck_628_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_452_);
                    lean_dec(v_a_439_);
                    v___x_454_ = lean_box(0);
                    v_isShared_455_ = v_isSharedCheck_628_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_snd_452_);
                v___x_456_ = l_Lean_Meta_Grind_Goal_getENode(
                    v___x_451_, v_snd_452_, v___y_446_, v___y_447_, v___y_448_, v___y_449_,
                );
                lean_dec(v___x_451_);
                if lean_obj_tag(v___x_456_) == 0 {
                    v_a_457_ = lean_ctor_get(v___x_456_, 0);
                    lean_inc(v_a_457_);
                    lean_dec_ref_known(v___x_456_, 1);
                    v_self_458_ = lean_ctor_get(v_a_457_, 0);
                    lean_inc_ref_n(v_self_458_, 2);
                    v_next_459_ = lean_ctor_get(v_a_457_, 1);
                    lean_inc_ref(v_next_459_);
                    lean_dec(v_a_457_);
                    v___x_460_ =
                        l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_self_458_, v___y_447_);
                    if lean_obj_tag(v___x_460_) == 0 {
                        v_a_461_ = lean_ctor_get(v___x_460_, 0);
                        v_isSharedCheck_611_ = (!lean_is_exclusive(v___x_460_)) as u8;
                        if v_isSharedCheck_611_ == 0 {
                            v___x_463_ = v___x_460_;
                            v_isShared_464_ = v_isSharedCheck_611_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_461_);
                            lean_dec(v___x_460_);
                            v___x_463_ = lean_box(0);
                            v_isShared_464_ = v_isSharedCheck_611_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_next_459_);
                        lean_dec_ref(v_self_458_);
                        lean_del_object(v___x_454_);
                        lean_dec(v_snd_452_);
                        lean_dec_ref(v_a_438_);
                        lean_dec_ref(v_a_437_);
                        lean_dec_ref(v_e_436_);
                        lean_dec_ref(v_a_434_);
                        v_a_612_ = lean_ctor_get(v___x_460_, 0);
                        v_isSharedCheck_619_ = (!lean_is_exclusive(v___x_460_)) as u8;
                        if v_isSharedCheck_619_ == 0 {
                            v___x_614_ = v___x_460_;
                            v_isShared_615_ = v_isSharedCheck_619_;
                            state = 25;
                            continue;
                        } else {
                            lean_inc(v_a_612_);
                            lean_dec(v___x_460_);
                            v___x_614_ = lean_box(0);
                            v_isShared_615_ = v_isSharedCheck_619_;
                            state = 25;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_454_);
                    lean_dec(v_snd_452_);
                    lean_dec_ref(v_a_438_);
                    lean_dec_ref(v_a_437_);
                    lean_dec_ref(v_e_436_);
                    lean_dec_ref(v_a_434_);
                    v_a_620_ = lean_ctor_get(v___x_456_, 0);
                    v_isSharedCheck_627_ = (!lean_is_exclusive(v___x_456_)) as u8;
                    if v_isSharedCheck_627_ == 0 {
                        v___x_622_ = v___x_456_;
                        v_isShared_623_ = v_isSharedCheck_627_;
                        state = 27;
                        continue;
                    } else {
                        lean_inc(v_a_620_);
                        lean_dec(v___x_456_);
                        v___x_622_ = lean_box(0);
                        v_isShared_623_ = v_isSharedCheck_627_;
                        state = 27;
                        continue;
                    }
                }
            }
            2 => {
                v___x_465_ = lean_box(0);
                v___x_489_ = l_Lean_Expr_cleanupAnnotations(v_a_461_);
                v___x_490_ = l_Lean_Expr_isApp(v___x_489_);
                if v___x_490_ == 0 {
                    lean_dec_ref(v___x_489_);
                    lean_dec_ref(v_self_458_);
                    v___x_491_ = lean_box(0);
                    v___x_492_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_491_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
                    v___y_480_ = v___x_492_;
                    state = 7;
                    continue;
                } else {
                    v_arg_493_ = lean_ctor_get(v___x_489_, 1);
                    lean_inc_ref(v_arg_493_);
                    v___x_494_ = l_Lean_Expr_appFnCleanup___redArg(v___x_489_);
                    v___x_495_ = l_Lean_Expr_isApp(v___x_494_);
                    if v___x_495_ == 0 {
                        lean_dec_ref(v___x_494_);
                        lean_dec_ref(v_arg_493_);
                        lean_dec_ref(v_self_458_);
                        v___x_496_ = lean_box(0);
                        v___x_497_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_496_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
                        v___y_480_ = v___x_497_;
                        state = 7;
                        continue;
                    } else {
                        v_arg_498_ = lean_ctor_get(v___x_494_, 1);
                        lean_inc_ref(v_arg_498_);
                        v___x_499_ = l_Lean_Expr_appFnCleanup___redArg(v___x_494_);
                        v___x_500_ = l_Lean_Expr_isApp(v___x_499_);
                        if v___x_500_ == 0 {
                            lean_dec_ref(v___x_499_);
                            lean_dec_ref(v_arg_498_);
                            lean_dec_ref(v_arg_493_);
                            lean_dec_ref(v_self_458_);
                            v___x_501_ = lean_box(0);
                            v___x_502_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_501_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
                            v___y_480_ = v___x_502_;
                            state = 7;
                            continue;
                        } else {
                            v_arg_503_ = lean_ctor_get(v___x_499_, 1);
                            lean_inc_ref(v_arg_503_);
                            v___x_504_ = l_Lean_Expr_appFnCleanup___redArg(v___x_499_);
                            v___x_505_ = l_Lean_Expr_isApp(v___x_504_);
                            if v___x_505_ == 0 {
                                lean_dec_ref(v___x_504_);
                                lean_dec_ref(v_arg_503_);
                                lean_dec_ref(v_arg_498_);
                                lean_dec_ref(v_arg_493_);
                                lean_dec_ref(v_self_458_);
                                v___x_506_ = lean_box(0);
                                v___x_507_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_506_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
                                v___y_480_ = v___x_507_;
                                state = 7;
                                continue;
                            } else {
                                v_arg_508_ = lean_ctor_get(v___x_504_, 1);
                                lean_inc_ref(v_arg_508_);
                                v___x_594_ = l_Lean_Expr_appFnCleanup___redArg(v___x_504_);
                                v___x_595_ = l_Lean_Expr_isApp(v___x_594_);
                                if v___x_595_ == 0 {
                                    lean_dec_ref(v___x_594_);
                                    lean_dec_ref(v_arg_508_);
                                    lean_dec_ref(v_arg_503_);
                                    lean_dec_ref(v_arg_498_);
                                    lean_dec_ref(v_arg_493_);
                                    lean_dec_ref(v_self_458_);
                                    v___x_596_ = lean_box(0);
                                    v___x_597_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_596_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
                                    v___y_480_ = v___x_597_;
                                    state = 7;
                                    continue;
                                } else {
                                    v_arg_598_ = lean_ctor_get(v___x_594_, 1);
                                    lean_inc_ref(v_arg_598_);
                                    v___x_599_ = l_Lean_Expr_appFnCleanup___redArg(v___x_594_);
                                    v___x_600_ = l_Lean_Expr_isApp(v___x_599_);
                                    if v___x_600_ == 0 {
                                        lean_dec_ref(v___x_599_);
                                        lean_dec_ref(v_arg_598_);
                                        lean_dec_ref(v_arg_508_);
                                        lean_dec_ref(v_arg_503_);
                                        lean_dec_ref(v_arg_498_);
                                        lean_dec_ref(v_arg_493_);
                                        lean_dec_ref(v_self_458_);
                                        v___x_601_ = lean_box(0);
                                        v___x_602_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_601_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
                                        v___y_480_ = v___x_602_;
                                        state = 7;
                                        continue;
                                    } else {
                                        v_arg_603_ = lean_ctor_get(v___x_599_, 1);
                                        lean_inc_ref(v_arg_603_);
                                        v___x_604_ = l_Lean_Expr_appFnCleanup___redArg(v___x_599_);
                                        v___x_605_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__8;
                                        v___x_606_ = l_Lean_Expr_isConstOf(v___x_604_, v___x_605_);
                                        lean_dec_ref(v___x_604_);
                                        if v___x_606_ == 0 {
                                            lean_dec_ref(v_arg_603_);
                                            lean_dec_ref(v_arg_598_);
                                            lean_dec_ref(v_arg_508_);
                                            lean_dec_ref(v_arg_503_);
                                            lean_dec_ref(v_arg_498_);
                                            lean_dec_ref(v_arg_493_);
                                            lean_dec_ref(v_self_458_);
                                            v___x_607_ = lean_box(0);
                                            v___x_608_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___lam__0(v___x_607_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
                                            v___y_480_ = v___x_608_;
                                            state = 7;
                                            continue;
                                        } else {
                                            v___x_609_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_435_, v_arg_603_);
                                            lean_dec_ref(v_arg_603_);
                                            if v___x_609_ == 0 {
                                                lean_dec_ref(v_arg_598_);
                                                v___y_510_ = v___x_609_;
                                                state = 10;
                                                continue;
                                            } else {
                                                v___x_610_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_435_, v_arg_598_);
                                                lean_dec_ref(v_arg_598_);
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
                    lean_del_object(v___x_463_);
                    lean_dec(v_snd_452_);
                    if v_isShared_455_ == 0 {
                        lean_ctor_set(v___x_454_, 1, v_next_459_);
                        lean_ctor_set(v___x_454_, 0, v___x_465_);
                        v___x_469_ = v___x_454_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_465_);
                        lean_ctor_set(v_reuseFailAlloc_471_, 1, v_next_459_);
                        v___x_469_ = v_reuseFailAlloc_471_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_next_459_);
                    lean_dec_ref(v_a_438_);
                    lean_dec_ref(v_a_437_);
                    lean_dec_ref(v_e_436_);
                    lean_dec_ref(v_a_434_);
                    v___x_472_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__0;
                    if v_isShared_455_ == 0 {
                        lean_ctor_set(v___x_454_, 0, v___x_472_);
                        v___x_474_ = v___x_454_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_472_);
                        lean_ctor_set(v_reuseFailAlloc_478_, 1, v_snd_452_);
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
                    lean_ctor_set(v___x_463_, 0, v___x_474_);
                    v___x_476_ = v___x_463_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_474_);
                    v___x_476_ = v_reuseFailAlloc_477_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_476_;
            }
            7 => {
                if lean_obj_tag(v___y_480_) == 0 {
                    lean_dec_ref_known(v___y_480_, 1);
                    state = 3;
                    continue;
                } else {
                    lean_del_object(v___x_463_);
                    lean_dec_ref(v_next_459_);
                    lean_del_object(v___x_454_);
                    lean_dec(v_snd_452_);
                    lean_dec_ref(v_a_438_);
                    lean_dec_ref(v_a_437_);
                    lean_dec_ref(v_e_436_);
                    lean_dec_ref(v_a_434_);
                    v_a_481_ = lean_ctor_get(v___y_480_, 0);
                    v_isSharedCheck_488_ = (!lean_is_exclusive(v___y_480_)) as u8;
                    if v_isSharedCheck_488_ == 0 {
                        v___x_483_ = v___y_480_;
                        v_isShared_484_ = v_isSharedCheck_488_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_481_);
                        lean_dec(v___y_480_);
                        v___x_483_ = lean_box(0);
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
                    v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
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
                    lean_dec_ref(v_arg_508_);
                    lean_dec_ref(v_arg_503_);
                    lean_dec_ref(v_arg_498_);
                    lean_dec_ref(v_arg_493_);
                    lean_dec_ref(v_self_458_);
                    state = 3;
                    continue;
                } else {
                    v___x_511_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_a_435_, v_arg_508_,
                        );
                    lean_dec_ref(v_arg_508_);
                    if v___x_511_ == 0 {
                        lean_dec_ref(v_arg_503_);
                        lean_dec_ref(v_arg_498_);
                        lean_dec_ref(v_arg_493_);
                        lean_dec_ref(v_self_458_);
                        state = 3;
                        continue;
                    } else {
                        v___x_512_ =
                            l_Lean_Meta_Structural_isInstHAddNat___redArg(v_arg_503_, v___y_447_);
                        if lean_obj_tag(v___x_512_) == 0 {
                            v_a_513_ = lean_ctor_get(v___x_512_, 0);
                            lean_inc(v_a_513_);
                            lean_dec_ref_known(v___x_512_, 1);
                            v___x_514_ = (lean_unbox(v_a_513_) as u8);
                            lean_dec(v_a_513_);
                            if v___x_514_ == 0 {
                                lean_dec_ref(v_arg_498_);
                                lean_dec_ref(v_arg_493_);
                                lean_dec_ref(v_self_458_);
                                state = 3;
                                continue;
                            } else {
                                v___x_515_ = l_Lean_Expr_appFn_x21(v_e_436_);
                                v___x_516_ = l_Lean_Expr_appFn_x21(v___x_515_);
                                lean_dec_ref(v___x_515_);
                                lean_inc_ref(v_arg_498_);
                                lean_inc_ref_n(v_a_437_, 2);
                                lean_inc_ref(v___x_516_);
                                v___x_517_ = l_Lean_mkAppB(v___x_516_, v_a_437_, v_arg_498_);
                                lean_inc_ref(v_arg_493_);
                                v___x_518_ = l_Lean_mkAppB(v___x_516_, v_a_437_, v_arg_493_);
                                v___x_519_ = l_Lean_Meta_mkMul(
                                    v___x_517_, v___x_518_, v___y_446_, v___y_447_, v___y_448_,
                                    v___y_449_,
                                );
                                if lean_obj_tag(v___x_519_) == 0 {
                                    v_a_520_ = lean_ctor_get(v___x_519_, 0);
                                    lean_inc(v_a_520_);
                                    lean_dec_ref_known(v___x_519_, 1);
                                    lean_inc(v___y_449_);
                                    lean_inc_ref(v___y_448_);
                                    lean_inc(v___y_447_);
                                    lean_inc_ref(v___y_446_);
                                    lean_inc(v___y_445_);
                                    lean_inc_ref(v___y_444_);
                                    lean_inc(v___y_443_);
                                    lean_inc_ref(v___y_442_);
                                    lean_inc(v___y_441_);
                                    lean_inc(v___y_440_);
                                    v___x_521_ = lean_grind_preprocess(
                                        v_a_520_, v___y_440_, v___y_441_, v___y_442_, v___y_443_,
                                        v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_,
                                        v___y_449_,
                                    );
                                    if lean_obj_tag(v___x_521_) == 0 {
                                        v_a_522_ = lean_ctor_get(v___x_521_, 0);
                                        lean_inc(v_a_522_);
                                        lean_dec_ref_known(v___x_521_, 1);
                                        v___x_523_ = l_Lean_Meta_Grind_getGeneration___redArg(
                                            v_e_436_, v___y_440_,
                                        );
                                        if lean_obj_tag(v___x_523_) == 0 {
                                            v_a_524_ = lean_ctor_get(v___x_523_, 0);
                                            lean_inc(v_a_524_);
                                            lean_dec_ref_known(v___x_523_, 1);
                                            v_expr_525_ = lean_ctor_get(v_a_522_, 0);
                                            lean_inc_ref_n(v_expr_525_, 2);
                                            lean_inc(v___y_449_);
                                            lean_inc_ref(v___y_448_);
                                            lean_inc(v___y_447_);
                                            lean_inc_ref(v___y_446_);
                                            lean_inc(v___y_445_);
                                            lean_inc_ref(v___y_444_);
                                            lean_inc(v___y_443_);
                                            lean_inc_ref(v___y_442_);
                                            lean_inc(v___y_441_);
                                            lean_inc(v___y_440_);
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
                                            if lean_obj_tag(v___x_526_) == 0 {
                                                lean_dec_ref_known(v___x_526_, 1);
                                                v___x_527_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg___closed__5;
                                                lean_inc_ref(v_a_438_);
                                                v___x_528_ = l_Lean_Meta_Grind_Arith_mkSemiringThm(
                                                    v___x_527_, v_a_438_, v___y_446_, v___y_447_,
                                                    v___y_448_, v___y_449_,
                                                );
                                                if lean_obj_tag(v___x_528_) == 0 {
                                                    v_a_529_ = lean_ctor_get(v___x_528_, 0);
                                                    lean_inc(v_a_529_);
                                                    lean_dec_ref_known(v___x_528_, 1);
                                                    if lean_obj_tag(v_a_529_) == 1 {
                                                        v_val_530_ = lean_ctor_get(v_a_529_, 0);
                                                        lean_inc(v_val_530_);
                                                        lean_dec_ref_known(v_a_529_, 1);
                                                        lean_inc(v___y_449_);
                                                        lean_inc_ref(v___y_448_);
                                                        lean_inc(v___y_447_);
                                                        lean_inc_ref(v___y_446_);
                                                        lean_inc(v___y_445_);
                                                        lean_inc_ref(v___y_444_);
                                                        lean_inc(v___y_443_);
                                                        lean_inc_ref(v___y_442_);
                                                        lean_inc(v___y_441_);
                                                        lean_inc(v___y_440_);
                                                        lean_inc_ref(v_a_434_);
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
                                                        if lean_obj_tag(v___x_531_) == 0 {
                                                            v_a_532_ = lean_ctor_get(v___x_531_, 0);
                                                            lean_inc(v_a_532_);
                                                            lean_dec_ref_known(v___x_531_, 1);
                                                            v___x_533_ =
                                                                l_Lean_Meta_Simp_Result_getProof(
                                                                    v_a_522_, v___y_446_,
                                                                    v___y_447_, v___y_448_,
                                                                    v___y_449_,
                                                                );
                                                            if lean_obj_tag(v___x_533_) == 0 {
                                                                v_a_534_ =
                                                                    lean_ctor_get(v___x_533_, 0);
                                                                lean_inc(v_a_534_);
                                                                lean_dec_ref_known(v___x_533_, 1);
                                                                lean_inc_ref(v_a_434_);
                                                                lean_inc_ref(v_expr_525_);
                                                                lean_inc_ref(v_a_437_);
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
                                                                lean_inc_ref(v_e_436_);
                                                                v___x_537_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_436_, v_expr_525_, v___x_535_, v___x_536_, v___y_440_, v___y_442_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
                                                                v___y_480_ = v___x_537_;
                                                                state = 7;
                                                                continue;
                                                            } else {
                                                                lean_dec(v_a_532_);
                                                                lean_dec(v_val_530_);
                                                                lean_dec_ref(v_expr_525_);
                                                                lean_dec_ref(v_arg_498_);
                                                                lean_dec_ref(v_arg_493_);
                                                                lean_del_object(v___x_463_);
                                                                lean_dec_ref(v_next_459_);
                                                                lean_del_object(v___x_454_);
                                                                lean_dec(v_snd_452_);
                                                                lean_dec_ref(v_a_438_);
                                                                lean_dec_ref(v_a_437_);
                                                                lean_dec_ref(v_e_436_);
                                                                lean_dec_ref(v_a_434_);
                                                                v_a_538_ =
                                                                    lean_ctor_get(v___x_533_, 0);
                                                                v_isSharedCheck_545_ =
                                                                    (!lean_is_exclusive(v___x_533_))
                                                                        as u8;
                                                                if v_isSharedCheck_545_ == 0 {
                                                                    v___x_540_ = v___x_533_;
                                                                    v_isShared_541_ =
                                                                        v_isSharedCheck_545_;
                                                                    state = 11;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_a_538_);
                                                                    lean_dec(v___x_533_);
                                                                    v___x_540_ = lean_box(0);
                                                                    v_isShared_541_ =
                                                                        v_isSharedCheck_545_;
                                                                    state = 11;
                                                                    continue;
                                                                }
                                                            }
                                                        } else {
                                                            lean_dec(v_val_530_);
                                                            lean_dec_ref(v_expr_525_);
                                                            lean_dec(v_a_522_);
                                                            lean_dec_ref(v_arg_498_);
                                                            lean_dec_ref(v_arg_493_);
                                                            lean_del_object(v___x_463_);
                                                            lean_dec_ref(v_next_459_);
                                                            lean_del_object(v___x_454_);
                                                            lean_dec(v_snd_452_);
                                                            lean_dec_ref(v_a_438_);
                                                            lean_dec_ref(v_a_437_);
                                                            lean_dec_ref(v_e_436_);
                                                            lean_dec_ref(v_a_434_);
                                                            v_a_546_ = lean_ctor_get(v___x_531_, 0);
                                                            v_isSharedCheck_553_ =
                                                                (!lean_is_exclusive(v___x_531_))
                                                                    as u8;
                                                            if v_isSharedCheck_553_ == 0 {
                                                                v___x_548_ = v___x_531_;
                                                                v_isShared_549_ =
                                                                    v_isSharedCheck_553_;
                                                                state = 13;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_546_);
                                                                lean_dec(v___x_531_);
                                                                v___x_548_ = lean_box(0);
                                                                v_isShared_549_ =
                                                                    v_isSharedCheck_553_;
                                                                state = 13;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        lean_dec(v_a_529_);
                                                        lean_dec_ref(v_expr_525_);
                                                        lean_dec(v_a_522_);
                                                        lean_dec_ref(v_arg_498_);
                                                        lean_dec_ref(v_arg_493_);
                                                        lean_dec_ref(v_self_458_);
                                                        state = 3;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_expr_525_);
                                                    lean_dec(v_a_522_);
                                                    lean_dec_ref(v_arg_498_);
                                                    lean_dec_ref(v_arg_493_);
                                                    lean_del_object(v___x_463_);
                                                    lean_dec_ref(v_next_459_);
                                                    lean_dec_ref(v_self_458_);
                                                    lean_del_object(v___x_454_);
                                                    lean_dec(v_snd_452_);
                                                    lean_dec_ref(v_a_438_);
                                                    lean_dec_ref(v_a_437_);
                                                    lean_dec_ref(v_e_436_);
                                                    lean_dec_ref(v_a_434_);
                                                    v_a_554_ = lean_ctor_get(v___x_528_, 0);
                                                    v_isSharedCheck_561_ =
                                                        (!lean_is_exclusive(v___x_528_)) as u8;
                                                    if v_isSharedCheck_561_ == 0 {
                                                        v___x_556_ = v___x_528_;
                                                        v_isShared_557_ = v_isSharedCheck_561_;
                                                        state = 15;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_554_);
                                                        lean_dec(v___x_528_);
                                                        v___x_556_ = lean_box(0);
                                                        v_isShared_557_ = v_isSharedCheck_561_;
                                                        state = 15;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v_expr_525_);
                                                lean_dec(v_a_522_);
                                                lean_dec_ref(v_arg_498_);
                                                lean_dec_ref(v_arg_493_);
                                                lean_dec_ref(v_self_458_);
                                                v___y_480_ = v___x_526_;
                                                state = 7;
                                                continue;
                                            }
                                        } else {
                                            lean_dec(v_a_522_);
                                            lean_dec_ref(v_arg_498_);
                                            lean_dec_ref(v_arg_493_);
                                            lean_del_object(v___x_463_);
                                            lean_dec_ref(v_next_459_);
                                            lean_dec_ref(v_self_458_);
                                            lean_del_object(v___x_454_);
                                            lean_dec(v_snd_452_);
                                            lean_dec_ref(v_a_438_);
                                            lean_dec_ref(v_a_437_);
                                            lean_dec_ref(v_e_436_);
                                            lean_dec_ref(v_a_434_);
                                            v_a_562_ = lean_ctor_get(v___x_523_, 0);
                                            v_isSharedCheck_569_ =
                                                (!lean_is_exclusive(v___x_523_)) as u8;
                                            if v_isSharedCheck_569_ == 0 {
                                                v___x_564_ = v___x_523_;
                                                v_isShared_565_ = v_isSharedCheck_569_;
                                                state = 17;
                                                continue;
                                            } else {
                                                lean_inc(v_a_562_);
                                                lean_dec(v___x_523_);
                                                v___x_564_ = lean_box(0);
                                                v_isShared_565_ = v_isSharedCheck_569_;
                                                state = 17;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v_arg_498_);
                                        lean_dec_ref(v_arg_493_);
                                        lean_del_object(v___x_463_);
                                        lean_dec_ref(v_next_459_);
                                        lean_dec_ref(v_self_458_);
                                        lean_del_object(v___x_454_);
                                        lean_dec(v_snd_452_);
                                        lean_dec_ref(v_a_438_);
                                        lean_dec_ref(v_a_437_);
                                        lean_dec_ref(v_e_436_);
                                        lean_dec_ref(v_a_434_);
                                        v_a_570_ = lean_ctor_get(v___x_521_, 0);
                                        v_isSharedCheck_577_ =
                                            (!lean_is_exclusive(v___x_521_)) as u8;
                                        if v_isSharedCheck_577_ == 0 {
                                            v___x_572_ = v___x_521_;
                                            v_isShared_573_ = v_isSharedCheck_577_;
                                            state = 19;
                                            continue;
                                        } else {
                                            lean_inc(v_a_570_);
                                            lean_dec(v___x_521_);
                                            v___x_572_ = lean_box(0);
                                            v_isShared_573_ = v_isSharedCheck_577_;
                                            state = 19;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v_arg_498_);
                                    lean_dec_ref(v_arg_493_);
                                    lean_del_object(v___x_463_);
                                    lean_dec_ref(v_next_459_);
                                    lean_dec_ref(v_self_458_);
                                    lean_del_object(v___x_454_);
                                    lean_dec(v_snd_452_);
                                    lean_dec_ref(v_a_438_);
                                    lean_dec_ref(v_a_437_);
                                    lean_dec_ref(v_e_436_);
                                    lean_dec_ref(v_a_434_);
                                    v_a_578_ = lean_ctor_get(v___x_519_, 0);
                                    v_isSharedCheck_585_ = (!lean_is_exclusive(v___x_519_)) as u8;
                                    if v_isSharedCheck_585_ == 0 {
                                        v___x_580_ = v___x_519_;
                                        v_isShared_581_ = v_isSharedCheck_585_;
                                        state = 21;
                                        continue;
                                    } else {
                                        lean_inc(v_a_578_);
                                        lean_dec(v___x_519_);
                                        v___x_580_ = lean_box(0);
                                        v_isShared_581_ = v_isSharedCheck_585_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref(v_arg_498_);
                            lean_dec_ref(v_arg_493_);
                            lean_del_object(v___x_463_);
                            lean_dec_ref(v_next_459_);
                            lean_dec_ref(v_self_458_);
                            lean_del_object(v___x_454_);
                            lean_dec(v_snd_452_);
                            lean_dec_ref(v_a_438_);
                            lean_dec_ref(v_a_437_);
                            lean_dec_ref(v_e_436_);
                            lean_dec_ref(v_a_434_);
                            v_a_586_ = lean_ctor_get(v___x_512_, 0);
                            v_isSharedCheck_593_ = (!lean_is_exclusive(v___x_512_)) as u8;
                            if v_isSharedCheck_593_ == 0 {
                                v___x_588_ = v___x_512_;
                                v_isShared_589_ = v_isSharedCheck_593_;
                                state = 23;
                                continue;
                            } else {
                                lean_inc(v_a_586_);
                                lean_dec(v___x_512_);
                                v___x_588_ = lean_box(0);
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
                    v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
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
                    v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_546_);
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
                    v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
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
                    v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_562_);
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
                    v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
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
                    v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
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
                    v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
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
                    v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
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
                    v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
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
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_630_: *mut LeanObject = *_args.add(0);
    let mut v_a_631_: *mut LeanObject = *_args.add(1);
    let mut v_e_632_: *mut LeanObject = *_args.add(2);
    let mut v_a_633_: *mut LeanObject = *_args.add(3);
    let mut v_a_634_: *mut LeanObject = *_args.add(4);
    let mut v_a_635_: *mut LeanObject = *_args.add(5);
    let mut v___y_636_: *mut LeanObject = *_args.add(6);
    let mut v___y_637_: *mut LeanObject = *_args.add(7);
    let mut v___y_638_: *mut LeanObject = *_args.add(8);
    let mut v___y_639_: *mut LeanObject = *_args.add(9);
    let mut v___y_640_: *mut LeanObject = *_args.add(10);
    let mut v___y_641_: *mut LeanObject = *_args.add(11);
    let mut v___y_642_: *mut LeanObject = *_args.add(12);
    let mut v___y_643_: *mut LeanObject = *_args.add(13);
    let mut v___y_644_: *mut LeanObject = *_args.add(14);
    let mut v___y_645_: *mut LeanObject = *_args.add(15);
    let mut v___y_646_: *mut LeanObject = *_args.add(16);
    let mut v_res_647_: *mut LeanObject = core::ptr::null_mut();
    v_res_647_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg(v_a_630_, v_a_631_, v_e_632_, v_a_633_, v_a_634_, v_a_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
    lean_dec(v___y_645_);
    lean_dec_ref(v___y_644_);
    lean_dec(v___y_643_);
    lean_dec_ref(v___y_642_);
    lean_dec(v___y_641_);
    lean_dec_ref(v___y_640_);
    lean_dec(v___y_639_);
    lean_dec_ref(v___y_638_);
    lean_dec(v___y_637_);
    lean_dec(v___y_636_);
    lean_dec_ref(v_a_631_);
    return v_res_647_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_propagatePower(
    mut v_e_656_: *mut LeanObject,
    mut v_a_657_: *mut LeanObject,
    mut v_a_658_: *mut LeanObject,
    mut v_a_659_: *mut LeanObject,
    mut v_a_660_: *mut LeanObject,
    mut v_a_661_: *mut LeanObject,
    mut v_a_662_: *mut LeanObject,
    mut v_a_663_: *mut LeanObject,
    mut v_a_664_: *mut LeanObject,
    mut v_a_665_: *mut LeanObject,
    mut v_a_666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: u8 = 0;
    let mut v_arg_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_675_: u8 = 0;
    let mut v_arg_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_678_: u8 = 0;
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_680_: u8 = 0;
    let mut v_arg_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_683_: u8 = 0;
    let mut v_arg_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_686_: u8 = 0;
    let mut v_arg_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_690_: u8 = 0;
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_693_: u8 = 0;
    let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_696_: u8 = 0;
    let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_705_: u8 = 0;
    let mut v_fst_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_715_: u8 = 0;
    let mut v_a_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_719_: u8 = 0;
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_723_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_656_);
                v___x_671_ = l_Lean_Expr_cleanupAnnotations(v_e_656_);
                v___x_672_ = l_Lean_Expr_isApp(v___x_671_);
                if v___x_672_ == 0 {
                    lean_dec_ref(v___x_671_);
                    lean_dec_ref(v_e_656_);
                    state = 1;
                    continue;
                } else {
                    v_arg_673_ = lean_ctor_get(v___x_671_, 1);
                    lean_inc_ref(v_arg_673_);
                    v___x_674_ = l_Lean_Expr_appFnCleanup___redArg(v___x_671_);
                    v___x_675_ = l_Lean_Expr_isApp(v___x_674_);
                    if v___x_675_ == 0 {
                        lean_dec_ref(v___x_674_);
                        lean_dec_ref(v_arg_673_);
                        lean_dec_ref(v_e_656_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_676_ = lean_ctor_get(v___x_674_, 1);
                        lean_inc_ref(v_arg_676_);
                        v___x_677_ = l_Lean_Expr_appFnCleanup___redArg(v___x_674_);
                        v___x_678_ = l_Lean_Expr_isApp(v___x_677_);
                        if v___x_678_ == 0 {
                            lean_dec_ref(v___x_677_);
                            lean_dec_ref(v_arg_676_);
                            lean_dec_ref(v_arg_673_);
                            lean_dec_ref(v_e_656_);
                            state = 1;
                            continue;
                        } else {
                            v___x_679_ = l_Lean_Expr_appFnCleanup___redArg(v___x_677_);
                            v___x_680_ = l_Lean_Expr_isApp(v___x_679_);
                            if v___x_680_ == 0 {
                                lean_dec_ref(v___x_679_);
                                lean_dec_ref(v_arg_676_);
                                lean_dec_ref(v_arg_673_);
                                lean_dec_ref(v_e_656_);
                                state = 1;
                                continue;
                            } else {
                                v_arg_681_ = lean_ctor_get(v___x_679_, 1);
                                lean_inc_ref(v_arg_681_);
                                v___x_682_ = l_Lean_Expr_appFnCleanup___redArg(v___x_679_);
                                v___x_683_ = l_Lean_Expr_isApp(v___x_682_);
                                if v___x_683_ == 0 {
                                    lean_dec_ref(v___x_682_);
                                    lean_dec_ref(v_arg_681_);
                                    lean_dec_ref(v_arg_676_);
                                    lean_dec_ref(v_arg_673_);
                                    lean_dec_ref(v_e_656_);
                                    state = 1;
                                    continue;
                                } else {
                                    v_arg_684_ = lean_ctor_get(v___x_682_, 1);
                                    lean_inc_ref(v_arg_684_);
                                    v___x_685_ = l_Lean_Expr_appFnCleanup___redArg(v___x_682_);
                                    v___x_686_ = l_Lean_Expr_isApp(v___x_685_);
                                    if v___x_686_ == 0 {
                                        lean_dec_ref(v___x_685_);
                                        lean_dec_ref(v_arg_684_);
                                        lean_dec_ref(v_arg_681_);
                                        lean_dec_ref(v_arg_676_);
                                        lean_dec_ref(v_arg_673_);
                                        lean_dec_ref(v_e_656_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v_arg_687_ = lean_ctor_get(v___x_685_, 1);
                                        lean_inc_ref(v_arg_687_);
                                        v___x_688_ = l_Lean_Expr_appFnCleanup___redArg(v___x_685_);
                                        v___x_689_ = l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2;
                                        v___x_690_ = l_Lean_Expr_isConstOf(v___x_688_, v___x_689_);
                                        lean_dec_ref(v___x_688_);
                                        if v___x_690_ == 0 {
                                            lean_dec_ref(v_arg_687_);
                                            lean_dec_ref(v_arg_684_);
                                            lean_dec_ref(v_arg_681_);
                                            lean_dec_ref(v_arg_676_);
                                            lean_dec_ref(v_arg_673_);
                                            lean_dec_ref(v_e_656_);
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_inc_ref(v_arg_684_);
                                            v___x_691_ = l_Lean_Expr_cleanupAnnotations(v_arg_684_);
                                            v___x_692_ = l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__4;
                                            v___x_693_ =
                                                l_Lean_Expr_isConstOf(v___x_691_, v___x_692_);
                                            lean_dec_ref(v___x_691_);
                                            if v___x_693_ == 0 {
                                                lean_dec_ref(v_arg_687_);
                                                lean_dec_ref(v_arg_684_);
                                                lean_dec_ref(v_arg_681_);
                                                lean_dec_ref(v_arg_676_);
                                                lean_dec_ref(v_arg_673_);
                                                lean_dec_ref(v_e_656_);
                                                v___x_694_ = lean_box(0);
                                                v___x_695_ = lean_alloc_ctor(0, 1, (0) as u32);
                                                lean_ctor_set(v___x_695_, 0, v___x_694_);
                                                return v___x_695_;
                                            } else {
                                                v___x_696_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_687_, v_arg_681_);
                                                lean_dec_ref(v_arg_681_);
                                                if v___x_696_ == 0 {
                                                    lean_dec_ref(v_arg_687_);
                                                    lean_dec_ref(v_arg_684_);
                                                    lean_dec_ref(v_arg_676_);
                                                    lean_dec_ref(v_arg_673_);
                                                    lean_dec_ref(v_e_656_);
                                                    v___x_697_ = lean_box(0);
                                                    v___x_698_ = lean_alloc_ctor(0, 1, (0) as u32);
                                                    lean_ctor_set(v___x_698_, 0, v___x_697_);
                                                    return v___x_698_;
                                                } else {
                                                    v___x_699_ = lean_box(0);
                                                    lean_inc_ref(v_arg_673_);
                                                    v___x_700_ = lean_alloc_ctor(0, 2, (0) as u32);
                                                    lean_ctor_set(v___x_700_, 0, v___x_699_);
                                                    lean_ctor_set(v___x_700_, 1, v_arg_673_);
                                                    v___x_701_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg(v_arg_673_, v_arg_684_, v_e_656_, v_arg_676_, v_arg_687_, v___x_700_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_);
                                                    lean_dec_ref(v_arg_684_);
                                                    if lean_obj_tag(v___x_701_) == 0 {
                                                        v_a_702_ = lean_ctor_get(v___x_701_, 0);
                                                        v_isSharedCheck_715_ =
                                                            (!lean_is_exclusive(v___x_701_)) as u8;
                                                        if v_isSharedCheck_715_ == 0 {
                                                            v___x_704_ = v___x_701_;
                                                            v_isShared_705_ = v_isSharedCheck_715_;
                                                            state = 2;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_702_);
                                                            lean_dec(v___x_701_);
                                                            v___x_704_ = lean_box(0);
                                                            v_isShared_705_ = v_isSharedCheck_715_;
                                                            state = 2;
                                                            continue;
                                                        }
                                                    } else {
                                                        v_a_716_ = lean_ctor_get(v___x_701_, 0);
                                                        v_isSharedCheck_723_ =
                                                            (!lean_is_exclusive(v___x_701_)) as u8;
                                                        if v_isSharedCheck_723_ == 0 {
                                                            v___x_718_ = v___x_701_;
                                                            v_isShared_719_ = v_isSharedCheck_723_;
                                                            state = 5;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_716_);
                                                            lean_dec(v___x_701_);
                                                            v___x_718_ = lean_box(0);
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
                v___x_669_ = lean_box(0);
                v___x_670_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_670_, 0, v___x_669_);
                return v___x_670_;
            }
            2 => {
                v_fst_706_ = lean_ctor_get(v_a_702_, 0);
                lean_inc(v_fst_706_);
                lean_dec(v_a_702_);
                if lean_obj_tag(v_fst_706_) == 0 {
                    v___x_707_ = lean_box(0);
                    if v_isShared_705_ == 0 {
                        lean_ctor_set(v___x_704_, 0, v___x_707_);
                        v___x_709_ = v___x_704_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
                        v___x_709_ = v_reuseFailAlloc_710_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_val_711_ = lean_ctor_get(v_fst_706_, 0);
                    lean_inc(v_val_711_);
                    lean_dec_ref_known(v_fst_706_, 1);
                    if v_isShared_705_ == 0 {
                        lean_ctor_set(v___x_704_, 0, v_val_711_);
                        v___x_713_ = v___x_704_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_714_, 0, v_val_711_);
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
                    v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_716_);
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
    mut v_e_724_: *mut LeanObject,
    mut v_a_725_: *mut LeanObject,
    mut v_a_726_: *mut LeanObject,
    mut v_a_727_: *mut LeanObject,
    mut v_a_728_: *mut LeanObject,
    mut v_a_729_: *mut LeanObject,
    mut v_a_730_: *mut LeanObject,
    mut v_a_731_: *mut LeanObject,
    mut v_a_732_: *mut LeanObject,
    mut v_a_733_: *mut LeanObject,
    mut v_a_734_: *mut LeanObject,
    mut v_a_735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_736_: *mut LeanObject = core::ptr::null_mut();
    v_res_736_ = l_Lean_Meta_Grind_Arith_CommRing_propagatePower(
        v_e_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_,
        v_a_733_, v_a_734_,
    );
    lean_dec(v_a_734_);
    lean_dec_ref(v_a_733_);
    lean_dec(v_a_732_);
    lean_dec_ref(v_a_731_);
    lean_dec(v_a_730_);
    lean_dec_ref(v_a_729_);
    lean_dec(v_a_728_);
    lean_dec_ref(v_a_727_);
    lean_dec(v_a_726_);
    lean_dec(v_a_725_);
    return v_res_736_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0(
    mut v_a_737_: *mut LeanObject,
    mut v_a_738_: *mut LeanObject,
    mut v_e_739_: *mut LeanObject,
    mut v_a_740_: *mut LeanObject,
    mut v_a_741_: *mut LeanObject,
    mut v_inst_742_: *mut LeanObject,
    mut v_a_743_: *mut LeanObject,
    mut v___y_744_: *mut LeanObject,
    mut v___y_745_: *mut LeanObject,
    mut v___y_746_: *mut LeanObject,
    mut v___y_747_: *mut LeanObject,
    mut v___y_748_: *mut LeanObject,
    mut v___y_749_: *mut LeanObject,
    mut v___y_750_: *mut LeanObject,
    mut v___y_751_: *mut LeanObject,
    mut v___y_752_: *mut LeanObject,
    mut v___y_753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    v___x_755_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___redArg(v_a_737_, v_a_738_, v_e_739_, v_a_740_, v_a_741_, v_a_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
    return v___x_755_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_756_: *mut LeanObject = *_args.add(0);
    let mut v_a_757_: *mut LeanObject = *_args.add(1);
    let mut v_e_758_: *mut LeanObject = *_args.add(2);
    let mut v_a_759_: *mut LeanObject = *_args.add(3);
    let mut v_a_760_: *mut LeanObject = *_args.add(4);
    let mut v_inst_761_: *mut LeanObject = *_args.add(5);
    let mut v_a_762_: *mut LeanObject = *_args.add(6);
    let mut v___y_763_: *mut LeanObject = *_args.add(7);
    let mut v___y_764_: *mut LeanObject = *_args.add(8);
    let mut v___y_765_: *mut LeanObject = *_args.add(9);
    let mut v___y_766_: *mut LeanObject = *_args.add(10);
    let mut v___y_767_: *mut LeanObject = *_args.add(11);
    let mut v___y_768_: *mut LeanObject = *_args.add(12);
    let mut v___y_769_: *mut LeanObject = *_args.add(13);
    let mut v___y_770_: *mut LeanObject = *_args.add(14);
    let mut v___y_771_: *mut LeanObject = *_args.add(15);
    let mut v___y_772_: *mut LeanObject = *_args.add(16);
    let mut v___y_773_: *mut LeanObject = *_args.add(17);
    let mut v_res_774_: *mut LeanObject = core::ptr::null_mut();
    v_res_774_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_Grind_Arith_CommRing_propagatePower_spec__0(v_a_756_, v_a_757_, v_e_758_, v_a_759_, v_a_760_, v_inst_761_, v_a_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
    lean_dec(v___y_772_);
    lean_dec_ref(v___y_771_);
    lean_dec(v___y_770_);
    lean_dec_ref(v___y_769_);
    lean_dec(v___y_768_);
    lean_dec_ref(v___y_767_);
    lean_dec(v___y_766_);
    lean_dec_ref(v___y_765_);
    lean_dec(v___y_764_);
    lean_dec(v___y_763_);
    lean_dec_ref(v_a_757_);
    return v_res_774_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_0__Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_14_()
-> *mut LeanObject {
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    v___x_776_ = l_Lean_Meta_Grind_Arith_CommRing_propagatePower___closed__2;
    v___x_777_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_propagatePower___boxed as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_778_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_776_, v___x_777_);
    return v___x_778_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_0__Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_14____boxed(
    mut v_a_779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_780_: *mut LeanObject = core::ptr::null_mut();
    v_res_780_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_0__Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_14_();
    return v_res_780_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_NatInstTesters(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_0__Lean_Meta_Grind_Arith_CommRing_propagatePower___regBuiltin_Lean_Meta_Grind_Arith_CommRing_propagatePower_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Power_905482453____hygCtx___hyg_14_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_NatInstTesters(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Power(builtin);
}
