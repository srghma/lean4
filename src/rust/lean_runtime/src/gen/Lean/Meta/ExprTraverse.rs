// Lean compiler output
// Module: Lean.Meta.ExprTraverse
// Imports: Lean.SubExpr
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl,
    l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl,
};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_mkForallFVars___boxed, l_Lean_Meta_mkLambdaFVars___boxed,
    l_Lean_Meta_mkLetFVars___boxed, l_Lean_Meta_withLetDecl___redArg,
    l_Lean_Meta_withLocalDecl___redArg,
};
use crate::r#gen::Lean::SubExpr::{
    initialize_Lean_SubExpr, l_Lean_Expr_traverseAppWithPos___redArg,
    l_Lean_SubExpr_Pos_pushBindingBody, l_Lean_SubExpr_Pos_pushBindingDomain,
    l_Lean_SubExpr_Pos_pushLetBody, l_Lean_SubExpr_Pos_pushLetValue,
    l_Lean_SubExpr_Pos_pushLetVarType, l_Lean_SubExpr_Pos_pushProj, l_Lean_SubExpr_Pos_root,
    runtime_initialize_Lean_SubExpr,
};
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::lean_imports_rs::Lean::Expr::lean_expr_instantiate_rev;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_1, lean_apply_2, lean_apply_3,
    lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag, lean_unbox,
};
pub static l_Lean_Meta_traverseLambdaWithPos___redArg___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_traverseLambdaWithPos___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_traverseLambdaWithPos___redArg___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg___lam__0(
    mut v_visit_428_: *mut LeanObject,
    mut v_x_429_: *mut LeanObject,
    mut v___y_430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_431_: *mut LeanObject = core::ptr::null_mut();
    v___x_431_ = lean_apply_1(v_visit_428_, v___y_430_);
    return v___x_431_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg___lam__0___boxed(
    mut v_visit_432_: *mut LeanObject,
    mut v_x_433_: *mut LeanObject,
    mut v___y_434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_435_: *mut LeanObject = core::ptr::null_mut();
    v_res_435_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg___lam__0(
        v_visit_432_,
        v_x_433_,
        v___y_434_,
    );
    lean_dec(v_x_433_);
    return v_res_435_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(
    mut v_t_436_: *mut LeanObject,
    mut v_visit_437_: *mut LeanObject,
    mut v_e_438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
    v___f_439_ = lean_alloc_closure(
        l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_439_, 0, v_visit_437_);
    v___x_440_ = l_Lean_SubExpr_Pos_root;
    v___x_441_ = lean_apply_3(v_t_436_, v___f_439_, v___x_440_, v_e_438_);
    return v___x_441_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos(
    mut v_M_442_: *mut LeanObject,
    mut v_t_443_: *mut LeanObject,
    mut v_visit_444_: *mut LeanObject,
    mut v_e_445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
    v___x_446_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(
        v_t_443_,
        v_visit_444_,
        v_e_445_,
    );
    return v___x_446_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__2(
    mut v_fvars_447_: *mut LeanObject,
    mut v_inst_448_: *mut LeanObject,
    mut v_body_449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_450_: u8 = 0;
    let mut v___x_451_: u8 = 0;
    let mut v___x_452_: u8 = 0;
    let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
    v___x_450_ = 0;
    v___x_451_ = 1;
    v___x_452_ = 1;
    v___x_453_ = lean_box((v___x_450_) as usize);
    v___x_454_ = lean_box((v___x_451_) as usize);
    v___x_455_ = lean_box((v___x_450_) as usize);
    v___x_456_ = lean_box((v___x_451_) as usize);
    v___x_457_ = lean_box((v___x_452_) as usize);
    v___x_458_ = lean_alloc_closure(
        l_Lean_Meta_mkLambdaFVars___boxed as *mut core::ffi::c_void,
        12,
        7,
    );
    lean_closure_set(v___x_458_, 0, v_fvars_447_);
    lean_closure_set(v___x_458_, 1, v_body_449_);
    lean_closure_set(v___x_458_, 2, v___x_453_);
    lean_closure_set(v___x_458_, 3, v___x_454_);
    lean_closure_set(v___x_458_, 4, v___x_455_);
    lean_closure_set(v___x_458_, 5, v___x_456_);
    lean_closure_set(v___x_458_, 6, v___x_457_);
    v___x_459_ = lean_apply_2(v_inst_448_, lean_box(0), v___x_458_);
    return v___x_459_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1(
    mut v_inst_460_: *mut LeanObject,
    mut v_inst_461_: *mut LeanObject,
    mut v_binderName_462_: *mut LeanObject,
    mut v_binderInfo_463_: u8,
    mut v___f_464_: *mut LeanObject,
    mut v_d_465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_466_: u8 = 0;
    let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
    v___x_466_ = 0;
    v___x_467_ = l_Lean_Meta_withLocalDecl___redArg(
        v_inst_460_,
        v_inst_461_,
        v_binderName_462_,
        v_binderInfo_463_,
        v_d_465_,
        v___f_464_,
        v___x_466_,
    );
    return v___x_467_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1___boxed(
    mut v_inst_468_: *mut LeanObject,
    mut v_inst_469_: *mut LeanObject,
    mut v_binderName_470_: *mut LeanObject,
    mut v_binderInfo_471_: *mut LeanObject,
    mut v___f_472_: *mut LeanObject,
    mut v_d_473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_binderInfo_120__boxed_474_: u8 = 0;
    let mut v_res_475_: *mut LeanObject = core::ptr::null_mut();
    v_binderInfo_120__boxed_474_ = (lean_unbox(v_binderInfo_471_) as u8);
    v_res_475_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1(v_inst_468_, v_inst_469_, v_binderName_470_, v_binderInfo_120__boxed_474_, v___f_472_, v_d_473_);
    return v_res_475_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__0___boxed(
    mut v_fvars_476_: *mut LeanObject,
    mut v_p_477_: *mut LeanObject,
    mut v_inst_478_: *mut LeanObject,
    mut v_inst_479_: *mut LeanObject,
    mut v_inst_480_: *mut LeanObject,
    mut v_f_481_: *mut LeanObject,
    mut v_body_482_: *mut LeanObject,
    mut v_x_483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_484_: *mut LeanObject = core::ptr::null_mut();
    v_res_484_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__0(v_fvars_476_, v_p_477_, v_inst_478_, v_inst_479_, v_inst_480_, v_f_481_, v_body_482_, v_x_483_);
    lean_dec(v_p_477_);
    return v_res_484_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg(
    mut v_inst_485_: *mut LeanObject,
    mut v_inst_486_: *mut LeanObject,
    mut v_inst_487_: *mut LeanObject,
    mut v_f_488_: *mut LeanObject,
    mut v_fvars_489_: *mut LeanObject,
    mut v_p_490_: *mut LeanObject,
    mut v_a_491_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_491_) == 6 {
        let mut v_toBind_492_: *mut LeanObject = core::ptr::null_mut();
        let mut v_binderName_493_: *mut LeanObject = core::ptr::null_mut();
        let mut v_binderType_494_: *mut LeanObject = core::ptr::null_mut();
        let mut v_body_495_: *mut LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_496_: u8 = 0;
        let mut v___f_497_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_499_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_501_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_492_ = lean_ctor_get(v_inst_485_, 1);
        lean_inc(v_toBind_492_);
        v_binderName_493_ = lean_ctor_get(v_a_491_, 0);
        lean_inc(v_binderName_493_);
        v_binderType_494_ = lean_ctor_get(v_a_491_, 1);
        lean_inc_ref(v_binderType_494_);
        v_body_495_ = lean_ctor_get(v_a_491_, 2);
        lean_inc_ref(v_body_495_);
        v_binderInfo_496_ = lean_ctor_get_uint8(
            v_a_491_,
            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
        );
        lean_dec_ref_known(v_a_491_, 3);
        lean_inc(v_f_488_);
        lean_inc_ref(v_inst_487_);
        lean_inc_ref(v_inst_485_);
        lean_inc(v_p_490_);
        lean_inc_ref(v_fvars_489_);
        v___f_497_ = lean_alloc_closure(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 7);
        lean_closure_set(v___f_497_, 0, v_fvars_489_);
        lean_closure_set(v___f_497_, 1, v_p_490_);
        lean_closure_set(v___f_497_, 2, v_inst_485_);
        lean_closure_set(v___f_497_, 3, v_inst_486_);
        lean_closure_set(v___f_497_, 4, v_inst_487_);
        lean_closure_set(v___f_497_, 5, v_f_488_);
        lean_closure_set(v___f_497_, 6, v_body_495_);
        v___x_498_ = lean_box((v_binderInfo_496_) as usize);
        v___f_499_ = lean_alloc_closure(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1___boxed as *mut core::ffi::c_void, 6, 5);
        lean_closure_set(v___f_499_, 0, v_inst_487_);
        lean_closure_set(v___f_499_, 1, v_inst_485_);
        lean_closure_set(v___f_499_, 2, v_binderName_493_);
        lean_closure_set(v___f_499_, 3, v___x_498_);
        lean_closure_set(v___f_499_, 4, v___f_497_);
        v___x_500_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_p_490_);
        lean_dec(v_p_490_);
        v___x_501_ = lean_expr_instantiate_rev(v_binderType_494_, v_fvars_489_);
        lean_dec_ref(v_fvars_489_);
        lean_dec_ref(v_binderType_494_);
        v___x_502_ = lean_apply_2(v_f_488_, v___x_500_, v___x_501_);
        v___x_503_ = lean_apply_4(
            v_toBind_492_,
            lean_box(0),
            lean_box(0),
            v___x_502_,
            v___f_499_,
        );
        return v___x_503_;
    } else {
        let mut v_toBind_504_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_505_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_506_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_487_);
        v_toBind_504_ = lean_ctor_get(v_inst_485_, 1);
        lean_inc(v_toBind_504_);
        lean_dec_ref(v_inst_485_);
        lean_inc_ref(v_fvars_489_);
        v___f_505_ = lean_alloc_closure(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__2 as *mut core::ffi::c_void, 3, 2);
        lean_closure_set(v___f_505_, 0, v_fvars_489_);
        lean_closure_set(v___f_505_, 1, v_inst_486_);
        v___x_506_ = lean_expr_instantiate_rev(v_a_491_, v_fvars_489_);
        lean_dec_ref(v_fvars_489_);
        lean_dec_ref(v_a_491_);
        v___x_507_ = lean_apply_2(v_f_488_, v_p_490_, v___x_506_);
        v___x_508_ = lean_apply_4(
            v_toBind_504_,
            lean_box(0),
            lean_box(0),
            v___x_507_,
            v___f_505_,
        );
        return v___x_508_;
    }
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__0(
    mut v_fvars_509_: *mut LeanObject,
    mut v_p_510_: *mut LeanObject,
    mut v_inst_511_: *mut LeanObject,
    mut v_inst_512_: *mut LeanObject,
    mut v_inst_513_: *mut LeanObject,
    mut v_f_514_: *mut LeanObject,
    mut v_body_515_: *mut LeanObject,
    mut v_x_516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
    v___x_517_ = lean_array_push(v_fvars_509_, v_x_516_);
    v___x_518_ = l_Lean_SubExpr_Pos_pushBindingBody(v_p_510_);
    v___x_519_ =
        l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg(
            v_inst_511_,
            v_inst_512_,
            v_inst_513_,
            v_f_514_,
            v___x_517_,
            v___x_518_,
            v_body_515_,
        );
    return v___x_519_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit(
    mut v_M_520_: *mut LeanObject,
    mut v_inst_521_: *mut LeanObject,
    mut v_inst_522_: *mut LeanObject,
    mut v_inst_523_: *mut LeanObject,
    mut v_f_524_: *mut LeanObject,
    mut v_fvars_525_: *mut LeanObject,
    mut v_p_526_: *mut LeanObject,
    mut v_a_527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
    v___x_528_ =
        l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg(
            v_inst_521_,
            v_inst_522_,
            v_inst_523_,
            v_f_524_,
            v_fvars_525_,
            v_p_526_,
            v_a_527_,
        );
    return v___x_528_;
}
pub unsafe fn l_Lean_Meta_traverseLambdaWithPos___redArg(
    mut v_inst_531_: *mut LeanObject,
    mut v_inst_532_: *mut LeanObject,
    mut v_inst_533_: *mut LeanObject,
    mut v_f_534_: *mut LeanObject,
    mut v_p_535_: *mut LeanObject,
    mut v_e_536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
    v___x_537_ = l_Lean_Meta_traverseLambdaWithPos___redArg___closed__0;
    v___x_538_ =
        l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg(
            v_inst_531_,
            v_inst_532_,
            v_inst_533_,
            v_f_534_,
            v___x_537_,
            v_p_535_,
            v_e_536_,
        );
    return v___x_538_;
}
pub unsafe fn l_Lean_Meta_traverseLambdaWithPos(
    mut v_M_539_: *mut LeanObject,
    mut v_inst_540_: *mut LeanObject,
    mut v_inst_541_: *mut LeanObject,
    mut v_inst_542_: *mut LeanObject,
    mut v_f_543_: *mut LeanObject,
    mut v_p_544_: *mut LeanObject,
    mut v_e_545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
    v___x_546_ = l_Lean_Meta_traverseLambdaWithPos___redArg(
        v_inst_540_,
        v_inst_541_,
        v_inst_542_,
        v_f_543_,
        v_p_544_,
        v_e_545_,
    );
    return v___x_546_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__2(
    mut v_fvars_547_: *mut LeanObject,
    mut v_inst_548_: *mut LeanObject,
    mut v_body_549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_550_: u8 = 0;
    let mut v___x_551_: u8 = 0;
    let mut v___x_552_: u8 = 0;
    let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    v___x_550_ = 0;
    v___x_551_ = 1;
    v___x_552_ = 1;
    v___x_553_ = lean_box((v___x_550_) as usize);
    v___x_554_ = lean_box((v___x_551_) as usize);
    v___x_555_ = lean_box((v___x_551_) as usize);
    v___x_556_ = lean_box((v___x_552_) as usize);
    lean_inc_ref(v_fvars_547_);
    v___x_557_ = lean_alloc_closure(
        l_Lean_Meta_mkForallFVars___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    lean_closure_set(v___x_557_, 0, v_fvars_547_);
    lean_closure_set(v___x_557_, 1, v_body_549_);
    lean_closure_set(v___x_557_, 2, v___x_553_);
    lean_closure_set(v___x_557_, 3, v___x_554_);
    lean_closure_set(v___x_557_, 4, v___x_555_);
    lean_closure_set(v___x_557_, 5, v___x_556_);
    v___x_558_ = lean_apply_2(v_inst_548_, lean_box(0), v___x_557_);
    return v___x_558_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__2___boxed(
    mut v_fvars_559_: *mut LeanObject,
    mut v_inst_560_: *mut LeanObject,
    mut v_body_561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_562_: *mut LeanObject = core::ptr::null_mut();
    v_res_562_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__2(v_fvars_559_, v_inst_560_, v_body_561_);
    lean_dec_ref(v_fvars_559_);
    return v_res_562_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0___boxed(
    mut v_fvars_563_: *mut LeanObject,
    mut v_p_564_: *mut LeanObject,
    mut v_inst_565_: *mut LeanObject,
    mut v_inst_566_: *mut LeanObject,
    mut v_inst_567_: *mut LeanObject,
    mut v_f_568_: *mut LeanObject,
    mut v_body_569_: *mut LeanObject,
    mut v_x_570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_571_: *mut LeanObject = core::ptr::null_mut();
    v_res_571_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0(v_fvars_563_, v_p_564_, v_inst_565_, v_inst_566_, v_inst_567_, v_f_568_, v_body_569_, v_x_570_);
    lean_dec(v_p_564_);
    lean_dec_ref(v_fvars_563_);
    return v_res_571_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg(
    mut v_inst_572_: *mut LeanObject,
    mut v_inst_573_: *mut LeanObject,
    mut v_inst_574_: *mut LeanObject,
    mut v_f_575_: *mut LeanObject,
    mut v_fvars_576_: *mut LeanObject,
    mut v_p_577_: *mut LeanObject,
    mut v_a_578_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_578_) == 7 {
        let mut v_toBind_579_: *mut LeanObject = core::ptr::null_mut();
        let mut v_binderName_580_: *mut LeanObject = core::ptr::null_mut();
        let mut v_binderType_581_: *mut LeanObject = core::ptr::null_mut();
        let mut v_body_582_: *mut LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_583_: u8 = 0;
        let mut v___f_584_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_586_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_590_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_579_ = lean_ctor_get(v_inst_572_, 1);
        lean_inc(v_toBind_579_);
        v_binderName_580_ = lean_ctor_get(v_a_578_, 0);
        lean_inc(v_binderName_580_);
        v_binderType_581_ = lean_ctor_get(v_a_578_, 1);
        lean_inc_ref(v_binderType_581_);
        v_body_582_ = lean_ctor_get(v_a_578_, 2);
        lean_inc_ref(v_body_582_);
        v_binderInfo_583_ = lean_ctor_get_uint8(
            v_a_578_,
            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
        );
        lean_dec_ref_known(v_a_578_, 3);
        lean_inc(v_f_575_);
        lean_inc_ref(v_inst_574_);
        lean_inc_ref(v_inst_572_);
        lean_inc(v_p_577_);
        lean_inc_ref(v_fvars_576_);
        v___f_584_ = lean_alloc_closure(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 7);
        lean_closure_set(v___f_584_, 0, v_fvars_576_);
        lean_closure_set(v___f_584_, 1, v_p_577_);
        lean_closure_set(v___f_584_, 2, v_inst_572_);
        lean_closure_set(v___f_584_, 3, v_inst_573_);
        lean_closure_set(v___f_584_, 4, v_inst_574_);
        lean_closure_set(v___f_584_, 5, v_f_575_);
        lean_closure_set(v___f_584_, 6, v_body_582_);
        v___x_585_ = lean_box((v_binderInfo_583_) as usize);
        v___f_586_ = lean_alloc_closure(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1___boxed as *mut core::ffi::c_void, 6, 5);
        lean_closure_set(v___f_586_, 0, v_inst_574_);
        lean_closure_set(v___f_586_, 1, v_inst_572_);
        lean_closure_set(v___f_586_, 2, v_binderName_580_);
        lean_closure_set(v___f_586_, 3, v___x_585_);
        lean_closure_set(v___f_586_, 4, v___f_584_);
        v___x_587_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_p_577_);
        lean_dec(v_p_577_);
        v___x_588_ = lean_expr_instantiate_rev(v_binderType_581_, v_fvars_576_);
        lean_dec_ref(v_binderType_581_);
        v___x_589_ = lean_apply_2(v_f_575_, v___x_587_, v___x_588_);
        v___x_590_ = lean_apply_4(
            v_toBind_579_,
            lean_box(0),
            lean_box(0),
            v___x_589_,
            v___f_586_,
        );
        return v___x_590_;
    } else {
        let mut v_toBind_591_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_592_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_574_);
        v_toBind_591_ = lean_ctor_get(v_inst_572_, 1);
        lean_inc(v_toBind_591_);
        lean_dec_ref(v_inst_572_);
        lean_inc_ref(v_fvars_576_);
        v___f_592_ = lean_alloc_closure(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__2___boxed as *mut core::ffi::c_void, 3, 2);
        lean_closure_set(v___f_592_, 0, v_fvars_576_);
        lean_closure_set(v___f_592_, 1, v_inst_573_);
        v___x_593_ = lean_expr_instantiate_rev(v_a_578_, v_fvars_576_);
        lean_dec_ref(v_a_578_);
        v___x_594_ = lean_apply_2(v_f_575_, v_p_577_, v___x_593_);
        v___x_595_ = lean_apply_4(
            v_toBind_591_,
            lean_box(0),
            lean_box(0),
            v___x_594_,
            v___f_592_,
        );
        return v___x_595_;
    }
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0(
    mut v_fvars_596_: *mut LeanObject,
    mut v_p_597_: *mut LeanObject,
    mut v_inst_598_: *mut LeanObject,
    mut v_inst_599_: *mut LeanObject,
    mut v_inst_600_: *mut LeanObject,
    mut v_f_601_: *mut LeanObject,
    mut v_body_602_: *mut LeanObject,
    mut v_x_603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_fvars_596_);
    v___x_604_ = lean_array_push(v_fvars_596_, v_x_603_);
    v___x_605_ = l_Lean_SubExpr_Pos_pushBindingBody(v_p_597_);
    v___x_606_ =
        l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg(
            v_inst_598_,
            v_inst_599_,
            v_inst_600_,
            v_f_601_,
            v___x_604_,
            v___x_605_,
            v_body_602_,
        );
    lean_dec_ref(v___x_604_);
    return v___x_606_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___boxed(
    mut v_inst_607_: *mut LeanObject,
    mut v_inst_608_: *mut LeanObject,
    mut v_inst_609_: *mut LeanObject,
    mut v_f_610_: *mut LeanObject,
    mut v_fvars_611_: *mut LeanObject,
    mut v_p_612_: *mut LeanObject,
    mut v_a_613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_614_: *mut LeanObject = core::ptr::null_mut();
    v_res_614_ =
        l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg(
            v_inst_607_,
            v_inst_608_,
            v_inst_609_,
            v_f_610_,
            v_fvars_611_,
            v_p_612_,
            v_a_613_,
        );
    lean_dec_ref(v_fvars_611_);
    return v_res_614_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit(
    mut v_M_615_: *mut LeanObject,
    mut v_inst_616_: *mut LeanObject,
    mut v_inst_617_: *mut LeanObject,
    mut v_inst_618_: *mut LeanObject,
    mut v_f_619_: *mut LeanObject,
    mut v_fvars_620_: *mut LeanObject,
    mut v_p_621_: *mut LeanObject,
    mut v_a_622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    v___x_623_ =
        l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg(
            v_inst_616_,
            v_inst_617_,
            v_inst_618_,
            v_f_619_,
            v_fvars_620_,
            v_p_621_,
            v_a_622_,
        );
    return v___x_623_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___boxed(
    mut v_M_624_: *mut LeanObject,
    mut v_inst_625_: *mut LeanObject,
    mut v_inst_626_: *mut LeanObject,
    mut v_inst_627_: *mut LeanObject,
    mut v_f_628_: *mut LeanObject,
    mut v_fvars_629_: *mut LeanObject,
    mut v_p_630_: *mut LeanObject,
    mut v_a_631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_632_: *mut LeanObject = core::ptr::null_mut();
    v_res_632_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit(
        v_M_624_,
        v_inst_625_,
        v_inst_626_,
        v_inst_627_,
        v_f_628_,
        v_fvars_629_,
        v_p_630_,
        v_a_631_,
    );
    lean_dec_ref(v_fvars_629_);
    return v_res_632_;
}
pub unsafe fn l_Lean_Meta_traverseForallWithPos___redArg(
    mut v_inst_633_: *mut LeanObject,
    mut v_inst_634_: *mut LeanObject,
    mut v_inst_635_: *mut LeanObject,
    mut v_f_636_: *mut LeanObject,
    mut v_p_637_: *mut LeanObject,
    mut v_e_638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    v___x_639_ = l_Lean_Meta_traverseLambdaWithPos___redArg___closed__0;
    v___x_640_ =
        l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg(
            v_inst_633_,
            v_inst_634_,
            v_inst_635_,
            v_f_636_,
            v___x_639_,
            v_p_637_,
            v_e_638_,
        );
    return v___x_640_;
}
pub unsafe fn l_Lean_Meta_traverseForallWithPos(
    mut v_M_641_: *mut LeanObject,
    mut v_inst_642_: *mut LeanObject,
    mut v_inst_643_: *mut LeanObject,
    mut v_inst_644_: *mut LeanObject,
    mut v_f_645_: *mut LeanObject,
    mut v_p_646_: *mut LeanObject,
    mut v_e_647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    v___x_648_ = l_Lean_Meta_traverseForallWithPos___redArg(
        v_inst_642_,
        v_inst_643_,
        v_inst_644_,
        v_f_645_,
        v_p_646_,
        v_e_647_,
    );
    return v___x_648_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__1(
    mut v_inst_649_: *mut LeanObject,
    mut v_inst_650_: *mut LeanObject,
    mut v_declName_651_: *mut LeanObject,
    mut v_type_652_: *mut LeanObject,
    mut v___f_653_: *mut LeanObject,
    mut v_value_654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_655_: u8 = 0;
    let mut v___x_656_: u8 = 0;
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    v___x_655_ = 0;
    v___x_656_ = 0;
    v___x_657_ = l_Lean_Meta_withLetDecl___redArg(
        v_inst_649_,
        v_inst_650_,
        v_declName_651_,
        v_type_652_,
        v_value_654_,
        v___f_653_,
        v___x_655_,
        v___x_656_,
    );
    return v___x_657_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__2(
    mut v_inst_658_: *mut LeanObject,
    mut v_inst_659_: *mut LeanObject,
    mut v_declName_660_: *mut LeanObject,
    mut v___f_661_: *mut LeanObject,
    mut v_p_662_: *mut LeanObject,
    mut v_value_663_: *mut LeanObject,
    mut v_fvars_664_: *mut LeanObject,
    mut v_f_665_: *mut LeanObject,
    mut v_toBind_666_: *mut LeanObject,
    mut v_type_667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    v___f_668_ = lean_alloc_closure(
        l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__1
            as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_668_, 0, v_inst_658_);
    lean_closure_set(v___f_668_, 1, v_inst_659_);
    lean_closure_set(v___f_668_, 2, v_declName_660_);
    lean_closure_set(v___f_668_, 3, v_type_667_);
    lean_closure_set(v___f_668_, 4, v___f_661_);
    v___x_669_ = l_Lean_SubExpr_Pos_pushLetValue(v_p_662_);
    v___x_670_ = lean_expr_instantiate_rev(v_value_663_, v_fvars_664_);
    v___x_671_ = lean_apply_2(v_f_665_, v___x_669_, v___x_670_);
    v___x_672_ = lean_apply_4(
        v_toBind_666_,
        lean_box(0),
        lean_box(0),
        v___x_671_,
        v___f_668_,
    );
    return v___x_672_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__2___boxed(
    mut v_inst_673_: *mut LeanObject,
    mut v_inst_674_: *mut LeanObject,
    mut v_declName_675_: *mut LeanObject,
    mut v___f_676_: *mut LeanObject,
    mut v_p_677_: *mut LeanObject,
    mut v_value_678_: *mut LeanObject,
    mut v_fvars_679_: *mut LeanObject,
    mut v_f_680_: *mut LeanObject,
    mut v_toBind_681_: *mut LeanObject,
    mut v_type_682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_683_: *mut LeanObject = core::ptr::null_mut();
    v_res_683_ =
        l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__2(
            v_inst_673_,
            v_inst_674_,
            v_declName_675_,
            v___f_676_,
            v_p_677_,
            v_value_678_,
            v_fvars_679_,
            v_f_680_,
            v_toBind_681_,
            v_type_682_,
        );
    lean_dec_ref(v_fvars_679_);
    lean_dec_ref(v_value_678_);
    lean_dec(v_p_677_);
    return v_res_683_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__3(
    mut v_fvars_684_: *mut LeanObject,
    mut v_inst_685_: *mut LeanObject,
    mut v_body_686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_687_: u8 = 0;
    let mut v___x_688_: u8 = 0;
    let mut v___x_689_: u8 = 0;
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
    v___x_687_ = 0;
    v___x_688_ = 1;
    v___x_689_ = 1;
    v___x_690_ = lean_box((v___x_687_) as usize);
    v___x_691_ = lean_box((v___x_688_) as usize);
    v___x_692_ = lean_box((v___x_689_) as usize);
    v___x_693_ = lean_alloc_closure(
        l_Lean_Meta_mkLetFVars___boxed as *mut core::ffi::c_void,
        10,
        5,
    );
    lean_closure_set(v___x_693_, 0, v_fvars_684_);
    lean_closure_set(v___x_693_, 1, v_body_686_);
    lean_closure_set(v___x_693_, 2, v___x_690_);
    lean_closure_set(v___x_693_, 3, v___x_691_);
    lean_closure_set(v___x_693_, 4, v___x_692_);
    v___x_694_ = lean_apply_2(v_inst_685_, lean_box(0), v___x_693_);
    return v___x_694_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__0___boxed(
    mut v_fvars_695_: *mut LeanObject,
    mut v_p_696_: *mut LeanObject,
    mut v_inst_697_: *mut LeanObject,
    mut v_inst_698_: *mut LeanObject,
    mut v_inst_699_: *mut LeanObject,
    mut v_f_700_: *mut LeanObject,
    mut v_body_701_: *mut LeanObject,
    mut v_x_702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_703_: *mut LeanObject = core::ptr::null_mut();
    v_res_703_ =
        l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__0(
            v_fvars_695_,
            v_p_696_,
            v_inst_697_,
            v_inst_698_,
            v_inst_699_,
            v_f_700_,
            v_body_701_,
            v_x_702_,
        );
    lean_dec(v_p_696_);
    return v_res_703_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg(
    mut v_inst_704_: *mut LeanObject,
    mut v_inst_705_: *mut LeanObject,
    mut v_inst_706_: *mut LeanObject,
    mut v_f_707_: *mut LeanObject,
    mut v_fvars_708_: *mut LeanObject,
    mut v_p_709_: *mut LeanObject,
    mut v_x_710_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_710_) == 8 {
        let mut v_toBind_711_: *mut LeanObject = core::ptr::null_mut();
        let mut v_declName_712_: *mut LeanObject = core::ptr::null_mut();
        let mut v_type_713_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_714_: *mut LeanObject = core::ptr::null_mut();
        let mut v_body_715_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_716_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_717_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_711_ = lean_ctor_get(v_inst_704_, 1);
        lean_inc_n(v_toBind_711_, 2);
        v_declName_712_ = lean_ctor_get(v_x_710_, 0);
        lean_inc(v_declName_712_);
        v_type_713_ = lean_ctor_get(v_x_710_, 1);
        lean_inc_ref(v_type_713_);
        v_value_714_ = lean_ctor_get(v_x_710_, 2);
        lean_inc_ref(v_value_714_);
        v_body_715_ = lean_ctor_get(v_x_710_, 3);
        lean_inc_ref(v_body_715_);
        lean_dec_ref_known(v_x_710_, 4);
        lean_inc_n(v_f_707_, 2);
        lean_inc_ref(v_inst_706_);
        lean_inc_ref(v_inst_704_);
        lean_inc_n(v_p_709_, 2);
        lean_inc_ref_n(v_fvars_708_, 2);
        v___f_716_ = lean_alloc_closure(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 7);
        lean_closure_set(v___f_716_, 0, v_fvars_708_);
        lean_closure_set(v___f_716_, 1, v_p_709_);
        lean_closure_set(v___f_716_, 2, v_inst_704_);
        lean_closure_set(v___f_716_, 3, v_inst_705_);
        lean_closure_set(v___f_716_, 4, v_inst_706_);
        lean_closure_set(v___f_716_, 5, v_f_707_);
        lean_closure_set(v___f_716_, 6, v_body_715_);
        v___f_717_ = lean_alloc_closure(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__2___boxed as *mut core::ffi::c_void, 10, 9);
        lean_closure_set(v___f_717_, 0, v_inst_706_);
        lean_closure_set(v___f_717_, 1, v_inst_704_);
        lean_closure_set(v___f_717_, 2, v_declName_712_);
        lean_closure_set(v___f_717_, 3, v___f_716_);
        lean_closure_set(v___f_717_, 4, v_p_709_);
        lean_closure_set(v___f_717_, 5, v_value_714_);
        lean_closure_set(v___f_717_, 6, v_fvars_708_);
        lean_closure_set(v___f_717_, 7, v_f_707_);
        lean_closure_set(v___f_717_, 8, v_toBind_711_);
        v___x_718_ = l_Lean_SubExpr_Pos_pushLetVarType(v_p_709_);
        lean_dec(v_p_709_);
        v___x_719_ = lean_expr_instantiate_rev(v_type_713_, v_fvars_708_);
        lean_dec_ref(v_fvars_708_);
        lean_dec_ref(v_type_713_);
        v___x_720_ = lean_apply_2(v_f_707_, v___x_718_, v___x_719_);
        v___x_721_ = lean_apply_4(
            v_toBind_711_,
            lean_box(0),
            lean_box(0),
            v___x_720_,
            v___f_717_,
        );
        return v___x_721_;
    } else {
        let mut v_toBind_722_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_723_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_706_);
        v_toBind_722_ = lean_ctor_get(v_inst_704_, 1);
        lean_inc(v_toBind_722_);
        lean_dec_ref(v_inst_704_);
        lean_inc_ref(v_fvars_708_);
        v___f_723_ = lean_alloc_closure(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__3 as *mut core::ffi::c_void, 3, 2);
        lean_closure_set(v___f_723_, 0, v_fvars_708_);
        lean_closure_set(v___f_723_, 1, v_inst_705_);
        v___x_724_ = lean_expr_instantiate_rev(v_x_710_, v_fvars_708_);
        lean_dec_ref(v_fvars_708_);
        lean_dec_ref(v_x_710_);
        v___x_725_ = lean_apply_2(v_f_707_, v_p_709_, v___x_724_);
        v___x_726_ = lean_apply_4(
            v_toBind_722_,
            lean_box(0),
            lean_box(0),
            v___x_725_,
            v___f_723_,
        );
        return v___x_726_;
    }
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__0(
    mut v_fvars_727_: *mut LeanObject,
    mut v_p_728_: *mut LeanObject,
    mut v_inst_729_: *mut LeanObject,
    mut v_inst_730_: *mut LeanObject,
    mut v_inst_731_: *mut LeanObject,
    mut v_f_732_: *mut LeanObject,
    mut v_body_733_: *mut LeanObject,
    mut v_x_734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    v___x_735_ = lean_array_push(v_fvars_727_, v_x_734_);
    v___x_736_ = l_Lean_SubExpr_Pos_pushLetBody(v_p_728_);
    v___x_737_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg(
        v_inst_729_,
        v_inst_730_,
        v_inst_731_,
        v_f_732_,
        v___x_735_,
        v___x_736_,
        v_body_733_,
    );
    return v___x_737_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit(
    mut v_M_738_: *mut LeanObject,
    mut v_inst_739_: *mut LeanObject,
    mut v_inst_740_: *mut LeanObject,
    mut v_inst_741_: *mut LeanObject,
    mut v_f_742_: *mut LeanObject,
    mut v_fvars_743_: *mut LeanObject,
    mut v_p_744_: *mut LeanObject,
    mut v_x_745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
    v___x_746_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg(
        v_inst_739_,
        v_inst_740_,
        v_inst_741_,
        v_f_742_,
        v_fvars_743_,
        v_p_744_,
        v_x_745_,
    );
    return v___x_746_;
}
pub unsafe fn l_Lean_Meta_traverseLetWithPos___redArg(
    mut v_inst_747_: *mut LeanObject,
    mut v_inst_748_: *mut LeanObject,
    mut v_inst_749_: *mut LeanObject,
    mut v_f_750_: *mut LeanObject,
    mut v_p_751_: *mut LeanObject,
    mut v_e_752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
    v___x_753_ = l_Lean_Meta_traverseLambdaWithPos___redArg___closed__0;
    v___x_754_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg(
        v_inst_747_,
        v_inst_748_,
        v_inst_749_,
        v_f_750_,
        v___x_753_,
        v_p_751_,
        v_e_752_,
    );
    return v___x_754_;
}
pub unsafe fn l_Lean_Meta_traverseLetWithPos(
    mut v_M_755_: *mut LeanObject,
    mut v_inst_756_: *mut LeanObject,
    mut v_inst_757_: *mut LeanObject,
    mut v_inst_758_: *mut LeanObject,
    mut v_f_759_: *mut LeanObject,
    mut v_p_760_: *mut LeanObject,
    mut v_e_761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    v___x_762_ = l_Lean_Meta_traverseLetWithPos___redArg(
        v_inst_756_,
        v_inst_757_,
        v_inst_758_,
        v_f_759_,
        v_p_760_,
        v_e_761_,
    );
    return v___x_762_;
}
pub unsafe fn l_Lean_Meta_traverseChildrenWithPos___redArg(
    mut v_inst_763_: *mut LeanObject,
    mut v_inst_764_: *mut LeanObject,
    mut v_inst_765_: *mut LeanObject,
    mut v_visit_766_: *mut LeanObject,
    mut v_p_767_: *mut LeanObject,
    mut v_e_768_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_e_768_) {
        7 => {
            let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
            v___x_769_ = l_Lean_Meta_traverseForallWithPos___redArg(
                v_inst_763_,
                v_inst_764_,
                v_inst_765_,
                v_visit_766_,
                v_p_767_,
                v_e_768_,
            );
            return v___x_769_;
        }
        6 => {
            let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
            v___x_770_ = l_Lean_Meta_traverseLambdaWithPos___redArg(
                v_inst_763_,
                v_inst_764_,
                v_inst_765_,
                v_visit_766_,
                v_p_767_,
                v_e_768_,
            );
            return v___x_770_;
        }
        8 => {
            let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
            v___x_771_ = l_Lean_Meta_traverseLetWithPos___redArg(
                v_inst_763_,
                v_inst_764_,
                v_inst_765_,
                v_visit_766_,
                v_p_767_,
                v_e_768_,
            );
            return v___x_771_;
        }
        5 => {
            let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_inst_765_);
            lean_dec(v_inst_764_);
            v___x_772_ = l_Lean_Expr_traverseAppWithPos___redArg(
                v_inst_763_,
                v_visit_766_,
                v_p_767_,
                v_e_768_,
            );
            return v___x_772_;
        }
        10 => {
            let mut v_toApplicative_773_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toFunctor_774_: *mut LeanObject = core::ptr::null_mut();
            let mut v_expr_775_: *mut LeanObject = core::ptr::null_mut();
            let mut v_map_776_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_773_ = lean_ctor_get(v_inst_763_, 0);
            lean_inc_ref(v_toApplicative_773_);
            lean_dec_ref(v_inst_765_);
            lean_dec(v_inst_764_);
            lean_dec_ref(v_inst_763_);
            v_toFunctor_774_ = lean_ctor_get(v_toApplicative_773_, 0);
            lean_inc_ref(v_toFunctor_774_);
            lean_dec_ref(v_toApplicative_773_);
            v_expr_775_ = lean_ctor_get(v_e_768_, 1);
            lean_inc_ref(v_expr_775_);
            v_map_776_ = lean_ctor_get(v_toFunctor_774_, 0);
            lean_inc(v_map_776_);
            lean_dec_ref(v_toFunctor_774_);
            v___x_777_ = lean_alloc_closure(
                l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl as *mut core::ffi::c_void,
                2,
                1,
            );
            lean_closure_set(v___x_777_, 0, v_e_768_);
            v___x_778_ = lean_apply_2(v_visit_766_, v_p_767_, v_expr_775_);
            v___x_779_ = lean_apply_4(v_map_776_, lean_box(0), lean_box(0), v___x_777_, v___x_778_);
            return v___x_779_;
        }
        11 => {
            let mut v_toApplicative_780_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toFunctor_781_: *mut LeanObject = core::ptr::null_mut();
            let mut v_struct_782_: *mut LeanObject = core::ptr::null_mut();
            let mut v_map_783_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_780_ = lean_ctor_get(v_inst_763_, 0);
            lean_inc_ref(v_toApplicative_780_);
            lean_dec_ref(v_inst_765_);
            lean_dec(v_inst_764_);
            lean_dec_ref(v_inst_763_);
            v_toFunctor_781_ = lean_ctor_get(v_toApplicative_780_, 0);
            lean_inc_ref(v_toFunctor_781_);
            lean_dec_ref(v_toApplicative_780_);
            v_struct_782_ = lean_ctor_get(v_e_768_, 2);
            lean_inc_ref(v_struct_782_);
            v_map_783_ = lean_ctor_get(v_toFunctor_781_, 0);
            lean_inc(v_map_783_);
            lean_dec_ref(v_toFunctor_781_);
            v___x_784_ = lean_alloc_closure(
                l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl as *mut core::ffi::c_void,
                2,
                1,
            );
            lean_closure_set(v___x_784_, 0, v_e_768_);
            v___x_785_ = l_Lean_SubExpr_Pos_pushProj(v_p_767_);
            lean_dec(v_p_767_);
            v___x_786_ = lean_apply_2(v_visit_766_, v___x_785_, v_struct_782_);
            v___x_787_ = lean_apply_4(v_map_783_, lean_box(0), lean_box(0), v___x_784_, v___x_786_);
            return v___x_787_;
        }
        _ => {
            let mut v_toApplicative_788_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_789_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_788_ = lean_ctor_get(v_inst_763_, 0);
            lean_inc_ref(v_toApplicative_788_);
            lean_dec(v_p_767_);
            lean_dec(v_visit_766_);
            lean_dec_ref(v_inst_765_);
            lean_dec(v_inst_764_);
            lean_dec_ref(v_inst_763_);
            v_toPure_789_ = lean_ctor_get(v_toApplicative_788_, 1);
            lean_inc(v_toPure_789_);
            lean_dec_ref(v_toApplicative_788_);
            v___x_790_ = lean_apply_2(v_toPure_789_, lean_box(0), v_e_768_);
            return v___x_790_;
        }
    }
}
pub unsafe fn l_Lean_Meta_traverseChildrenWithPos(
    mut v_M_791_: *mut LeanObject,
    mut v_inst_792_: *mut LeanObject,
    mut v_inst_793_: *mut LeanObject,
    mut v_inst_794_: *mut LeanObject,
    mut v_visit_795_: *mut LeanObject,
    mut v_p_796_: *mut LeanObject,
    mut v_e_797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    v___x_798_ = l_Lean_Meta_traverseChildrenWithPos___redArg(
        v_inst_792_,
        v_inst_793_,
        v_inst_794_,
        v_visit_795_,
        v_p_796_,
        v_e_797_,
    );
    return v___x_798_;
}
pub unsafe fn l_Lean_Meta_traverseLambda___redArg(
    mut v_inst_799_: *mut LeanObject,
    mut v_inst_800_: *mut LeanObject,
    mut v_inst_801_: *mut LeanObject,
    mut v_visit_802_: *mut LeanObject,
    mut v_e_803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    v___x_804_ = lean_alloc_closure(
        l_Lean_Meta_traverseLambdaWithPos as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___x_804_, 0, lean_box(0));
    lean_closure_set(v___x_804_, 1, v_inst_799_);
    lean_closure_set(v___x_804_, 2, v_inst_800_);
    lean_closure_set(v___x_804_, 3, v_inst_801_);
    v___x_805_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(
        v___x_804_,
        v_visit_802_,
        v_e_803_,
    );
    return v___x_805_;
}
pub unsafe fn l_Lean_Meta_traverseLambda(
    mut v_M_806_: *mut LeanObject,
    mut v_inst_807_: *mut LeanObject,
    mut v_inst_808_: *mut LeanObject,
    mut v_inst_809_: *mut LeanObject,
    mut v_visit_810_: *mut LeanObject,
    mut v_e_811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    v___x_812_ = l_Lean_Meta_traverseLambda___redArg(
        v_inst_807_,
        v_inst_808_,
        v_inst_809_,
        v_visit_810_,
        v_e_811_,
    );
    return v___x_812_;
}
pub unsafe fn l_Lean_Meta_traverseForall___redArg(
    mut v_inst_813_: *mut LeanObject,
    mut v_inst_814_: *mut LeanObject,
    mut v_inst_815_: *mut LeanObject,
    mut v_visit_816_: *mut LeanObject,
    mut v_e_817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
    v___x_818_ = lean_alloc_closure(
        l_Lean_Meta_traverseForallWithPos as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___x_818_, 0, lean_box(0));
    lean_closure_set(v___x_818_, 1, v_inst_813_);
    lean_closure_set(v___x_818_, 2, v_inst_814_);
    lean_closure_set(v___x_818_, 3, v_inst_815_);
    v___x_819_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(
        v___x_818_,
        v_visit_816_,
        v_e_817_,
    );
    return v___x_819_;
}
pub unsafe fn l_Lean_Meta_traverseForall(
    mut v_M_820_: *mut LeanObject,
    mut v_inst_821_: *mut LeanObject,
    mut v_inst_822_: *mut LeanObject,
    mut v_inst_823_: *mut LeanObject,
    mut v_visit_824_: *mut LeanObject,
    mut v_e_825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    v___x_826_ = l_Lean_Meta_traverseForall___redArg(
        v_inst_821_,
        v_inst_822_,
        v_inst_823_,
        v_visit_824_,
        v_e_825_,
    );
    return v___x_826_;
}
pub unsafe fn l_Lean_Meta_traverseLet___redArg(
    mut v_inst_827_: *mut LeanObject,
    mut v_inst_828_: *mut LeanObject,
    mut v_inst_829_: *mut LeanObject,
    mut v_visit_830_: *mut LeanObject,
    mut v_e_831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    v___x_832_ = lean_alloc_closure(
        l_Lean_Meta_traverseLetWithPos as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___x_832_, 0, lean_box(0));
    lean_closure_set(v___x_832_, 1, v_inst_827_);
    lean_closure_set(v___x_832_, 2, v_inst_828_);
    lean_closure_set(v___x_832_, 3, v_inst_829_);
    v___x_833_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(
        v___x_832_,
        v_visit_830_,
        v_e_831_,
    );
    return v___x_833_;
}
pub unsafe fn l_Lean_Meta_traverseLet(
    mut v_M_834_: *mut LeanObject,
    mut v_inst_835_: *mut LeanObject,
    mut v_inst_836_: *mut LeanObject,
    mut v_inst_837_: *mut LeanObject,
    mut v_visit_838_: *mut LeanObject,
    mut v_e_839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    v___x_840_ = l_Lean_Meta_traverseLet___redArg(
        v_inst_835_,
        v_inst_836_,
        v_inst_837_,
        v_visit_838_,
        v_e_839_,
    );
    return v___x_840_;
}
pub unsafe fn l_Lean_Meta_traverseChildren___redArg(
    mut v_inst_841_: *mut LeanObject,
    mut v_inst_842_: *mut LeanObject,
    mut v_inst_843_: *mut LeanObject,
    mut v_visit_844_: *mut LeanObject,
    mut v_e_845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    v___x_846_ = lean_alloc_closure(
        l_Lean_Meta_traverseChildrenWithPos as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___x_846_, 0, lean_box(0));
    lean_closure_set(v___x_846_, 1, v_inst_841_);
    lean_closure_set(v___x_846_, 2, v_inst_842_);
    lean_closure_set(v___x_846_, 3, v_inst_843_);
    v___x_847_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(
        v___x_846_,
        v_visit_844_,
        v_e_845_,
    );
    return v___x_847_;
}
pub unsafe fn l_Lean_Meta_traverseChildren(
    mut v_M_848_: *mut LeanObject,
    mut v_inst_849_: *mut LeanObject,
    mut v_inst_850_: *mut LeanObject,
    mut v_inst_851_: *mut LeanObject,
    mut v_visit_852_: *mut LeanObject,
    mut v_e_853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    v___x_854_ = l_Lean_Meta_traverseChildren___redArg(
        v_inst_849_,
        v_inst_850_,
        v_inst_851_,
        v_visit_852_,
        v_e_853_,
    );
    return v___x_854_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_ExprTraverse(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_SubExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_ExprTraverse(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_ExprTraverse(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_SubExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_ExprTraverse(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_ExprTraverse(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_ExprTraverse(builtin);
}
