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
use crate::ffi::lean_array_push;
use crate::ffi::lean_expr_instantiate_rev;
pub static l_Lean_Meta_traverseLambdaWithPos___redArg___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Meta_traverseLambdaWithPos___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_traverseLambdaWithPos___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg___lam__0(
    mut v_visit_428_: *mut crate::leanh::LeanObject,
    mut v_x_429_: *mut crate::leanh::LeanObject,
    mut v___y_430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_431_ = crate::leanh::lean_apply_1(v_visit_428_, v___y_430_);
    return v___x_431_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg___lam__0___boxed(
    mut v_visit_432_: *mut crate::leanh::LeanObject,
    mut v_x_433_: *mut crate::leanh::LeanObject,
    mut v___y_434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_435_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg___lam__0(
        v_visit_432_,
        v_x_433_,
        v___y_434_,
    );
    crate::leanh::lean_dec(v_x_433_);
    return v_res_435_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(
    mut v_t_436_: *mut crate::leanh::LeanObject,
    mut v_visit_437_: *mut crate::leanh::LeanObject,
    mut v_e_438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_439_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_439_, 0, v_visit_437_);
    v___x_440_ = l_Lean_SubExpr_Pos_root;
    v___x_441_ = crate::leanh::lean_apply_3(v_t_436_, v___f_439_, v___x_440_, v_e_438_);
    return v___x_441_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos(
    mut v_M_442_: *mut crate::leanh::LeanObject,
    mut v_t_443_: *mut crate::leanh::LeanObject,
    mut v_visit_444_: *mut crate::leanh::LeanObject,
    mut v_e_445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_446_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(
        v_t_443_,
        v_visit_444_,
        v_e_445_,
    );
    return v___x_446_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__2(
    mut v_fvars_447_: *mut crate::leanh::LeanObject,
    mut v_inst_448_: *mut crate::leanh::LeanObject,
    mut v_body_449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_450_: u8 = 0;
    let mut v___x_451_: u8 = 0;
    let mut v___x_452_: u8 = 0;
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_450_ = 0;
    v___x_451_ = 1;
    v___x_452_ = 1;
    v___x_453_ = crate::leanh::lean_box((v___x_450_) as usize);
    v___x_454_ = crate::leanh::lean_box((v___x_451_) as usize);
    v___x_455_ = crate::leanh::lean_box((v___x_450_) as usize);
    v___x_456_ = crate::leanh::lean_box((v___x_451_) as usize);
    v___x_457_ = crate::leanh::lean_box((v___x_452_) as usize);
    v___x_458_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_mkLambdaFVars___boxed as *mut core::ffi::c_void,
        12,
        7,
    );
    crate::leanh::lean_closure_set(v___x_458_, 0, v_fvars_447_);
    crate::leanh::lean_closure_set(v___x_458_, 1, v_body_449_);
    crate::leanh::lean_closure_set(v___x_458_, 2, v___x_453_);
    crate::leanh::lean_closure_set(v___x_458_, 3, v___x_454_);
    crate::leanh::lean_closure_set(v___x_458_, 4, v___x_455_);
    crate::leanh::lean_closure_set(v___x_458_, 5, v___x_456_);
    crate::leanh::lean_closure_set(v___x_458_, 6, v___x_457_);
    v___x_459_ = crate::leanh::lean_apply_2(v_inst_448_, crate::leanh::lean_box(0), v___x_458_);
    return v___x_459_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1(
    mut v_inst_460_: *mut crate::leanh::LeanObject,
    mut v_inst_461_: *mut crate::leanh::LeanObject,
    mut v_binderName_462_: *mut crate::leanh::LeanObject,
    mut v_binderInfo_463_: u8,
    mut v___f_464_: *mut crate::leanh::LeanObject,
    mut v_d_465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_466_: u8 = 0;
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_468_: *mut crate::leanh::LeanObject,
    mut v_inst_469_: *mut crate::leanh::LeanObject,
    mut v_binderName_470_: *mut crate::leanh::LeanObject,
    mut v_binderInfo_471_: *mut crate::leanh::LeanObject,
    mut v___f_472_: *mut crate::leanh::LeanObject,
    mut v_d_473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_binderInfo_120__boxed_474_: u8 = 0;
    let mut v_res_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_binderInfo_120__boxed_474_ = (crate::leanh::lean_unbox(v_binderInfo_471_) as u8);
    v_res_475_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1(v_inst_468_, v_inst_469_, v_binderName_470_, v_binderInfo_120__boxed_474_, v___f_472_, v_d_473_);
    return v_res_475_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__0___boxed(
    mut v_fvars_476_: *mut crate::leanh::LeanObject,
    mut v_p_477_: *mut crate::leanh::LeanObject,
    mut v_inst_478_: *mut crate::leanh::LeanObject,
    mut v_inst_479_: *mut crate::leanh::LeanObject,
    mut v_inst_480_: *mut crate::leanh::LeanObject,
    mut v_f_481_: *mut crate::leanh::LeanObject,
    mut v_body_482_: *mut crate::leanh::LeanObject,
    mut v_x_483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_484_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__0(v_fvars_476_, v_p_477_, v_inst_478_, v_inst_479_, v_inst_480_, v_f_481_, v_body_482_, v_x_483_);
    crate::leanh::lean_dec(v_p_477_);
    return v_res_484_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg(
    mut v_inst_485_: *mut crate::leanh::LeanObject,
    mut v_inst_486_: *mut crate::leanh::LeanObject,
    mut v_inst_487_: *mut crate::leanh::LeanObject,
    mut v_f_488_: *mut crate::leanh::LeanObject,
    mut v_fvars_489_: *mut crate::leanh::LeanObject,
    mut v_p_490_: *mut crate::leanh::LeanObject,
    mut v_a_491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_491_) == 6 {
        let mut v_toBind_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderName_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderType_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_496_: u8 = 0;
        let mut v___f_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_492_ = crate::leanh::lean_ctor_get(v_inst_485_, 1);
        crate::leanh::lean_inc(v_toBind_492_);
        v_binderName_493_ = crate::leanh::lean_ctor_get(v_a_491_, 0);
        crate::leanh::lean_inc(v_binderName_493_);
        v_binderType_494_ = crate::leanh::lean_ctor_get(v_a_491_, 1);
        crate::leanh::lean_inc_ref(v_binderType_494_);
        v_body_495_ = crate::leanh::lean_ctor_get(v_a_491_, 2);
        crate::leanh::lean_inc_ref(v_body_495_);
        v_binderInfo_496_ = crate::leanh::lean_ctor_get_uint8(
            v_a_491_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        );
        crate::leanh::lean_dec_ref_known(v_a_491_, 3);
        crate::leanh::lean_inc(v_f_488_);
        crate::leanh::lean_inc_ref(v_inst_487_);
        crate::leanh::lean_inc_ref(v_inst_485_);
        crate::leanh::lean_inc(v_p_490_);
        crate::leanh::lean_inc_ref(v_fvars_489_);
        v___f_497_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 7);
        crate::leanh::lean_closure_set(v___f_497_, 0, v_fvars_489_);
        crate::leanh::lean_closure_set(v___f_497_, 1, v_p_490_);
        crate::leanh::lean_closure_set(v___f_497_, 2, v_inst_485_);
        crate::leanh::lean_closure_set(v___f_497_, 3, v_inst_486_);
        crate::leanh::lean_closure_set(v___f_497_, 4, v_inst_487_);
        crate::leanh::lean_closure_set(v___f_497_, 5, v_f_488_);
        crate::leanh::lean_closure_set(v___f_497_, 6, v_body_495_);
        v___x_498_ = crate::leanh::lean_box((v_binderInfo_496_) as usize);
        v___f_499_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1___boxed as *mut core::ffi::c_void, 6, 5);
        crate::leanh::lean_closure_set(v___f_499_, 0, v_inst_487_);
        crate::leanh::lean_closure_set(v___f_499_, 1, v_inst_485_);
        crate::leanh::lean_closure_set(v___f_499_, 2, v_binderName_493_);
        crate::leanh::lean_closure_set(v___f_499_, 3, v___x_498_);
        crate::leanh::lean_closure_set(v___f_499_, 4, v___f_497_);
        v___x_500_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_p_490_);
        crate::leanh::lean_dec(v_p_490_);
        v___x_501_ = lean_expr_instantiate_rev(v_binderType_494_, v_fvars_489_);
        crate::leanh::lean_dec_ref(v_fvars_489_);
        crate::leanh::lean_dec_ref(v_binderType_494_);
        v___x_502_ = crate::leanh::lean_apply_2(v_f_488_, v___x_500_, v___x_501_);
        v___x_503_ = crate::leanh::lean_apply_4(
            v_toBind_492_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_502_,
            v___f_499_,
        );
        return v___x_503_;
    } else {
        let mut v_toBind_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_487_);
        v_toBind_504_ = crate::leanh::lean_ctor_get(v_inst_485_, 1);
        crate::leanh::lean_inc(v_toBind_504_);
        crate::leanh::lean_dec_ref(v_inst_485_);
        crate::leanh::lean_inc_ref(v_fvars_489_);
        v___f_505_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__2 as *mut core::ffi::c_void, 3, 2);
        crate::leanh::lean_closure_set(v___f_505_, 0, v_fvars_489_);
        crate::leanh::lean_closure_set(v___f_505_, 1, v_inst_486_);
        v___x_506_ = lean_expr_instantiate_rev(v_a_491_, v_fvars_489_);
        crate::leanh::lean_dec_ref(v_fvars_489_);
        crate::leanh::lean_dec_ref(v_a_491_);
        v___x_507_ = crate::leanh::lean_apply_2(v_f_488_, v_p_490_, v___x_506_);
        v___x_508_ = crate::leanh::lean_apply_4(
            v_toBind_504_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_507_,
            v___f_505_,
        );
        return v___x_508_;
    }
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__0(
    mut v_fvars_509_: *mut crate::leanh::LeanObject,
    mut v_p_510_: *mut crate::leanh::LeanObject,
    mut v_inst_511_: *mut crate::leanh::LeanObject,
    mut v_inst_512_: *mut crate::leanh::LeanObject,
    mut v_inst_513_: *mut crate::leanh::LeanObject,
    mut v_f_514_: *mut crate::leanh::LeanObject,
    mut v_body_515_: *mut crate::leanh::LeanObject,
    mut v_x_516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_M_520_: *mut crate::leanh::LeanObject,
    mut v_inst_521_: *mut crate::leanh::LeanObject,
    mut v_inst_522_: *mut crate::leanh::LeanObject,
    mut v_inst_523_: *mut crate::leanh::LeanObject,
    mut v_f_524_: *mut crate::leanh::LeanObject,
    mut v_fvars_525_: *mut crate::leanh::LeanObject,
    mut v_p_526_: *mut crate::leanh::LeanObject,
    mut v_a_527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_531_: *mut crate::leanh::LeanObject,
    mut v_inst_532_: *mut crate::leanh::LeanObject,
    mut v_inst_533_: *mut crate::leanh::LeanObject,
    mut v_f_534_: *mut crate::leanh::LeanObject,
    mut v_p_535_: *mut crate::leanh::LeanObject,
    mut v_e_536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_M_539_: *mut crate::leanh::LeanObject,
    mut v_inst_540_: *mut crate::leanh::LeanObject,
    mut v_inst_541_: *mut crate::leanh::LeanObject,
    mut v_inst_542_: *mut crate::leanh::LeanObject,
    mut v_f_543_: *mut crate::leanh::LeanObject,
    mut v_p_544_: *mut crate::leanh::LeanObject,
    mut v_e_545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_fvars_547_: *mut crate::leanh::LeanObject,
    mut v_inst_548_: *mut crate::leanh::LeanObject,
    mut v_body_549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_550_: u8 = 0;
    let mut v___x_551_: u8 = 0;
    let mut v___x_552_: u8 = 0;
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_550_ = 0;
    v___x_551_ = 1;
    v___x_552_ = 1;
    v___x_553_ = crate::leanh::lean_box((v___x_550_) as usize);
    v___x_554_ = crate::leanh::lean_box((v___x_551_) as usize);
    v___x_555_ = crate::leanh::lean_box((v___x_551_) as usize);
    v___x_556_ = crate::leanh::lean_box((v___x_552_) as usize);
    crate::leanh::lean_inc_ref(v_fvars_547_);
    v___x_557_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_mkForallFVars___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    crate::leanh::lean_closure_set(v___x_557_, 0, v_fvars_547_);
    crate::leanh::lean_closure_set(v___x_557_, 1, v_body_549_);
    crate::leanh::lean_closure_set(v___x_557_, 2, v___x_553_);
    crate::leanh::lean_closure_set(v___x_557_, 3, v___x_554_);
    crate::leanh::lean_closure_set(v___x_557_, 4, v___x_555_);
    crate::leanh::lean_closure_set(v___x_557_, 5, v___x_556_);
    v___x_558_ = crate::leanh::lean_apply_2(v_inst_548_, crate::leanh::lean_box(0), v___x_557_);
    return v___x_558_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__2___boxed(
    mut v_fvars_559_: *mut crate::leanh::LeanObject,
    mut v_inst_560_: *mut crate::leanh::LeanObject,
    mut v_body_561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_562_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__2(v_fvars_559_, v_inst_560_, v_body_561_);
    crate::leanh::lean_dec_ref(v_fvars_559_);
    return v_res_562_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0___boxed(
    mut v_fvars_563_: *mut crate::leanh::LeanObject,
    mut v_p_564_: *mut crate::leanh::LeanObject,
    mut v_inst_565_: *mut crate::leanh::LeanObject,
    mut v_inst_566_: *mut crate::leanh::LeanObject,
    mut v_inst_567_: *mut crate::leanh::LeanObject,
    mut v_f_568_: *mut crate::leanh::LeanObject,
    mut v_body_569_: *mut crate::leanh::LeanObject,
    mut v_x_570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_571_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0(v_fvars_563_, v_p_564_, v_inst_565_, v_inst_566_, v_inst_567_, v_f_568_, v_body_569_, v_x_570_);
    crate::leanh::lean_dec(v_p_564_);
    crate::leanh::lean_dec_ref(v_fvars_563_);
    return v_res_571_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg(
    mut v_inst_572_: *mut crate::leanh::LeanObject,
    mut v_inst_573_: *mut crate::leanh::LeanObject,
    mut v_inst_574_: *mut crate::leanh::LeanObject,
    mut v_f_575_: *mut crate::leanh::LeanObject,
    mut v_fvars_576_: *mut crate::leanh::LeanObject,
    mut v_p_577_: *mut crate::leanh::LeanObject,
    mut v_a_578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_578_) == 7 {
        let mut v_toBind_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderName_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderType_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_583_: u8 = 0;
        let mut v___f_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_579_ = crate::leanh::lean_ctor_get(v_inst_572_, 1);
        crate::leanh::lean_inc(v_toBind_579_);
        v_binderName_580_ = crate::leanh::lean_ctor_get(v_a_578_, 0);
        crate::leanh::lean_inc(v_binderName_580_);
        v_binderType_581_ = crate::leanh::lean_ctor_get(v_a_578_, 1);
        crate::leanh::lean_inc_ref(v_binderType_581_);
        v_body_582_ = crate::leanh::lean_ctor_get(v_a_578_, 2);
        crate::leanh::lean_inc_ref(v_body_582_);
        v_binderInfo_583_ = crate::leanh::lean_ctor_get_uint8(
            v_a_578_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        );
        crate::leanh::lean_dec_ref_known(v_a_578_, 3);
        crate::leanh::lean_inc(v_f_575_);
        crate::leanh::lean_inc_ref(v_inst_574_);
        crate::leanh::lean_inc_ref(v_inst_572_);
        crate::leanh::lean_inc(v_p_577_);
        crate::leanh::lean_inc_ref(v_fvars_576_);
        v___f_584_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 7);
        crate::leanh::lean_closure_set(v___f_584_, 0, v_fvars_576_);
        crate::leanh::lean_closure_set(v___f_584_, 1, v_p_577_);
        crate::leanh::lean_closure_set(v___f_584_, 2, v_inst_572_);
        crate::leanh::lean_closure_set(v___f_584_, 3, v_inst_573_);
        crate::leanh::lean_closure_set(v___f_584_, 4, v_inst_574_);
        crate::leanh::lean_closure_set(v___f_584_, 5, v_f_575_);
        crate::leanh::lean_closure_set(v___f_584_, 6, v_body_582_);
        v___x_585_ = crate::leanh::lean_box((v_binderInfo_583_) as usize);
        v___f_586_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1___boxed as *mut core::ffi::c_void, 6, 5);
        crate::leanh::lean_closure_set(v___f_586_, 0, v_inst_574_);
        crate::leanh::lean_closure_set(v___f_586_, 1, v_inst_572_);
        crate::leanh::lean_closure_set(v___f_586_, 2, v_binderName_580_);
        crate::leanh::lean_closure_set(v___f_586_, 3, v___x_585_);
        crate::leanh::lean_closure_set(v___f_586_, 4, v___f_584_);
        v___x_587_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_p_577_);
        crate::leanh::lean_dec(v_p_577_);
        v___x_588_ = lean_expr_instantiate_rev(v_binderType_581_, v_fvars_576_);
        crate::leanh::lean_dec_ref(v_binderType_581_);
        v___x_589_ = crate::leanh::lean_apply_2(v_f_575_, v___x_587_, v___x_588_);
        v___x_590_ = crate::leanh::lean_apply_4(
            v_toBind_579_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_589_,
            v___f_586_,
        );
        return v___x_590_;
    } else {
        let mut v_toBind_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_574_);
        v_toBind_591_ = crate::leanh::lean_ctor_get(v_inst_572_, 1);
        crate::leanh::lean_inc(v_toBind_591_);
        crate::leanh::lean_dec_ref(v_inst_572_);
        crate::leanh::lean_inc_ref(v_fvars_576_);
        v___f_592_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__2___boxed as *mut core::ffi::c_void, 3, 2);
        crate::leanh::lean_closure_set(v___f_592_, 0, v_fvars_576_);
        crate::leanh::lean_closure_set(v___f_592_, 1, v_inst_573_);
        v___x_593_ = lean_expr_instantiate_rev(v_a_578_, v_fvars_576_);
        crate::leanh::lean_dec_ref(v_a_578_);
        v___x_594_ = crate::leanh::lean_apply_2(v_f_575_, v_p_577_, v___x_593_);
        v___x_595_ = crate::leanh::lean_apply_4(
            v_toBind_591_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_594_,
            v___f_592_,
        );
        return v___x_595_;
    }
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0(
    mut v_fvars_596_: *mut crate::leanh::LeanObject,
    mut v_p_597_: *mut crate::leanh::LeanObject,
    mut v_inst_598_: *mut crate::leanh::LeanObject,
    mut v_inst_599_: *mut crate::leanh::LeanObject,
    mut v_inst_600_: *mut crate::leanh::LeanObject,
    mut v_f_601_: *mut crate::leanh::LeanObject,
    mut v_body_602_: *mut crate::leanh::LeanObject,
    mut v_x_603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_fvars_596_);
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
    crate::leanh::lean_dec_ref(v___x_604_);
    return v___x_606_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___boxed(
    mut v_inst_607_: *mut crate::leanh::LeanObject,
    mut v_inst_608_: *mut crate::leanh::LeanObject,
    mut v_inst_609_: *mut crate::leanh::LeanObject,
    mut v_f_610_: *mut crate::leanh::LeanObject,
    mut v_fvars_611_: *mut crate::leanh::LeanObject,
    mut v_p_612_: *mut crate::leanh::LeanObject,
    mut v_a_613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_fvars_611_);
    return v_res_614_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit(
    mut v_M_615_: *mut crate::leanh::LeanObject,
    mut v_inst_616_: *mut crate::leanh::LeanObject,
    mut v_inst_617_: *mut crate::leanh::LeanObject,
    mut v_inst_618_: *mut crate::leanh::LeanObject,
    mut v_f_619_: *mut crate::leanh::LeanObject,
    mut v_fvars_620_: *mut crate::leanh::LeanObject,
    mut v_p_621_: *mut crate::leanh::LeanObject,
    mut v_a_622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_M_624_: *mut crate::leanh::LeanObject,
    mut v_inst_625_: *mut crate::leanh::LeanObject,
    mut v_inst_626_: *mut crate::leanh::LeanObject,
    mut v_inst_627_: *mut crate::leanh::LeanObject,
    mut v_f_628_: *mut crate::leanh::LeanObject,
    mut v_fvars_629_: *mut crate::leanh::LeanObject,
    mut v_p_630_: *mut crate::leanh::LeanObject,
    mut v_a_631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_fvars_629_);
    return v_res_632_;
}
pub unsafe fn l_Lean_Meta_traverseForallWithPos___redArg(
    mut v_inst_633_: *mut crate::leanh::LeanObject,
    mut v_inst_634_: *mut crate::leanh::LeanObject,
    mut v_inst_635_: *mut crate::leanh::LeanObject,
    mut v_f_636_: *mut crate::leanh::LeanObject,
    mut v_p_637_: *mut crate::leanh::LeanObject,
    mut v_e_638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_M_641_: *mut crate::leanh::LeanObject,
    mut v_inst_642_: *mut crate::leanh::LeanObject,
    mut v_inst_643_: *mut crate::leanh::LeanObject,
    mut v_inst_644_: *mut crate::leanh::LeanObject,
    mut v_f_645_: *mut crate::leanh::LeanObject,
    mut v_p_646_: *mut crate::leanh::LeanObject,
    mut v_e_647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_649_: *mut crate::leanh::LeanObject,
    mut v_inst_650_: *mut crate::leanh::LeanObject,
    mut v_declName_651_: *mut crate::leanh::LeanObject,
    mut v_type_652_: *mut crate::leanh::LeanObject,
    mut v___f_653_: *mut crate::leanh::LeanObject,
    mut v_value_654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_655_: u8 = 0;
    let mut v___x_656_: u8 = 0;
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_658_: *mut crate::leanh::LeanObject,
    mut v_inst_659_: *mut crate::leanh::LeanObject,
    mut v_declName_660_: *mut crate::leanh::LeanObject,
    mut v___f_661_: *mut crate::leanh::LeanObject,
    mut v_p_662_: *mut crate::leanh::LeanObject,
    mut v_value_663_: *mut crate::leanh::LeanObject,
    mut v_fvars_664_: *mut crate::leanh::LeanObject,
    mut v_f_665_: *mut crate::leanh::LeanObject,
    mut v_toBind_666_: *mut crate::leanh::LeanObject,
    mut v_type_667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_668_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__1
            as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_668_, 0, v_inst_658_);
    crate::leanh::lean_closure_set(v___f_668_, 1, v_inst_659_);
    crate::leanh::lean_closure_set(v___f_668_, 2, v_declName_660_);
    crate::leanh::lean_closure_set(v___f_668_, 3, v_type_667_);
    crate::leanh::lean_closure_set(v___f_668_, 4, v___f_661_);
    v___x_669_ = l_Lean_SubExpr_Pos_pushLetValue(v_p_662_);
    v___x_670_ = lean_expr_instantiate_rev(v_value_663_, v_fvars_664_);
    v___x_671_ = crate::leanh::lean_apply_2(v_f_665_, v___x_669_, v___x_670_);
    v___x_672_ = crate::leanh::lean_apply_4(
        v_toBind_666_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_671_,
        v___f_668_,
    );
    return v___x_672_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__2___boxed(
    mut v_inst_673_: *mut crate::leanh::LeanObject,
    mut v_inst_674_: *mut crate::leanh::LeanObject,
    mut v_declName_675_: *mut crate::leanh::LeanObject,
    mut v___f_676_: *mut crate::leanh::LeanObject,
    mut v_p_677_: *mut crate::leanh::LeanObject,
    mut v_value_678_: *mut crate::leanh::LeanObject,
    mut v_fvars_679_: *mut crate::leanh::LeanObject,
    mut v_f_680_: *mut crate::leanh::LeanObject,
    mut v_toBind_681_: *mut crate::leanh::LeanObject,
    mut v_type_682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_fvars_679_);
    crate::leanh::lean_dec_ref(v_value_678_);
    crate::leanh::lean_dec(v_p_677_);
    return v_res_683_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__3(
    mut v_fvars_684_: *mut crate::leanh::LeanObject,
    mut v_inst_685_: *mut crate::leanh::LeanObject,
    mut v_body_686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_687_: u8 = 0;
    let mut v___x_688_: u8 = 0;
    let mut v___x_689_: u8 = 0;
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_687_ = 0;
    v___x_688_ = 1;
    v___x_689_ = 1;
    v___x_690_ = crate::leanh::lean_box((v___x_687_) as usize);
    v___x_691_ = crate::leanh::lean_box((v___x_688_) as usize);
    v___x_692_ = crate::leanh::lean_box((v___x_689_) as usize);
    v___x_693_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_mkLetFVars___boxed as *mut core::ffi::c_void,
        10,
        5,
    );
    crate::leanh::lean_closure_set(v___x_693_, 0, v_fvars_684_);
    crate::leanh::lean_closure_set(v___x_693_, 1, v_body_686_);
    crate::leanh::lean_closure_set(v___x_693_, 2, v___x_690_);
    crate::leanh::lean_closure_set(v___x_693_, 3, v___x_691_);
    crate::leanh::lean_closure_set(v___x_693_, 4, v___x_692_);
    v___x_694_ = crate::leanh::lean_apply_2(v_inst_685_, crate::leanh::lean_box(0), v___x_693_);
    return v___x_694_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__0___boxed(
    mut v_fvars_695_: *mut crate::leanh::LeanObject,
    mut v_p_696_: *mut crate::leanh::LeanObject,
    mut v_inst_697_: *mut crate::leanh::LeanObject,
    mut v_inst_698_: *mut crate::leanh::LeanObject,
    mut v_inst_699_: *mut crate::leanh::LeanObject,
    mut v_f_700_: *mut crate::leanh::LeanObject,
    mut v_body_701_: *mut crate::leanh::LeanObject,
    mut v_x_702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_p_696_);
    return v_res_703_;
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg(
    mut v_inst_704_: *mut crate::leanh::LeanObject,
    mut v_inst_705_: *mut crate::leanh::LeanObject,
    mut v_inst_706_: *mut crate::leanh::LeanObject,
    mut v_f_707_: *mut crate::leanh::LeanObject,
    mut v_fvars_708_: *mut crate::leanh::LeanObject,
    mut v_p_709_: *mut crate::leanh::LeanObject,
    mut v_x_710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_710_) == 8 {
        let mut v_toBind_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_declName_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_type_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_711_ = crate::leanh::lean_ctor_get(v_inst_704_, 1);
        crate::leanh::lean_inc_n(v_toBind_711_, 2);
        v_declName_712_ = crate::leanh::lean_ctor_get(v_x_710_, 0);
        crate::leanh::lean_inc(v_declName_712_);
        v_type_713_ = crate::leanh::lean_ctor_get(v_x_710_, 1);
        crate::leanh::lean_inc_ref(v_type_713_);
        v_value_714_ = crate::leanh::lean_ctor_get(v_x_710_, 2);
        crate::leanh::lean_inc_ref(v_value_714_);
        v_body_715_ = crate::leanh::lean_ctor_get(v_x_710_, 3);
        crate::leanh::lean_inc_ref(v_body_715_);
        crate::leanh::lean_dec_ref_known(v_x_710_, 4);
        crate::leanh::lean_inc_n(v_f_707_, 2);
        crate::leanh::lean_inc_ref(v_inst_706_);
        crate::leanh::lean_inc_ref(v_inst_704_);
        crate::leanh::lean_inc_n(v_p_709_, 2);
        crate::leanh::lean_inc_ref_n(v_fvars_708_, 2);
        v___f_716_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 7);
        crate::leanh::lean_closure_set(v___f_716_, 0, v_fvars_708_);
        crate::leanh::lean_closure_set(v___f_716_, 1, v_p_709_);
        crate::leanh::lean_closure_set(v___f_716_, 2, v_inst_704_);
        crate::leanh::lean_closure_set(v___f_716_, 3, v_inst_705_);
        crate::leanh::lean_closure_set(v___f_716_, 4, v_inst_706_);
        crate::leanh::lean_closure_set(v___f_716_, 5, v_f_707_);
        crate::leanh::lean_closure_set(v___f_716_, 6, v_body_715_);
        v___f_717_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__2___boxed as *mut core::ffi::c_void, 10, 9);
        crate::leanh::lean_closure_set(v___f_717_, 0, v_inst_706_);
        crate::leanh::lean_closure_set(v___f_717_, 1, v_inst_704_);
        crate::leanh::lean_closure_set(v___f_717_, 2, v_declName_712_);
        crate::leanh::lean_closure_set(v___f_717_, 3, v___f_716_);
        crate::leanh::lean_closure_set(v___f_717_, 4, v_p_709_);
        crate::leanh::lean_closure_set(v___f_717_, 5, v_value_714_);
        crate::leanh::lean_closure_set(v___f_717_, 6, v_fvars_708_);
        crate::leanh::lean_closure_set(v___f_717_, 7, v_f_707_);
        crate::leanh::lean_closure_set(v___f_717_, 8, v_toBind_711_);
        v___x_718_ = l_Lean_SubExpr_Pos_pushLetVarType(v_p_709_);
        crate::leanh::lean_dec(v_p_709_);
        v___x_719_ = lean_expr_instantiate_rev(v_type_713_, v_fvars_708_);
        crate::leanh::lean_dec_ref(v_fvars_708_);
        crate::leanh::lean_dec_ref(v_type_713_);
        v___x_720_ = crate::leanh::lean_apply_2(v_f_707_, v___x_718_, v___x_719_);
        v___x_721_ = crate::leanh::lean_apply_4(
            v_toBind_711_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_720_,
            v___f_717_,
        );
        return v___x_721_;
    } else {
        let mut v_toBind_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_706_);
        v_toBind_722_ = crate::leanh::lean_ctor_get(v_inst_704_, 1);
        crate::leanh::lean_inc(v_toBind_722_);
        crate::leanh::lean_dec_ref(v_inst_704_);
        crate::leanh::lean_inc_ref(v_fvars_708_);
        v___f_723_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__3 as *mut core::ffi::c_void, 3, 2);
        crate::leanh::lean_closure_set(v___f_723_, 0, v_fvars_708_);
        crate::leanh::lean_closure_set(v___f_723_, 1, v_inst_705_);
        v___x_724_ = lean_expr_instantiate_rev(v_x_710_, v_fvars_708_);
        crate::leanh::lean_dec_ref(v_fvars_708_);
        crate::leanh::lean_dec_ref(v_x_710_);
        v___x_725_ = crate::leanh::lean_apply_2(v_f_707_, v_p_709_, v___x_724_);
        v___x_726_ = crate::leanh::lean_apply_4(
            v_toBind_722_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_725_,
            v___f_723_,
        );
        return v___x_726_;
    }
}
pub unsafe fn l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__0(
    mut v_fvars_727_: *mut crate::leanh::LeanObject,
    mut v_p_728_: *mut crate::leanh::LeanObject,
    mut v_inst_729_: *mut crate::leanh::LeanObject,
    mut v_inst_730_: *mut crate::leanh::LeanObject,
    mut v_inst_731_: *mut crate::leanh::LeanObject,
    mut v_f_732_: *mut crate::leanh::LeanObject,
    mut v_body_733_: *mut crate::leanh::LeanObject,
    mut v_x_734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_M_738_: *mut crate::leanh::LeanObject,
    mut v_inst_739_: *mut crate::leanh::LeanObject,
    mut v_inst_740_: *mut crate::leanh::LeanObject,
    mut v_inst_741_: *mut crate::leanh::LeanObject,
    mut v_f_742_: *mut crate::leanh::LeanObject,
    mut v_fvars_743_: *mut crate::leanh::LeanObject,
    mut v_p_744_: *mut crate::leanh::LeanObject,
    mut v_x_745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_747_: *mut crate::leanh::LeanObject,
    mut v_inst_748_: *mut crate::leanh::LeanObject,
    mut v_inst_749_: *mut crate::leanh::LeanObject,
    mut v_f_750_: *mut crate::leanh::LeanObject,
    mut v_p_751_: *mut crate::leanh::LeanObject,
    mut v_e_752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_M_755_: *mut crate::leanh::LeanObject,
    mut v_inst_756_: *mut crate::leanh::LeanObject,
    mut v_inst_757_: *mut crate::leanh::LeanObject,
    mut v_inst_758_: *mut crate::leanh::LeanObject,
    mut v_f_759_: *mut crate::leanh::LeanObject,
    mut v_p_760_: *mut crate::leanh::LeanObject,
    mut v_e_761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_763_: *mut crate::leanh::LeanObject,
    mut v_inst_764_: *mut crate::leanh::LeanObject,
    mut v_inst_765_: *mut crate::leanh::LeanObject,
    mut v_visit_766_: *mut crate::leanh::LeanObject,
    mut v_p_767_: *mut crate::leanh::LeanObject,
    mut v_e_768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_e_768_) {
        7 => {
            let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
            let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
            let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
            let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_inst_765_);
            crate::leanh::lean_dec(v_inst_764_);
            v___x_772_ = l_Lean_Expr_traverseAppWithPos___redArg(
                v_inst_763_,
                v_visit_766_,
                v_p_767_,
                v_e_768_,
            );
            return v___x_772_;
        }
        10 => {
            let mut v_toApplicative_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toFunctor_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_map_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_773_ = crate::leanh::lean_ctor_get(v_inst_763_, 0);
            crate::leanh::lean_inc_ref(v_toApplicative_773_);
            crate::leanh::lean_dec_ref(v_inst_765_);
            crate::leanh::lean_dec(v_inst_764_);
            crate::leanh::lean_dec_ref(v_inst_763_);
            v_toFunctor_774_ = crate::leanh::lean_ctor_get(v_toApplicative_773_, 0);
            crate::leanh::lean_inc_ref(v_toFunctor_774_);
            crate::leanh::lean_dec_ref(v_toApplicative_773_);
            v_expr_775_ = crate::leanh::lean_ctor_get(v_e_768_, 1);
            crate::leanh::lean_inc_ref(v_expr_775_);
            v_map_776_ = crate::leanh::lean_ctor_get(v_toFunctor_774_, 0);
            crate::leanh::lean_inc(v_map_776_);
            crate::leanh::lean_dec_ref(v_toFunctor_774_);
            v___x_777_ = crate::leanh::lean_alloc_closure(
                l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl as *mut core::ffi::c_void,
                2,
                1,
            );
            crate::leanh::lean_closure_set(v___x_777_, 0, v_e_768_);
            v___x_778_ = crate::leanh::lean_apply_2(v_visit_766_, v_p_767_, v_expr_775_);
            v___x_779_ = crate::leanh::lean_apply_4(
                v_map_776_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_777_,
                v___x_778_,
            );
            return v___x_779_;
        }
        11 => {
            let mut v_toApplicative_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toFunctor_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_struct_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_map_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_780_ = crate::leanh::lean_ctor_get(v_inst_763_, 0);
            crate::leanh::lean_inc_ref(v_toApplicative_780_);
            crate::leanh::lean_dec_ref(v_inst_765_);
            crate::leanh::lean_dec(v_inst_764_);
            crate::leanh::lean_dec_ref(v_inst_763_);
            v_toFunctor_781_ = crate::leanh::lean_ctor_get(v_toApplicative_780_, 0);
            crate::leanh::lean_inc_ref(v_toFunctor_781_);
            crate::leanh::lean_dec_ref(v_toApplicative_780_);
            v_struct_782_ = crate::leanh::lean_ctor_get(v_e_768_, 2);
            crate::leanh::lean_inc_ref(v_struct_782_);
            v_map_783_ = crate::leanh::lean_ctor_get(v_toFunctor_781_, 0);
            crate::leanh::lean_inc(v_map_783_);
            crate::leanh::lean_dec_ref(v_toFunctor_781_);
            v___x_784_ = crate::leanh::lean_alloc_closure(
                l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl as *mut core::ffi::c_void,
                2,
                1,
            );
            crate::leanh::lean_closure_set(v___x_784_, 0, v_e_768_);
            v___x_785_ = l_Lean_SubExpr_Pos_pushProj(v_p_767_);
            crate::leanh::lean_dec(v_p_767_);
            v___x_786_ = crate::leanh::lean_apply_2(v_visit_766_, v___x_785_, v_struct_782_);
            v___x_787_ = crate::leanh::lean_apply_4(
                v_map_783_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_784_,
                v___x_786_,
            );
            return v___x_787_;
        }
        _ => {
            let mut v_toApplicative_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_788_ = crate::leanh::lean_ctor_get(v_inst_763_, 0);
            crate::leanh::lean_inc_ref(v_toApplicative_788_);
            crate::leanh::lean_dec(v_p_767_);
            crate::leanh::lean_dec(v_visit_766_);
            crate::leanh::lean_dec_ref(v_inst_765_);
            crate::leanh::lean_dec(v_inst_764_);
            crate::leanh::lean_dec_ref(v_inst_763_);
            v_toPure_789_ = crate::leanh::lean_ctor_get(v_toApplicative_788_, 1);
            crate::leanh::lean_inc(v_toPure_789_);
            crate::leanh::lean_dec_ref(v_toApplicative_788_);
            v___x_790_ =
                crate::leanh::lean_apply_2(v_toPure_789_, crate::leanh::lean_box(0), v_e_768_);
            return v___x_790_;
        }
    }
}
pub unsafe fn l_Lean_Meta_traverseChildrenWithPos(
    mut v_M_791_: *mut crate::leanh::LeanObject,
    mut v_inst_792_: *mut crate::leanh::LeanObject,
    mut v_inst_793_: *mut crate::leanh::LeanObject,
    mut v_inst_794_: *mut crate::leanh::LeanObject,
    mut v_visit_795_: *mut crate::leanh::LeanObject,
    mut v_p_796_: *mut crate::leanh::LeanObject,
    mut v_e_797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_799_: *mut crate::leanh::LeanObject,
    mut v_inst_800_: *mut crate::leanh::LeanObject,
    mut v_inst_801_: *mut crate::leanh::LeanObject,
    mut v_visit_802_: *mut crate::leanh::LeanObject,
    mut v_e_803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_804_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_traverseLambdaWithPos as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___x_804_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_804_, 1, v_inst_799_);
    crate::leanh::lean_closure_set(v___x_804_, 2, v_inst_800_);
    crate::leanh::lean_closure_set(v___x_804_, 3, v_inst_801_);
    v___x_805_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(
        v___x_804_,
        v_visit_802_,
        v_e_803_,
    );
    return v___x_805_;
}
pub unsafe fn l_Lean_Meta_traverseLambda(
    mut v_M_806_: *mut crate::leanh::LeanObject,
    mut v_inst_807_: *mut crate::leanh::LeanObject,
    mut v_inst_808_: *mut crate::leanh::LeanObject,
    mut v_inst_809_: *mut crate::leanh::LeanObject,
    mut v_visit_810_: *mut crate::leanh::LeanObject,
    mut v_e_811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_813_: *mut crate::leanh::LeanObject,
    mut v_inst_814_: *mut crate::leanh::LeanObject,
    mut v_inst_815_: *mut crate::leanh::LeanObject,
    mut v_visit_816_: *mut crate::leanh::LeanObject,
    mut v_e_817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_818_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_traverseForallWithPos as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___x_818_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_818_, 1, v_inst_813_);
    crate::leanh::lean_closure_set(v___x_818_, 2, v_inst_814_);
    crate::leanh::lean_closure_set(v___x_818_, 3, v_inst_815_);
    v___x_819_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(
        v___x_818_,
        v_visit_816_,
        v_e_817_,
    );
    return v___x_819_;
}
pub unsafe fn l_Lean_Meta_traverseForall(
    mut v_M_820_: *mut crate::leanh::LeanObject,
    mut v_inst_821_: *mut crate::leanh::LeanObject,
    mut v_inst_822_: *mut crate::leanh::LeanObject,
    mut v_inst_823_: *mut crate::leanh::LeanObject,
    mut v_visit_824_: *mut crate::leanh::LeanObject,
    mut v_e_825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_827_: *mut crate::leanh::LeanObject,
    mut v_inst_828_: *mut crate::leanh::LeanObject,
    mut v_inst_829_: *mut crate::leanh::LeanObject,
    mut v_visit_830_: *mut crate::leanh::LeanObject,
    mut v_e_831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_832_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_traverseLetWithPos as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___x_832_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_832_, 1, v_inst_827_);
    crate::leanh::lean_closure_set(v___x_832_, 2, v_inst_828_);
    crate::leanh::lean_closure_set(v___x_832_, 3, v_inst_829_);
    v___x_833_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(
        v___x_832_,
        v_visit_830_,
        v_e_831_,
    );
    return v___x_833_;
}
pub unsafe fn l_Lean_Meta_traverseLet(
    mut v_M_834_: *mut crate::leanh::LeanObject,
    mut v_inst_835_: *mut crate::leanh::LeanObject,
    mut v_inst_836_: *mut crate::leanh::LeanObject,
    mut v_inst_837_: *mut crate::leanh::LeanObject,
    mut v_visit_838_: *mut crate::leanh::LeanObject,
    mut v_e_839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_841_: *mut crate::leanh::LeanObject,
    mut v_inst_842_: *mut crate::leanh::LeanObject,
    mut v_inst_843_: *mut crate::leanh::LeanObject,
    mut v_visit_844_: *mut crate::leanh::LeanObject,
    mut v_e_845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_846_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_traverseChildrenWithPos as *mut core::ffi::c_void,
        7,
        4,
    );
    crate::leanh::lean_closure_set(v___x_846_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_846_, 1, v_inst_841_);
    crate::leanh::lean_closure_set(v___x_846_, 2, v_inst_842_);
    crate::leanh::lean_closure_set(v___x_846_, 3, v_inst_843_);
    v___x_847_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(
        v___x_846_,
        v_visit_844_,
        v_e_845_,
    );
    return v___x_847_;
}
pub unsafe fn l_Lean_Meta_traverseChildren(
    mut v_M_848_: *mut crate::leanh::LeanObject,
    mut v_inst_849_: *mut crate::leanh::LeanObject,
    mut v_inst_850_: *mut crate::leanh::LeanObject,
    mut v_inst_851_: *mut crate::leanh::LeanObject,
    mut v_visit_852_: *mut crate::leanh::LeanObject,
    mut v_e_853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
pub unsafe fn runtime_initialize_Lean_Meta_ExprTraverse(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_SubExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_ExprTraverse(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_ExprTraverse(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_SubExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_ExprTraverse(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_ExprTraverse(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_ExprTraverse(builtin);
}
