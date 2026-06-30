// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC.DenoteExpr
// Imports: Lean.Meta.Tactic.Grind.AC.Util
use crate::ffi::lean_nat_dec_lt;
use crate::r#gen::Init::GetElem::l_outOfBounds___redArg;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_get_x21___redArg;
use crate::r#gen::Lean::Expr::{
    l_Lean_instInhabitedExpr, l_Lean_mkApp3, l_Lean_mkAppB, l_Lean_mkConst,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::AC::Util::{
    initialize_Lean_Meta_Tactic_Grind_AC_Util, runtime_initialize_Lean_Meta_Tactic_Grind_AC_Util,
};
pub static l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0___closed__0_value:
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
    m_data: [69, 113, 0],
};
static mut l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0___closed__1_value:
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
            l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        16122875713692181903 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0___closed__0_value:
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
    m_data: [78, 101, 0],
};
static mut l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0___closed__1_value:
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
            l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        6695605208187598753 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0___closed__1_value
) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__0(
    mut v_x_228_: *mut leanh::LeanObject,
    mut v___x_229_: *mut leanh::LeanObject,
    mut v_toPure_230_: *mut leanh::LeanObject,
    mut v_____do__lift_231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_vars_232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_234_: u8 = 0;
    v_vars_232_ = leanh::lean_ctor_get(v_____do__lift_231_, 10);
    v_size_233_ = leanh::lean_ctor_get(v_vars_232_, 2);
    v___x_234_ = lean_nat_dec_lt(v_x_228_, v_size_233_);
    if v___x_234_ == 0 {
        let mut v___x_235_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_236_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_235_ = l_outOfBounds___redArg(v___x_229_);
        v___x_236_ =
            leanh::lean_apply_2(v_toPure_230_, leanh::lean_box(0), v___x_235_);
        return v___x_236_;
    } else {
        let mut v___x_237_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_238_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_237_ = l_Lean_PersistentArray_get_x21___redArg(v___x_229_, v_vars_232_, v_x_228_);
        v___x_238_ =
            leanh::lean_apply_2(v_toPure_230_, leanh::lean_box(0), v___x_237_);
        return v___x_238_;
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__0___boxed(
    mut v_x_239_: *mut leanh::LeanObject,
    mut v___x_240_: *mut leanh::LeanObject,
    mut v_toPure_241_: *mut leanh::LeanObject,
    mut v_____do__lift_242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_243_ = l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__0(
        v_x_239_,
        v___x_240_,
        v_toPure_241_,
        v_____do__lift_242_,
    );
    leanh::lean_dec_ref(v_____do__lift_242_);
    leanh::lean_dec_ref(v___x_240_);
    leanh::lean_dec(v_x_239_);
    return v_res_243_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__1(
    mut v_____do__lift_244_: *mut leanh::LeanObject,
    mut v_____do__lift_245_: *mut leanh::LeanObject,
    mut v_toPure_246_: *mut leanh::LeanObject,
    mut v_x_247_: *mut leanh::LeanObject,
    mut v___x_248_: *mut leanh::LeanObject,
    mut v_____do__lift_249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_op_250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_257_: u8 = 0;
    let mut v___x_258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_op_250_ = leanh::lean_ctor_get(v_____do__lift_244_, 3);
                leanh::lean_inc_ref(v_op_250_);
                leanh::lean_dec_ref(v_____do__lift_244_);
                v_vars_255_ = leanh::lean_ctor_get(v_____do__lift_245_, 10);
                v_size_256_ = leanh::lean_ctor_get(v_vars_255_, 2);
                v___x_257_ = lean_nat_dec_lt(v_x_247_, v_size_256_);
                if v___x_257_ == 0 {
                    v___x_258_ = l_outOfBounds___redArg(v___x_248_);
                    v___y_252_ = v___x_258_;
                    state = 1;
                    continue;
                } else {
                    v___x_259_ =
                        l_Lean_PersistentArray_get_x21___redArg(v___x_248_, v_vars_255_, v_x_247_);
                    v___y_252_ = v___x_259_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_253_ = l_Lean_mkAppB(v_op_250_, v___y_252_, v_____do__lift_249_);
                v___x_254_ = leanh::lean_apply_2(
                    v_toPure_246_,
                    leanh::lean_box(0),
                    v___x_253_,
                );
                return v___x_254_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__1___boxed(
    mut v_____do__lift_260_: *mut leanh::LeanObject,
    mut v_____do__lift_261_: *mut leanh::LeanObject,
    mut v_toPure_262_: *mut leanh::LeanObject,
    mut v_x_263_: *mut leanh::LeanObject,
    mut v___x_264_: *mut leanh::LeanObject,
    mut v_____do__lift_265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_266_ = l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__1(
        v_____do__lift_260_,
        v_____do__lift_261_,
        v_toPure_262_,
        v_x_263_,
        v___x_264_,
        v_____do__lift_265_,
    );
    leanh::lean_dec_ref(v___x_264_);
    leanh::lean_dec(v_x_263_);
    leanh::lean_dec_ref(v_____do__lift_261_);
    return v_res_266_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_denoteExpr___redArg(
    mut v_inst_267_: *mut leanh::LeanObject,
    mut v_inst_268_: *mut leanh::LeanObject,
    mut v_s_269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_270_ = leanh::lean_ctor_get(v_inst_267_, 0);
    v_toBind_271_ = leanh::lean_ctor_get(v_inst_267_, 1);
    leanh::lean_inc(v_toBind_271_);
    v_toPure_272_ = leanh::lean_ctor_get(v_toApplicative_270_, 1);
    leanh::lean_inc(v_toPure_272_);
    v___x_273_ = l_Lean_instInhabitedExpr;
    if leanh::lean_obj_tag(v_s_269_) == 0 {
        let mut v_x_274_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_275_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_276_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_267_);
        v_x_274_ = leanh::lean_ctor_get(v_s_269_, 0);
        leanh::lean_inc(v_x_274_);
        leanh::lean_dec_ref_known(v_s_269_, 1);
        v___f_275_ = leanh::lean_alloc_closure(
            l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__0___boxed as *mut core::ffi::c_void,
            4,
            3,
        );
        leanh::lean_closure_set(v___f_275_, 0, v_x_274_);
        leanh::lean_closure_set(v___f_275_, 1, v___x_273_);
        leanh::lean_closure_set(v___f_275_, 2, v_toPure_272_);
        v___x_276_ = leanh::lean_apply_4(
            v_toBind_271_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_inst_268_,
            v___f_275_,
        );
        return v___x_276_;
    } else {
        let mut v_x_277_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_s_278_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_279_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_280_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_x_277_ = leanh::lean_ctor_get(v_s_269_, 0);
        leanh::lean_inc(v_x_277_);
        v_s_278_ = leanh::lean_ctor_get(v_s_269_, 1);
        leanh::lean_inc_ref(v_s_278_);
        leanh::lean_dec_ref_known(v_s_269_, 2);
        leanh::lean_inc(v_toBind_271_);
        leanh::lean_inc(v_inst_268_);
        v___f_279_ = leanh::lean_alloc_closure(
            l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__3 as *mut core::ffi::c_void,
            8,
            7,
        );
        leanh::lean_closure_set(v___f_279_, 0, v_toPure_272_);
        leanh::lean_closure_set(v___f_279_, 1, v_x_277_);
        leanh::lean_closure_set(v___f_279_, 2, v___x_273_);
        leanh::lean_closure_set(v___f_279_, 3, v_inst_267_);
        leanh::lean_closure_set(v___f_279_, 4, v_inst_268_);
        leanh::lean_closure_set(v___f_279_, 5, v_s_278_);
        leanh::lean_closure_set(v___f_279_, 6, v_toBind_271_);
        v___x_280_ = leanh::lean_apply_4(
            v_toBind_271_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_inst_268_,
            v___f_279_,
        );
        return v___x_280_;
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__2(
    mut v_____do__lift_281_: *mut leanh::LeanObject,
    mut v_toPure_282_: *mut leanh::LeanObject,
    mut v_x_283_: *mut leanh::LeanObject,
    mut v___x_284_: *mut leanh::LeanObject,
    mut v_inst_285_: *mut leanh::LeanObject,
    mut v_inst_286_: *mut leanh::LeanObject,
    mut v_s_287_: *mut leanh::LeanObject,
    mut v_toBind_288_: *mut leanh::LeanObject,
    mut v_____do__lift_289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_290_ = leanh::lean_alloc_closure(
        l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_290_, 0, v_____do__lift_281_);
    leanh::lean_closure_set(v___f_290_, 1, v_____do__lift_289_);
    leanh::lean_closure_set(v___f_290_, 2, v_toPure_282_);
    leanh::lean_closure_set(v___f_290_, 3, v_x_283_);
    leanh::lean_closure_set(v___f_290_, 4, v___x_284_);
    v___x_291_ = l_Lean_Grind_AC_Seq_denoteExpr___redArg(v_inst_285_, v_inst_286_, v_s_287_);
    v___x_292_ = leanh::lean_apply_4(
        v_toBind_288_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_291_,
        v___f_290_,
    );
    return v___x_292_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__3(
    mut v_toPure_293_: *mut leanh::LeanObject,
    mut v_x_294_: *mut leanh::LeanObject,
    mut v___x_295_: *mut leanh::LeanObject,
    mut v_inst_296_: *mut leanh::LeanObject,
    mut v_inst_297_: *mut leanh::LeanObject,
    mut v_s_298_: *mut leanh::LeanObject,
    mut v_toBind_299_: *mut leanh::LeanObject,
    mut v_____do__lift_300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_299_);
    leanh::lean_inc(v_inst_297_);
    v___f_301_ = leanh::lean_alloc_closure(
        l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__2 as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___f_301_, 0, v_____do__lift_300_);
    leanh::lean_closure_set(v___f_301_, 1, v_toPure_293_);
    leanh::lean_closure_set(v___f_301_, 2, v_x_294_);
    leanh::lean_closure_set(v___f_301_, 3, v___x_295_);
    leanh::lean_closure_set(v___f_301_, 4, v_inst_296_);
    leanh::lean_closure_set(v___f_301_, 5, v_inst_297_);
    leanh::lean_closure_set(v___f_301_, 6, v_s_298_);
    leanh::lean_closure_set(v___f_301_, 7, v_toBind_299_);
    v___x_302_ = leanh::lean_apply_4(
        v_toBind_299_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_297_,
        v___f_301_,
    );
    return v___x_302_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_denoteExpr(
    mut v_M_303_: *mut leanh::LeanObject,
    mut v_inst_304_: *mut leanh::LeanObject,
    mut v_inst_305_: *mut leanh::LeanObject,
    mut v_s_306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_307_ = l_Lean_Grind_AC_Seq_denoteExpr___redArg(v_inst_304_, v_inst_305_, v_s_306_);
    return v___x_307_;
}
pub unsafe fn l_Lean_Grind_AC_Expr_denoteExpr___redArg___lam__1(
    mut v_____do__lift_308_: *mut leanh::LeanObject,
    mut v_____do__lift_309_: *mut leanh::LeanObject,
    mut v_toPure_310_: *mut leanh::LeanObject,
    mut v_____do__lift_311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_op_312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_op_312_ = leanh::lean_ctor_get(v_____do__lift_308_, 3);
    leanh::lean_inc_ref(v_op_312_);
    leanh::lean_dec_ref(v_____do__lift_308_);
    v___x_313_ = l_Lean_mkAppB(v_op_312_, v_____do__lift_309_, v_____do__lift_311_);
    v___x_314_ = leanh::lean_apply_2(v_toPure_310_, leanh::lean_box(0), v___x_313_);
    return v___x_314_;
}
pub unsafe fn l_Lean_Grind_AC_Expr_denoteExpr___redArg___lam__2(
    mut v_toPure_315_: *mut leanh::LeanObject,
    mut v_inst_316_: *mut leanh::LeanObject,
    mut v_inst_317_: *mut leanh::LeanObject,
    mut v_rhs_318_: *mut leanh::LeanObject,
    mut v_toBind_319_: *mut leanh::LeanObject,
    mut v_lhs_320_: *mut leanh::LeanObject,
    mut v_____do__lift_321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_319_);
    leanh::lean_inc(v_inst_317_);
    leanh::lean_inc_ref(v_inst_316_);
    v___f_322_ = leanh::lean_alloc_closure(
        l_Lean_Grind_AC_Expr_denoteExpr___redArg___lam__0 as *mut core::ffi::c_void,
        7,
        6,
    );
    leanh::lean_closure_set(v___f_322_, 0, v_____do__lift_321_);
    leanh::lean_closure_set(v___f_322_, 1, v_toPure_315_);
    leanh::lean_closure_set(v___f_322_, 2, v_inst_316_);
    leanh::lean_closure_set(v___f_322_, 3, v_inst_317_);
    leanh::lean_closure_set(v___f_322_, 4, v_rhs_318_);
    leanh::lean_closure_set(v___f_322_, 5, v_toBind_319_);
    v___x_323_ = l_Lean_Grind_AC_Expr_denoteExpr___redArg(v_inst_316_, v_inst_317_, v_lhs_320_);
    v___x_324_ = leanh::lean_apply_4(
        v_toBind_319_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_323_,
        v___f_322_,
    );
    return v___x_324_;
}
pub unsafe fn l_Lean_Grind_AC_Expr_denoteExpr___redArg(
    mut v_inst_325_: *mut leanh::LeanObject,
    mut v_inst_326_: *mut leanh::LeanObject,
    mut v_e_327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_e_327_) == 0 {
        let mut v_toApplicative_328_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_329_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_330_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_332_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_333_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_334_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_328_ = leanh::lean_ctor_get(v_inst_325_, 0);
        leanh::lean_inc_ref(v_toApplicative_328_);
        v_toBind_329_ = leanh::lean_ctor_get(v_inst_325_, 1);
        leanh::lean_inc(v_toBind_329_);
        leanh::lean_dec_ref(v_inst_325_);
        v_toPure_330_ = leanh::lean_ctor_get(v_toApplicative_328_, 1);
        leanh::lean_inc(v_toPure_330_);
        leanh::lean_dec_ref(v_toApplicative_328_);
        v_x_331_ = leanh::lean_ctor_get(v_e_327_, 0);
        leanh::lean_inc(v_x_331_);
        leanh::lean_dec_ref_known(v_e_327_, 1);
        v___x_332_ = l_Lean_instInhabitedExpr;
        v___f_333_ = leanh::lean_alloc_closure(
            l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__0___boxed as *mut core::ffi::c_void,
            4,
            3,
        );
        leanh::lean_closure_set(v___f_333_, 0, v_x_331_);
        leanh::lean_closure_set(v___f_333_, 1, v___x_332_);
        leanh::lean_closure_set(v___f_333_, 2, v_toPure_330_);
        v___x_334_ = leanh::lean_apply_4(
            v_toBind_329_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_inst_326_,
            v___f_333_,
        );
        return v___x_334_;
    } else {
        let mut v_toApplicative_335_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_336_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_337_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_lhs_338_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_rhs_339_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_340_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_335_ = leanh::lean_ctor_get(v_inst_325_, 0);
        v_toBind_336_ = leanh::lean_ctor_get(v_inst_325_, 1);
        leanh::lean_inc_n(v_toBind_336_, 2);
        v_toPure_337_ = leanh::lean_ctor_get(v_toApplicative_335_, 1);
        leanh::lean_inc(v_toPure_337_);
        v_lhs_338_ = leanh::lean_ctor_get(v_e_327_, 0);
        leanh::lean_inc_ref(v_lhs_338_);
        v_rhs_339_ = leanh::lean_ctor_get(v_e_327_, 1);
        leanh::lean_inc_ref(v_rhs_339_);
        leanh::lean_dec_ref_known(v_e_327_, 2);
        leanh::lean_inc(v_inst_326_);
        v___f_340_ = leanh::lean_alloc_closure(
            l_Lean_Grind_AC_Expr_denoteExpr___redArg___lam__2 as *mut core::ffi::c_void,
            7,
            6,
        );
        leanh::lean_closure_set(v___f_340_, 0, v_toPure_337_);
        leanh::lean_closure_set(v___f_340_, 1, v_inst_325_);
        leanh::lean_closure_set(v___f_340_, 2, v_inst_326_);
        leanh::lean_closure_set(v___f_340_, 3, v_rhs_339_);
        leanh::lean_closure_set(v___f_340_, 4, v_toBind_336_);
        leanh::lean_closure_set(v___f_340_, 5, v_lhs_338_);
        v___x_341_ = leanh::lean_apply_4(
            v_toBind_336_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_inst_326_,
            v___f_340_,
        );
        return v___x_341_;
    }
}
pub unsafe fn l_Lean_Grind_AC_Expr_denoteExpr___redArg___lam__0(
    mut v_____do__lift_342_: *mut leanh::LeanObject,
    mut v_toPure_343_: *mut leanh::LeanObject,
    mut v_inst_344_: *mut leanh::LeanObject,
    mut v_inst_345_: *mut leanh::LeanObject,
    mut v_rhs_346_: *mut leanh::LeanObject,
    mut v_toBind_347_: *mut leanh::LeanObject,
    mut v_____do__lift_348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_349_ = leanh::lean_alloc_closure(
        l_Lean_Grind_AC_Expr_denoteExpr___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_349_, 0, v_____do__lift_342_);
    leanh::lean_closure_set(v___f_349_, 1, v_____do__lift_348_);
    leanh::lean_closure_set(v___f_349_, 2, v_toPure_343_);
    v___x_350_ = l_Lean_Grind_AC_Expr_denoteExpr___redArg(v_inst_344_, v_inst_345_, v_rhs_346_);
    v___x_351_ = leanh::lean_apply_4(
        v_toBind_347_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_350_,
        v___f_349_,
    );
    return v___x_351_;
}
pub unsafe fn l_Lean_Grind_AC_Expr_denoteExpr(
    mut v_M_352_: *mut leanh::LeanObject,
    mut v_inst_353_: *mut leanh::LeanObject,
    mut v_inst_354_: *mut leanh::LeanObject,
    mut v_e_355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_356_ = l_Lean_Grind_AC_Expr_denoteExpr___redArg(v_inst_353_, v_inst_354_, v_e_355_);
    return v___x_356_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0(
    mut v_s_360_: *mut leanh::LeanObject,
    mut v_____do__lift_361_: *mut leanh::LeanObject,
    mut v_toPure_362_: *mut leanh::LeanObject,
    mut v_____do__lift_363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_type_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_type_364_ = leanh::lean_ctor_get(v_s_360_, 1);
    leanh::lean_inc_ref(v_type_364_);
    v_u_365_ = leanh::lean_ctor_get(v_s_360_, 2);
    leanh::lean_inc(v_u_365_);
    leanh::lean_dec_ref(v_s_360_);
    v___x_366_ = l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0___closed__1;
    v___x_367_ = leanh::lean_box(0);
    v___x_368_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_368_, 0, v_u_365_);
    leanh::lean_ctor_set(v___x_368_, 1, v___x_367_);
    v___x_369_ = l_Lean_mkConst(v___x_366_, v___x_368_);
    v___x_370_ = l_Lean_mkApp3(
        v___x_369_,
        v_type_364_,
        v_____do__lift_361_,
        v_____do__lift_363_,
    );
    v___x_371_ = leanh::lean_apply_2(v_toPure_362_, leanh::lean_box(0), v___x_370_);
    return v___x_371_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__1(
    mut v_s_372_: *mut leanh::LeanObject,
    mut v_toPure_373_: *mut leanh::LeanObject,
    mut v_inst_374_: *mut leanh::LeanObject,
    mut v_inst_375_: *mut leanh::LeanObject,
    mut v_rhs_376_: *mut leanh::LeanObject,
    mut v_toBind_377_: *mut leanh::LeanObject,
    mut v_____do__lift_378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_379_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_379_, 0, v_s_372_);
    leanh::lean_closure_set(v___f_379_, 1, v_____do__lift_378_);
    leanh::lean_closure_set(v___f_379_, 2, v_toPure_373_);
    v___x_380_ = l_Lean_Grind_AC_Seq_denoteExpr___redArg(v_inst_374_, v_inst_375_, v_rhs_376_);
    v___x_381_ = leanh::lean_apply_4(
        v_toBind_377_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_380_,
        v___f_379_,
    );
    return v___x_381_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__2(
    mut v_c_382_: *mut leanh::LeanObject,
    mut v_toPure_383_: *mut leanh::LeanObject,
    mut v_inst_384_: *mut leanh::LeanObject,
    mut v_inst_385_: *mut leanh::LeanObject,
    mut v_toBind_386_: *mut leanh::LeanObject,
    mut v_s_387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lhs_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lhs_388_ = leanh::lean_ctor_get(v_c_382_, 0);
    leanh::lean_inc_ref(v_lhs_388_);
    v_rhs_389_ = leanh::lean_ctor_get(v_c_382_, 1);
    leanh::lean_inc_ref(v_rhs_389_);
    leanh::lean_dec_ref(v_c_382_);
    leanh::lean_inc(v_toBind_386_);
    leanh::lean_inc(v_inst_385_);
    leanh::lean_inc_ref(v_inst_384_);
    v___f_390_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__1 as *mut core::ffi::c_void,
        7,
        6,
    );
    leanh::lean_closure_set(v___f_390_, 0, v_s_387_);
    leanh::lean_closure_set(v___f_390_, 1, v_toPure_383_);
    leanh::lean_closure_set(v___f_390_, 2, v_inst_384_);
    leanh::lean_closure_set(v___f_390_, 3, v_inst_385_);
    leanh::lean_closure_set(v___f_390_, 4, v_rhs_389_);
    leanh::lean_closure_set(v___f_390_, 5, v_toBind_386_);
    v___x_391_ = l_Lean_Grind_AC_Seq_denoteExpr___redArg(v_inst_384_, v_inst_385_, v_lhs_388_);
    v___x_392_ = leanh::lean_apply_4(
        v_toBind_386_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_391_,
        v___f_390_,
    );
    return v___x_392_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg(
    mut v_inst_393_: *mut leanh::LeanObject,
    mut v_inst_394_: *mut leanh::LeanObject,
    mut v_c_395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_396_ = leanh::lean_ctor_get(v_inst_393_, 0);
    v_toBind_397_ = leanh::lean_ctor_get(v_inst_393_, 1);
    leanh::lean_inc_n(v_toBind_397_, 2);
    v_toPure_398_ = leanh::lean_ctor_get(v_toApplicative_396_, 1);
    leanh::lean_inc(v_toPure_398_);
    leanh::lean_inc(v_inst_394_);
    v___f_399_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_399_, 0, v_c_395_);
    leanh::lean_closure_set(v___f_399_, 1, v_toPure_398_);
    leanh::lean_closure_set(v___f_399_, 2, v_inst_393_);
    leanh::lean_closure_set(v___f_399_, 3, v_inst_394_);
    leanh::lean_closure_set(v___f_399_, 4, v_toBind_397_);
    v___x_400_ = leanh::lean_apply_4(
        v_toBind_397_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_394_,
        v___f_399_,
    );
    return v___x_400_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr(
    mut v_M_401_: *mut leanh::LeanObject,
    mut v_inst_402_: *mut leanh::LeanObject,
    mut v_inst_403_: *mut leanh::LeanObject,
    mut v_c_404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_405_ =
        l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg(v_inst_402_, v_inst_403_, v_c_404_);
    return v___x_405_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0(
    mut v_s_409_: *mut leanh::LeanObject,
    mut v_____do__lift_410_: *mut leanh::LeanObject,
    mut v_toPure_411_: *mut leanh::LeanObject,
    mut v_____do__lift_412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_type_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_type_413_ = leanh::lean_ctor_get(v_s_409_, 1);
    leanh::lean_inc_ref(v_type_413_);
    v_u_414_ = leanh::lean_ctor_get(v_s_409_, 2);
    leanh::lean_inc(v_u_414_);
    leanh::lean_dec_ref(v_s_409_);
    v___x_415_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0___closed__1;
    v___x_416_ = leanh::lean_box(0);
    v___x_417_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_417_, 0, v_u_414_);
    leanh::lean_ctor_set(v___x_417_, 1, v___x_416_);
    v___x_418_ = l_Lean_mkConst(v___x_415_, v___x_417_);
    v___x_419_ = l_Lean_mkApp3(
        v___x_418_,
        v_type_413_,
        v_____do__lift_410_,
        v_____do__lift_412_,
    );
    v___x_420_ = leanh::lean_apply_2(v_toPure_411_, leanh::lean_box(0), v___x_419_);
    return v___x_420_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__1(
    mut v_s_421_: *mut leanh::LeanObject,
    mut v_toPure_422_: *mut leanh::LeanObject,
    mut v_inst_423_: *mut leanh::LeanObject,
    mut v_inst_424_: *mut leanh::LeanObject,
    mut v_rhs_425_: *mut leanh::LeanObject,
    mut v_toBind_426_: *mut leanh::LeanObject,
    mut v_____do__lift_427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_428_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_428_, 0, v_s_421_);
    leanh::lean_closure_set(v___f_428_, 1, v_____do__lift_427_);
    leanh::lean_closure_set(v___f_428_, 2, v_toPure_422_);
    v___x_429_ = l_Lean_Grind_AC_Seq_denoteExpr___redArg(v_inst_423_, v_inst_424_, v_rhs_425_);
    v___x_430_ = leanh::lean_apply_4(
        v_toBind_426_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_429_,
        v___f_428_,
    );
    return v___x_430_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__2(
    mut v_c_431_: *mut leanh::LeanObject,
    mut v_toPure_432_: *mut leanh::LeanObject,
    mut v_inst_433_: *mut leanh::LeanObject,
    mut v_inst_434_: *mut leanh::LeanObject,
    mut v_toBind_435_: *mut leanh::LeanObject,
    mut v_s_436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lhs_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lhs_437_ = leanh::lean_ctor_get(v_c_431_, 0);
    leanh::lean_inc_ref(v_lhs_437_);
    v_rhs_438_ = leanh::lean_ctor_get(v_c_431_, 1);
    leanh::lean_inc_ref(v_rhs_438_);
    leanh::lean_dec_ref(v_c_431_);
    leanh::lean_inc(v_toBind_435_);
    leanh::lean_inc(v_inst_434_);
    leanh::lean_inc_ref(v_inst_433_);
    v___f_439_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__1 as *mut core::ffi::c_void,
        7,
        6,
    );
    leanh::lean_closure_set(v___f_439_, 0, v_s_436_);
    leanh::lean_closure_set(v___f_439_, 1, v_toPure_432_);
    leanh::lean_closure_set(v___f_439_, 2, v_inst_433_);
    leanh::lean_closure_set(v___f_439_, 3, v_inst_434_);
    leanh::lean_closure_set(v___f_439_, 4, v_rhs_438_);
    leanh::lean_closure_set(v___f_439_, 5, v_toBind_435_);
    v___x_440_ = l_Lean_Grind_AC_Seq_denoteExpr___redArg(v_inst_433_, v_inst_434_, v_lhs_437_);
    v___x_441_ = leanh::lean_apply_4(
        v_toBind_435_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_440_,
        v___f_439_,
    );
    return v___x_441_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg(
    mut v_inst_442_: *mut leanh::LeanObject,
    mut v_inst_443_: *mut leanh::LeanObject,
    mut v_c_444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_445_ = leanh::lean_ctor_get(v_inst_442_, 0);
    v_toBind_446_ = leanh::lean_ctor_get(v_inst_442_, 1);
    leanh::lean_inc_n(v_toBind_446_, 2);
    v_toPure_447_ = leanh::lean_ctor_get(v_toApplicative_445_, 1);
    leanh::lean_inc(v_toPure_447_);
    leanh::lean_inc(v_inst_443_);
    v___f_448_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_448_, 0, v_c_444_);
    leanh::lean_closure_set(v___f_448_, 1, v_toPure_447_);
    leanh::lean_closure_set(v___f_448_, 2, v_inst_442_);
    leanh::lean_closure_set(v___f_448_, 3, v_inst_443_);
    leanh::lean_closure_set(v___f_448_, 4, v_toBind_446_);
    v___x_449_ = leanh::lean_apply_4(
        v_toBind_446_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_443_,
        v___f_448_,
    );
    return v___x_449_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr(
    mut v_M_450_: *mut leanh::LeanObject,
    mut v_inst_451_: *mut leanh::LeanObject,
    mut v_inst_452_: *mut leanh::LeanObject,
    mut v_c_453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_454_ =
        l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg(v_inst_451_, v_inst_452_, v_c_453_);
    return v___x_454_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(builtin);
}