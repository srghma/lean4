// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC.DenoteExpr
// Imports: Lean.Meta.Tactic.Grind.AC.Util
use crate::r#gen::Init::GetElem::l_outOfBounds___redArg;
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_get_x21___redArg;
use crate::r#gen::Lean::Expr::{
    l_Lean_instInhabitedExpr, l_Lean_mkApp3, l_Lean_mkAppB, l_Lean_mkConst,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::AC::Util::{
    initialize_Lean_Meta_Tactic_Grind_AC_Util, runtime_initialize_Lean_Meta_Tactic_Grind_AC_Util,
};
use crate::lean_imports_rs::Init::Prelude::lean_nat_dec_lt;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag,
};
pub static l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0___closed__0_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0___closed__0_value
        ) as *mut LeanObject,
        16122875713692181903 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0___closed__0_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0___closed__0_value
        ) as *mut LeanObject,
        6695605208187598753 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0___closed__1_value
) as *mut LeanObject;
pub unsafe fn l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__0(
    mut v_x_228_: *mut LeanObject,
    mut v___x_229_: *mut LeanObject,
    mut v_toPure_230_: *mut LeanObject,
    mut v_____do__lift_231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_vars_232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_234_: u8 = 0;
    v_vars_232_ = lean_ctor_get(v_____do__lift_231_, 10);
    v_size_233_ = lean_ctor_get(v_vars_232_, 2);
    v___x_234_ = lean_nat_dec_lt(v_x_228_, v_size_233_);
    if v___x_234_ == 0 {
        let mut v___x_235_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_236_: *mut LeanObject = core::ptr::null_mut();
        v___x_235_ = l_outOfBounds___redArg(v___x_229_);
        v___x_236_ = lean_apply_2(v_toPure_230_, lean_box(0), v___x_235_);
        return v___x_236_;
    } else {
        let mut v___x_237_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_238_: *mut LeanObject = core::ptr::null_mut();
        v___x_237_ = l_Lean_PersistentArray_get_x21___redArg(v___x_229_, v_vars_232_, v_x_228_);
        v___x_238_ = lean_apply_2(v_toPure_230_, lean_box(0), v___x_237_);
        return v___x_238_;
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__0___boxed(
    mut v_x_239_: *mut LeanObject,
    mut v___x_240_: *mut LeanObject,
    mut v_toPure_241_: *mut LeanObject,
    mut v_____do__lift_242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_243_: *mut LeanObject = core::ptr::null_mut();
    v_res_243_ = l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__0(
        v_x_239_,
        v___x_240_,
        v_toPure_241_,
        v_____do__lift_242_,
    );
    lean_dec_ref(v_____do__lift_242_);
    lean_dec_ref(v___x_240_);
    lean_dec(v_x_239_);
    return v_res_243_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__1(
    mut v_____do__lift_244_: *mut LeanObject,
    mut v_____do__lift_245_: *mut LeanObject,
    mut v_toPure_246_: *mut LeanObject,
    mut v_x_247_: *mut LeanObject,
    mut v___x_248_: *mut LeanObject,
    mut v_____do__lift_249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_op_250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_257_: u8 = 0;
    let mut v___x_258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_259_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_op_250_ = lean_ctor_get(v_____do__lift_244_, 3);
                lean_inc_ref(v_op_250_);
                lean_dec_ref(v_____do__lift_244_);
                v_vars_255_ = lean_ctor_get(v_____do__lift_245_, 10);
                v_size_256_ = lean_ctor_get(v_vars_255_, 2);
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
                v___x_254_ = lean_apply_2(v_toPure_246_, lean_box(0), v___x_253_);
                return v___x_254_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__1___boxed(
    mut v_____do__lift_260_: *mut LeanObject,
    mut v_____do__lift_261_: *mut LeanObject,
    mut v_toPure_262_: *mut LeanObject,
    mut v_x_263_: *mut LeanObject,
    mut v___x_264_: *mut LeanObject,
    mut v_____do__lift_265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_266_: *mut LeanObject = core::ptr::null_mut();
    v_res_266_ = l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__1(
        v_____do__lift_260_,
        v_____do__lift_261_,
        v_toPure_262_,
        v_x_263_,
        v___x_264_,
        v_____do__lift_265_,
    );
    lean_dec_ref(v___x_264_);
    lean_dec(v_x_263_);
    lean_dec_ref(v_____do__lift_261_);
    return v_res_266_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_denoteExpr___redArg(
    mut v_inst_267_: *mut LeanObject,
    mut v_inst_268_: *mut LeanObject,
    mut v_s_269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_270_ = lean_ctor_get(v_inst_267_, 0);
    v_toBind_271_ = lean_ctor_get(v_inst_267_, 1);
    lean_inc(v_toBind_271_);
    v_toPure_272_ = lean_ctor_get(v_toApplicative_270_, 1);
    lean_inc(v_toPure_272_);
    v___x_273_ = l_Lean_instInhabitedExpr;
    if lean_obj_tag(v_s_269_) == 0 {
        let mut v_x_274_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_275_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_276_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_267_);
        v_x_274_ = lean_ctor_get(v_s_269_, 0);
        lean_inc(v_x_274_);
        lean_dec_ref_known(v_s_269_, 1);
        v___f_275_ = lean_alloc_closure(
            l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__0___boxed as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_275_, 0, v_x_274_);
        lean_closure_set(v___f_275_, 1, v___x_273_);
        lean_closure_set(v___f_275_, 2, v_toPure_272_);
        v___x_276_ = lean_apply_4(
            v_toBind_271_,
            lean_box(0),
            lean_box(0),
            v_inst_268_,
            v___f_275_,
        );
        return v___x_276_;
    } else {
        let mut v_x_277_: *mut LeanObject = core::ptr::null_mut();
        let mut v_s_278_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_279_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_280_: *mut LeanObject = core::ptr::null_mut();
        v_x_277_ = lean_ctor_get(v_s_269_, 0);
        lean_inc(v_x_277_);
        v_s_278_ = lean_ctor_get(v_s_269_, 1);
        lean_inc_ref(v_s_278_);
        lean_dec_ref_known(v_s_269_, 2);
        lean_inc(v_toBind_271_);
        lean_inc(v_inst_268_);
        v___f_279_ = lean_alloc_closure(
            l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__3 as *mut core::ffi::c_void,
            8,
            7,
        );
        lean_closure_set(v___f_279_, 0, v_toPure_272_);
        lean_closure_set(v___f_279_, 1, v_x_277_);
        lean_closure_set(v___f_279_, 2, v___x_273_);
        lean_closure_set(v___f_279_, 3, v_inst_267_);
        lean_closure_set(v___f_279_, 4, v_inst_268_);
        lean_closure_set(v___f_279_, 5, v_s_278_);
        lean_closure_set(v___f_279_, 6, v_toBind_271_);
        v___x_280_ = lean_apply_4(
            v_toBind_271_,
            lean_box(0),
            lean_box(0),
            v_inst_268_,
            v___f_279_,
        );
        return v___x_280_;
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__2(
    mut v_____do__lift_281_: *mut LeanObject,
    mut v_toPure_282_: *mut LeanObject,
    mut v_x_283_: *mut LeanObject,
    mut v___x_284_: *mut LeanObject,
    mut v_inst_285_: *mut LeanObject,
    mut v_inst_286_: *mut LeanObject,
    mut v_s_287_: *mut LeanObject,
    mut v_toBind_288_: *mut LeanObject,
    mut v_____do__lift_289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut LeanObject = core::ptr::null_mut();
    v___f_290_ = lean_alloc_closure(
        l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__1___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_290_, 0, v_____do__lift_281_);
    lean_closure_set(v___f_290_, 1, v_____do__lift_289_);
    lean_closure_set(v___f_290_, 2, v_toPure_282_);
    lean_closure_set(v___f_290_, 3, v_x_283_);
    lean_closure_set(v___f_290_, 4, v___x_284_);
    v___x_291_ = l_Lean_Grind_AC_Seq_denoteExpr___redArg(v_inst_285_, v_inst_286_, v_s_287_);
    v___x_292_ = lean_apply_4(
        v_toBind_288_,
        lean_box(0),
        lean_box(0),
        v___x_291_,
        v___f_290_,
    );
    return v___x_292_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__3(
    mut v_toPure_293_: *mut LeanObject,
    mut v_x_294_: *mut LeanObject,
    mut v___x_295_: *mut LeanObject,
    mut v_inst_296_: *mut LeanObject,
    mut v_inst_297_: *mut LeanObject,
    mut v_s_298_: *mut LeanObject,
    mut v_toBind_299_: *mut LeanObject,
    mut v_____do__lift_300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_299_);
    lean_inc(v_inst_297_);
    v___f_301_ = lean_alloc_closure(
        l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__2 as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_301_, 0, v_____do__lift_300_);
    lean_closure_set(v___f_301_, 1, v_toPure_293_);
    lean_closure_set(v___f_301_, 2, v_x_294_);
    lean_closure_set(v___f_301_, 3, v___x_295_);
    lean_closure_set(v___f_301_, 4, v_inst_296_);
    lean_closure_set(v___f_301_, 5, v_inst_297_);
    lean_closure_set(v___f_301_, 6, v_s_298_);
    lean_closure_set(v___f_301_, 7, v_toBind_299_);
    v___x_302_ = lean_apply_4(
        v_toBind_299_,
        lean_box(0),
        lean_box(0),
        v_inst_297_,
        v___f_301_,
    );
    return v___x_302_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_denoteExpr(
    mut v_M_303_: *mut LeanObject,
    mut v_inst_304_: *mut LeanObject,
    mut v_inst_305_: *mut LeanObject,
    mut v_s_306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_307_: *mut LeanObject = core::ptr::null_mut();
    v___x_307_ = l_Lean_Grind_AC_Seq_denoteExpr___redArg(v_inst_304_, v_inst_305_, v_s_306_);
    return v___x_307_;
}
pub unsafe fn l_Lean_Grind_AC_Expr_denoteExpr___redArg___lam__1(
    mut v_____do__lift_308_: *mut LeanObject,
    mut v_____do__lift_309_: *mut LeanObject,
    mut v_toPure_310_: *mut LeanObject,
    mut v_____do__lift_311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_op_312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
    v_op_312_ = lean_ctor_get(v_____do__lift_308_, 3);
    lean_inc_ref(v_op_312_);
    lean_dec_ref(v_____do__lift_308_);
    v___x_313_ = l_Lean_mkAppB(v_op_312_, v_____do__lift_309_, v_____do__lift_311_);
    v___x_314_ = lean_apply_2(v_toPure_310_, lean_box(0), v___x_313_);
    return v___x_314_;
}
pub unsafe fn l_Lean_Grind_AC_Expr_denoteExpr___redArg___lam__2(
    mut v_toPure_315_: *mut LeanObject,
    mut v_inst_316_: *mut LeanObject,
    mut v_inst_317_: *mut LeanObject,
    mut v_rhs_318_: *mut LeanObject,
    mut v_toBind_319_: *mut LeanObject,
    mut v_lhs_320_: *mut LeanObject,
    mut v_____do__lift_321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_319_);
    lean_inc(v_inst_317_);
    lean_inc_ref(v_inst_316_);
    v___f_322_ = lean_alloc_closure(
        l_Lean_Grind_AC_Expr_denoteExpr___redArg___lam__0 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_322_, 0, v_____do__lift_321_);
    lean_closure_set(v___f_322_, 1, v_toPure_315_);
    lean_closure_set(v___f_322_, 2, v_inst_316_);
    lean_closure_set(v___f_322_, 3, v_inst_317_);
    lean_closure_set(v___f_322_, 4, v_rhs_318_);
    lean_closure_set(v___f_322_, 5, v_toBind_319_);
    v___x_323_ = l_Lean_Grind_AC_Expr_denoteExpr___redArg(v_inst_316_, v_inst_317_, v_lhs_320_);
    v___x_324_ = lean_apply_4(
        v_toBind_319_,
        lean_box(0),
        lean_box(0),
        v___x_323_,
        v___f_322_,
    );
    return v___x_324_;
}
pub unsafe fn l_Lean_Grind_AC_Expr_denoteExpr___redArg(
    mut v_inst_325_: *mut LeanObject,
    mut v_inst_326_: *mut LeanObject,
    mut v_e_327_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_327_) == 0 {
        let mut v_toApplicative_328_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_329_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_330_: *mut LeanObject = core::ptr::null_mut();
        let mut v_x_331_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_333_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_328_ = lean_ctor_get(v_inst_325_, 0);
        lean_inc_ref(v_toApplicative_328_);
        v_toBind_329_ = lean_ctor_get(v_inst_325_, 1);
        lean_inc(v_toBind_329_);
        lean_dec_ref(v_inst_325_);
        v_toPure_330_ = lean_ctor_get(v_toApplicative_328_, 1);
        lean_inc(v_toPure_330_);
        lean_dec_ref(v_toApplicative_328_);
        v_x_331_ = lean_ctor_get(v_e_327_, 0);
        lean_inc(v_x_331_);
        lean_dec_ref_known(v_e_327_, 1);
        v___x_332_ = l_Lean_instInhabitedExpr;
        v___f_333_ = lean_alloc_closure(
            l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__0___boxed as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_333_, 0, v_x_331_);
        lean_closure_set(v___f_333_, 1, v___x_332_);
        lean_closure_set(v___f_333_, 2, v_toPure_330_);
        v___x_334_ = lean_apply_4(
            v_toBind_329_,
            lean_box(0),
            lean_box(0),
            v_inst_326_,
            v___f_333_,
        );
        return v___x_334_;
    } else {
        let mut v_toApplicative_335_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_336_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_337_: *mut LeanObject = core::ptr::null_mut();
        let mut v_lhs_338_: *mut LeanObject = core::ptr::null_mut();
        let mut v_rhs_339_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_340_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_335_ = lean_ctor_get(v_inst_325_, 0);
        v_toBind_336_ = lean_ctor_get(v_inst_325_, 1);
        lean_inc_n(v_toBind_336_, 2);
        v_toPure_337_ = lean_ctor_get(v_toApplicative_335_, 1);
        lean_inc(v_toPure_337_);
        v_lhs_338_ = lean_ctor_get(v_e_327_, 0);
        lean_inc_ref(v_lhs_338_);
        v_rhs_339_ = lean_ctor_get(v_e_327_, 1);
        lean_inc_ref(v_rhs_339_);
        lean_dec_ref_known(v_e_327_, 2);
        lean_inc(v_inst_326_);
        v___f_340_ = lean_alloc_closure(
            l_Lean_Grind_AC_Expr_denoteExpr___redArg___lam__2 as *mut core::ffi::c_void,
            7,
            6,
        );
        lean_closure_set(v___f_340_, 0, v_toPure_337_);
        lean_closure_set(v___f_340_, 1, v_inst_325_);
        lean_closure_set(v___f_340_, 2, v_inst_326_);
        lean_closure_set(v___f_340_, 3, v_rhs_339_);
        lean_closure_set(v___f_340_, 4, v_toBind_336_);
        lean_closure_set(v___f_340_, 5, v_lhs_338_);
        v___x_341_ = lean_apply_4(
            v_toBind_336_,
            lean_box(0),
            lean_box(0),
            v_inst_326_,
            v___f_340_,
        );
        return v___x_341_;
    }
}
pub unsafe fn l_Lean_Grind_AC_Expr_denoteExpr___redArg___lam__0(
    mut v_____do__lift_342_: *mut LeanObject,
    mut v_toPure_343_: *mut LeanObject,
    mut v_inst_344_: *mut LeanObject,
    mut v_inst_345_: *mut LeanObject,
    mut v_rhs_346_: *mut LeanObject,
    mut v_toBind_347_: *mut LeanObject,
    mut v_____do__lift_348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
    v___f_349_ = lean_alloc_closure(
        l_Lean_Grind_AC_Expr_denoteExpr___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_349_, 0, v_____do__lift_342_);
    lean_closure_set(v___f_349_, 1, v_____do__lift_348_);
    lean_closure_set(v___f_349_, 2, v_toPure_343_);
    v___x_350_ = l_Lean_Grind_AC_Expr_denoteExpr___redArg(v_inst_344_, v_inst_345_, v_rhs_346_);
    v___x_351_ = lean_apply_4(
        v_toBind_347_,
        lean_box(0),
        lean_box(0),
        v___x_350_,
        v___f_349_,
    );
    return v___x_351_;
}
pub unsafe fn l_Lean_Grind_AC_Expr_denoteExpr(
    mut v_M_352_: *mut LeanObject,
    mut v_inst_353_: *mut LeanObject,
    mut v_inst_354_: *mut LeanObject,
    mut v_e_355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    v___x_356_ = l_Lean_Grind_AC_Expr_denoteExpr___redArg(v_inst_353_, v_inst_354_, v_e_355_);
    return v___x_356_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0(
    mut v_s_360_: *mut LeanObject,
    mut v_____do__lift_361_: *mut LeanObject,
    mut v_toPure_362_: *mut LeanObject,
    mut v_____do__lift_363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_type_364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
    v_type_364_ = lean_ctor_get(v_s_360_, 1);
    lean_inc_ref(v_type_364_);
    v_u_365_ = lean_ctor_get(v_s_360_, 2);
    lean_inc(v_u_365_);
    lean_dec_ref(v_s_360_);
    v___x_366_ = l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0___closed__1;
    v___x_367_ = lean_box(0);
    v___x_368_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_368_, 0, v_u_365_);
    lean_ctor_set(v___x_368_, 1, v___x_367_);
    v___x_369_ = l_Lean_mkConst(v___x_366_, v___x_368_);
    v___x_370_ = l_Lean_mkApp3(
        v___x_369_,
        v_type_364_,
        v_____do__lift_361_,
        v_____do__lift_363_,
    );
    v___x_371_ = lean_apply_2(v_toPure_362_, lean_box(0), v___x_370_);
    return v___x_371_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__1(
    mut v_s_372_: *mut LeanObject,
    mut v_toPure_373_: *mut LeanObject,
    mut v_inst_374_: *mut LeanObject,
    mut v_inst_375_: *mut LeanObject,
    mut v_rhs_376_: *mut LeanObject,
    mut v_toBind_377_: *mut LeanObject,
    mut v_____do__lift_378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
    v___f_379_ = lean_alloc_closure(
        l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_379_, 0, v_s_372_);
    lean_closure_set(v___f_379_, 1, v_____do__lift_378_);
    lean_closure_set(v___f_379_, 2, v_toPure_373_);
    v___x_380_ = l_Lean_Grind_AC_Seq_denoteExpr___redArg(v_inst_374_, v_inst_375_, v_rhs_376_);
    v___x_381_ = lean_apply_4(
        v_toBind_377_,
        lean_box(0),
        lean_box(0),
        v___x_380_,
        v___f_379_,
    );
    return v___x_381_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__2(
    mut v_c_382_: *mut LeanObject,
    mut v_toPure_383_: *mut LeanObject,
    mut v_inst_384_: *mut LeanObject,
    mut v_inst_385_: *mut LeanObject,
    mut v_toBind_386_: *mut LeanObject,
    mut v_s_387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lhs_388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
    v_lhs_388_ = lean_ctor_get(v_c_382_, 0);
    lean_inc_ref(v_lhs_388_);
    v_rhs_389_ = lean_ctor_get(v_c_382_, 1);
    lean_inc_ref(v_rhs_389_);
    lean_dec_ref(v_c_382_);
    lean_inc(v_toBind_386_);
    lean_inc(v_inst_385_);
    lean_inc_ref(v_inst_384_);
    v___f_390_ = lean_alloc_closure(
        l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__1 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_390_, 0, v_s_387_);
    lean_closure_set(v___f_390_, 1, v_toPure_383_);
    lean_closure_set(v___f_390_, 2, v_inst_384_);
    lean_closure_set(v___f_390_, 3, v_inst_385_);
    lean_closure_set(v___f_390_, 4, v_rhs_389_);
    lean_closure_set(v___f_390_, 5, v_toBind_386_);
    v___x_391_ = l_Lean_Grind_AC_Seq_denoteExpr___redArg(v_inst_384_, v_inst_385_, v_lhs_388_);
    v___x_392_ = lean_apply_4(
        v_toBind_386_,
        lean_box(0),
        lean_box(0),
        v___x_391_,
        v___f_390_,
    );
    return v___x_392_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg(
    mut v_inst_393_: *mut LeanObject,
    mut v_inst_394_: *mut LeanObject,
    mut v_c_395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_396_ = lean_ctor_get(v_inst_393_, 0);
    v_toBind_397_ = lean_ctor_get(v_inst_393_, 1);
    lean_inc_n(v_toBind_397_, 2);
    v_toPure_398_ = lean_ctor_get(v_toApplicative_396_, 1);
    lean_inc(v_toPure_398_);
    lean_inc(v_inst_394_);
    v___f_399_ = lean_alloc_closure(
        l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_399_, 0, v_c_395_);
    lean_closure_set(v___f_399_, 1, v_toPure_398_);
    lean_closure_set(v___f_399_, 2, v_inst_393_);
    lean_closure_set(v___f_399_, 3, v_inst_394_);
    lean_closure_set(v___f_399_, 4, v_toBind_397_);
    v___x_400_ = lean_apply_4(
        v_toBind_397_,
        lean_box(0),
        lean_box(0),
        v_inst_394_,
        v___f_399_,
    );
    return v___x_400_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr(
    mut v_M_401_: *mut LeanObject,
    mut v_inst_402_: *mut LeanObject,
    mut v_inst_403_: *mut LeanObject,
    mut v_c_404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_405_: *mut LeanObject = core::ptr::null_mut();
    v___x_405_ =
        l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg(v_inst_402_, v_inst_403_, v_c_404_);
    return v___x_405_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0(
    mut v_s_409_: *mut LeanObject,
    mut v_____do__lift_410_: *mut LeanObject,
    mut v_toPure_411_: *mut LeanObject,
    mut v_____do__lift_412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_type_413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
    v_type_413_ = lean_ctor_get(v_s_409_, 1);
    lean_inc_ref(v_type_413_);
    v_u_414_ = lean_ctor_get(v_s_409_, 2);
    lean_inc(v_u_414_);
    lean_dec_ref(v_s_409_);
    v___x_415_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0___closed__1;
    v___x_416_ = lean_box(0);
    v___x_417_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_417_, 0, v_u_414_);
    lean_ctor_set(v___x_417_, 1, v___x_416_);
    v___x_418_ = l_Lean_mkConst(v___x_415_, v___x_417_);
    v___x_419_ = l_Lean_mkApp3(
        v___x_418_,
        v_type_413_,
        v_____do__lift_410_,
        v_____do__lift_412_,
    );
    v___x_420_ = lean_apply_2(v_toPure_411_, lean_box(0), v___x_419_);
    return v___x_420_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__1(
    mut v_s_421_: *mut LeanObject,
    mut v_toPure_422_: *mut LeanObject,
    mut v_inst_423_: *mut LeanObject,
    mut v_inst_424_: *mut LeanObject,
    mut v_rhs_425_: *mut LeanObject,
    mut v_toBind_426_: *mut LeanObject,
    mut v_____do__lift_427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut LeanObject = core::ptr::null_mut();
    v___f_428_ = lean_alloc_closure(
        l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_428_, 0, v_s_421_);
    lean_closure_set(v___f_428_, 1, v_____do__lift_427_);
    lean_closure_set(v___f_428_, 2, v_toPure_422_);
    v___x_429_ = l_Lean_Grind_AC_Seq_denoteExpr___redArg(v_inst_423_, v_inst_424_, v_rhs_425_);
    v___x_430_ = lean_apply_4(
        v_toBind_426_,
        lean_box(0),
        lean_box(0),
        v___x_429_,
        v___f_428_,
    );
    return v___x_430_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__2(
    mut v_c_431_: *mut LeanObject,
    mut v_toPure_432_: *mut LeanObject,
    mut v_inst_433_: *mut LeanObject,
    mut v_inst_434_: *mut LeanObject,
    mut v_toBind_435_: *mut LeanObject,
    mut v_s_436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lhs_437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
    v_lhs_437_ = lean_ctor_get(v_c_431_, 0);
    lean_inc_ref(v_lhs_437_);
    v_rhs_438_ = lean_ctor_get(v_c_431_, 1);
    lean_inc_ref(v_rhs_438_);
    lean_dec_ref(v_c_431_);
    lean_inc(v_toBind_435_);
    lean_inc(v_inst_434_);
    lean_inc_ref(v_inst_433_);
    v___f_439_ = lean_alloc_closure(
        l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__1 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_439_, 0, v_s_436_);
    lean_closure_set(v___f_439_, 1, v_toPure_432_);
    lean_closure_set(v___f_439_, 2, v_inst_433_);
    lean_closure_set(v___f_439_, 3, v_inst_434_);
    lean_closure_set(v___f_439_, 4, v_rhs_438_);
    lean_closure_set(v___f_439_, 5, v_toBind_435_);
    v___x_440_ = l_Lean_Grind_AC_Seq_denoteExpr___redArg(v_inst_433_, v_inst_434_, v_lhs_437_);
    v___x_441_ = lean_apply_4(
        v_toBind_435_,
        lean_box(0),
        lean_box(0),
        v___x_440_,
        v___f_439_,
    );
    return v___x_441_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg(
    mut v_inst_442_: *mut LeanObject,
    mut v_inst_443_: *mut LeanObject,
    mut v_c_444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_445_ = lean_ctor_get(v_inst_442_, 0);
    v_toBind_446_ = lean_ctor_get(v_inst_442_, 1);
    lean_inc_n(v_toBind_446_, 2);
    v_toPure_447_ = lean_ctor_get(v_toApplicative_445_, 1);
    lean_inc(v_toPure_447_);
    lean_inc(v_inst_443_);
    v___f_448_ = lean_alloc_closure(
        l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_448_, 0, v_c_444_);
    lean_closure_set(v___f_448_, 1, v_toPure_447_);
    lean_closure_set(v___f_448_, 2, v_inst_442_);
    lean_closure_set(v___f_448_, 3, v_inst_443_);
    lean_closure_set(v___f_448_, 4, v_toBind_446_);
    v___x_449_ = lean_apply_4(
        v_toBind_446_,
        lean_box(0),
        lean_box(0),
        v_inst_443_,
        v___f_448_,
    );
    return v___x_449_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr(
    mut v_M_450_: *mut LeanObject,
    mut v_inst_451_: *mut LeanObject,
    mut v_inst_452_: *mut LeanObject,
    mut v_c_453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
    v___x_454_ =
        l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg(v_inst_451_, v_inst_452_, v_c_453_);
    return v___x_454_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(builtin);
}
