// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Result
// Imports: Lean.Meta.Sym.Simp.SimpM Lean.Meta.Sym.InferType
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr2;
use crate::r#gen::Lean::Expr::{l_Lean_mkApp6, l_Lean_mkConst};
use crate::r#gen::Lean::Meta::Sym::InferType::{
    initialize_Lean_Meta_Sym_InferType, l_Lean_Meta_Sym_getLevel___redArg,
    l_Lean_Meta_Sym_inferType___redArg, runtime_initialize_Lean_Meta_Sym_InferType,
};
use crate::r#gen::Lean::Meta::Sym::Simp::SimpM::{
    initialize_Lean_Meta_Sym_Simp_SimpM, runtime_initialize_Lean_Meta_Sym_Simp_SimpM,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unbox,
};
pub static l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
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
static mut l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___closed__1_value: LeanStringObject<6> =
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
        m_data: [116, 114, 97, 110, 115, 0],
    };
static mut l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___closed__1_value)
        as *mut LeanObject;
static l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___closed__0_value)
                as *mut LeanObject,
            16122875713692181903 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___closed__1_value)
                as *mut LeanObject,
            17532416664988428445 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___closed__2_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_isRfl(mut v_x_236_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_236_) == 0 {
        let mut v_done_237_: u8 = 0;
        v_done_237_ = lean_ctor_get_uint8(v_x_236_, 0 as u32);
        if v_done_237_ == 0 {
            let mut v___x_238_: u8 = 0;
            v___x_238_ = 1;
            return v___x_238_;
        } else {
            let mut v___x_239_: u8 = 0;
            v___x_239_ = 0;
            return v___x_239_;
        }
    } else {
        let mut v___x_240_: u8 = 0;
        v___x_240_ = 0;
        return v___x_240_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_isRfl___boxed(
    mut v_x_241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_242_: u8 = 0;
    let mut v_r_243_: *mut LeanObject = core::ptr::null_mut();
    v_res_242_ = l_Lean_Meta_Sym_Simp_Result_isRfl(v_x_241_);
    lean_dec_ref(v_x_241_);
    v_r_243_ = lean_box((v_res_242_) as usize);
    return v_r_243_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(
    mut v_e_u2081_249_: *mut LeanObject,
    mut v_e_u2082_250_: *mut LeanObject,
    mut v_h_u2081_251_: *mut LeanObject,
    mut v_e_u2083_252_: *mut LeanObject,
    mut v_h_u2082_253_: *mut LeanObject,
    mut v_a_254_: *mut LeanObject,
    mut v_a_255_: *mut LeanObject,
    mut v_a_256_: *mut LeanObject,
    mut v_a_257_: *mut LeanObject,
    mut v_a_258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_266_: u8 = 0;
    let mut v___x_267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_275_: u8 = 0;
    let mut v_a_276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_279_: u8 = 0;
    let mut v___x_281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_283_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_u2081_249_);
                v___x_260_ = l_Lean_Meta_Sym_inferType___redArg(
                    v_e_u2081_249_,
                    v_a_254_,
                    v_a_255_,
                    v_a_256_,
                    v_a_257_,
                    v_a_258_,
                );
                if lean_obj_tag(v___x_260_) == 0 {
                    v_a_261_ = lean_ctor_get(v___x_260_, 0);
                    lean_inc_n(v_a_261_, 2);
                    lean_dec_ref_known(v___x_260_, 1);
                    v___x_262_ = l_Lean_Meta_Sym_getLevel___redArg(
                        v_a_261_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_,
                    );
                    if lean_obj_tag(v___x_262_) == 0 {
                        v_a_263_ = lean_ctor_get(v___x_262_, 0);
                        v_isSharedCheck_275_ = (!lean_is_exclusive(v___x_262_)) as u8;
                        if v_isSharedCheck_275_ == 0 {
                            v___x_265_ = v___x_262_;
                            v_isShared_266_ = v_isSharedCheck_275_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_263_);
                            lean_dec(v___x_262_);
                            v___x_265_ = lean_box(0);
                            v_isShared_266_ = v_isSharedCheck_275_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_261_);
                        lean_dec_ref(v_h_u2082_253_);
                        lean_dec_ref(v_e_u2083_252_);
                        lean_dec_ref(v_h_u2081_251_);
                        lean_dec_ref(v_e_u2082_250_);
                        lean_dec_ref(v_e_u2081_249_);
                        v_a_276_ = lean_ctor_get(v___x_262_, 0);
                        v_isSharedCheck_283_ = (!lean_is_exclusive(v___x_262_)) as u8;
                        if v_isSharedCheck_283_ == 0 {
                            v___x_278_ = v___x_262_;
                            v_isShared_279_ = v_isSharedCheck_283_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_276_);
                            lean_dec(v___x_262_);
                            v___x_278_ = lean_box(0);
                            v_isShared_279_ = v_isSharedCheck_283_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_h_u2082_253_);
                    lean_dec_ref(v_e_u2083_252_);
                    lean_dec_ref(v_h_u2081_251_);
                    lean_dec_ref(v_e_u2082_250_);
                    lean_dec_ref(v_e_u2081_249_);
                    return v___x_260_;
                }
            }
            1 => {
                v___x_267_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___closed__2;
                v___x_268_ = lean_box(0);
                v___x_269_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_269_, 0, v_a_263_);
                lean_ctor_set(v___x_269_, 1, v___x_268_);
                v___x_270_ = l_Lean_mkConst(v___x_267_, v___x_269_);
                v___x_271_ = l_Lean_mkApp6(
                    v___x_270_,
                    v_a_261_,
                    v_e_u2081_249_,
                    v_e_u2082_250_,
                    v_e_u2083_252_,
                    v_h_u2081_251_,
                    v_h_u2082_253_,
                );
                if v_isShared_266_ == 0 {
                    lean_ctor_set(v___x_265_, 0, v___x_271_);
                    v___x_273_ = v___x_265_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_271_);
                    v___x_273_ = v_reuseFailAlloc_274_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_273_;
            }
            3 => {
                if v_isShared_279_ == 0 {
                    v___x_281_ = v___x_278_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
                    v___x_281_ = v_reuseFailAlloc_282_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_281_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkEqTrans___redArg___boxed(
    mut v_e_u2081_284_: *mut LeanObject,
    mut v_e_u2082_285_: *mut LeanObject,
    mut v_h_u2081_286_: *mut LeanObject,
    mut v_e_u2083_287_: *mut LeanObject,
    mut v_h_u2082_288_: *mut LeanObject,
    mut v_a_289_: *mut LeanObject,
    mut v_a_290_: *mut LeanObject,
    mut v_a_291_: *mut LeanObject,
    mut v_a_292_: *mut LeanObject,
    mut v_a_293_: *mut LeanObject,
    mut v_a_294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_295_: *mut LeanObject = core::ptr::null_mut();
    v_res_295_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(
        v_e_u2081_284_,
        v_e_u2082_285_,
        v_h_u2081_286_,
        v_e_u2083_287_,
        v_h_u2082_288_,
        v_a_289_,
        v_a_290_,
        v_a_291_,
        v_a_292_,
        v_a_293_,
    );
    lean_dec(v_a_293_);
    lean_dec_ref(v_a_292_);
    lean_dec(v_a_291_);
    lean_dec_ref(v_a_290_);
    lean_dec(v_a_289_);
    return v_res_295_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkEqTrans(
    mut v_e_u2081_296_: *mut LeanObject,
    mut v_e_u2082_297_: *mut LeanObject,
    mut v_h_u2081_298_: *mut LeanObject,
    mut v_e_u2083_299_: *mut LeanObject,
    mut v_h_u2082_300_: *mut LeanObject,
    mut v_a_301_: *mut LeanObject,
    mut v_a_302_: *mut LeanObject,
    mut v_a_303_: *mut LeanObject,
    mut v_a_304_: *mut LeanObject,
    mut v_a_305_: *mut LeanObject,
    mut v_a_306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_308_: *mut LeanObject = core::ptr::null_mut();
    v___x_308_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(
        v_e_u2081_296_,
        v_e_u2082_297_,
        v_h_u2081_298_,
        v_e_u2083_299_,
        v_h_u2082_300_,
        v_a_302_,
        v_a_303_,
        v_a_304_,
        v_a_305_,
        v_a_306_,
    );
    return v___x_308_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkEqTrans___boxed(
    mut v_e_u2081_309_: *mut LeanObject,
    mut v_e_u2082_310_: *mut LeanObject,
    mut v_h_u2081_311_: *mut LeanObject,
    mut v_e_u2083_312_: *mut LeanObject,
    mut v_h_u2082_313_: *mut LeanObject,
    mut v_a_314_: *mut LeanObject,
    mut v_a_315_: *mut LeanObject,
    mut v_a_316_: *mut LeanObject,
    mut v_a_317_: *mut LeanObject,
    mut v_a_318_: *mut LeanObject,
    mut v_a_319_: *mut LeanObject,
    mut v_a_320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_321_: *mut LeanObject = core::ptr::null_mut();
    v_res_321_ = l_Lean_Meta_Sym_Simp_mkEqTrans(
        v_e_u2081_309_,
        v_e_u2082_310_,
        v_h_u2081_311_,
        v_e_u2083_312_,
        v_h_u2082_313_,
        v_a_314_,
        v_a_315_,
        v_a_316_,
        v_a_317_,
        v_a_318_,
        v_a_319_,
    );
    lean_dec(v_a_319_);
    lean_dec_ref(v_a_318_);
    lean_dec(v_a_317_);
    lean_dec_ref(v_a_316_);
    lean_dec(v_a_315_);
    lean_dec_ref(v_a_314_);
    return v_res_321_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkEqTransResult___redArg(
    mut v_e_u2081_322_: *mut LeanObject,
    mut v_e_u2082_323_: *mut LeanObject,
    mut v_h_u2081_324_: *mut LeanObject,
    mut v_r_u2082_325_: *mut LeanObject,
    mut v_cd_u2081_326_: u8,
    mut v_a_327_: *mut LeanObject,
    mut v_a_328_: *mut LeanObject,
    mut v_a_329_: *mut LeanObject,
    mut v_a_330_: *mut LeanObject,
    mut v_a_331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_done_333_: u8 = 0;
    let mut v_contextDependent_334_: u8 = 0;
    let mut v___y_336_: u8 = 0;
    let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_x27_339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_done_341_: u8 = 0;
    let mut v_contextDependent_342_: u8 = 0;
    let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_345_: u8 = 0;
    let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_350_: u8 = 0;
    let mut v___y_352_: u8 = 0;
    let mut v___x_354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_359_: u8 = 0;
    let mut v_a_360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_363_: u8 = 0;
    let mut v___x_365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_367_: u8 = 0;
    let mut v_isSharedCheck_368_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_r_u2082_325_) == 0 {
                    lean_dec_ref(v_e_u2081_322_);
                    v_done_333_ = lean_ctor_get_uint8(v_r_u2082_325_, 0 as u32);
                    v_contextDependent_334_ = lean_ctor_get_uint8(v_r_u2082_325_, 1 as u32);
                    lean_dec_ref_known(v_r_u2082_325_, 0);
                    if v_cd_u2081_326_ == 0 {
                        v___y_336_ = v_contextDependent_334_;
                        state = 1;
                        continue;
                    } else {
                        v___y_336_ = v_cd_u2081_326_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_e_x27_339_ = lean_ctor_get(v_r_u2082_325_, 0);
                    v_proof_340_ = lean_ctor_get(v_r_u2082_325_, 1);
                    v_done_341_ = lean_ctor_get_uint8(
                        v_r_u2082_325_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v_contextDependent_342_ = lean_ctor_get_uint8(
                        v_r_u2082_325_,
                        (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    );
                    v_isSharedCheck_368_ = (!lean_is_exclusive(v_r_u2082_325_)) as u8;
                    if v_isSharedCheck_368_ == 0 {
                        v___x_344_ = v_r_u2082_325_;
                        v_isShared_345_ = v_isSharedCheck_368_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_proof_340_);
                        lean_inc(v_e_x27_339_);
                        lean_dec(v_r_u2082_325_);
                        v___x_344_ = lean_box(0);
                        v_isShared_345_ = v_isSharedCheck_368_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_337_ = lean_alloc_ctor(1, 2, (2) as u32);
                lean_ctor_set(v___x_337_, 0, v_e_u2082_323_);
                lean_ctor_set(v___x_337_, 1, v_h_u2081_324_);
                lean_ctor_set_uint8(
                    v___x_337_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v_done_333_,
                );
                lean_ctor_set_uint8(
                    v___x_337_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v___y_336_,
                );
                v___x_338_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_338_, 0, v___x_337_);
                return v___x_338_;
            }
            2 => {
                lean_inc_ref(v_e_x27_339_);
                v___x_346_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(
                    v_e_u2081_322_,
                    v_e_u2082_323_,
                    v_h_u2081_324_,
                    v_e_x27_339_,
                    v_proof_340_,
                    v_a_327_,
                    v_a_328_,
                    v_a_329_,
                    v_a_330_,
                    v_a_331_,
                );
                if lean_obj_tag(v___x_346_) == 0 {
                    v_a_347_ = lean_ctor_get(v___x_346_, 0);
                    v_isSharedCheck_359_ = (!lean_is_exclusive(v___x_346_)) as u8;
                    if v_isSharedCheck_359_ == 0 {
                        v___x_349_ = v___x_346_;
                        v_isShared_350_ = v_isSharedCheck_359_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_347_);
                        lean_dec(v___x_346_);
                        v___x_349_ = lean_box(0);
                        v_isShared_350_ = v_isSharedCheck_359_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_344_);
                    lean_dec_ref(v_e_x27_339_);
                    v_a_360_ = lean_ctor_get(v___x_346_, 0);
                    v_isSharedCheck_367_ = (!lean_is_exclusive(v___x_346_)) as u8;
                    if v_isSharedCheck_367_ == 0 {
                        v___x_362_ = v___x_346_;
                        v_isShared_363_ = v_isSharedCheck_367_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_360_);
                        lean_dec(v___x_346_);
                        v___x_362_ = lean_box(0);
                        v_isShared_363_ = v_isSharedCheck_367_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                if v_cd_u2081_326_ == 0 {
                    v___y_352_ = v_contextDependent_342_;
                    state = 4;
                    continue;
                } else {
                    v___y_352_ = v_cd_u2081_326_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_345_ == 0 {
                    lean_ctor_set(v___x_344_, 1, v_a_347_);
                    v___x_354_ = v___x_344_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 2, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_358_, 0, v_e_x27_339_);
                    lean_ctor_set(v_reuseFailAlloc_358_, 1, v_a_347_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_358_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_done_341_,
                    );
                    v___x_354_ = v_reuseFailAlloc_358_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_ctor_set_uint8(
                    v___x_354_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v___y_352_,
                );
                if v_isShared_350_ == 0 {
                    lean_ctor_set(v___x_349_, 0, v___x_354_);
                    v___x_356_ = v___x_349_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_354_);
                    v___x_356_ = v_reuseFailAlloc_357_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_356_;
            }
            7 => {
                if v_isShared_363_ == 0 {
                    v___x_365_ = v___x_362_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_360_);
                    v___x_365_ = v_reuseFailAlloc_366_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_365_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkEqTransResult___redArg___boxed(
    mut v_e_u2081_369_: *mut LeanObject,
    mut v_e_u2082_370_: *mut LeanObject,
    mut v_h_u2081_371_: *mut LeanObject,
    mut v_r_u2082_372_: *mut LeanObject,
    mut v_cd_u2081_373_: *mut LeanObject,
    mut v_a_374_: *mut LeanObject,
    mut v_a_375_: *mut LeanObject,
    mut v_a_376_: *mut LeanObject,
    mut v_a_377_: *mut LeanObject,
    mut v_a_378_: *mut LeanObject,
    mut v_a_379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cd_u2081_boxed_380_: u8 = 0;
    let mut v_res_381_: *mut LeanObject = core::ptr::null_mut();
    v_cd_u2081_boxed_380_ = (lean_unbox(v_cd_u2081_373_) as u8);
    v_res_381_ = l_Lean_Meta_Sym_Simp_mkEqTransResult___redArg(
        v_e_u2081_369_,
        v_e_u2082_370_,
        v_h_u2081_371_,
        v_r_u2082_372_,
        v_cd_u2081_boxed_380_,
        v_a_374_,
        v_a_375_,
        v_a_376_,
        v_a_377_,
        v_a_378_,
    );
    lean_dec(v_a_378_);
    lean_dec_ref(v_a_377_);
    lean_dec(v_a_376_);
    lean_dec_ref(v_a_375_);
    lean_dec(v_a_374_);
    return v_res_381_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkEqTransResult(
    mut v_e_u2081_382_: *mut LeanObject,
    mut v_e_u2082_383_: *mut LeanObject,
    mut v_h_u2081_384_: *mut LeanObject,
    mut v_r_u2082_385_: *mut LeanObject,
    mut v_cd_u2081_386_: u8,
    mut v_a_387_: *mut LeanObject,
    mut v_a_388_: *mut LeanObject,
    mut v_a_389_: *mut LeanObject,
    mut v_a_390_: *mut LeanObject,
    mut v_a_391_: *mut LeanObject,
    mut v_a_392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_done_394_: u8 = 0;
    let mut v_contextDependent_395_: u8 = 0;
    let mut v___y_397_: u8 = 0;
    let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_x27_400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_done_402_: u8 = 0;
    let mut v_contextDependent_403_: u8 = 0;
    let mut v___x_405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_406_: u8 = 0;
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_411_: u8 = 0;
    let mut v___y_413_: u8 = 0;
    let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_420_: u8 = 0;
    let mut v_a_421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_424_: u8 = 0;
    let mut v___x_426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_428_: u8 = 0;
    let mut v_isSharedCheck_429_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_r_u2082_385_) == 0 {
                    lean_dec_ref(v_e_u2081_382_);
                    v_done_394_ = lean_ctor_get_uint8(v_r_u2082_385_, 0 as u32);
                    v_contextDependent_395_ = lean_ctor_get_uint8(v_r_u2082_385_, 1 as u32);
                    lean_dec_ref_known(v_r_u2082_385_, 0);
                    if v_cd_u2081_386_ == 0 {
                        v___y_397_ = v_contextDependent_395_;
                        state = 1;
                        continue;
                    } else {
                        v___y_397_ = v_cd_u2081_386_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_e_x27_400_ = lean_ctor_get(v_r_u2082_385_, 0);
                    v_proof_401_ = lean_ctor_get(v_r_u2082_385_, 1);
                    v_done_402_ = lean_ctor_get_uint8(
                        v_r_u2082_385_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v_contextDependent_403_ = lean_ctor_get_uint8(
                        v_r_u2082_385_,
                        (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    );
                    v_isSharedCheck_429_ = (!lean_is_exclusive(v_r_u2082_385_)) as u8;
                    if v_isSharedCheck_429_ == 0 {
                        v___x_405_ = v_r_u2082_385_;
                        v_isShared_406_ = v_isSharedCheck_429_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_proof_401_);
                        lean_inc(v_e_x27_400_);
                        lean_dec(v_r_u2082_385_);
                        v___x_405_ = lean_box(0);
                        v_isShared_406_ = v_isSharedCheck_429_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_398_ = lean_alloc_ctor(1, 2, (2) as u32);
                lean_ctor_set(v___x_398_, 0, v_e_u2082_383_);
                lean_ctor_set(v___x_398_, 1, v_h_u2081_384_);
                lean_ctor_set_uint8(
                    v___x_398_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v_done_394_,
                );
                lean_ctor_set_uint8(
                    v___x_398_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v___y_397_,
                );
                v___x_399_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_399_, 0, v___x_398_);
                return v___x_399_;
            }
            2 => {
                lean_inc_ref(v_e_x27_400_);
                v___x_407_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(
                    v_e_u2081_382_,
                    v_e_u2082_383_,
                    v_h_u2081_384_,
                    v_e_x27_400_,
                    v_proof_401_,
                    v_a_388_,
                    v_a_389_,
                    v_a_390_,
                    v_a_391_,
                    v_a_392_,
                );
                if lean_obj_tag(v___x_407_) == 0 {
                    v_a_408_ = lean_ctor_get(v___x_407_, 0);
                    v_isSharedCheck_420_ = (!lean_is_exclusive(v___x_407_)) as u8;
                    if v_isSharedCheck_420_ == 0 {
                        v___x_410_ = v___x_407_;
                        v_isShared_411_ = v_isSharedCheck_420_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_408_);
                        lean_dec(v___x_407_);
                        v___x_410_ = lean_box(0);
                        v_isShared_411_ = v_isSharedCheck_420_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_405_);
                    lean_dec_ref(v_e_x27_400_);
                    v_a_421_ = lean_ctor_get(v___x_407_, 0);
                    v_isSharedCheck_428_ = (!lean_is_exclusive(v___x_407_)) as u8;
                    if v_isSharedCheck_428_ == 0 {
                        v___x_423_ = v___x_407_;
                        v_isShared_424_ = v_isSharedCheck_428_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_421_);
                        lean_dec(v___x_407_);
                        v___x_423_ = lean_box(0);
                        v_isShared_424_ = v_isSharedCheck_428_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                if v_cd_u2081_386_ == 0 {
                    v___y_413_ = v_contextDependent_403_;
                    state = 4;
                    continue;
                } else {
                    v___y_413_ = v_cd_u2081_386_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_406_ == 0 {
                    lean_ctor_set(v___x_405_, 1, v_a_408_);
                    v___x_415_ = v___x_405_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 2, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_419_, 0, v_e_x27_400_);
                    lean_ctor_set(v_reuseFailAlloc_419_, 1, v_a_408_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_419_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_done_402_,
                    );
                    v___x_415_ = v_reuseFailAlloc_419_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_ctor_set_uint8(
                    v___x_415_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v___y_413_,
                );
                if v_isShared_411_ == 0 {
                    lean_ctor_set(v___x_410_, 0, v___x_415_);
                    v___x_417_ = v___x_410_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
                    v___x_417_ = v_reuseFailAlloc_418_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_417_;
            }
            7 => {
                if v_isShared_424_ == 0 {
                    v___x_426_ = v___x_423_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_421_);
                    v___x_426_ = v_reuseFailAlloc_427_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_426_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_mkEqTransResult___boxed(
    mut v_e_u2081_430_: *mut LeanObject,
    mut v_e_u2082_431_: *mut LeanObject,
    mut v_h_u2081_432_: *mut LeanObject,
    mut v_r_u2082_433_: *mut LeanObject,
    mut v_cd_u2081_434_: *mut LeanObject,
    mut v_a_435_: *mut LeanObject,
    mut v_a_436_: *mut LeanObject,
    mut v_a_437_: *mut LeanObject,
    mut v_a_438_: *mut LeanObject,
    mut v_a_439_: *mut LeanObject,
    mut v_a_440_: *mut LeanObject,
    mut v_a_441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cd_u2081_boxed_442_: u8 = 0;
    let mut v_res_443_: *mut LeanObject = core::ptr::null_mut();
    v_cd_u2081_boxed_442_ = (lean_unbox(v_cd_u2081_434_) as u8);
    v_res_443_ = l_Lean_Meta_Sym_Simp_mkEqTransResult(
        v_e_u2081_430_,
        v_e_u2082_431_,
        v_h_u2081_432_,
        v_r_u2082_433_,
        v_cd_u2081_boxed_442_,
        v_a_435_,
        v_a_436_,
        v_a_437_,
        v_a_438_,
        v_a_439_,
        v_a_440_,
    );
    lean_dec(v_a_440_);
    lean_dec_ref(v_a_439_);
    lean_dec(v_a_438_);
    lean_dec_ref(v_a_437_);
    lean_dec(v_a_436_);
    lean_dec_ref(v_a_435_);
    return v_res_443_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_markAsDone(
    mut v_x_444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_contextDependent_445_: u8 = 0;
    let mut v___x_447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_448_: u8 = 0;
    let mut v___x_449_: u8 = 0;
    let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_453_: u8 = 0;
    let mut v_e_x27_454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_456_: u8 = 0;
    let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_459_: u8 = 0;
    let mut v___x_460_: u8 = 0;
    let mut v___x_462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_464_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_444_) == 0 {
                    v_contextDependent_445_ = lean_ctor_get_uint8(v_x_444_, 1 as u32);
                    v_isSharedCheck_453_ = (!lean_is_exclusive(v_x_444_)) as u8;
                    if v_isSharedCheck_453_ == 0 {
                        v___x_447_ = v_x_444_;
                        v_isShared_448_ = v_isSharedCheck_453_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_x_444_);
                        v___x_447_ = lean_box(0);
                        v_isShared_448_ = v_isSharedCheck_453_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_e_x27_454_ = lean_ctor_get(v_x_444_, 0);
                    v_proof_455_ = lean_ctor_get(v_x_444_, 1);
                    v_contextDependent_456_ = lean_ctor_get_uint8(
                        v_x_444_,
                        (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    );
                    v_isSharedCheck_464_ = (!lean_is_exclusive(v_x_444_)) as u8;
                    if v_isSharedCheck_464_ == 0 {
                        v___x_458_ = v_x_444_;
                        v_isShared_459_ = v_isSharedCheck_464_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_proof_455_);
                        lean_inc(v_e_x27_454_);
                        lean_dec(v_x_444_);
                        v___x_458_ = lean_box(0);
                        v_isShared_459_ = v_isSharedCheck_464_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_449_ = 1;
                if v_isShared_448_ == 0 {
                    v___x_451_ = v___x_447_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 0, (2) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_452_, 1 as u32, v_contextDependent_445_);
                    v___x_451_ = v_reuseFailAlloc_452_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(v___x_451_, 0 as u32, v___x_449_);
                return v___x_451_;
            }
            3 => {
                v___x_460_ = 1;
                if v_isShared_459_ == 0 {
                    v___x_462_ = v___x_458_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 2, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_463_, 0, v_e_x27_454_);
                    lean_ctor_set(v_reuseFailAlloc_463_, 1, v_proof_455_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_463_,
                        (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                        v_contextDependent_456_,
                    );
                    v___x_462_ = v_reuseFailAlloc_463_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_ctor_set_uint8(
                    v___x_462_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_460_,
                );
                return v___x_462_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_getResultExpr(
    mut v_x_465_: *mut LeanObject,
    mut v_x_466_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_466_) == 0 {
        lean_inc_ref(v_x_465_);
        return v_x_465_;
    } else {
        let mut v_e_x27_467_: *mut LeanObject = core::ptr::null_mut();
        v_e_x27_467_ = lean_ctor_get(v_x_466_, 0);
        lean_inc_ref(v_e_x27_467_);
        return v_e_x27_467_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Result_getResultExpr___boxed(
    mut v_x_468_: *mut LeanObject,
    mut v_x_469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_470_: *mut LeanObject = core::ptr::null_mut();
    v_res_470_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v_x_468_, v_x_469_);
    lean_dec_ref(v_x_469_);
    lean_dec_ref(v_x_468_);
    return v_res_470_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Simp_Result(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Simp_Result(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Simp_Result(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_InferType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Result(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Simp_Result(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Simp_Result(builtin);
}
