// Lean compiler output
// Module: Init.Data.Sum.Basic
// Imports: Init.PropLemmas
use crate::r#gen::Init::PropLemmas::{
    initialize_Init_PropLemmas, runtime_initialize_Init_PropLemmas,
};
pub static l_Sum_swap___redArg___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Sum_swap___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Sum_swap___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Sum_swap___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Sum_swap___redArg___closed__1_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Sum_swap___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Sum_swap___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Sum_swap___redArg___closed__1_value) as *mut leanh::LeanObject;
pub unsafe fn l_Sum_instBEq_beq___redArg(
    mut v_inst_262_: *mut leanh::LeanObject,
    mut v_inst_263_: *mut leanh::LeanObject,
    mut v_x_264_: *mut leanh::LeanObject,
    mut v_x_265_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_264_) == 0 {
        leanh::lean_dec_ref(v_inst_263_);
        if leanh::lean_obj_tag(v_x_265_) == 0 {
            let mut v_val_266_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_267_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_268_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_269_: u8 = 0;
            v_val_266_ = leanh::lean_ctor_get(v_x_264_, 0);
            leanh::lean_inc(v_val_266_);
            leanh::lean_dec_ref_known(v_x_264_, 1);
            v_val_267_ = leanh::lean_ctor_get(v_x_265_, 0);
            leanh::lean_inc(v_val_267_);
            leanh::lean_dec_ref_known(v_x_265_, 1);
            v___x_268_ = leanh::lean_apply_2(v_inst_262_, v_val_266_, v_val_267_);
            v___x_269_ = (leanh::lean_unbox(v___x_268_) as u8);
            return v___x_269_;
        } else {
            let mut v___x_270_: u8 = 0;
            leanh::lean_dec_ref_known(v_x_264_, 1);
            leanh::lean_dec_ref(v_x_265_);
            leanh::lean_dec_ref(v_inst_262_);
            v___x_270_ = 0;
            return v___x_270_;
        }
    } else {
        leanh::lean_dec_ref(v_inst_262_);
        if leanh::lean_obj_tag(v_x_265_) == 1 {
            let mut v_val_271_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_272_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_273_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_274_: u8 = 0;
            v_val_271_ = leanh::lean_ctor_get(v_x_264_, 0);
            leanh::lean_inc(v_val_271_);
            leanh::lean_dec_ref_known(v_x_264_, 1);
            v_val_272_ = leanh::lean_ctor_get(v_x_265_, 0);
            leanh::lean_inc(v_val_272_);
            leanh::lean_dec_ref_known(v_x_265_, 1);
            v___x_273_ = leanh::lean_apply_2(v_inst_263_, v_val_271_, v_val_272_);
            v___x_274_ = (leanh::lean_unbox(v___x_273_) as u8);
            return v___x_274_;
        } else {
            let mut v___x_275_: u8 = 0;
            leanh::lean_dec_ref_known(v_x_264_, 1);
            leanh::lean_dec_ref(v_x_265_);
            leanh::lean_dec_ref(v_inst_263_);
            v___x_275_ = 0;
            return v___x_275_;
        }
    }
}
pub unsafe fn l_Sum_instBEq_beq___redArg___boxed(
    mut v_inst_276_: *mut leanh::LeanObject,
    mut v_inst_277_: *mut leanh::LeanObject,
    mut v_x_278_: *mut leanh::LeanObject,
    mut v_x_279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_280_: u8 = 0;
    let mut v_r_281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_280_ = l_Sum_instBEq_beq___redArg(v_inst_276_, v_inst_277_, v_x_278_, v_x_279_);
    v_r_281_ = leanh::lean_box((v_res_280_) as usize);
    return v_r_281_;
}
pub unsafe fn l_Sum_instBEq_beq(
    mut v_00_u03b1_282_: *mut leanh::LeanObject,
    mut v_00_u03b2_283_: *mut leanh::LeanObject,
    mut v_inst_284_: *mut leanh::LeanObject,
    mut v_inst_285_: *mut leanh::LeanObject,
    mut v_x_286_: *mut leanh::LeanObject,
    mut v_x_287_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_288_: u8 = 0;
    v___x_288_ = l_Sum_instBEq_beq___redArg(v_inst_284_, v_inst_285_, v_x_286_, v_x_287_);
    return v___x_288_;
}
pub unsafe fn l_Sum_instBEq_beq___boxed(
    mut v_00_u03b1_289_: *mut leanh::LeanObject,
    mut v_00_u03b2_290_: *mut leanh::LeanObject,
    mut v_inst_291_: *mut leanh::LeanObject,
    mut v_inst_292_: *mut leanh::LeanObject,
    mut v_x_293_: *mut leanh::LeanObject,
    mut v_x_294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_295_: u8 = 0;
    let mut v_r_296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_295_ = l_Sum_instBEq_beq(
        v_00_u03b1_289_,
        v_00_u03b2_290_,
        v_inst_291_,
        v_inst_292_,
        v_x_293_,
        v_x_294_,
    );
    v_r_296_ = leanh::lean_box((v_res_295_) as usize);
    return v_r_296_;
}
pub unsafe fn l_Sum_instBEq___redArg(
    mut v_inst_297_: *mut leanh::LeanObject,
    mut v_inst_298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_299_ =
        leanh::lean_alloc_closure(l_Sum_instBEq_beq___boxed as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_299_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_299_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_299_, 2, v_inst_297_);
    leanh::lean_closure_set(v___x_299_, 3, v_inst_298_);
    return v___x_299_;
}
pub unsafe fn l_Sum_instBEq(
    mut v_00_u03b1_300_: *mut leanh::LeanObject,
    mut v_00_u03b2_301_: *mut leanh::LeanObject,
    mut v_inst_302_: *mut leanh::LeanObject,
    mut v_inst_303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_304_ =
        leanh::lean_alloc_closure(l_Sum_instBEq_beq___boxed as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_304_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_304_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_304_, 2, v_inst_302_);
    leanh::lean_closure_set(v___x_304_, 3, v_inst_303_);
    return v___x_304_;
}
pub unsafe fn l_Sum_isLeft___redArg(mut v_x_305_: *mut leanh::LeanObject) -> u8 {
    if leanh::lean_obj_tag(v_x_305_) == 0 {
        let mut v___x_306_: u8 = 0;
        v___x_306_ = 1;
        return v___x_306_;
    } else {
        let mut v___x_307_: u8 = 0;
        v___x_307_ = 0;
        return v___x_307_;
    }
}
pub unsafe fn l_Sum_isLeft___redArg___boxed(
    mut v_x_308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_309_: u8 = 0;
    let mut v_r_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_309_ = l_Sum_isLeft___redArg(v_x_308_);
    leanh::lean_dec_ref(v_x_308_);
    v_r_310_ = leanh::lean_box((v_res_309_) as usize);
    return v_r_310_;
}
pub unsafe fn l_Sum_isLeft(
    mut v_00_u03b1_311_: *mut leanh::LeanObject,
    mut v_00_u03b2_312_: *mut leanh::LeanObject,
    mut v_x_313_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_314_: u8 = 0;
    v___x_314_ = l_Sum_isLeft___redArg(v_x_313_);
    return v___x_314_;
}
pub unsafe fn l_Sum_isLeft___boxed(
    mut v_00_u03b1_315_: *mut leanh::LeanObject,
    mut v_00_u03b2_316_: *mut leanh::LeanObject,
    mut v_x_317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_318_: u8 = 0;
    let mut v_r_319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_318_ = l_Sum_isLeft(v_00_u03b1_315_, v_00_u03b2_316_, v_x_317_);
    leanh::lean_dec_ref(v_x_317_);
    v_r_319_ = leanh::lean_box((v_res_318_) as usize);
    return v_r_319_;
}
pub unsafe fn l_Sum_isRight___redArg(mut v_x_320_: *mut leanh::LeanObject) -> u8 {
    if leanh::lean_obj_tag(v_x_320_) == 0 {
        let mut v___x_321_: u8 = 0;
        v___x_321_ = 0;
        return v___x_321_;
    } else {
        let mut v___x_322_: u8 = 0;
        v___x_322_ = 1;
        return v___x_322_;
    }
}
pub unsafe fn l_Sum_isRight___redArg___boxed(
    mut v_x_323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_324_: u8 = 0;
    let mut v_r_325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_324_ = l_Sum_isRight___redArg(v_x_323_);
    leanh::lean_dec_ref(v_x_323_);
    v_r_325_ = leanh::lean_box((v_res_324_) as usize);
    return v_r_325_;
}
pub unsafe fn l_Sum_isRight(
    mut v_00_u03b1_326_: *mut leanh::LeanObject,
    mut v_00_u03b2_327_: *mut leanh::LeanObject,
    mut v_x_328_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_329_: u8 = 0;
    v___x_329_ = l_Sum_isRight___redArg(v_x_328_);
    return v___x_329_;
}
pub unsafe fn l_Sum_isRight___boxed(
    mut v_00_u03b1_330_: *mut leanh::LeanObject,
    mut v_00_u03b2_331_: *mut leanh::LeanObject,
    mut v_x_332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_333_: u8 = 0;
    let mut v_r_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_333_ = l_Sum_isRight(v_00_u03b1_330_, v_00_u03b2_331_, v_x_332_);
    leanh::lean_dec_ref(v_x_332_);
    v_r_334_ = leanh::lean_box((v_res_333_) as usize);
    return v_r_334_;
}
pub unsafe fn l_Sum_getLeft___redArg(
    mut v_x_335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_336_ = leanh::lean_ctor_get(v_x_335_, 0);
    leanh::lean_inc(v_val_336_);
    return v_val_336_;
}
pub unsafe fn l_Sum_getLeft___redArg___boxed(
    mut v_x_337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_338_ = l_Sum_getLeft___redArg(v_x_337_);
    leanh::lean_dec_ref(v_x_337_);
    return v_res_338_;
}
pub unsafe fn l_Sum_getLeft(
    mut v_00_u03b1_339_: *mut leanh::LeanObject,
    mut v_00_u03b2_340_: *mut leanh::LeanObject,
    mut v_x_341_: *mut leanh::LeanObject,
    mut v_x_342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_343_ = leanh::lean_ctor_get(v_x_341_, 0);
    leanh::lean_inc(v_val_343_);
    return v_val_343_;
}
pub unsafe fn l_Sum_getLeft___boxed(
    mut v_00_u03b1_344_: *mut leanh::LeanObject,
    mut v_00_u03b2_345_: *mut leanh::LeanObject,
    mut v_x_346_: *mut leanh::LeanObject,
    mut v_x_347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_348_ = l_Sum_getLeft(v_00_u03b1_344_, v_00_u03b2_345_, v_x_346_, v_x_347_);
    leanh::lean_dec_ref(v_x_346_);
    return v_res_348_;
}
pub unsafe fn l_Sum_getRight___redArg(
    mut v_x_349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_350_ = leanh::lean_ctor_get(v_x_349_, 0);
    leanh::lean_inc(v_val_350_);
    return v_val_350_;
}
pub unsafe fn l_Sum_getRight___redArg___boxed(
    mut v_x_351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_352_ = l_Sum_getRight___redArg(v_x_351_);
    leanh::lean_dec_ref(v_x_351_);
    return v_res_352_;
}
pub unsafe fn l_Sum_getRight(
    mut v_00_u03b1_353_: *mut leanh::LeanObject,
    mut v_00_u03b2_354_: *mut leanh::LeanObject,
    mut v_x_355_: *mut leanh::LeanObject,
    mut v_x_356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_357_ = leanh::lean_ctor_get(v_x_355_, 0);
    leanh::lean_inc(v_val_357_);
    return v_val_357_;
}
pub unsafe fn l_Sum_getRight___boxed(
    mut v_00_u03b1_358_: *mut leanh::LeanObject,
    mut v_00_u03b2_359_: *mut leanh::LeanObject,
    mut v_x_360_: *mut leanh::LeanObject,
    mut v_x_361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_362_ = l_Sum_getRight(v_00_u03b1_358_, v_00_u03b2_359_, v_x_360_, v_x_361_);
    leanh::lean_dec_ref(v_x_360_);
    return v_res_362_;
}
pub unsafe fn l_Sum_getLeft_x3f___redArg(
    mut v_x_363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_367_: u8 = 0;
    let mut v___x_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_371_: u8 = 0;
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_363_) == 0 {
                    v_val_364_ = leanh::lean_ctor_get(v_x_363_, 0);
                    v_isSharedCheck_371_ = (!leanh::lean_is_exclusive(v_x_363_)) as u8;
                    if v_isSharedCheck_371_ == 0 {
                        v___x_366_ = v_x_363_;
                        v_isShared_367_ = v_isSharedCheck_371_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_364_);
                        leanh::lean_dec(v_x_363_);
                        v___x_366_ = leanh::lean_box(0);
                        v_isShared_367_ = v_isSharedCheck_371_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_x_363_, 1);
                    v___x_372_ = leanh::lean_box(0);
                    return v___x_372_;
                }
            }
            1 => {
                if v_isShared_367_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_366_, 1);
                    v___x_369_ = v___x_366_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_370_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_370_, 0, v_val_364_);
                    v___x_369_ = v_reuseFailAlloc_370_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_369_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Sum_getLeft_x3f(
    mut v_00_u03b1_373_: *mut leanh::LeanObject,
    mut v_00_u03b2_374_: *mut leanh::LeanObject,
    mut v_x_375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_376_ = l_Sum_getLeft_x3f___redArg(v_x_375_);
    return v___x_376_;
}
pub unsafe fn l_Sum_getRight_x3f___redArg(
    mut v_x_377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_382_: u8 = 0;
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_386_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_377_) == 0 {
                    leanh::lean_dec_ref_known(v_x_377_, 1);
                    v___x_378_ = leanh::lean_box(0);
                    return v___x_378_;
                } else {
                    v_val_379_ = leanh::lean_ctor_get(v_x_377_, 0);
                    v_isSharedCheck_386_ = (!leanh::lean_is_exclusive(v_x_377_)) as u8;
                    if v_isSharedCheck_386_ == 0 {
                        v___x_381_ = v_x_377_;
                        v_isShared_382_ = v_isSharedCheck_386_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_379_);
                        leanh::lean_dec(v_x_377_);
                        v___x_381_ = leanh::lean_box(0);
                        v_isShared_382_ = v_isSharedCheck_386_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_382_ == 0 {
                    v___x_384_ = v___x_381_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_385_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_385_, 0, v_val_379_);
                    v___x_384_ = v_reuseFailAlloc_385_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_384_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Sum_getRight_x3f(
    mut v_00_u03b1_387_: *mut leanh::LeanObject,
    mut v_00_u03b2_388_: *mut leanh::LeanObject,
    mut v_x_389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_390_ = l_Sum_getRight_x3f___redArg(v_x_389_);
    return v___x_390_;
}
pub unsafe fn l_Sum_elim___redArg(
    mut v_f_391_: *mut leanh::LeanObject,
    mut v_g_392_: *mut leanh::LeanObject,
    mut v_x_393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_393_) == 0 {
        let mut v_a_394_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_g_392_);
        v_a_394_ = leanh::lean_ctor_get(v_x_393_, 0);
        leanh::lean_inc(v_a_394_);
        leanh::lean_dec_ref_known(v_x_393_, 1);
        v___x_395_ = leanh::lean_apply_1(v_f_391_, v_a_394_);
        return v___x_395_;
    } else {
        let mut v_a_396_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_391_);
        v_a_396_ = leanh::lean_ctor_get(v_x_393_, 0);
        leanh::lean_inc(v_a_396_);
        leanh::lean_dec_ref_known(v_x_393_, 1);
        v___x_397_ = leanh::lean_apply_1(v_g_392_, v_a_396_);
        return v___x_397_;
    }
}
pub unsafe fn l_Sum_elim(
    mut v_00_u03b1_398_: *mut leanh::LeanObject,
    mut v_00_u03b2_399_: *mut leanh::LeanObject,
    mut v_00_u03b3_400_: *mut leanh::LeanObject,
    mut v_f_401_: *mut leanh::LeanObject,
    mut v_g_402_: *mut leanh::LeanObject,
    mut v_x_403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_404_ = l_Sum_elim___redArg(v_f_401_, v_g_402_, v_x_403_);
    return v___x_404_;
}
pub unsafe fn l_Sum_map___redArg___lam__0(
    mut v_f_405_: *mut leanh::LeanObject,
    mut v___y_406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_407_ = leanh::lean_apply_1(v_f_405_, v___y_406_);
    v___x_408_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_408_, 0, v___x_407_);
    return v___x_408_;
}
pub unsafe fn l_Sum_map___redArg___lam__1(
    mut v_g_409_: *mut leanh::LeanObject,
    mut v___y_410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_411_ = leanh::lean_apply_1(v_g_409_, v___y_410_);
    v___x_412_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_412_, 0, v___x_411_);
    return v___x_412_;
}
pub unsafe fn l_Sum_map___redArg(
    mut v_f_413_: *mut leanh::LeanObject,
    mut v_g_414_: *mut leanh::LeanObject,
    mut v_a_415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_416_ = leanh::lean_alloc_closure(
        l_Sum_map___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_416_, 0, v_f_413_);
    v___f_417_ = leanh::lean_alloc_closure(
        l_Sum_map___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_417_, 0, v_g_414_);
    v___x_418_ = l_Sum_elim___redArg(v___f_416_, v___f_417_, v_a_415_);
    return v___x_418_;
}
pub unsafe fn l_Sum_map(
    mut v_00_u03b1_419_: *mut leanh::LeanObject,
    mut v_00_u03b1_x27_420_: *mut leanh::LeanObject,
    mut v_00_u03b2_421_: *mut leanh::LeanObject,
    mut v_00_u03b2_x27_422_: *mut leanh::LeanObject,
    mut v_f_423_: *mut leanh::LeanObject,
    mut v_g_424_: *mut leanh::LeanObject,
    mut v_a_425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_426_ = l_Sum_map___redArg(v_f_423_, v_g_424_, v_a_425_);
    return v___x_426_;
}
pub unsafe fn l_Sum_swap___redArg___lam__0(
    mut v_val_427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_428_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_428_, 0, v_val_427_);
    return v___x_428_;
}
pub unsafe fn l_Sum_swap___redArg___lam__1(
    mut v_val_429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_430_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_430_, 0, v_val_429_);
    return v___x_430_;
}
pub unsafe fn l_Sum_swap___redArg(
    mut v_a_433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_434_ = l_Sum_swap___redArg___closed__0;
    v___f_435_ = l_Sum_swap___redArg___closed__1;
    v___x_436_ = l_Sum_elim___redArg(v___f_434_, v___f_435_, v_a_433_);
    return v___x_436_;
}
pub unsafe fn l_Sum_swap(
    mut v_00_u03b1_437_: *mut leanh::LeanObject,
    mut v_00_u03b2_438_: *mut leanh::LeanObject,
    mut v_a_439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_440_ = l_Sum_swap___redArg(v_a_439_);
    return v___x_440_;
}
pub unsafe fn l_Sum_instDecidableLiftRel___redArg(
    mut v_inst_441_: *mut leanh::LeanObject,
    mut v_inst_442_: *mut leanh::LeanObject,
    mut v_x_443_: *mut leanh::LeanObject,
    mut v_x_444_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_443_) == 0 {
        leanh::lean_dec_ref(v_inst_442_);
        if leanh::lean_obj_tag(v_x_444_) == 0 {
            let mut v_val_445_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_446_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_447_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_448_: u8 = 0;
            v_val_445_ = leanh::lean_ctor_get(v_x_443_, 0);
            leanh::lean_inc(v_val_445_);
            leanh::lean_dec_ref_known(v_x_443_, 1);
            v_val_446_ = leanh::lean_ctor_get(v_x_444_, 0);
            leanh::lean_inc(v_val_446_);
            leanh::lean_dec_ref_known(v_x_444_, 1);
            v___x_447_ = leanh::lean_apply_2(v_inst_441_, v_val_445_, v_val_446_);
            v___x_448_ = (leanh::lean_unbox(v___x_447_) as u8);
            return v___x_448_;
        } else {
            let mut v___x_449_: u8 = 0;
            leanh::lean_dec_ref_known(v_x_444_, 1);
            leanh::lean_dec_ref_known(v_x_443_, 1);
            leanh::lean_dec_ref(v_inst_441_);
            v___x_449_ = 0;
            return v___x_449_;
        }
    } else {
        leanh::lean_dec_ref(v_inst_441_);
        if leanh::lean_obj_tag(v_x_444_) == 0 {
            let mut v___x_450_: u8 = 0;
            leanh::lean_dec_ref_known(v_x_444_, 1);
            leanh::lean_dec_ref_known(v_x_443_, 1);
            leanh::lean_dec_ref(v_inst_442_);
            v___x_450_ = 0;
            return v___x_450_;
        } else {
            let mut v_val_451_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_452_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_453_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_454_: u8 = 0;
            v_val_451_ = leanh::lean_ctor_get(v_x_443_, 0);
            leanh::lean_inc(v_val_451_);
            leanh::lean_dec_ref_known(v_x_443_, 1);
            v_val_452_ = leanh::lean_ctor_get(v_x_444_, 0);
            leanh::lean_inc(v_val_452_);
            leanh::lean_dec_ref_known(v_x_444_, 1);
            v___x_453_ = leanh::lean_apply_2(v_inst_442_, v_val_451_, v_val_452_);
            v___x_454_ = (leanh::lean_unbox(v___x_453_) as u8);
            return v___x_454_;
        }
    }
}
pub unsafe fn l_Sum_instDecidableLiftRel___redArg___boxed(
    mut v_inst_455_: *mut leanh::LeanObject,
    mut v_inst_456_: *mut leanh::LeanObject,
    mut v_x_457_: *mut leanh::LeanObject,
    mut v_x_458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_459_: u8 = 0;
    let mut v_r_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_459_ = l_Sum_instDecidableLiftRel___redArg(v_inst_455_, v_inst_456_, v_x_457_, v_x_458_);
    v_r_460_ = leanh::lean_box((v_res_459_) as usize);
    return v_r_460_;
}
pub unsafe fn l_Sum_instDecidableLiftRel(
    mut v_00_u03b1_461_: *mut leanh::LeanObject,
    mut v_00_u03b3_462_: *mut leanh::LeanObject,
    mut v_00_u03b2_463_: *mut leanh::LeanObject,
    mut v_00_u03b4_464_: *mut leanh::LeanObject,
    mut v_r_465_: *mut leanh::LeanObject,
    mut v_s_466_: *mut leanh::LeanObject,
    mut v_inst_467_: *mut leanh::LeanObject,
    mut v_inst_468_: *mut leanh::LeanObject,
    mut v_x_469_: *mut leanh::LeanObject,
    mut v_x_470_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_471_: u8 = 0;
    v___x_471_ = l_Sum_instDecidableLiftRel___redArg(v_inst_467_, v_inst_468_, v_x_469_, v_x_470_);
    return v___x_471_;
}
pub unsafe fn l_Sum_instDecidableLiftRel___boxed(
    mut v_00_u03b1_472_: *mut leanh::LeanObject,
    mut v_00_u03b3_473_: *mut leanh::LeanObject,
    mut v_00_u03b2_474_: *mut leanh::LeanObject,
    mut v_00_u03b4_475_: *mut leanh::LeanObject,
    mut v_r_476_: *mut leanh::LeanObject,
    mut v_s_477_: *mut leanh::LeanObject,
    mut v_inst_478_: *mut leanh::LeanObject,
    mut v_inst_479_: *mut leanh::LeanObject,
    mut v_x_480_: *mut leanh::LeanObject,
    mut v_x_481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_482_: u8 = 0;
    let mut v_r_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_482_ = l_Sum_instDecidableLiftRel(
        v_00_u03b1_472_,
        v_00_u03b3_473_,
        v_00_u03b2_474_,
        v_00_u03b4_475_,
        v_r_476_,
        v_s_477_,
        v_inst_478_,
        v_inst_479_,
        v_x_480_,
        v_x_481_,
    );
    v_r_483_ = leanh::lean_box((v_res_482_) as usize);
    return v_r_483_;
}
pub unsafe fn l_Sum_instDecidableRelSumLex___redArg(
    mut v_inst_484_: *mut leanh::LeanObject,
    mut v_inst_485_: *mut leanh::LeanObject,
    mut v_x_486_: *mut leanh::LeanObject,
    mut v_x_487_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_486_) == 0 {
        leanh::lean_dec_ref(v_inst_485_);
        if leanh::lean_obj_tag(v_x_487_) == 0 {
            let mut v_val_488_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_489_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_490_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_491_: u8 = 0;
            v_val_488_ = leanh::lean_ctor_get(v_x_486_, 0);
            leanh::lean_inc(v_val_488_);
            leanh::lean_dec_ref_known(v_x_486_, 1);
            v_val_489_ = leanh::lean_ctor_get(v_x_487_, 0);
            leanh::lean_inc(v_val_489_);
            leanh::lean_dec_ref_known(v_x_487_, 1);
            v___x_490_ = leanh::lean_apply_2(v_inst_484_, v_val_488_, v_val_489_);
            v___x_491_ = (leanh::lean_unbox(v___x_490_) as u8);
            return v___x_491_;
        } else {
            let mut v___x_492_: u8 = 0;
            leanh::lean_dec_ref_known(v_x_487_, 1);
            leanh::lean_dec_ref_known(v_x_486_, 1);
            leanh::lean_dec_ref(v_inst_484_);
            v___x_492_ = 1;
            return v___x_492_;
        }
    } else {
        leanh::lean_dec_ref(v_inst_484_);
        if leanh::lean_obj_tag(v_x_487_) == 0 {
            let mut v___x_493_: u8 = 0;
            leanh::lean_dec_ref_known(v_x_487_, 1);
            leanh::lean_dec_ref_known(v_x_486_, 1);
            leanh::lean_dec_ref(v_inst_485_);
            v___x_493_ = 0;
            return v___x_493_;
        } else {
            let mut v_val_494_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_495_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_496_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_497_: u8 = 0;
            v_val_494_ = leanh::lean_ctor_get(v_x_486_, 0);
            leanh::lean_inc(v_val_494_);
            leanh::lean_dec_ref_known(v_x_486_, 1);
            v_val_495_ = leanh::lean_ctor_get(v_x_487_, 0);
            leanh::lean_inc(v_val_495_);
            leanh::lean_dec_ref_known(v_x_487_, 1);
            v___x_496_ = leanh::lean_apply_2(v_inst_485_, v_val_494_, v_val_495_);
            v___x_497_ = (leanh::lean_unbox(v___x_496_) as u8);
            return v___x_497_;
        }
    }
}
pub unsafe fn l_Sum_instDecidableRelSumLex___redArg___boxed(
    mut v_inst_498_: *mut leanh::LeanObject,
    mut v_inst_499_: *mut leanh::LeanObject,
    mut v_x_500_: *mut leanh::LeanObject,
    mut v_x_501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_502_: u8 = 0;
    let mut v_r_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_502_ =
        l_Sum_instDecidableRelSumLex___redArg(v_inst_498_, v_inst_499_, v_x_500_, v_x_501_);
    v_r_503_ = leanh::lean_box((v_res_502_) as usize);
    return v_r_503_;
}
pub unsafe fn l_Sum_instDecidableRelSumLex(
    mut v_00_u03b1_504_: *mut leanh::LeanObject,
    mut v_r_505_: *mut leanh::LeanObject,
    mut v_00_u03b1_506_: *mut leanh::LeanObject,
    mut v_s_507_: *mut leanh::LeanObject,
    mut v_inst_508_: *mut leanh::LeanObject,
    mut v_inst_509_: *mut leanh::LeanObject,
    mut v_x_510_: *mut leanh::LeanObject,
    mut v_x_511_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_512_: u8 = 0;
    v___x_512_ =
        l_Sum_instDecidableRelSumLex___redArg(v_inst_508_, v_inst_509_, v_x_510_, v_x_511_);
    return v___x_512_;
}
pub unsafe fn l_Sum_instDecidableRelSumLex___boxed(
    mut v_00_u03b1_513_: *mut leanh::LeanObject,
    mut v_r_514_: *mut leanh::LeanObject,
    mut v_00_u03b1_515_: *mut leanh::LeanObject,
    mut v_s_516_: *mut leanh::LeanObject,
    mut v_inst_517_: *mut leanh::LeanObject,
    mut v_inst_518_: *mut leanh::LeanObject,
    mut v_x_519_: *mut leanh::LeanObject,
    mut v_x_520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_521_: u8 = 0;
    let mut v_r_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_521_ = l_Sum_instDecidableRelSumLex(
        v_00_u03b1_513_,
        v_r_514_,
        v_00_u03b1_515_,
        v_s_516_,
        v_inst_517_,
        v_inst_518_,
        v_x_519_,
        v_x_520_,
    );
    v_r_522_ = leanh::lean_box((v_res_521_) as usize);
    return v_r_522_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Sum_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_PropLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Sum_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Sum_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_PropLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Sum_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Sum_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Sum_Basic(builtin);
}