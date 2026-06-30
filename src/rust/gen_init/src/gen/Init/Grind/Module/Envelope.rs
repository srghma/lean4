// Lean compiler output
// Module: Init.Grind.Module.Envelope
// Imports: Init.Grind.Ordered.Module Init.Data.AC Init.Omega Init.RCases
use crate::ffi::{lean_int_dec_lt, lean_nat_abs, lean_nat_to_int};
use crate::r#gen::Init::Data::AC::{initialize_Init_Data_AC, runtime_initialize_Init_Data_AC};
use crate::r#gen::Init::Grind::Ordered::Module::{
    initialize_Init_Grind_Ordered_Module, runtime_initialize_Init_Grind_Ordered_Module,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::RCases::{initialize_Init_RCases, runtime_initialize_Init_RCases};
static mut l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Init_Grind_Module_Envelope_0__Lean_Grind_IntModule_OfNatModule_r_match__1_splitter___redArg(
    mut v_x_241_: *mut leanh::LeanObject,
    mut v_x_242_: *mut leanh::LeanObject,
    mut v_h__1_243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_244_ = leanh::lean_ctor_get(v_x_241_, 0);
    leanh::lean_inc(v_fst_244_);
    v_snd_245_ = leanh::lean_ctor_get(v_x_241_, 1);
    leanh::lean_inc(v_snd_245_);
    leanh::lean_dec_ref(v_x_241_);
    v_fst_246_ = leanh::lean_ctor_get(v_x_242_, 0);
    leanh::lean_inc(v_fst_246_);
    v_snd_247_ = leanh::lean_ctor_get(v_x_242_, 1);
    leanh::lean_inc(v_snd_247_);
    leanh::lean_dec_ref(v_x_242_);
    v___x_248_ =
        leanh::lean_apply_4(v_h__1_243_, v_fst_244_, v_snd_245_, v_fst_246_, v_snd_247_);
    return v___x_248_;
}
pub unsafe fn l___private_Init_Grind_Module_Envelope_0__Lean_Grind_IntModule_OfNatModule_r_match__1_splitter(
    mut v_00_u03b1_249_: *mut leanh::LeanObject,
    mut v_motive_250_: *mut leanh::LeanObject,
    mut v_x_251_: *mut leanh::LeanObject,
    mut v_x_252_: *mut leanh::LeanObject,
    mut v_h__1_253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_254_ = leanh::lean_ctor_get(v_x_251_, 0);
    leanh::lean_inc(v_fst_254_);
    v_snd_255_ = leanh::lean_ctor_get(v_x_251_, 1);
    leanh::lean_inc(v_snd_255_);
    leanh::lean_dec_ref(v_x_251_);
    v_fst_256_ = leanh::lean_ctor_get(v_x_252_, 0);
    leanh::lean_inc(v_fst_256_);
    v_snd_257_ = leanh::lean_ctor_get(v_x_252_, 1);
    leanh::lean_inc(v_snd_257_);
    leanh::lean_dec_ref(v_x_252_);
    v___x_258_ =
        leanh::lean_apply_4(v_h__1_253_, v_fst_254_, v_snd_255_, v_fst_256_, v_snd_257_);
    return v___x_258_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_Q_mk___redArg(
    mut v_p_259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_p_259_);
    return v_p_259_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_Q_mk___redArg___boxed(
    mut v_p_260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_261_ = l_Lean_Grind_IntModule_OfNatModule_Q_mk___redArg(v_p_260_);
    leanh::lean_dec_ref(v_p_260_);
    return v_res_261_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_Q_mk(
    mut v_00_u03b1_262_: *mut leanh::LeanObject,
    mut v_inst_263_: *mut leanh::LeanObject,
    mut v_p_264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_p_264_);
    return v_p_264_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_Q_mk___boxed(
    mut v_00_u03b1_265_: *mut leanh::LeanObject,
    mut v_inst_266_: *mut leanh::LeanObject,
    mut v_p_267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_268_ = l_Lean_Grind_IntModule_OfNatModule_Q_mk(v_00_u03b1_265_, v_inst_266_, v_p_267_);
    leanh::lean_dec_ref(v_p_267_);
    leanh::lean_dec_ref(v_inst_266_);
    return v_res_268_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_Q_liftOn_u2082___redArg(
    mut v_q_u2081_269_: *mut leanh::LeanObject,
    mut v_q_u2082_270_: *mut leanh::LeanObject,
    mut v_f_271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_272_ = leanh::lean_apply_2(v_f_271_, v_q_u2081_269_, v_q_u2082_270_);
    return v___x_272_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_Q_liftOn_u2082(
    mut v_00_u03b1_273_: *mut leanh::LeanObject,
    mut v_inst_274_: *mut leanh::LeanObject,
    mut v_00_u03b2_275_: *mut leanh::LeanObject,
    mut v_q_u2081_276_: *mut leanh::LeanObject,
    mut v_q_u2082_277_: *mut leanh::LeanObject,
    mut v_f_278_: *mut leanh::LeanObject,
    mut v_h_279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_280_ = leanh::lean_apply_2(v_f_278_, v_q_u2081_276_, v_q_u2082_277_);
    return v___x_280_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_Q_liftOn_u2082___boxed(
    mut v_00_u03b1_281_: *mut leanh::LeanObject,
    mut v_inst_282_: *mut leanh::LeanObject,
    mut v_00_u03b2_283_: *mut leanh::LeanObject,
    mut v_q_u2081_284_: *mut leanh::LeanObject,
    mut v_q_u2082_285_: *mut leanh::LeanObject,
    mut v_f_286_: *mut leanh::LeanObject,
    mut v_h_287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_288_ = l_Lean_Grind_IntModule_OfNatModule_Q_liftOn_u2082(
        v_00_u03b1_281_,
        v_inst_282_,
        v_00_u03b2_283_,
        v_q_u2081_284_,
        v_q_u2082_285_,
        v_f_286_,
        v_h_287_,
    );
    leanh::lean_dec_ref(v_inst_282_);
    return v_res_288_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_nsmul___redArg(
    mut v_inst_289_: *mut leanh::LeanObject,
    mut v_n_290_: *mut leanh::LeanObject,
    mut v_q_291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_nsmul_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_297_: u8 = 0;
    let mut v___x_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_303_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_nsmul_292_ = leanh::lean_ctor_get(v_inst_289_, 1);
                leanh::lean_inc(v_nsmul_292_);
                leanh::lean_dec_ref(v_inst_289_);
                v_fst_293_ = leanh::lean_ctor_get(v_q_291_, 0);
                v_snd_294_ = leanh::lean_ctor_get(v_q_291_, 1);
                v_isSharedCheck_303_ = (!leanh::lean_is_exclusive(v_q_291_)) as u8;
                if v_isSharedCheck_303_ == 0 {
                    v___x_296_ = v_q_291_;
                    v_isShared_297_ = v_isSharedCheck_303_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_294_);
                    leanh::lean_inc(v_fst_293_);
                    leanh::lean_dec(v_q_291_);
                    v___x_296_ = leanh::lean_box(0);
                    v_isShared_297_ = v_isSharedCheck_303_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_nsmul_292_);
                leanh::lean_inc(v_n_290_);
                v___x_298_ = leanh::lean_apply_2(v_nsmul_292_, v_n_290_, v_fst_293_);
                v___x_299_ = leanh::lean_apply_2(v_nsmul_292_, v_n_290_, v_snd_294_);
                if v_isShared_297_ == 0 {
                    leanh::lean_ctor_set(v___x_296_, 1, v___x_299_);
                    leanh::lean_ctor_set(v___x_296_, 0, v___x_298_);
                    v___x_301_ = v___x_296_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_302_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_298_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_302_, 1, v___x_299_);
                    v___x_301_ = v_reuseFailAlloc_302_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_301_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_nsmul(
    mut v_00_u03b1_304_: *mut leanh::LeanObject,
    mut v_inst_305_: *mut leanh::LeanObject,
    mut v_n_306_: *mut leanh::LeanObject,
    mut v_q_307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_308_ = l_Lean_Grind_IntModule_OfNatModule_nsmul___redArg(v_inst_305_, v_n_306_, v_q_307_);
    return v___x_308_;
}
pub unsafe fn _init_l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_309_ = leanh::lean_unsigned_to_nat(0);
    v___x_310_ = lean_nat_to_int(v___x_309_);
    return v___x_310_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg(
    mut v_inst_311_: *mut leanh::LeanObject,
    mut v_n_312_: *mut leanh::LeanObject,
    mut v_q_313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_318_: u8 = 0;
    let mut v___x_319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: u8 = 0;
    let mut v_nsmul_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nsmul_328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_335_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_314_ = leanh::lean_ctor_get(v_q_313_, 0);
                v_snd_315_ = leanh::lean_ctor_get(v_q_313_, 1);
                v_isSharedCheck_335_ = (!leanh::lean_is_exclusive(v_q_313_)) as u8;
                if v_isSharedCheck_335_ == 0 {
                    v___x_317_ = v_q_313_;
                    v_isShared_318_ = v_isSharedCheck_335_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_315_);
                    leanh::lean_inc(v_fst_314_);
                    leanh::lean_dec(v_q_313_);
                    v___x_317_ = leanh::lean_box(0);
                    v_isShared_318_ = v_isSharedCheck_335_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_319_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___closed__0_once
                    ),
                    _init_l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___closed__0,
                );
                v___x_320_ = lean_int_dec_lt(v_n_312_, v___x_319_);
                if v___x_320_ == 0 {
                    v_nsmul_321_ = leanh::lean_ctor_get(v_inst_311_, 1);
                    leanh::lean_inc_n(v_nsmul_321_, 2);
                    leanh::lean_dec_ref(v_inst_311_);
                    v___x_322_ = lean_nat_abs(v_n_312_);
                    leanh::lean_inc(v___x_322_);
                    v___x_323_ = leanh::lean_apply_2(v_nsmul_321_, v___x_322_, v_fst_314_);
                    v___x_324_ = leanh::lean_apply_2(v_nsmul_321_, v___x_322_, v_snd_315_);
                    if v_isShared_318_ == 0 {
                        leanh::lean_ctor_set(v___x_317_, 1, v___x_324_);
                        leanh::lean_ctor_set(v___x_317_, 0, v___x_323_);
                        v___x_326_ = v___x_317_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_327_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_323_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_327_, 1, v___x_324_);
                        v___x_326_ = v_reuseFailAlloc_327_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_nsmul_328_ = leanh::lean_ctor_get(v_inst_311_, 1);
                    leanh::lean_inc_n(v_nsmul_328_, 2);
                    leanh::lean_dec_ref(v_inst_311_);
                    v___x_329_ = lean_nat_abs(v_n_312_);
                    leanh::lean_inc(v___x_329_);
                    v___x_330_ = leanh::lean_apply_2(v_nsmul_328_, v___x_329_, v_snd_315_);
                    v___x_331_ = leanh::lean_apply_2(v_nsmul_328_, v___x_329_, v_fst_314_);
                    if v_isShared_318_ == 0 {
                        leanh::lean_ctor_set(v___x_317_, 1, v___x_331_);
                        leanh::lean_ctor_set(v___x_317_, 0, v___x_330_);
                        v___x_333_ = v___x_317_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_334_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_330_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_334_, 1, v___x_331_);
                        v___x_333_ = v_reuseFailAlloc_334_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_326_;
            }
            3 => {
                return v___x_333_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___boxed(
    mut v_inst_336_: *mut leanh::LeanObject,
    mut v_n_337_: *mut leanh::LeanObject,
    mut v_q_338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_339_ = l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg(v_inst_336_, v_n_337_, v_q_338_);
    leanh::lean_dec(v_n_337_);
    return v_res_339_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_zsmul(
    mut v_00_u03b1_340_: *mut leanh::LeanObject,
    mut v_inst_341_: *mut leanh::LeanObject,
    mut v_n_342_: *mut leanh::LeanObject,
    mut v_q_343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_344_ = l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg(v_inst_341_, v_n_342_, v_q_343_);
    return v___x_344_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_zsmul___boxed(
    mut v_00_u03b1_345_: *mut leanh::LeanObject,
    mut v_inst_346_: *mut leanh::LeanObject,
    mut v_n_347_: *mut leanh::LeanObject,
    mut v_q_348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_349_ =
        l_Lean_Grind_IntModule_OfNatModule_zsmul(v_00_u03b1_345_, v_inst_346_, v_n_347_, v_q_348_);
    leanh::lean_dec(v_n_347_);
    return v_res_349_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_sub___redArg(
    mut v_inst_350_: *mut leanh::LeanObject,
    mut v_q_u2081_351_: *mut leanh::LeanObject,
    mut v_q_u2082_352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toAddCommMonoid_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toAdd_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_361_: u8 = 0;
    let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_367_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toAddCommMonoid_353_ = leanh::lean_ctor_get(v_inst_350_, 0);
                leanh::lean_inc_ref(v_toAddCommMonoid_353_);
                leanh::lean_dec_ref(v_inst_350_);
                v_toAdd_354_ = leanh::lean_ctor_get(v_toAddCommMonoid_353_, 1);
                leanh::lean_inc(v_toAdd_354_);
                leanh::lean_dec_ref(v_toAddCommMonoid_353_);
                v_fst_355_ = leanh::lean_ctor_get(v_q_u2081_351_, 0);
                leanh::lean_inc(v_fst_355_);
                v_snd_356_ = leanh::lean_ctor_get(v_q_u2081_351_, 1);
                leanh::lean_inc(v_snd_356_);
                leanh::lean_dec(v_q_u2081_351_);
                v_fst_357_ = leanh::lean_ctor_get(v_q_u2082_352_, 0);
                v_snd_358_ = leanh::lean_ctor_get(v_q_u2082_352_, 1);
                v_isSharedCheck_367_ = (!leanh::lean_is_exclusive(v_q_u2082_352_)) as u8;
                if v_isSharedCheck_367_ == 0 {
                    v___x_360_ = v_q_u2082_352_;
                    v_isShared_361_ = v_isSharedCheck_367_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_358_);
                    leanh::lean_inc(v_fst_357_);
                    leanh::lean_dec(v_q_u2082_352_);
                    v___x_360_ = leanh::lean_box(0);
                    v_isShared_361_ = v_isSharedCheck_367_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_toAdd_354_);
                v___x_362_ = leanh::lean_apply_2(v_toAdd_354_, v_fst_355_, v_snd_358_);
                v___x_363_ = leanh::lean_apply_2(v_toAdd_354_, v_fst_357_, v_snd_356_);
                if v_isShared_361_ == 0 {
                    leanh::lean_ctor_set(v___x_360_, 1, v___x_363_);
                    leanh::lean_ctor_set(v___x_360_, 0, v___x_362_);
                    v___x_365_ = v___x_360_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_366_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_362_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_366_, 1, v___x_363_);
                    v___x_365_ = v_reuseFailAlloc_366_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_365_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_sub(
    mut v_00_u03b1_368_: *mut leanh::LeanObject,
    mut v_inst_369_: *mut leanh::LeanObject,
    mut v_q_u2081_370_: *mut leanh::LeanObject,
    mut v_q_u2082_371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_372_ = l_Lean_Grind_IntModule_OfNatModule_sub___redArg(
        v_inst_369_,
        v_q_u2081_370_,
        v_q_u2082_371_,
    );
    return v___x_372_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_add___redArg(
    mut v_inst_373_: *mut leanh::LeanObject,
    mut v_q_u2081_374_: *mut leanh::LeanObject,
    mut v_q_u2082_375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toAddCommMonoid_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toAdd_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_384_: u8 = 0;
    let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_390_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toAddCommMonoid_376_ = leanh::lean_ctor_get(v_inst_373_, 0);
                leanh::lean_inc_ref(v_toAddCommMonoid_376_);
                leanh::lean_dec_ref(v_inst_373_);
                v_toAdd_377_ = leanh::lean_ctor_get(v_toAddCommMonoid_376_, 1);
                leanh::lean_inc(v_toAdd_377_);
                leanh::lean_dec_ref(v_toAddCommMonoid_376_);
                v_fst_378_ = leanh::lean_ctor_get(v_q_u2081_374_, 0);
                leanh::lean_inc(v_fst_378_);
                v_snd_379_ = leanh::lean_ctor_get(v_q_u2081_374_, 1);
                leanh::lean_inc(v_snd_379_);
                leanh::lean_dec(v_q_u2081_374_);
                v_fst_380_ = leanh::lean_ctor_get(v_q_u2082_375_, 0);
                v_snd_381_ = leanh::lean_ctor_get(v_q_u2082_375_, 1);
                v_isSharedCheck_390_ = (!leanh::lean_is_exclusive(v_q_u2082_375_)) as u8;
                if v_isSharedCheck_390_ == 0 {
                    v___x_383_ = v_q_u2082_375_;
                    v_isShared_384_ = v_isSharedCheck_390_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_381_);
                    leanh::lean_inc(v_fst_380_);
                    leanh::lean_dec(v_q_u2082_375_);
                    v___x_383_ = leanh::lean_box(0);
                    v_isShared_384_ = v_isSharedCheck_390_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_toAdd_377_);
                v___x_385_ = leanh::lean_apply_2(v_toAdd_377_, v_fst_378_, v_fst_380_);
                v___x_386_ = leanh::lean_apply_2(v_toAdd_377_, v_snd_379_, v_snd_381_);
                if v_isShared_384_ == 0 {
                    leanh::lean_ctor_set(v___x_383_, 1, v___x_386_);
                    leanh::lean_ctor_set(v___x_383_, 0, v___x_385_);
                    v___x_388_ = v___x_383_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_389_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_385_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_389_, 1, v___x_386_);
                    v___x_388_ = v_reuseFailAlloc_389_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_388_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_add(
    mut v_00_u03b1_391_: *mut leanh::LeanObject,
    mut v_inst_392_: *mut leanh::LeanObject,
    mut v_q_u2081_393_: *mut leanh::LeanObject,
    mut v_q_u2082_394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_395_ = l_Lean_Grind_IntModule_OfNatModule_add___redArg(
        v_inst_392_,
        v_q_u2081_393_,
        v_q_u2082_394_,
    );
    return v___x_395_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_neg___redArg(
    mut v_q_396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_401_: u8 = 0;
    let mut v___x_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_405_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_397_ = leanh::lean_ctor_get(v_q_396_, 0);
                v_snd_398_ = leanh::lean_ctor_get(v_q_396_, 1);
                v_isSharedCheck_405_ = (!leanh::lean_is_exclusive(v_q_396_)) as u8;
                if v_isSharedCheck_405_ == 0 {
                    v___x_400_ = v_q_396_;
                    v_isShared_401_ = v_isSharedCheck_405_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_398_);
                    leanh::lean_inc(v_fst_397_);
                    leanh::lean_dec(v_q_396_);
                    v___x_400_ = leanh::lean_box(0);
                    v_isShared_401_ = v_isSharedCheck_405_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_401_ == 0 {
                    leanh::lean_ctor_set(v___x_400_, 1, v_fst_397_);
                    leanh::lean_ctor_set(v___x_400_, 0, v_snd_398_);
                    v___x_403_ = v___x_400_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_404_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_404_, 0, v_snd_398_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_404_, 1, v_fst_397_);
                    v___x_403_ = v_reuseFailAlloc_404_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_403_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_neg(
    mut v_00_u03b1_406_: *mut leanh::LeanObject,
    mut v_inst_407_: *mut leanh::LeanObject,
    mut v_q_408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_409_ = l_Lean_Grind_IntModule_OfNatModule_neg___redArg(v_q_408_);
    return v___x_409_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_neg___boxed(
    mut v_00_u03b1_410_: *mut leanh::LeanObject,
    mut v_inst_411_: *mut leanh::LeanObject,
    mut v_q_412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_413_ = l_Lean_Grind_IntModule_OfNatModule_neg(v_00_u03b1_410_, v_inst_411_, v_q_412_);
    leanh::lean_dec_ref(v_inst_411_);
    return v_res_413_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_zero___redArg(
    mut v_inst_414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toAddCommMonoid_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toZero_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_419_: u8 = 0;
    let mut v___x_421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_423_: u8 = 0;
    let mut v_unused_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toAddCommMonoid_415_ = leanh::lean_ctor_get(v_inst_414_, 0);
                leanh::lean_inc_ref(v_toAddCommMonoid_415_);
                leanh::lean_dec_ref(v_inst_414_);
                v_toZero_416_ = leanh::lean_ctor_get(v_toAddCommMonoid_415_, 0);
                v_isSharedCheck_423_ =
                    (!leanh::lean_is_exclusive(v_toAddCommMonoid_415_)) as u8;
                if v_isSharedCheck_423_ == 0 {
                    v_unused_424_ = leanh::lean_ctor_get(v_toAddCommMonoid_415_, 1);
                    leanh::lean_dec(v_unused_424_);
                    v___x_418_ = v_toAddCommMonoid_415_;
                    v_isShared_419_ = v_isSharedCheck_423_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toZero_416_);
                    leanh::lean_dec(v_toAddCommMonoid_415_);
                    v___x_418_ = leanh::lean_box(0);
                    v_isShared_419_ = v_isSharedCheck_423_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_toZero_416_);
                if v_isShared_419_ == 0 {
                    leanh::lean_ctor_set(v___x_418_, 1, v_toZero_416_);
                    v___x_421_ = v___x_418_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_422_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_422_, 0, v_toZero_416_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_422_, 1, v_toZero_416_);
                    v___x_421_ = v_reuseFailAlloc_422_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_421_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_zero(
    mut v_00_u03b1_425_: *mut leanh::LeanObject,
    mut v_inst_426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_427_ = l_Lean_Grind_IntModule_OfNatModule_zero___redArg(v_inst_426_);
    return v___x_427_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_ofNatModule___redArg(
    mut v_inst_428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v_inst_428_, 5);
    v___x_429_ = l_Lean_Grind_IntModule_OfNatModule_zero___redArg(v_inst_428_);
    v___x_430_ = leanh::lean_alloc_closure(
        l_Lean_Grind_IntModule_OfNatModule_add as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___x_430_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_430_, 1, v_inst_428_);
    v___x_431_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_431_, 0, v___x_429_);
    leanh::lean_ctor_set(v___x_431_, 1, v___x_430_);
    v___x_432_ = leanh::lean_alloc_closure(
        l_Lean_Grind_IntModule_OfNatModule_neg___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_432_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_432_, 1, v_inst_428_);
    v___x_433_ = leanh::lean_alloc_closure(
        l_Lean_Grind_IntModule_OfNatModule_sub as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___x_433_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_433_, 1, v_inst_428_);
    v___x_434_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_434_, 0, v___x_431_);
    leanh::lean_ctor_set(v___x_434_, 1, v___x_432_);
    leanh::lean_ctor_set(v___x_434_, 2, v___x_433_);
    v___x_435_ = leanh::lean_alloc_closure(
        l_Lean_Grind_IntModule_OfNatModule_nsmul as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___x_435_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_435_, 1, v_inst_428_);
    v___x_436_ = leanh::lean_alloc_closure(
        l_Lean_Grind_IntModule_OfNatModule_zsmul___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___x_436_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_436_, 1, v_inst_428_);
    v___x_437_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_437_, 0, v___x_434_);
    leanh::lean_ctor_set(v___x_437_, 1, v___x_435_);
    leanh::lean_ctor_set(v___x_437_, 2, v___x_436_);
    return v___x_437_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_ofNatModule(
    mut v_00_u03b1_438_: *mut leanh::LeanObject,
    mut v_inst_439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_440_ = l_Lean_Grind_IntModule_OfNatModule_ofNatModule___redArg(v_inst_439_);
    return v___x_440_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_toQ___redArg(
    mut v_inst_441_: *mut leanh::LeanObject,
    mut v_a_442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toAddCommMonoid_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toZero_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_447_: u8 = 0;
    let mut v___x_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_451_: u8 = 0;
    let mut v_unused_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toAddCommMonoid_443_ = leanh::lean_ctor_get(v_inst_441_, 0);
                leanh::lean_inc_ref(v_toAddCommMonoid_443_);
                leanh::lean_dec_ref(v_inst_441_);
                v_toZero_444_ = leanh::lean_ctor_get(v_toAddCommMonoid_443_, 0);
                v_isSharedCheck_451_ =
                    (!leanh::lean_is_exclusive(v_toAddCommMonoid_443_)) as u8;
                if v_isSharedCheck_451_ == 0 {
                    v_unused_452_ = leanh::lean_ctor_get(v_toAddCommMonoid_443_, 1);
                    leanh::lean_dec(v_unused_452_);
                    v___x_446_ = v_toAddCommMonoid_443_;
                    v_isShared_447_ = v_isSharedCheck_451_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toZero_444_);
                    leanh::lean_dec(v_toAddCommMonoid_443_);
                    v___x_446_ = leanh::lean_box(0);
                    v_isShared_447_ = v_isSharedCheck_451_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_447_ == 0 {
                    leanh::lean_ctor_set(v___x_446_, 1, v_toZero_444_);
                    leanh::lean_ctor_set(v___x_446_, 0, v_a_442_);
                    v___x_449_ = v___x_446_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_450_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_450_, 0, v_a_442_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_450_, 1, v_toZero_444_);
                    v___x_449_ = v_reuseFailAlloc_450_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_449_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_toQ(
    mut v_00_u03b1_453_: *mut leanh::LeanObject,
    mut v_inst_454_: *mut leanh::LeanObject,
    mut v_a_455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_456_ = l_Lean_Grind_IntModule_OfNatModule_toQ___redArg(v_inst_454_, v_a_455_);
    return v___x_456_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_instLEQOfOrderedAdd(
    mut v_00_u03b1_457_: *mut leanh::LeanObject,
    mut v_inst_458_: *mut leanh::LeanObject,
    mut v_inst_459_: *mut leanh::LeanObject,
    mut v_inst_460_: *mut leanh::LeanObject,
    mut v_inst_461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_462_ = leanh::lean_box(0);
    return v___x_462_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_instLEQOfOrderedAdd___boxed(
    mut v_00_u03b1_463_: *mut leanh::LeanObject,
    mut v_inst_464_: *mut leanh::LeanObject,
    mut v_inst_465_: *mut leanh::LeanObject,
    mut v_inst_466_: *mut leanh::LeanObject,
    mut v_inst_467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_468_ = l_Lean_Grind_IntModule_OfNatModule_instLEQOfOrderedAdd(
        v_00_u03b1_463_,
        v_inst_464_,
        v_inst_465_,
        v_inst_466_,
        v_inst_467_,
    );
    leanh::lean_dec_ref(v_inst_464_);
    return v_res_468_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_instLTQOfOrderedAdd(
    mut v_00_u03b1_469_: *mut leanh::LeanObject,
    mut v_inst_470_: *mut leanh::LeanObject,
    mut v_inst_471_: *mut leanh::LeanObject,
    mut v_inst_472_: *mut leanh::LeanObject,
    mut v_inst_473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_474_ = leanh::lean_box(0);
    return v___x_474_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_instLTQOfOrderedAdd___boxed(
    mut v_00_u03b1_475_: *mut leanh::LeanObject,
    mut v_inst_476_: *mut leanh::LeanObject,
    mut v_inst_477_: *mut leanh::LeanObject,
    mut v_inst_478_: *mut leanh::LeanObject,
    mut v_inst_479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_480_ = l_Lean_Grind_IntModule_OfNatModule_instLTQOfOrderedAdd(
        v_00_u03b1_475_,
        v_inst_476_,
        v_inst_477_,
        v_inst_478_,
        v_inst_479_,
    );
    leanh::lean_dec_ref(v_inst_476_);
    return v_res_480_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Module_Envelope(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Ordered_Module(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_AC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_RCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_Module_Envelope(
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
pub unsafe fn initialize_Init_Grind_Module_Envelope(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Ordered_Module(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_AC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_RCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Module_Envelope(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Module_Envelope(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Grind_Module_Envelope(builtin);
}