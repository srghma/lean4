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
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Init_Grind_Module_Envelope_0__Lean_Grind_IntModule_OfNatModule_r_match__1_splitter___redArg(
    mut v_x_241_: *mut crate::leanh::LeanObject,
    mut v_x_242_: *mut crate::leanh::LeanObject,
    mut v_h__1_243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_244_ = crate::leanh::lean_ctor_get(v_x_241_, 0);
    crate::leanh::lean_inc(v_fst_244_);
    v_snd_245_ = crate::leanh::lean_ctor_get(v_x_241_, 1);
    crate::leanh::lean_inc(v_snd_245_);
    crate::leanh::lean_dec_ref(v_x_241_);
    v_fst_246_ = crate::leanh::lean_ctor_get(v_x_242_, 0);
    crate::leanh::lean_inc(v_fst_246_);
    v_snd_247_ = crate::leanh::lean_ctor_get(v_x_242_, 1);
    crate::leanh::lean_inc(v_snd_247_);
    crate::leanh::lean_dec_ref(v_x_242_);
    v___x_248_ =
        crate::leanh::lean_apply_4(v_h__1_243_, v_fst_244_, v_snd_245_, v_fst_246_, v_snd_247_);
    return v___x_248_;
}
pub unsafe fn l___private_Init_Grind_Module_Envelope_0__Lean_Grind_IntModule_OfNatModule_r_match__1_splitter(
    mut v_00_u03b1_249_: *mut crate::leanh::LeanObject,
    mut v_motive_250_: *mut crate::leanh::LeanObject,
    mut v_x_251_: *mut crate::leanh::LeanObject,
    mut v_x_252_: *mut crate::leanh::LeanObject,
    mut v_h__1_253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_254_ = crate::leanh::lean_ctor_get(v_x_251_, 0);
    crate::leanh::lean_inc(v_fst_254_);
    v_snd_255_ = crate::leanh::lean_ctor_get(v_x_251_, 1);
    crate::leanh::lean_inc(v_snd_255_);
    crate::leanh::lean_dec_ref(v_x_251_);
    v_fst_256_ = crate::leanh::lean_ctor_get(v_x_252_, 0);
    crate::leanh::lean_inc(v_fst_256_);
    v_snd_257_ = crate::leanh::lean_ctor_get(v_x_252_, 1);
    crate::leanh::lean_inc(v_snd_257_);
    crate::leanh::lean_dec_ref(v_x_252_);
    v___x_258_ =
        crate::leanh::lean_apply_4(v_h__1_253_, v_fst_254_, v_snd_255_, v_fst_256_, v_snd_257_);
    return v___x_258_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_Q_mk___redArg(
    mut v_p_259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_p_259_);
    return v_p_259_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_Q_mk___redArg___boxed(
    mut v_p_260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_261_ = l_Lean_Grind_IntModule_OfNatModule_Q_mk___redArg(v_p_260_);
    crate::leanh::lean_dec_ref(v_p_260_);
    return v_res_261_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_Q_mk(
    mut v_00_u03b1_262_: *mut crate::leanh::LeanObject,
    mut v_inst_263_: *mut crate::leanh::LeanObject,
    mut v_p_264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_p_264_);
    return v_p_264_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_Q_mk___boxed(
    mut v_00_u03b1_265_: *mut crate::leanh::LeanObject,
    mut v_inst_266_: *mut crate::leanh::LeanObject,
    mut v_p_267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_268_ = l_Lean_Grind_IntModule_OfNatModule_Q_mk(v_00_u03b1_265_, v_inst_266_, v_p_267_);
    crate::leanh::lean_dec_ref(v_p_267_);
    crate::leanh::lean_dec_ref(v_inst_266_);
    return v_res_268_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_Q_liftOn_u2082___redArg(
    mut v_q_u2081_269_: *mut crate::leanh::LeanObject,
    mut v_q_u2082_270_: *mut crate::leanh::LeanObject,
    mut v_f_271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_272_ = crate::leanh::lean_apply_2(v_f_271_, v_q_u2081_269_, v_q_u2082_270_);
    return v___x_272_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_Q_liftOn_u2082(
    mut v_00_u03b1_273_: *mut crate::leanh::LeanObject,
    mut v_inst_274_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_275_: *mut crate::leanh::LeanObject,
    mut v_q_u2081_276_: *mut crate::leanh::LeanObject,
    mut v_q_u2082_277_: *mut crate::leanh::LeanObject,
    mut v_f_278_: *mut crate::leanh::LeanObject,
    mut v_h_279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_280_ = crate::leanh::lean_apply_2(v_f_278_, v_q_u2081_276_, v_q_u2082_277_);
    return v___x_280_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_Q_liftOn_u2082___boxed(
    mut v_00_u03b1_281_: *mut crate::leanh::LeanObject,
    mut v_inst_282_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_283_: *mut crate::leanh::LeanObject,
    mut v_q_u2081_284_: *mut crate::leanh::LeanObject,
    mut v_q_u2082_285_: *mut crate::leanh::LeanObject,
    mut v_f_286_: *mut crate::leanh::LeanObject,
    mut v_h_287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_288_ = l_Lean_Grind_IntModule_OfNatModule_Q_liftOn_u2082(
        v_00_u03b1_281_,
        v_inst_282_,
        v_00_u03b2_283_,
        v_q_u2081_284_,
        v_q_u2082_285_,
        v_f_286_,
        v_h_287_,
    );
    crate::leanh::lean_dec_ref(v_inst_282_);
    return v_res_288_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_nsmul___redArg(
    mut v_inst_289_: *mut crate::leanh::LeanObject,
    mut v_n_290_: *mut crate::leanh::LeanObject,
    mut v_q_291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nsmul_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_297_: u8 = 0;
    let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_303_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_nsmul_292_ = crate::leanh::lean_ctor_get(v_inst_289_, 1);
                crate::leanh::lean_inc(v_nsmul_292_);
                crate::leanh::lean_dec_ref(v_inst_289_);
                v_fst_293_ = crate::leanh::lean_ctor_get(v_q_291_, 0);
                v_snd_294_ = crate::leanh::lean_ctor_get(v_q_291_, 1);
                v_isSharedCheck_303_ = (!crate::leanh::lean_is_exclusive(v_q_291_)) as u8;
                if v_isSharedCheck_303_ == 0 {
                    v___x_296_ = v_q_291_;
                    v_isShared_297_ = v_isSharedCheck_303_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_294_);
                    crate::leanh::lean_inc(v_fst_293_);
                    crate::leanh::lean_dec(v_q_291_);
                    v___x_296_ = crate::leanh::lean_box(0);
                    v_isShared_297_ = v_isSharedCheck_303_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_nsmul_292_);
                crate::leanh::lean_inc(v_n_290_);
                v___x_298_ = crate::leanh::lean_apply_2(v_nsmul_292_, v_n_290_, v_fst_293_);
                v___x_299_ = crate::leanh::lean_apply_2(v_nsmul_292_, v_n_290_, v_snd_294_);
                if v_isShared_297_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_296_, 1, v___x_299_);
                    crate::leanh::lean_ctor_set(v___x_296_, 0, v___x_298_);
                    v___x_301_ = v___x_296_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_302_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_298_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_302_, 1, v___x_299_);
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
    mut v_00_u03b1_304_: *mut crate::leanh::LeanObject,
    mut v_inst_305_: *mut crate::leanh::LeanObject,
    mut v_n_306_: *mut crate::leanh::LeanObject,
    mut v_q_307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_308_ = l_Lean_Grind_IntModule_OfNatModule_nsmul___redArg(v_inst_305_, v_n_306_, v_q_307_);
    return v___x_308_;
}
pub unsafe fn _init_l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_309_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_310_ = lean_nat_to_int(v___x_309_);
    return v___x_310_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg(
    mut v_inst_311_: *mut crate::leanh::LeanObject,
    mut v_n_312_: *mut crate::leanh::LeanObject,
    mut v_q_313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_318_: u8 = 0;
    let mut v___x_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: u8 = 0;
    let mut v_nsmul_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nsmul_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_335_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_314_ = crate::leanh::lean_ctor_get(v_q_313_, 0);
                v_snd_315_ = crate::leanh::lean_ctor_get(v_q_313_, 1);
                v_isSharedCheck_335_ = (!crate::leanh::lean_is_exclusive(v_q_313_)) as u8;
                if v_isSharedCheck_335_ == 0 {
                    v___x_317_ = v_q_313_;
                    v_isShared_318_ = v_isSharedCheck_335_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_315_);
                    crate::leanh::lean_inc(v_fst_314_);
                    crate::leanh::lean_dec(v_q_313_);
                    v___x_317_ = crate::leanh::lean_box(0);
                    v_isShared_318_ = v_isSharedCheck_335_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_319_ = crate::leanh::lean_obj_once(
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
                    v_nsmul_321_ = crate::leanh::lean_ctor_get(v_inst_311_, 1);
                    crate::leanh::lean_inc_n(v_nsmul_321_, 2);
                    crate::leanh::lean_dec_ref(v_inst_311_);
                    v___x_322_ = lean_nat_abs(v_n_312_);
                    crate::leanh::lean_inc(v___x_322_);
                    v___x_323_ = crate::leanh::lean_apply_2(v_nsmul_321_, v___x_322_, v_fst_314_);
                    v___x_324_ = crate::leanh::lean_apply_2(v_nsmul_321_, v___x_322_, v_snd_315_);
                    if v_isShared_318_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_317_, 1, v___x_324_);
                        crate::leanh::lean_ctor_set(v___x_317_, 0, v___x_323_);
                        v___x_326_ = v___x_317_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_327_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_323_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_327_, 1, v___x_324_);
                        v___x_326_ = v_reuseFailAlloc_327_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_nsmul_328_ = crate::leanh::lean_ctor_get(v_inst_311_, 1);
                    crate::leanh::lean_inc_n(v_nsmul_328_, 2);
                    crate::leanh::lean_dec_ref(v_inst_311_);
                    v___x_329_ = lean_nat_abs(v_n_312_);
                    crate::leanh::lean_inc(v___x_329_);
                    v___x_330_ = crate::leanh::lean_apply_2(v_nsmul_328_, v___x_329_, v_snd_315_);
                    v___x_331_ = crate::leanh::lean_apply_2(v_nsmul_328_, v___x_329_, v_fst_314_);
                    if v_isShared_318_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_317_, 1, v___x_331_);
                        crate::leanh::lean_ctor_set(v___x_317_, 0, v___x_330_);
                        v___x_333_ = v___x_317_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_334_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_330_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_334_, 1, v___x_331_);
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
    mut v_inst_336_: *mut crate::leanh::LeanObject,
    mut v_n_337_: *mut crate::leanh::LeanObject,
    mut v_q_338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_339_ = l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg(v_inst_336_, v_n_337_, v_q_338_);
    crate::leanh::lean_dec(v_n_337_);
    return v_res_339_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_zsmul(
    mut v_00_u03b1_340_: *mut crate::leanh::LeanObject,
    mut v_inst_341_: *mut crate::leanh::LeanObject,
    mut v_n_342_: *mut crate::leanh::LeanObject,
    mut v_q_343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_344_ = l_Lean_Grind_IntModule_OfNatModule_zsmul___redArg(v_inst_341_, v_n_342_, v_q_343_);
    return v___x_344_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_zsmul___boxed(
    mut v_00_u03b1_345_: *mut crate::leanh::LeanObject,
    mut v_inst_346_: *mut crate::leanh::LeanObject,
    mut v_n_347_: *mut crate::leanh::LeanObject,
    mut v_q_348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_349_ =
        l_Lean_Grind_IntModule_OfNatModule_zsmul(v_00_u03b1_345_, v_inst_346_, v_n_347_, v_q_348_);
    crate::leanh::lean_dec(v_n_347_);
    return v_res_349_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_sub___redArg(
    mut v_inst_350_: *mut crate::leanh::LeanObject,
    mut v_q_u2081_351_: *mut crate::leanh::LeanObject,
    mut v_q_u2082_352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toAddCommMonoid_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toAdd_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_361_: u8 = 0;
    let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_367_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toAddCommMonoid_353_ = crate::leanh::lean_ctor_get(v_inst_350_, 0);
                crate::leanh::lean_inc_ref(v_toAddCommMonoid_353_);
                crate::leanh::lean_dec_ref(v_inst_350_);
                v_toAdd_354_ = crate::leanh::lean_ctor_get(v_toAddCommMonoid_353_, 1);
                crate::leanh::lean_inc(v_toAdd_354_);
                crate::leanh::lean_dec_ref(v_toAddCommMonoid_353_);
                v_fst_355_ = crate::leanh::lean_ctor_get(v_q_u2081_351_, 0);
                crate::leanh::lean_inc(v_fst_355_);
                v_snd_356_ = crate::leanh::lean_ctor_get(v_q_u2081_351_, 1);
                crate::leanh::lean_inc(v_snd_356_);
                crate::leanh::lean_dec(v_q_u2081_351_);
                v_fst_357_ = crate::leanh::lean_ctor_get(v_q_u2082_352_, 0);
                v_snd_358_ = crate::leanh::lean_ctor_get(v_q_u2082_352_, 1);
                v_isSharedCheck_367_ = (!crate::leanh::lean_is_exclusive(v_q_u2082_352_)) as u8;
                if v_isSharedCheck_367_ == 0 {
                    v___x_360_ = v_q_u2082_352_;
                    v_isShared_361_ = v_isSharedCheck_367_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_358_);
                    crate::leanh::lean_inc(v_fst_357_);
                    crate::leanh::lean_dec(v_q_u2082_352_);
                    v___x_360_ = crate::leanh::lean_box(0);
                    v_isShared_361_ = v_isSharedCheck_367_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_toAdd_354_);
                v___x_362_ = crate::leanh::lean_apply_2(v_toAdd_354_, v_fst_355_, v_snd_358_);
                v___x_363_ = crate::leanh::lean_apply_2(v_toAdd_354_, v_fst_357_, v_snd_356_);
                if v_isShared_361_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_360_, 1, v___x_363_);
                    crate::leanh::lean_ctor_set(v___x_360_, 0, v___x_362_);
                    v___x_365_ = v___x_360_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_366_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_362_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_366_, 1, v___x_363_);
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
    mut v_00_u03b1_368_: *mut crate::leanh::LeanObject,
    mut v_inst_369_: *mut crate::leanh::LeanObject,
    mut v_q_u2081_370_: *mut crate::leanh::LeanObject,
    mut v_q_u2082_371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_372_ = l_Lean_Grind_IntModule_OfNatModule_sub___redArg(
        v_inst_369_,
        v_q_u2081_370_,
        v_q_u2082_371_,
    );
    return v___x_372_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_add___redArg(
    mut v_inst_373_: *mut crate::leanh::LeanObject,
    mut v_q_u2081_374_: *mut crate::leanh::LeanObject,
    mut v_q_u2082_375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toAddCommMonoid_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toAdd_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_384_: u8 = 0;
    let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_390_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toAddCommMonoid_376_ = crate::leanh::lean_ctor_get(v_inst_373_, 0);
                crate::leanh::lean_inc_ref(v_toAddCommMonoid_376_);
                crate::leanh::lean_dec_ref(v_inst_373_);
                v_toAdd_377_ = crate::leanh::lean_ctor_get(v_toAddCommMonoid_376_, 1);
                crate::leanh::lean_inc(v_toAdd_377_);
                crate::leanh::lean_dec_ref(v_toAddCommMonoid_376_);
                v_fst_378_ = crate::leanh::lean_ctor_get(v_q_u2081_374_, 0);
                crate::leanh::lean_inc(v_fst_378_);
                v_snd_379_ = crate::leanh::lean_ctor_get(v_q_u2081_374_, 1);
                crate::leanh::lean_inc(v_snd_379_);
                crate::leanh::lean_dec(v_q_u2081_374_);
                v_fst_380_ = crate::leanh::lean_ctor_get(v_q_u2082_375_, 0);
                v_snd_381_ = crate::leanh::lean_ctor_get(v_q_u2082_375_, 1);
                v_isSharedCheck_390_ = (!crate::leanh::lean_is_exclusive(v_q_u2082_375_)) as u8;
                if v_isSharedCheck_390_ == 0 {
                    v___x_383_ = v_q_u2082_375_;
                    v_isShared_384_ = v_isSharedCheck_390_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_381_);
                    crate::leanh::lean_inc(v_fst_380_);
                    crate::leanh::lean_dec(v_q_u2082_375_);
                    v___x_383_ = crate::leanh::lean_box(0);
                    v_isShared_384_ = v_isSharedCheck_390_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_toAdd_377_);
                v___x_385_ = crate::leanh::lean_apply_2(v_toAdd_377_, v_fst_378_, v_fst_380_);
                v___x_386_ = crate::leanh::lean_apply_2(v_toAdd_377_, v_snd_379_, v_snd_381_);
                if v_isShared_384_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_383_, 1, v___x_386_);
                    crate::leanh::lean_ctor_set(v___x_383_, 0, v___x_385_);
                    v___x_388_ = v___x_383_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_389_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_385_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_389_, 1, v___x_386_);
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
    mut v_00_u03b1_391_: *mut crate::leanh::LeanObject,
    mut v_inst_392_: *mut crate::leanh::LeanObject,
    mut v_q_u2081_393_: *mut crate::leanh::LeanObject,
    mut v_q_u2082_394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_395_ = l_Lean_Grind_IntModule_OfNatModule_add___redArg(
        v_inst_392_,
        v_q_u2081_393_,
        v_q_u2082_394_,
    );
    return v___x_395_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_neg___redArg(
    mut v_q_396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_401_: u8 = 0;
    let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_405_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_397_ = crate::leanh::lean_ctor_get(v_q_396_, 0);
                v_snd_398_ = crate::leanh::lean_ctor_get(v_q_396_, 1);
                v_isSharedCheck_405_ = (!crate::leanh::lean_is_exclusive(v_q_396_)) as u8;
                if v_isSharedCheck_405_ == 0 {
                    v___x_400_ = v_q_396_;
                    v_isShared_401_ = v_isSharedCheck_405_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_398_);
                    crate::leanh::lean_inc(v_fst_397_);
                    crate::leanh::lean_dec(v_q_396_);
                    v___x_400_ = crate::leanh::lean_box(0);
                    v_isShared_401_ = v_isSharedCheck_405_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_401_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_400_, 1, v_fst_397_);
                    crate::leanh::lean_ctor_set(v___x_400_, 0, v_snd_398_);
                    v___x_403_ = v___x_400_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_404_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_404_, 0, v_snd_398_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_404_, 1, v_fst_397_);
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
    mut v_00_u03b1_406_: *mut crate::leanh::LeanObject,
    mut v_inst_407_: *mut crate::leanh::LeanObject,
    mut v_q_408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_409_ = l_Lean_Grind_IntModule_OfNatModule_neg___redArg(v_q_408_);
    return v___x_409_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_neg___boxed(
    mut v_00_u03b1_410_: *mut crate::leanh::LeanObject,
    mut v_inst_411_: *mut crate::leanh::LeanObject,
    mut v_q_412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_413_ = l_Lean_Grind_IntModule_OfNatModule_neg(v_00_u03b1_410_, v_inst_411_, v_q_412_);
    crate::leanh::lean_dec_ref(v_inst_411_);
    return v_res_413_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_zero___redArg(
    mut v_inst_414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toAddCommMonoid_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toZero_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_419_: u8 = 0;
    let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_423_: u8 = 0;
    let mut v_unused_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toAddCommMonoid_415_ = crate::leanh::lean_ctor_get(v_inst_414_, 0);
                crate::leanh::lean_inc_ref(v_toAddCommMonoid_415_);
                crate::leanh::lean_dec_ref(v_inst_414_);
                v_toZero_416_ = crate::leanh::lean_ctor_get(v_toAddCommMonoid_415_, 0);
                v_isSharedCheck_423_ =
                    (!crate::leanh::lean_is_exclusive(v_toAddCommMonoid_415_)) as u8;
                if v_isSharedCheck_423_ == 0 {
                    v_unused_424_ = crate::leanh::lean_ctor_get(v_toAddCommMonoid_415_, 1);
                    crate::leanh::lean_dec(v_unused_424_);
                    v___x_418_ = v_toAddCommMonoid_415_;
                    v_isShared_419_ = v_isSharedCheck_423_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toZero_416_);
                    crate::leanh::lean_dec(v_toAddCommMonoid_415_);
                    v___x_418_ = crate::leanh::lean_box(0);
                    v_isShared_419_ = v_isSharedCheck_423_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_toZero_416_);
                if v_isShared_419_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_418_, 1, v_toZero_416_);
                    v___x_421_ = v___x_418_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_422_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_422_, 0, v_toZero_416_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_422_, 1, v_toZero_416_);
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
    mut v_00_u03b1_425_: *mut crate::leanh::LeanObject,
    mut v_inst_426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_427_ = l_Lean_Grind_IntModule_OfNatModule_zero___redArg(v_inst_426_);
    return v___x_427_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_ofNatModule___redArg(
    mut v_inst_428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref_n(v_inst_428_, 5);
    v___x_429_ = l_Lean_Grind_IntModule_OfNatModule_zero___redArg(v_inst_428_);
    v___x_430_ = crate::leanh::lean_alloc_closure(
        l_Lean_Grind_IntModule_OfNatModule_add as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_430_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_430_, 1, v_inst_428_);
    v___x_431_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_431_, 0, v___x_429_);
    crate::leanh::lean_ctor_set(v___x_431_, 1, v___x_430_);
    v___x_432_ = crate::leanh::lean_alloc_closure(
        l_Lean_Grind_IntModule_OfNatModule_neg___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_432_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_432_, 1, v_inst_428_);
    v___x_433_ = crate::leanh::lean_alloc_closure(
        l_Lean_Grind_IntModule_OfNatModule_sub as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_433_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_433_, 1, v_inst_428_);
    v___x_434_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_434_, 0, v___x_431_);
    crate::leanh::lean_ctor_set(v___x_434_, 1, v___x_432_);
    crate::leanh::lean_ctor_set(v___x_434_, 2, v___x_433_);
    v___x_435_ = crate::leanh::lean_alloc_closure(
        l_Lean_Grind_IntModule_OfNatModule_nsmul as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_435_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_435_, 1, v_inst_428_);
    v___x_436_ = crate::leanh::lean_alloc_closure(
        l_Lean_Grind_IntModule_OfNatModule_zsmul___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_436_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_436_, 1, v_inst_428_);
    v___x_437_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_437_, 0, v___x_434_);
    crate::leanh::lean_ctor_set(v___x_437_, 1, v___x_435_);
    crate::leanh::lean_ctor_set(v___x_437_, 2, v___x_436_);
    return v___x_437_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_ofNatModule(
    mut v_00_u03b1_438_: *mut crate::leanh::LeanObject,
    mut v_inst_439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_440_ = l_Lean_Grind_IntModule_OfNatModule_ofNatModule___redArg(v_inst_439_);
    return v___x_440_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_toQ___redArg(
    mut v_inst_441_: *mut crate::leanh::LeanObject,
    mut v_a_442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toAddCommMonoid_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toZero_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_447_: u8 = 0;
    let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_451_: u8 = 0;
    let mut v_unused_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toAddCommMonoid_443_ = crate::leanh::lean_ctor_get(v_inst_441_, 0);
                crate::leanh::lean_inc_ref(v_toAddCommMonoid_443_);
                crate::leanh::lean_dec_ref(v_inst_441_);
                v_toZero_444_ = crate::leanh::lean_ctor_get(v_toAddCommMonoid_443_, 0);
                v_isSharedCheck_451_ =
                    (!crate::leanh::lean_is_exclusive(v_toAddCommMonoid_443_)) as u8;
                if v_isSharedCheck_451_ == 0 {
                    v_unused_452_ = crate::leanh::lean_ctor_get(v_toAddCommMonoid_443_, 1);
                    crate::leanh::lean_dec(v_unused_452_);
                    v___x_446_ = v_toAddCommMonoid_443_;
                    v_isShared_447_ = v_isSharedCheck_451_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toZero_444_);
                    crate::leanh::lean_dec(v_toAddCommMonoid_443_);
                    v___x_446_ = crate::leanh::lean_box(0);
                    v_isShared_447_ = v_isSharedCheck_451_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_447_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_446_, 1, v_toZero_444_);
                    crate::leanh::lean_ctor_set(v___x_446_, 0, v_a_442_);
                    v___x_449_ = v___x_446_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_450_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_450_, 0, v_a_442_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_450_, 1, v_toZero_444_);
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
    mut v_00_u03b1_453_: *mut crate::leanh::LeanObject,
    mut v_inst_454_: *mut crate::leanh::LeanObject,
    mut v_a_455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_456_ = l_Lean_Grind_IntModule_OfNatModule_toQ___redArg(v_inst_454_, v_a_455_);
    return v___x_456_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_instLEQOfOrderedAdd(
    mut v_00_u03b1_457_: *mut crate::leanh::LeanObject,
    mut v_inst_458_: *mut crate::leanh::LeanObject,
    mut v_inst_459_: *mut crate::leanh::LeanObject,
    mut v_inst_460_: *mut crate::leanh::LeanObject,
    mut v_inst_461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_462_ = crate::leanh::lean_box(0);
    return v___x_462_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_instLEQOfOrderedAdd___boxed(
    mut v_00_u03b1_463_: *mut crate::leanh::LeanObject,
    mut v_inst_464_: *mut crate::leanh::LeanObject,
    mut v_inst_465_: *mut crate::leanh::LeanObject,
    mut v_inst_466_: *mut crate::leanh::LeanObject,
    mut v_inst_467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_468_ = l_Lean_Grind_IntModule_OfNatModule_instLEQOfOrderedAdd(
        v_00_u03b1_463_,
        v_inst_464_,
        v_inst_465_,
        v_inst_466_,
        v_inst_467_,
    );
    crate::leanh::lean_dec_ref(v_inst_464_);
    return v_res_468_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_instLTQOfOrderedAdd(
    mut v_00_u03b1_469_: *mut crate::leanh::LeanObject,
    mut v_inst_470_: *mut crate::leanh::LeanObject,
    mut v_inst_471_: *mut crate::leanh::LeanObject,
    mut v_inst_472_: *mut crate::leanh::LeanObject,
    mut v_inst_473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_474_ = crate::leanh::lean_box(0);
    return v___x_474_;
}
pub unsafe fn l_Lean_Grind_IntModule_OfNatModule_instLTQOfOrderedAdd___boxed(
    mut v_00_u03b1_475_: *mut crate::leanh::LeanObject,
    mut v_inst_476_: *mut crate::leanh::LeanObject,
    mut v_inst_477_: *mut crate::leanh::LeanObject,
    mut v_inst_478_: *mut crate::leanh::LeanObject,
    mut v_inst_479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_480_ = l_Lean_Grind_IntModule_OfNatModule_instLTQOfOrderedAdd(
        v_00_u03b1_475_,
        v_inst_476_,
        v_inst_477_,
        v_inst_478_,
        v_inst_479_,
    );
    crate::leanh::lean_dec_ref(v_inst_476_);
    return v_res_480_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Module_Envelope(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Ordered_Module(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_AC(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_RCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_Module_Envelope(
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
pub unsafe fn initialize_Init_Grind_Module_Envelope(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Ordered_Module(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_AC(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_RCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Module_Envelope(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Module_Envelope(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Grind_Module_Envelope(builtin);
}
