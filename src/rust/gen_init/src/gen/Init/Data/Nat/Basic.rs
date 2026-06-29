// Lean compiler output
// Module: Init.Data.Nat.Basic
// Imports: Init.SimpLemmas Init.Data.NeZero Init.Grind.Tactics
use crate::ffi::{lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_sub};
use crate::r#gen::Init::Data::NeZero::{
    initialize_Init_Data_NeZero, runtime_initialize_Init_Data_NeZero,
};
use crate::r#gen::Init::Grind::Tactics::{
    initialize_Init_Grind_Tactics, runtime_initialize_Init_Grind_Tactics,
};
use crate::r#gen::Init::SimpLemmas::{
    initialize_Init_SimpLemmas, runtime_initialize_Init_SimpLemmas,
};
pub static mut l_Nat_instTransLt: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Nat_instTransLe: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Nat_instTransLtLe: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Nat_instTransLeLt: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Nat_instMax___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Nat_instMax___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Nat_instMax___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_instMax___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Nat_instMax: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_instMax___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Nat_recCompiled___redArg(
    mut v_zero_237_: *mut crate::leanh::LeanObject,
    mut v_succ_238_: *mut crate::leanh::LeanObject,
    mut v_x_239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_241_: u8 = 0;
    v_zero_240_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_241_ = lean_nat_dec_eq(v_x_239_, v_zero_240_);
    if v_isZero_241_ == 1 {
        crate::leanh::lean_dec(v_succ_238_);
        crate::leanh::lean_inc(v_zero_237_);
        return v_zero_237_;
    } else {
        let mut v_one_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_one_242_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_243_ = lean_nat_sub(v_x_239_, v_one_242_);
        crate::leanh::lean_inc(v_succ_238_);
        v___x_244_ = l_Nat_recCompiled___redArg(v_zero_237_, v_succ_238_, v_n_243_);
        v___x_245_ = crate::leanh::lean_apply_2(v_succ_238_, v_n_243_, v___x_244_);
        return v___x_245_;
    }
}
pub unsafe fn l_Nat_recCompiled___redArg___boxed(
    mut v_zero_246_: *mut crate::leanh::LeanObject,
    mut v_succ_247_: *mut crate::leanh::LeanObject,
    mut v_x_248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_249_ = l_Nat_recCompiled___redArg(v_zero_246_, v_succ_247_, v_x_248_);
    crate::leanh::lean_dec(v_x_248_);
    crate::leanh::lean_dec(v_zero_246_);
    return v_res_249_;
}
pub unsafe fn l_Nat_recCompiled(
    mut v_motive_250_: *mut crate::leanh::LeanObject,
    mut v_zero_251_: *mut crate::leanh::LeanObject,
    mut v_succ_252_: *mut crate::leanh::LeanObject,
    mut v_x_253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_254_ = l_Nat_recCompiled___redArg(v_zero_251_, v_succ_252_, v_x_253_);
    return v___x_254_;
}
pub unsafe fn l_Nat_recCompiled___boxed(
    mut v_motive_255_: *mut crate::leanh::LeanObject,
    mut v_zero_256_: *mut crate::leanh::LeanObject,
    mut v_succ_257_: *mut crate::leanh::LeanObject,
    mut v_x_258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_259_ = l_Nat_recCompiled(v_motive_255_, v_zero_256_, v_succ_257_, v_x_258_);
    crate::leanh::lean_dec(v_x_258_);
    crate::leanh::lean_dec(v_zero_256_);
    return v_res_259_;
}
pub unsafe fn l_Nat_recAux___redArg(
    mut v_zero_260_: *mut crate::leanh::LeanObject,
    mut v_succ_261_: *mut crate::leanh::LeanObject,
    mut v_t_262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_263_ = l_Nat_recCompiled___redArg(v_zero_260_, v_succ_261_, v_t_262_);
    return v___x_263_;
}
pub unsafe fn l_Nat_recAux___redArg___boxed(
    mut v_zero_264_: *mut crate::leanh::LeanObject,
    mut v_succ_265_: *mut crate::leanh::LeanObject,
    mut v_t_266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_267_ = l_Nat_recAux___redArg(v_zero_264_, v_succ_265_, v_t_266_);
    crate::leanh::lean_dec(v_t_266_);
    crate::leanh::lean_dec(v_zero_264_);
    return v_res_267_;
}
pub unsafe fn l_Nat_recAux(
    mut v_motive_268_: *mut crate::leanh::LeanObject,
    mut v_zero_269_: *mut crate::leanh::LeanObject,
    mut v_succ_270_: *mut crate::leanh::LeanObject,
    mut v_t_271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_272_ = l_Nat_recCompiled___redArg(v_zero_269_, v_succ_270_, v_t_271_);
    return v___x_272_;
}
pub unsafe fn l_Nat_recAux___boxed(
    mut v_motive_273_: *mut crate::leanh::LeanObject,
    mut v_zero_274_: *mut crate::leanh::LeanObject,
    mut v_succ_275_: *mut crate::leanh::LeanObject,
    mut v_t_276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_277_ = l_Nat_recAux(v_motive_273_, v_zero_274_, v_succ_275_, v_t_276_);
    crate::leanh::lean_dec(v_t_276_);
    crate::leanh::lean_dec(v_zero_274_);
    return v_res_277_;
}
pub unsafe fn l_Nat_casesAuxOn___redArg(
    mut v_t_278_: *mut crate::leanh::LeanObject,
    mut v_zero_279_: *mut crate::leanh::LeanObject,
    mut v_succ_280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_282_: u8 = 0;
    v_zero_281_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_282_ = lean_nat_dec_eq(v_t_278_, v_zero_281_);
    if v_isZero_282_ == 1 {
        crate::leanh::lean_dec(v_succ_280_);
        crate::leanh::lean_inc(v_zero_279_);
        return v_zero_279_;
    } else {
        let mut v_one_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_one_283_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_284_ = lean_nat_sub(v_t_278_, v_one_283_);
        v___x_285_ = crate::leanh::lean_apply_1(v_succ_280_, v_n_284_);
        return v___x_285_;
    }
}
pub unsafe fn l_Nat_casesAuxOn___redArg___boxed(
    mut v_t_286_: *mut crate::leanh::LeanObject,
    mut v_zero_287_: *mut crate::leanh::LeanObject,
    mut v_succ_288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_289_ = l_Nat_casesAuxOn___redArg(v_t_286_, v_zero_287_, v_succ_288_);
    crate::leanh::lean_dec(v_zero_287_);
    crate::leanh::lean_dec(v_t_286_);
    return v_res_289_;
}
pub unsafe fn l_Nat_casesAuxOn(
    mut v_motive_290_: *mut crate::leanh::LeanObject,
    mut v_t_291_: *mut crate::leanh::LeanObject,
    mut v_zero_292_: *mut crate::leanh::LeanObject,
    mut v_succ_293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_295_: u8 = 0;
    v_zero_294_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_295_ = lean_nat_dec_eq(v_t_291_, v_zero_294_);
    if v_isZero_295_ == 1 {
        crate::leanh::lean_dec(v_succ_293_);
        crate::leanh::lean_inc(v_zero_292_);
        return v_zero_292_;
    } else {
        let mut v_one_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_one_296_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_297_ = lean_nat_sub(v_t_291_, v_one_296_);
        v___x_298_ = crate::leanh::lean_apply_1(v_succ_293_, v_n_297_);
        return v___x_298_;
    }
}
pub unsafe fn l_Nat_casesAuxOn___boxed(
    mut v_motive_299_: *mut crate::leanh::LeanObject,
    mut v_t_300_: *mut crate::leanh::LeanObject,
    mut v_zero_301_: *mut crate::leanh::LeanObject,
    mut v_succ_302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_303_ = l_Nat_casesAuxOn(v_motive_299_, v_t_300_, v_zero_301_, v_succ_302_);
    crate::leanh::lean_dec(v_zero_301_);
    crate::leanh::lean_dec(v_t_300_);
    return v_res_303_;
}
pub unsafe fn l_Nat_repeat___redArg(
    mut v_f_304_: *mut crate::leanh::LeanObject,
    mut v_x_305_: *mut crate::leanh::LeanObject,
    mut v_x_306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_308_: u8 = 0;
    v_zero_307_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_308_ = lean_nat_dec_eq(v_x_305_, v_zero_307_);
    if v_isZero_308_ == 1 {
        crate::leanh::lean_dec(v_f_304_);
        crate::leanh::lean_inc(v_x_306_);
        return v_x_306_;
    } else {
        let mut v_one_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_one_309_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_310_ = lean_nat_sub(v_x_305_, v_one_309_);
        crate::leanh::lean_inc(v_f_304_);
        v___x_311_ = l_Nat_repeat___redArg(v_f_304_, v_n_310_, v_x_306_);
        crate::leanh::lean_dec(v_n_310_);
        v___x_312_ = crate::leanh::lean_apply_1(v_f_304_, v___x_311_);
        return v___x_312_;
    }
}
pub unsafe fn l_Nat_repeat___redArg___boxed(
    mut v_f_313_: *mut crate::leanh::LeanObject,
    mut v_x_314_: *mut crate::leanh::LeanObject,
    mut v_x_315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_316_ = l_Nat_repeat___redArg(v_f_313_, v_x_314_, v_x_315_);
    crate::leanh::lean_dec(v_x_315_);
    crate::leanh::lean_dec(v_x_314_);
    return v_res_316_;
}
pub unsafe fn l_Nat_repeat(
    mut v_00_u03b1_317_: *mut crate::leanh::LeanObject,
    mut v_f_318_: *mut crate::leanh::LeanObject,
    mut v_x_319_: *mut crate::leanh::LeanObject,
    mut v_x_320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_321_ = l_Nat_repeat___redArg(v_f_318_, v_x_319_, v_x_320_);
    return v___x_321_;
}
pub unsafe fn l_Nat_repeat___boxed(
    mut v_00_u03b1_322_: *mut crate::leanh::LeanObject,
    mut v_f_323_: *mut crate::leanh::LeanObject,
    mut v_x_324_: *mut crate::leanh::LeanObject,
    mut v_x_325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_326_ = l_Nat_repeat(v_00_u03b1_322_, v_f_323_, v_x_324_, v_x_325_);
    crate::leanh::lean_dec(v_x_325_);
    crate::leanh::lean_dec(v_x_324_);
    return v_res_326_;
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___redArg(
    mut v_f_327_: *mut crate::leanh::LeanObject,
    mut v_x_328_: *mut crate::leanh::LeanObject,
    mut v_x_329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_331_: u8 = 0;
    let mut v_one_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_330_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_331_ = lean_nat_dec_eq(v_x_328_, v_zero_330_);
                if v_isZero_331_ == 1 {
                    crate::leanh::lean_dec(v_x_328_);
                    crate::leanh::lean_dec(v_f_327_);
                    return v_x_329_;
                } else {
                    v_one_332_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_333_ = lean_nat_sub(v_x_328_, v_one_332_);
                    crate::leanh::lean_dec(v_x_328_);
                    crate::leanh::lean_inc(v_f_327_);
                    v___x_334_ = crate::leanh::lean_apply_1(v_f_327_, v_x_329_);
                    v_x_328_ = v_n_333_;
                    v_x_329_ = v___x_334_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(
    mut v_00_u03b1_336_: *mut crate::leanh::LeanObject,
    mut v_f_337_: *mut crate::leanh::LeanObject,
    mut v_x_338_: *mut crate::leanh::LeanObject,
    mut v_x_339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_340_ =
        l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___redArg(v_f_337_, v_x_338_, v_x_339_);
    return v___x_340_;
}
pub unsafe fn l_Nat_repeatTR___redArg(
    mut v_f_341_: *mut crate::leanh::LeanObject,
    mut v_n_342_: *mut crate::leanh::LeanObject,
    mut v_a_343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_344_ =
        l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___redArg(v_f_341_, v_n_342_, v_a_343_);
    return v___x_344_;
}
pub unsafe fn l_Nat_repeatTR(
    mut v_00_u03b1_345_: *mut crate::leanh::LeanObject,
    mut v_f_346_: *mut crate::leanh::LeanObject,
    mut v_n_347_: *mut crate::leanh::LeanObject,
    mut v_a_348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_349_ =
        l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___redArg(v_f_346_, v_n_347_, v_a_348_);
    return v___x_349_;
}
pub unsafe fn l_Nat_blt(
    mut v_a_350_: *mut crate::leanh::LeanObject,
    mut v_b_351_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: u8 = 0;
    v___x_352_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_353_ = lean_nat_add(v_a_350_, v___x_352_);
    v___x_354_ = lean_nat_dec_le(v___x_353_, v_b_351_);
    crate::leanh::lean_dec(v___x_353_);
    return v___x_354_;
}
pub unsafe fn l_Nat_blt___boxed(
    mut v_a_355_: *mut crate::leanh::LeanObject,
    mut v_b_356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_357_: u8 = 0;
    let mut v_r_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_357_ = l_Nat_blt(v_a_355_, v_b_356_);
    crate::leanh::lean_dec(v_b_356_);
    crate::leanh::lean_dec(v_a_355_);
    v_r_358_ = crate::leanh::lean_box((v_res_357_) as usize);
    return v_r_358_;
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter___redArg(
    mut v_x_359_: *mut crate::leanh::LeanObject,
    mut v_x_360_: *mut crate::leanh::LeanObject,
    mut v_h__1_361_: *mut crate::leanh::LeanObject,
    mut v_h__2_362_: *mut crate::leanh::LeanObject,
    mut v_h__3_363_: *mut crate::leanh::LeanObject,
    mut v_h__4_364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_366_: u8 = 0;
    v_zero_365_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_366_ = lean_nat_dec_eq(v_x_359_, v_zero_365_);
    if v_isZero_366_ == 1 {
        let mut v_isZero_367_: u8 = 0;
        crate::leanh::lean_dec(v_h__4_364_);
        crate::leanh::lean_dec(v_h__3_363_);
        v_isZero_367_ = lean_nat_dec_eq(v_x_360_, v_zero_365_);
        if v_isZero_367_ == 1 {
            let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_362_);
            v___x_368_ = crate::leanh::lean_box(0);
            v___x_369_ = crate::leanh::lean_apply_1(v_h__1_361_, v___x_368_);
            return v___x_369_;
        } else {
            let mut v_one_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_361_);
            v_one_370_ = crate::leanh::lean_unsigned_to_nat(1);
            v_n_371_ = lean_nat_sub(v_x_360_, v_one_370_);
            v___x_372_ = crate::leanh::lean_apply_1(v_h__2_362_, v_n_371_);
            return v___x_372_;
        }
    } else {
        let mut v_one_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_375_: u8 = 0;
        crate::leanh::lean_dec(v_h__2_362_);
        crate::leanh::lean_dec(v_h__1_361_);
        v_one_373_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_374_ = lean_nat_sub(v_x_359_, v_one_373_);
        v_isZero_375_ = lean_nat_dec_eq(v_x_360_, v_zero_365_);
        if v_isZero_375_ == 1 {
            let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_364_);
            v___x_376_ = crate::leanh::lean_apply_1(v_h__3_363_, v_n_374_);
            return v___x_376_;
        } else {
            let mut v_n_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_363_);
            v_n_377_ = lean_nat_sub(v_x_360_, v_one_373_);
            v___x_378_ = crate::leanh::lean_apply_2(v_h__4_364_, v_n_374_, v_n_377_);
            return v___x_378_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter___redArg___boxed(
    mut v_x_379_: *mut crate::leanh::LeanObject,
    mut v_x_380_: *mut crate::leanh::LeanObject,
    mut v_h__1_381_: *mut crate::leanh::LeanObject,
    mut v_h__2_382_: *mut crate::leanh::LeanObject,
    mut v_h__3_383_: *mut crate::leanh::LeanObject,
    mut v_h__4_384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_385_ = l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter___redArg(
        v_x_379_,
        v_x_380_,
        v_h__1_381_,
        v_h__2_382_,
        v_h__3_383_,
        v_h__4_384_,
    );
    crate::leanh::lean_dec(v_x_380_);
    crate::leanh::lean_dec(v_x_379_);
    return v_res_385_;
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter(
    mut v_motive_386_: *mut crate::leanh::LeanObject,
    mut v_x_387_: *mut crate::leanh::LeanObject,
    mut v_x_388_: *mut crate::leanh::LeanObject,
    mut v_h__1_389_: *mut crate::leanh::LeanObject,
    mut v_h__2_390_: *mut crate::leanh::LeanObject,
    mut v_h__3_391_: *mut crate::leanh::LeanObject,
    mut v_h__4_392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_394_: u8 = 0;
    v_zero_393_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_394_ = lean_nat_dec_eq(v_x_387_, v_zero_393_);
    if v_isZero_394_ == 1 {
        let mut v_isZero_395_: u8 = 0;
        crate::leanh::lean_dec(v_h__4_392_);
        crate::leanh::lean_dec(v_h__3_391_);
        v_isZero_395_ = lean_nat_dec_eq(v_x_388_, v_zero_393_);
        if v_isZero_395_ == 1 {
            let mut v___x_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_390_);
            v___x_396_ = crate::leanh::lean_box(0);
            v___x_397_ = crate::leanh::lean_apply_1(v_h__1_389_, v___x_396_);
            return v___x_397_;
        } else {
            let mut v_one_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_389_);
            v_one_398_ = crate::leanh::lean_unsigned_to_nat(1);
            v_n_399_ = lean_nat_sub(v_x_388_, v_one_398_);
            v___x_400_ = crate::leanh::lean_apply_1(v_h__2_390_, v_n_399_);
            return v___x_400_;
        }
    } else {
        let mut v_one_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_403_: u8 = 0;
        crate::leanh::lean_dec(v_h__2_390_);
        crate::leanh::lean_dec(v_h__1_389_);
        v_one_401_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_402_ = lean_nat_sub(v_x_387_, v_one_401_);
        v_isZero_403_ = lean_nat_dec_eq(v_x_388_, v_zero_393_);
        if v_isZero_403_ == 1 {
            let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_392_);
            v___x_404_ = crate::leanh::lean_apply_1(v_h__3_391_, v_n_402_);
            return v___x_404_;
        } else {
            let mut v_n_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_391_);
            v_n_405_ = lean_nat_sub(v_x_388_, v_one_401_);
            v___x_406_ = crate::leanh::lean_apply_2(v_h__4_392_, v_n_402_, v_n_405_);
            return v___x_406_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter___boxed(
    mut v_motive_407_: *mut crate::leanh::LeanObject,
    mut v_x_408_: *mut crate::leanh::LeanObject,
    mut v_x_409_: *mut crate::leanh::LeanObject,
    mut v_h__1_410_: *mut crate::leanh::LeanObject,
    mut v_h__2_411_: *mut crate::leanh::LeanObject,
    mut v_h__3_412_: *mut crate::leanh::LeanObject,
    mut v_h__4_413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_414_ = l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter(
        v_motive_407_,
        v_x_408_,
        v_x_409_,
        v_h__1_410_,
        v_h__2_411_,
        v_h__3_412_,
        v_h__4_413_,
    );
    crate::leanh::lean_dec(v_x_409_);
    crate::leanh::lean_dec(v_x_408_);
    return v_res_414_;
}
pub unsafe fn _init_l_Nat_instTransLt() -> *mut crate::leanh::LeanObject {
    let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_415_ = crate::leanh::lean_box(0);
    return v___x_415_;
}
pub unsafe fn _init_l_Nat_instTransLe() -> *mut crate::leanh::LeanObject {
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_416_ = crate::leanh::lean_box(0);
    return v___x_416_;
}
pub unsafe fn _init_l_Nat_instTransLtLe() -> *mut crate::leanh::LeanObject {
    let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_417_ = crate::leanh::lean_box(0);
    return v___x_417_;
}
pub unsafe fn _init_l_Nat_instTransLeLt() -> *mut crate::leanh::LeanObject {
    let mut v___x_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_418_ = crate::leanh::lean_box(0);
    return v___x_418_;
}
pub unsafe fn l_Nat_min(
    mut v_n_419_: *mut crate::leanh::LeanObject,
    mut v_m_420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_421_: u8 = 0;
    v___x_421_ = lean_nat_dec_le(v_n_419_, v_m_420_);
    if v___x_421_ == 0 {
        crate::leanh::lean_inc(v_m_420_);
        return v_m_420_;
    } else {
        crate::leanh::lean_inc(v_n_419_);
        return v_n_419_;
    }
}
pub unsafe fn l_Nat_min___boxed(
    mut v_n_422_: *mut crate::leanh::LeanObject,
    mut v_m_423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_424_ = l_Nat_min(v_n_422_, v_m_423_);
    crate::leanh::lean_dec(v_m_423_);
    crate::leanh::lean_dec(v_n_422_);
    return v_res_424_;
}
pub unsafe fn l_Nat_instMax___lam__0(
    mut v_x_425_: *mut crate::leanh::LeanObject,
    mut v_y_426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_427_: u8 = 0;
    v___x_427_ = lean_nat_dec_le(v_x_425_, v_y_426_);
    if v___x_427_ == 0 {
        crate::leanh::lean_inc(v_x_425_);
        return v_x_425_;
    } else {
        crate::leanh::lean_inc(v_y_426_);
        return v_y_426_;
    }
}
pub unsafe fn l_Nat_instMax___lam__0___boxed(
    mut v_x_428_: *mut crate::leanh::LeanObject,
    mut v_y_429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_430_ = l_Nat_instMax___lam__0(v_x_428_, v_y_429_);
    crate::leanh::lean_dec(v_y_429_);
    crate::leanh::lean_dec(v_x_428_);
    return v_res_430_;
}
pub unsafe fn l_Nat_max(
    mut v_n_433_: *mut crate::leanh::LeanObject,
    mut v_m_434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_435_: u8 = 0;
    v___x_435_ = lean_nat_dec_le(v_n_433_, v_m_434_);
    if v___x_435_ == 0 {
        crate::leanh::lean_inc(v_n_433_);
        return v_n_433_;
    } else {
        crate::leanh::lean_inc(v_m_434_);
        return v_m_434_;
    }
}
pub unsafe fn l_Nat_max___boxed(
    mut v_n_436_: *mut crate::leanh::LeanObject,
    mut v_m_437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_438_ = l_Nat_max(v_n_436_, v_m_437_);
    crate::leanh::lean_dec(v_m_437_);
    crate::leanh::lean_dec(v_n_436_);
    return v_res_438_;
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_repeat_match__1_splitter___redArg(
    mut v_x_439_: *mut crate::leanh::LeanObject,
    mut v_x_440_: *mut crate::leanh::LeanObject,
    mut v_h__1_441_: *mut crate::leanh::LeanObject,
    mut v_h__2_442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_444_: u8 = 0;
    v_zero_443_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_444_ = lean_nat_dec_eq(v_x_439_, v_zero_443_);
    if v_isZero_444_ == 1 {
        let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_442_);
        v___x_445_ = crate::leanh::lean_apply_1(v_h__1_441_, v_x_440_);
        return v___x_445_;
    } else {
        let mut v_one_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_441_);
        v_one_446_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_447_ = lean_nat_sub(v_x_439_, v_one_446_);
        v___x_448_ = crate::leanh::lean_apply_2(v_h__2_442_, v_n_447_, v_x_440_);
        return v___x_448_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_repeat_match__1_splitter___redArg___boxed(
    mut v_x_449_: *mut crate::leanh::LeanObject,
    mut v_x_450_: *mut crate::leanh::LeanObject,
    mut v_h__1_451_: *mut crate::leanh::LeanObject,
    mut v_h__2_452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_453_ = l___private_Init_Data_Nat_Basic_0__Nat_repeat_match__1_splitter___redArg(
        v_x_449_,
        v_x_450_,
        v_h__1_451_,
        v_h__2_452_,
    );
    crate::leanh::lean_dec(v_x_449_);
    return v_res_453_;
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_repeat_match__1_splitter(
    mut v_00_u03b1_454_: *mut crate::leanh::LeanObject,
    mut v_motive_455_: *mut crate::leanh::LeanObject,
    mut v_x_456_: *mut crate::leanh::LeanObject,
    mut v_x_457_: *mut crate::leanh::LeanObject,
    mut v_h__1_458_: *mut crate::leanh::LeanObject,
    mut v_h__2_459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_461_: u8 = 0;
    v_zero_460_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_461_ = lean_nat_dec_eq(v_x_456_, v_zero_460_);
    if v_isZero_461_ == 1 {
        let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_459_);
        v___x_462_ = crate::leanh::lean_apply_1(v_h__1_458_, v_x_457_);
        return v___x_462_;
    } else {
        let mut v_one_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_458_);
        v_one_463_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_464_ = lean_nat_sub(v_x_456_, v_one_463_);
        v___x_465_ = crate::leanh::lean_apply_2(v_h__2_459_, v_n_464_, v_x_457_);
        return v___x_465_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_repeat_match__1_splitter___boxed(
    mut v_00_u03b1_466_: *mut crate::leanh::LeanObject,
    mut v_motive_467_: *mut crate::leanh::LeanObject,
    mut v_x_468_: *mut crate::leanh::LeanObject,
    mut v_x_469_: *mut crate::leanh::LeanObject,
    mut v_h__1_470_: *mut crate::leanh::LeanObject,
    mut v_h__2_471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_472_ = l___private_Init_Data_Nat_Basic_0__Nat_repeat_match__1_splitter(
        v_00_u03b1_466_,
        v_motive_467_,
        v_x_468_,
        v_x_469_,
        v_h__1_470_,
        v_h__2_471_,
    );
    crate::leanh::lean_dec(v_x_468_);
    return v_res_472_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Nat_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_SimpLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_NeZero(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Nat_instTransLt = _init_l_Nat_instTransLt();
    l_Nat_instTransLe = _init_l_Nat_instTransLe();
    l_Nat_instTransLtLe = _init_l_Nat_instTransLtLe();
    l_Nat_instTransLeLt = _init_l_Nat_instTransLeLt();
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Nat_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Nat_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_SimpLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_NeZero(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Nat_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Nat_Basic(builtin);
}
