// Lean compiler output
// Module: Init.Data.Nat.Basic
// Imports: Init.SimpLemmas Init.Data.NeZero Init.Grind.Tactics
use crate::r#gen::Init::Data::NeZero::{
    initialize_Init_Data_NeZero, runtime_initialize_Init_Data_NeZero,
};
use crate::r#gen::Init::Grind::Tactics::{
    initialize_Init_Grind_Tactics, runtime_initialize_Init_Grind_Tactics,
};
use crate::r#gen::Init::SimpLemmas::{
    initialize_Init_SimpLemmas, runtime_initialize_Init_SimpLemmas,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_sub,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_box, lean_dec, lean_dec_ref,
    lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_unsigned_to_nat,
};
pub static mut l_Nat_instTransLt: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Nat_instTransLe: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Nat_instTransLtLe: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Nat_instTransLeLt: *mut LeanObject = core::ptr::null_mut();
pub static l_Nat_instMax___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Nat_instMax___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Nat_instMax___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Nat_instMax___closed__0_value) as *mut LeanObject;
pub static mut l_Nat_instMax: *mut LeanObject =
    core::ptr::addr_of!(l_Nat_instMax___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Nat_recCompiled___redArg(
    mut v_zero_237_: *mut LeanObject,
    mut v_succ_238_: *mut LeanObject,
    mut v_x_239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_241_: u8 = 0;
    v_zero_240_ = lean_unsigned_to_nat(0);
    v_isZero_241_ = lean_nat_dec_eq(v_x_239_, v_zero_240_);
    if v_isZero_241_ == 1 {
        lean_dec(v_succ_238_);
        lean_inc(v_zero_237_);
        return v_zero_237_;
    } else {
        let mut v_one_242_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_243_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_244_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_245_: *mut LeanObject = core::ptr::null_mut();
        v_one_242_ = lean_unsigned_to_nat(1);
        v_n_243_ = lean_nat_sub(v_x_239_, v_one_242_);
        lean_inc(v_succ_238_);
        v___x_244_ = l_Nat_recCompiled___redArg(v_zero_237_, v_succ_238_, v_n_243_);
        v___x_245_ = lean_apply_2(v_succ_238_, v_n_243_, v___x_244_);
        return v___x_245_;
    }
}
pub unsafe fn l_Nat_recCompiled___redArg___boxed(
    mut v_zero_246_: *mut LeanObject,
    mut v_succ_247_: *mut LeanObject,
    mut v_x_248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_249_: *mut LeanObject = core::ptr::null_mut();
    v_res_249_ = l_Nat_recCompiled___redArg(v_zero_246_, v_succ_247_, v_x_248_);
    lean_dec(v_x_248_);
    lean_dec(v_zero_246_);
    return v_res_249_;
}
pub unsafe fn l_Nat_recCompiled(
    mut v_motive_250_: *mut LeanObject,
    mut v_zero_251_: *mut LeanObject,
    mut v_succ_252_: *mut LeanObject,
    mut v_x_253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_254_: *mut LeanObject = core::ptr::null_mut();
    v___x_254_ = l_Nat_recCompiled___redArg(v_zero_251_, v_succ_252_, v_x_253_);
    return v___x_254_;
}
pub unsafe fn l_Nat_recCompiled___boxed(
    mut v_motive_255_: *mut LeanObject,
    mut v_zero_256_: *mut LeanObject,
    mut v_succ_257_: *mut LeanObject,
    mut v_x_258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_259_: *mut LeanObject = core::ptr::null_mut();
    v_res_259_ = l_Nat_recCompiled(v_motive_255_, v_zero_256_, v_succ_257_, v_x_258_);
    lean_dec(v_x_258_);
    lean_dec(v_zero_256_);
    return v_res_259_;
}
pub unsafe fn l_Nat_recAux___redArg(
    mut v_zero_260_: *mut LeanObject,
    mut v_succ_261_: *mut LeanObject,
    mut v_t_262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_263_: *mut LeanObject = core::ptr::null_mut();
    v___x_263_ = l_Nat_recCompiled___redArg(v_zero_260_, v_succ_261_, v_t_262_);
    return v___x_263_;
}
pub unsafe fn l_Nat_recAux___redArg___boxed(
    mut v_zero_264_: *mut LeanObject,
    mut v_succ_265_: *mut LeanObject,
    mut v_t_266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_267_: *mut LeanObject = core::ptr::null_mut();
    v_res_267_ = l_Nat_recAux___redArg(v_zero_264_, v_succ_265_, v_t_266_);
    lean_dec(v_t_266_);
    lean_dec(v_zero_264_);
    return v_res_267_;
}
pub unsafe fn l_Nat_recAux(
    mut v_motive_268_: *mut LeanObject,
    mut v_zero_269_: *mut LeanObject,
    mut v_succ_270_: *mut LeanObject,
    mut v_t_271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_272_: *mut LeanObject = core::ptr::null_mut();
    v___x_272_ = l_Nat_recCompiled___redArg(v_zero_269_, v_succ_270_, v_t_271_);
    return v___x_272_;
}
pub unsafe fn l_Nat_recAux___boxed(
    mut v_motive_273_: *mut LeanObject,
    mut v_zero_274_: *mut LeanObject,
    mut v_succ_275_: *mut LeanObject,
    mut v_t_276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_277_: *mut LeanObject = core::ptr::null_mut();
    v_res_277_ = l_Nat_recAux(v_motive_273_, v_zero_274_, v_succ_275_, v_t_276_);
    lean_dec(v_t_276_);
    lean_dec(v_zero_274_);
    return v_res_277_;
}
pub unsafe fn l_Nat_casesAuxOn___redArg(
    mut v_t_278_: *mut LeanObject,
    mut v_zero_279_: *mut LeanObject,
    mut v_succ_280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_282_: u8 = 0;
    v_zero_281_ = lean_unsigned_to_nat(0);
    v_isZero_282_ = lean_nat_dec_eq(v_t_278_, v_zero_281_);
    if v_isZero_282_ == 1 {
        lean_dec(v_succ_280_);
        lean_inc(v_zero_279_);
        return v_zero_279_;
    } else {
        let mut v_one_283_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_284_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_285_: *mut LeanObject = core::ptr::null_mut();
        v_one_283_ = lean_unsigned_to_nat(1);
        v_n_284_ = lean_nat_sub(v_t_278_, v_one_283_);
        v___x_285_ = lean_apply_1(v_succ_280_, v_n_284_);
        return v___x_285_;
    }
}
pub unsafe fn l_Nat_casesAuxOn___redArg___boxed(
    mut v_t_286_: *mut LeanObject,
    mut v_zero_287_: *mut LeanObject,
    mut v_succ_288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_289_: *mut LeanObject = core::ptr::null_mut();
    v_res_289_ = l_Nat_casesAuxOn___redArg(v_t_286_, v_zero_287_, v_succ_288_);
    lean_dec(v_zero_287_);
    lean_dec(v_t_286_);
    return v_res_289_;
}
pub unsafe fn l_Nat_casesAuxOn(
    mut v_motive_290_: *mut LeanObject,
    mut v_t_291_: *mut LeanObject,
    mut v_zero_292_: *mut LeanObject,
    mut v_succ_293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_295_: u8 = 0;
    v_zero_294_ = lean_unsigned_to_nat(0);
    v_isZero_295_ = lean_nat_dec_eq(v_t_291_, v_zero_294_);
    if v_isZero_295_ == 1 {
        lean_dec(v_succ_293_);
        lean_inc(v_zero_292_);
        return v_zero_292_;
    } else {
        let mut v_one_296_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_297_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
        v_one_296_ = lean_unsigned_to_nat(1);
        v_n_297_ = lean_nat_sub(v_t_291_, v_one_296_);
        v___x_298_ = lean_apply_1(v_succ_293_, v_n_297_);
        return v___x_298_;
    }
}
pub unsafe fn l_Nat_casesAuxOn___boxed(
    mut v_motive_299_: *mut LeanObject,
    mut v_t_300_: *mut LeanObject,
    mut v_zero_301_: *mut LeanObject,
    mut v_succ_302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_303_: *mut LeanObject = core::ptr::null_mut();
    v_res_303_ = l_Nat_casesAuxOn(v_motive_299_, v_t_300_, v_zero_301_, v_succ_302_);
    lean_dec(v_zero_301_);
    lean_dec(v_t_300_);
    return v_res_303_;
}
pub unsafe fn l_Nat_repeat___redArg(
    mut v_f_304_: *mut LeanObject,
    mut v_x_305_: *mut LeanObject,
    mut v_x_306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_308_: u8 = 0;
    v_zero_307_ = lean_unsigned_to_nat(0);
    v_isZero_308_ = lean_nat_dec_eq(v_x_305_, v_zero_307_);
    if v_isZero_308_ == 1 {
        lean_dec(v_f_304_);
        lean_inc(v_x_306_);
        return v_x_306_;
    } else {
        let mut v_one_309_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_310_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_311_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
        v_one_309_ = lean_unsigned_to_nat(1);
        v_n_310_ = lean_nat_sub(v_x_305_, v_one_309_);
        lean_inc(v_f_304_);
        v___x_311_ = l_Nat_repeat___redArg(v_f_304_, v_n_310_, v_x_306_);
        lean_dec(v_n_310_);
        v___x_312_ = lean_apply_1(v_f_304_, v___x_311_);
        return v___x_312_;
    }
}
pub unsafe fn l_Nat_repeat___redArg___boxed(
    mut v_f_313_: *mut LeanObject,
    mut v_x_314_: *mut LeanObject,
    mut v_x_315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_316_: *mut LeanObject = core::ptr::null_mut();
    v_res_316_ = l_Nat_repeat___redArg(v_f_313_, v_x_314_, v_x_315_);
    lean_dec(v_x_315_);
    lean_dec(v_x_314_);
    return v_res_316_;
}
pub unsafe fn l_Nat_repeat(
    mut v_00_u03b1_317_: *mut LeanObject,
    mut v_f_318_: *mut LeanObject,
    mut v_x_319_: *mut LeanObject,
    mut v_x_320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_321_: *mut LeanObject = core::ptr::null_mut();
    v___x_321_ = l_Nat_repeat___redArg(v_f_318_, v_x_319_, v_x_320_);
    return v___x_321_;
}
pub unsafe fn l_Nat_repeat___boxed(
    mut v_00_u03b1_322_: *mut LeanObject,
    mut v_f_323_: *mut LeanObject,
    mut v_x_324_: *mut LeanObject,
    mut v_x_325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_326_: *mut LeanObject = core::ptr::null_mut();
    v_res_326_ = l_Nat_repeat(v_00_u03b1_322_, v_f_323_, v_x_324_, v_x_325_);
    lean_dec(v_x_325_);
    lean_dec(v_x_324_);
    return v_res_326_;
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___redArg(
    mut v_f_327_: *mut LeanObject,
    mut v_x_328_: *mut LeanObject,
    mut v_x_329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_331_: u8 = 0;
    let mut v_one_332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_330_ = lean_unsigned_to_nat(0);
                v_isZero_331_ = lean_nat_dec_eq(v_x_328_, v_zero_330_);
                if v_isZero_331_ == 1 {
                    lean_dec(v_x_328_);
                    lean_dec(v_f_327_);
                    return v_x_329_;
                } else {
                    v_one_332_ = lean_unsigned_to_nat(1);
                    v_n_333_ = lean_nat_sub(v_x_328_, v_one_332_);
                    lean_dec(v_x_328_);
                    lean_inc(v_f_327_);
                    v___x_334_ = lean_apply_1(v_f_327_, v_x_329_);
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
    mut v_00_u03b1_336_: *mut LeanObject,
    mut v_f_337_: *mut LeanObject,
    mut v_x_338_: *mut LeanObject,
    mut v_x_339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
    v___x_340_ =
        l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___redArg(v_f_337_, v_x_338_, v_x_339_);
    return v___x_340_;
}
pub unsafe fn l_Nat_repeatTR___redArg(
    mut v_f_341_: *mut LeanObject,
    mut v_n_342_: *mut LeanObject,
    mut v_a_343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
    v___x_344_ =
        l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___redArg(v_f_341_, v_n_342_, v_a_343_);
    return v___x_344_;
}
pub unsafe fn l_Nat_repeatTR(
    mut v_00_u03b1_345_: *mut LeanObject,
    mut v_f_346_: *mut LeanObject,
    mut v_n_347_: *mut LeanObject,
    mut v_a_348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
    v___x_349_ =
        l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___redArg(v_f_346_, v_n_347_, v_a_348_);
    return v___x_349_;
}
pub unsafe fn l_Nat_blt(mut v_a_350_: *mut LeanObject, mut v_b_351_: *mut LeanObject) -> u8 {
    let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_354_: u8 = 0;
    v___x_352_ = lean_unsigned_to_nat(1);
    v___x_353_ = lean_nat_add(v_a_350_, v___x_352_);
    v___x_354_ = lean_nat_dec_le(v___x_353_, v_b_351_);
    lean_dec(v___x_353_);
    return v___x_354_;
}
pub unsafe fn l_Nat_blt___boxed(
    mut v_a_355_: *mut LeanObject,
    mut v_b_356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_357_: u8 = 0;
    let mut v_r_358_: *mut LeanObject = core::ptr::null_mut();
    v_res_357_ = l_Nat_blt(v_a_355_, v_b_356_);
    lean_dec(v_b_356_);
    lean_dec(v_a_355_);
    v_r_358_ = lean_box((v_res_357_) as usize);
    return v_r_358_;
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter___redArg(
    mut v_x_359_: *mut LeanObject,
    mut v_x_360_: *mut LeanObject,
    mut v_h__1_361_: *mut LeanObject,
    mut v_h__2_362_: *mut LeanObject,
    mut v_h__3_363_: *mut LeanObject,
    mut v_h__4_364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_366_: u8 = 0;
    v_zero_365_ = lean_unsigned_to_nat(0);
    v_isZero_366_ = lean_nat_dec_eq(v_x_359_, v_zero_365_);
    if v_isZero_366_ == 1 {
        let mut v_isZero_367_: u8 = 0;
        lean_dec(v_h__4_364_);
        lean_dec(v_h__3_363_);
        v_isZero_367_ = lean_nat_dec_eq(v_x_360_, v_zero_365_);
        if v_isZero_367_ == 1 {
            let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_369_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_362_);
            v___x_368_ = lean_box(0);
            v___x_369_ = lean_apply_1(v_h__1_361_, v___x_368_);
            return v___x_369_;
        } else {
            let mut v_one_370_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_371_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_372_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_361_);
            v_one_370_ = lean_unsigned_to_nat(1);
            v_n_371_ = lean_nat_sub(v_x_360_, v_one_370_);
            v___x_372_ = lean_apply_1(v_h__2_362_, v_n_371_);
            return v___x_372_;
        }
    } else {
        let mut v_one_373_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_374_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_375_: u8 = 0;
        lean_dec(v_h__2_362_);
        lean_dec(v_h__1_361_);
        v_one_373_ = lean_unsigned_to_nat(1);
        v_n_374_ = lean_nat_sub(v_x_359_, v_one_373_);
        v_isZero_375_ = lean_nat_dec_eq(v_x_360_, v_zero_365_);
        if v_isZero_375_ == 1 {
            let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_364_);
            v___x_376_ = lean_apply_1(v_h__3_363_, v_n_374_);
            return v___x_376_;
        } else {
            let mut v_n_377_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_378_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_363_);
            v_n_377_ = lean_nat_sub(v_x_360_, v_one_373_);
            v___x_378_ = lean_apply_2(v_h__4_364_, v_n_374_, v_n_377_);
            return v___x_378_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter___redArg___boxed(
    mut v_x_379_: *mut LeanObject,
    mut v_x_380_: *mut LeanObject,
    mut v_h__1_381_: *mut LeanObject,
    mut v_h__2_382_: *mut LeanObject,
    mut v_h__3_383_: *mut LeanObject,
    mut v_h__4_384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_385_: *mut LeanObject = core::ptr::null_mut();
    v_res_385_ = l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter___redArg(
        v_x_379_,
        v_x_380_,
        v_h__1_381_,
        v_h__2_382_,
        v_h__3_383_,
        v_h__4_384_,
    );
    lean_dec(v_x_380_);
    lean_dec(v_x_379_);
    return v_res_385_;
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter(
    mut v_motive_386_: *mut LeanObject,
    mut v_x_387_: *mut LeanObject,
    mut v_x_388_: *mut LeanObject,
    mut v_h__1_389_: *mut LeanObject,
    mut v_h__2_390_: *mut LeanObject,
    mut v_h__3_391_: *mut LeanObject,
    mut v_h__4_392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_394_: u8 = 0;
    v_zero_393_ = lean_unsigned_to_nat(0);
    v_isZero_394_ = lean_nat_dec_eq(v_x_387_, v_zero_393_);
    if v_isZero_394_ == 1 {
        let mut v_isZero_395_: u8 = 0;
        lean_dec(v_h__4_392_);
        lean_dec(v_h__3_391_);
        v_isZero_395_ = lean_nat_dec_eq(v_x_388_, v_zero_393_);
        if v_isZero_395_ == 1 {
            let mut v___x_396_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_390_);
            v___x_396_ = lean_box(0);
            v___x_397_ = lean_apply_1(v_h__1_389_, v___x_396_);
            return v___x_397_;
        } else {
            let mut v_one_398_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_399_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_400_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_389_);
            v_one_398_ = lean_unsigned_to_nat(1);
            v_n_399_ = lean_nat_sub(v_x_388_, v_one_398_);
            v___x_400_ = lean_apply_1(v_h__2_390_, v_n_399_);
            return v___x_400_;
        }
    } else {
        let mut v_one_401_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_402_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_403_: u8 = 0;
        lean_dec(v_h__2_390_);
        lean_dec(v_h__1_389_);
        v_one_401_ = lean_unsigned_to_nat(1);
        v_n_402_ = lean_nat_sub(v_x_387_, v_one_401_);
        v_isZero_403_ = lean_nat_dec_eq(v_x_388_, v_zero_393_);
        if v_isZero_403_ == 1 {
            let mut v___x_404_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_392_);
            v___x_404_ = lean_apply_1(v_h__3_391_, v_n_402_);
            return v___x_404_;
        } else {
            let mut v_n_405_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_406_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_391_);
            v_n_405_ = lean_nat_sub(v_x_388_, v_one_401_);
            v___x_406_ = lean_apply_2(v_h__4_392_, v_n_402_, v_n_405_);
            return v___x_406_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter___boxed(
    mut v_motive_407_: *mut LeanObject,
    mut v_x_408_: *mut LeanObject,
    mut v_x_409_: *mut LeanObject,
    mut v_h__1_410_: *mut LeanObject,
    mut v_h__2_411_: *mut LeanObject,
    mut v_h__3_412_: *mut LeanObject,
    mut v_h__4_413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_414_: *mut LeanObject = core::ptr::null_mut();
    v_res_414_ = l___private_Init_Data_Nat_Basic_0__Nat_beq_match__1_splitter(
        v_motive_407_,
        v_x_408_,
        v_x_409_,
        v_h__1_410_,
        v_h__2_411_,
        v_h__3_412_,
        v_h__4_413_,
    );
    lean_dec(v_x_409_);
    lean_dec(v_x_408_);
    return v_res_414_;
}
pub unsafe fn _init_l_Nat_instTransLt() -> *mut LeanObject {
    let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
    v___x_415_ = lean_box(0);
    return v___x_415_;
}
pub unsafe fn _init_l_Nat_instTransLe() -> *mut LeanObject {
    let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
    v___x_416_ = lean_box(0);
    return v___x_416_;
}
pub unsafe fn _init_l_Nat_instTransLtLe() -> *mut LeanObject {
    let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
    v___x_417_ = lean_box(0);
    return v___x_417_;
}
pub unsafe fn _init_l_Nat_instTransLeLt() -> *mut LeanObject {
    let mut v___x_418_: *mut LeanObject = core::ptr::null_mut();
    v___x_418_ = lean_box(0);
    return v___x_418_;
}
pub unsafe fn l_Nat_min(
    mut v_n_419_: *mut LeanObject,
    mut v_m_420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_421_: u8 = 0;
    v___x_421_ = lean_nat_dec_le(v_n_419_, v_m_420_);
    if v___x_421_ == 0 {
        lean_inc(v_m_420_);
        return v_m_420_;
    } else {
        lean_inc(v_n_419_);
        return v_n_419_;
    }
}
pub unsafe fn l_Nat_min___boxed(
    mut v_n_422_: *mut LeanObject,
    mut v_m_423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_424_: *mut LeanObject = core::ptr::null_mut();
    v_res_424_ = l_Nat_min(v_n_422_, v_m_423_);
    lean_dec(v_m_423_);
    lean_dec(v_n_422_);
    return v_res_424_;
}
pub unsafe fn l_Nat_instMax___lam__0(
    mut v_x_425_: *mut LeanObject,
    mut v_y_426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_427_: u8 = 0;
    v___x_427_ = lean_nat_dec_le(v_x_425_, v_y_426_);
    if v___x_427_ == 0 {
        lean_inc(v_x_425_);
        return v_x_425_;
    } else {
        lean_inc(v_y_426_);
        return v_y_426_;
    }
}
pub unsafe fn l_Nat_instMax___lam__0___boxed(
    mut v_x_428_: *mut LeanObject,
    mut v_y_429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_430_: *mut LeanObject = core::ptr::null_mut();
    v_res_430_ = l_Nat_instMax___lam__0(v_x_428_, v_y_429_);
    lean_dec(v_y_429_);
    lean_dec(v_x_428_);
    return v_res_430_;
}
pub unsafe fn l_Nat_max(
    mut v_n_433_: *mut LeanObject,
    mut v_m_434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_435_: u8 = 0;
    v___x_435_ = lean_nat_dec_le(v_n_433_, v_m_434_);
    if v___x_435_ == 0 {
        lean_inc(v_n_433_);
        return v_n_433_;
    } else {
        lean_inc(v_m_434_);
        return v_m_434_;
    }
}
pub unsafe fn l_Nat_max___boxed(
    mut v_n_436_: *mut LeanObject,
    mut v_m_437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_438_: *mut LeanObject = core::ptr::null_mut();
    v_res_438_ = l_Nat_max(v_n_436_, v_m_437_);
    lean_dec(v_m_437_);
    lean_dec(v_n_436_);
    return v_res_438_;
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_repeat_match__1_splitter___redArg(
    mut v_x_439_: *mut LeanObject,
    mut v_x_440_: *mut LeanObject,
    mut v_h__1_441_: *mut LeanObject,
    mut v_h__2_442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_444_: u8 = 0;
    v_zero_443_ = lean_unsigned_to_nat(0);
    v_isZero_444_ = lean_nat_dec_eq(v_x_439_, v_zero_443_);
    if v_isZero_444_ == 1 {
        let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_442_);
        v___x_445_ = lean_apply_1(v_h__1_441_, v_x_440_);
        return v___x_445_;
    } else {
        let mut v_one_446_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_447_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_441_);
        v_one_446_ = lean_unsigned_to_nat(1);
        v_n_447_ = lean_nat_sub(v_x_439_, v_one_446_);
        v___x_448_ = lean_apply_2(v_h__2_442_, v_n_447_, v_x_440_);
        return v___x_448_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_repeat_match__1_splitter___redArg___boxed(
    mut v_x_449_: *mut LeanObject,
    mut v_x_450_: *mut LeanObject,
    mut v_h__1_451_: *mut LeanObject,
    mut v_h__2_452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_453_: *mut LeanObject = core::ptr::null_mut();
    v_res_453_ = l___private_Init_Data_Nat_Basic_0__Nat_repeat_match__1_splitter___redArg(
        v_x_449_,
        v_x_450_,
        v_h__1_451_,
        v_h__2_452_,
    );
    lean_dec(v_x_449_);
    return v_res_453_;
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_repeat_match__1_splitter(
    mut v_00_u03b1_454_: *mut LeanObject,
    mut v_motive_455_: *mut LeanObject,
    mut v_x_456_: *mut LeanObject,
    mut v_x_457_: *mut LeanObject,
    mut v_h__1_458_: *mut LeanObject,
    mut v_h__2_459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_461_: u8 = 0;
    v_zero_460_ = lean_unsigned_to_nat(0);
    v_isZero_461_ = lean_nat_dec_eq(v_x_456_, v_zero_460_);
    if v_isZero_461_ == 1 {
        let mut v___x_462_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_459_);
        v___x_462_ = lean_apply_1(v_h__1_458_, v_x_457_);
        return v___x_462_;
    } else {
        let mut v_one_463_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_464_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_465_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_458_);
        v_one_463_ = lean_unsigned_to_nat(1);
        v_n_464_ = lean_nat_sub(v_x_456_, v_one_463_);
        v___x_465_ = lean_apply_2(v_h__2_459_, v_n_464_, v_x_457_);
        return v___x_465_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_repeat_match__1_splitter___boxed(
    mut v_00_u03b1_466_: *mut LeanObject,
    mut v_motive_467_: *mut LeanObject,
    mut v_x_468_: *mut LeanObject,
    mut v_x_469_: *mut LeanObject,
    mut v_h__1_470_: *mut LeanObject,
    mut v_h__2_471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_472_: *mut LeanObject = core::ptr::null_mut();
    v_res_472_ = l___private_Init_Data_Nat_Basic_0__Nat_repeat_match__1_splitter(
        v_00_u03b1_466_,
        v_motive_467_,
        v_x_468_,
        v_x_469_,
        v_h__1_470_,
        v_h__2_471_,
    );
    lean_dec(v_x_468_);
    return v_res_472_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Nat_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_SimpLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_NeZero(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Nat_instTransLt = _init_l_Nat_instTransLt();
    l_Nat_instTransLe = _init_l_Nat_instTransLe();
    l_Nat_instTransLtLe = _init_l_Nat_instTransLtLe();
    l_Nat_instTransLeLt = _init_l_Nat_instTransLeLt();
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Nat_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Nat_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_SimpLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_NeZero(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Nat_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Nat_Basic(builtin);
}
