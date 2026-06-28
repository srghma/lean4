// Lean compiler output
// Module: Init.Data.Nat.Lemmas
// Imports: Init.Data.Nat.Bitwise.Basic Init.Data.Nat.Log2 Init.Data.Nat.Log2 Init.TacticsExtra Init.Data.Nat.Div.Basic Init.PropLemmas Init.ByCases Init.Data.Nat.Dvd Init.Data.Nat.Linear Init.Data.Nat.MinMax Init.Data.Nat.Mod Init.Omega Init.RCases
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Nat::Bitwise::Basic::{
    initialize_Init_Data_Nat_Bitwise_Basic, runtime_initialize_Init_Data_Nat_Bitwise_Basic,
};
use crate::r#gen::Init::Data::Nat::Div::Basic::{
    initialize_Init_Data_Nat_Div_Basic, runtime_initialize_Init_Data_Nat_Div_Basic,
};
use crate::r#gen::Init::Data::Nat::Dvd::{
    initialize_Init_Data_Nat_Dvd, runtime_initialize_Init_Data_Nat_Dvd,
};
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::Data::Nat::Log2::{
    initialize_Init_Data_Nat_Log2, runtime_initialize_Init_Data_Nat_Log2,
};
use crate::r#gen::Init::Data::Nat::MinMax::{
    initialize_Init_Data_Nat_MinMax, runtime_initialize_Init_Data_Nat_MinMax,
};
use crate::r#gen::Init::Data::Nat::Mod::{
    initialize_Init_Data_Nat_Mod, runtime_initialize_Init_Data_Nat_Mod,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::PropLemmas::{
    initialize_Init_PropLemmas, runtime_initialize_Init_PropLemmas,
};
use crate::r#gen::Init::RCases::{initialize_Init_RCases, runtime_initialize_Init_RCases};
use crate::r#gen::Init::TacticsExtra::{
    initialize_Init_TacticsExtra, runtime_initialize_Init_TacticsExtra,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub,
};
pub unsafe fn l_Nat_decidableBallLT___redArg___lam__0(
    mut v_x_213_: *mut crate::leanh::LeanObject,
    mut v_n_214_: *mut crate::leanh::LeanObject,
    mut v_h_215_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: u8 = 0;
    v___x_216_ = crate::leanh::lean_apply_2(v_x_213_, v_n_214_, crate::leanh::lean_box(0));
    v___x_217_ = (crate::leanh::lean_unbox(v___x_216_) as u8);
    return v___x_217_;
}
pub unsafe fn l_Nat_decidableBallLT___redArg___lam__0___boxed(
    mut v_x_218_: *mut crate::leanh::LeanObject,
    mut v_n_219_: *mut crate::leanh::LeanObject,
    mut v_h_220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_221_: u8 = 0;
    let mut v_r_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_221_ = l_Nat_decidableBallLT___redArg___lam__0(v_x_218_, v_n_219_, v_h_220_);
    v_r_222_ = crate::leanh::lean_box((v_res_221_) as usize);
    return v_r_222_;
}
pub unsafe fn l_Nat_decidableBallLT___redArg(
    mut v_x_223_: *mut crate::leanh::LeanObject,
    mut v_x_224_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_226_: u8 = 0;
    v_zero_225_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_226_ = lean_nat_dec_eq(v_x_223_, v_zero_225_);
    if v_isZero_226_ == 1 {
        crate::leanh::lean_dec_ref(v_x_224_);
        return v_isZero_226_;
    } else {
        let mut v___f_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_230_: u8 = 0;
        crate::leanh::lean_inc_ref(v_x_224_);
        v___f_227_ = crate::leanh::lean_alloc_closure(
            l_Nat_decidableBallLT___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_227_, 0, v_x_224_);
        v_one_228_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_229_ = lean_nat_sub(v_x_223_, v_one_228_);
        v___x_230_ = l_Nat_decidableBallLT___redArg(v_n_229_, v___f_227_);
        if v___x_230_ == 0 {
            crate::leanh::lean_dec(v_n_229_);
            crate::leanh::lean_dec_ref(v_x_224_);
            return v___x_230_;
        } else {
            let mut v___x_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_232_: u8 = 0;
            v___x_231_ = crate::leanh::lean_apply_2(v_x_224_, v_n_229_, crate::leanh::lean_box(0));
            v___x_232_ = (crate::leanh::lean_unbox(v___x_231_) as u8);
            return v___x_232_;
        }
    }
}
pub unsafe fn l_Nat_decidableBallLT___redArg___boxed(
    mut v_x_233_: *mut crate::leanh::LeanObject,
    mut v_x_234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_235_: u8 = 0;
    let mut v_r_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_235_ = l_Nat_decidableBallLT___redArg(v_x_233_, v_x_234_);
    crate::leanh::lean_dec(v_x_233_);
    v_r_236_ = crate::leanh::lean_box((v_res_235_) as usize);
    return v_r_236_;
}
pub unsafe fn l_Nat_decidableBallLT(
    mut v_x_237_: *mut crate::leanh::LeanObject,
    mut v_x_238_: *mut crate::leanh::LeanObject,
    mut v_x_239_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_240_: u8 = 0;
    v___x_240_ = l_Nat_decidableBallLT___redArg(v_x_237_, v_x_239_);
    return v___x_240_;
}
pub unsafe fn l_Nat_decidableBallLT___boxed(
    mut v_x_241_: *mut crate::leanh::LeanObject,
    mut v_x_242_: *mut crate::leanh::LeanObject,
    mut v_x_243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_244_: u8 = 0;
    let mut v_r_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_244_ = l_Nat_decidableBallLT(v_x_241_, v_x_242_, v_x_243_);
    crate::leanh::lean_dec(v_x_241_);
    v_r_245_ = crate::leanh::lean_box((v_res_244_) as usize);
    return v_r_245_;
}
pub unsafe fn l_Nat_decidableForallFin___redArg___lam__0(
    mut v_inst_246_: *mut crate::leanh::LeanObject,
    mut v_n_247_: *mut crate::leanh::LeanObject,
    mut v_h_248_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: u8 = 0;
    v___x_249_ = crate::leanh::lean_apply_1(v_inst_246_, v_n_247_);
    v___x_250_ = (crate::leanh::lean_unbox(v___x_249_) as u8);
    return v___x_250_;
}
pub unsafe fn l_Nat_decidableForallFin___redArg___lam__0___boxed(
    mut v_inst_251_: *mut crate::leanh::LeanObject,
    mut v_n_252_: *mut crate::leanh::LeanObject,
    mut v_h_253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_254_: u8 = 0;
    let mut v_r_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_254_ = l_Nat_decidableForallFin___redArg___lam__0(v_inst_251_, v_n_252_, v_h_253_);
    v_r_255_ = crate::leanh::lean_box((v_res_254_) as usize);
    return v_r_255_;
}
pub unsafe fn l_Nat_decidableForallFin___redArg(
    mut v_n_256_: *mut crate::leanh::LeanObject,
    mut v_inst_257_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_259_: u8 = 0;
    v___f_258_ = crate::leanh::lean_alloc_closure(
        l_Nat_decidableForallFin___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_258_, 0, v_inst_257_);
    v___x_259_ = l_Nat_decidableBallLT___redArg(v_n_256_, v___f_258_);
    return v___x_259_;
}
pub unsafe fn l_Nat_decidableForallFin___redArg___boxed(
    mut v_n_260_: *mut crate::leanh::LeanObject,
    mut v_inst_261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_262_: u8 = 0;
    let mut v_r_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_262_ = l_Nat_decidableForallFin___redArg(v_n_260_, v_inst_261_);
    crate::leanh::lean_dec(v_n_260_);
    v_r_263_ = crate::leanh::lean_box((v_res_262_) as usize);
    return v_r_263_;
}
pub unsafe fn l_Nat_decidableForallFin(
    mut v_n_264_: *mut crate::leanh::LeanObject,
    mut v_P_265_: *mut crate::leanh::LeanObject,
    mut v_inst_266_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_267_: u8 = 0;
    v___x_267_ = l_Nat_decidableForallFin___redArg(v_n_264_, v_inst_266_);
    return v___x_267_;
}
pub unsafe fn l_Nat_decidableForallFin___boxed(
    mut v_n_268_: *mut crate::leanh::LeanObject,
    mut v_P_269_: *mut crate::leanh::LeanObject,
    mut v_inst_270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_271_: u8 = 0;
    let mut v_r_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_271_ = l_Nat_decidableForallFin(v_n_268_, v_P_269_, v_inst_270_);
    crate::leanh::lean_dec(v_n_268_);
    v_r_272_ = crate::leanh::lean_box((v_res_271_) as usize);
    return v_r_272_;
}
pub unsafe fn l_Nat_decidableBallLE___redArg___lam__0(
    mut v_inst_273_: *mut crate::leanh::LeanObject,
    mut v_n_274_: *mut crate::leanh::LeanObject,
    mut v_h_275_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_277_: u8 = 0;
    v___x_276_ = crate::leanh::lean_apply_2(v_inst_273_, v_n_274_, crate::leanh::lean_box(0));
    v___x_277_ = (crate::leanh::lean_unbox(v___x_276_) as u8);
    return v___x_277_;
}
pub unsafe fn l_Nat_decidableBallLE___redArg___lam__0___boxed(
    mut v_inst_278_: *mut crate::leanh::LeanObject,
    mut v_n_279_: *mut crate::leanh::LeanObject,
    mut v_h_280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_281_: u8 = 0;
    let mut v_r_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_281_ = l_Nat_decidableBallLE___redArg___lam__0(v_inst_278_, v_n_279_, v_h_280_);
    v_r_282_ = crate::leanh::lean_box((v_res_281_) as usize);
    return v_r_282_;
}
pub unsafe fn l_Nat_decidableBallLE___redArg(
    mut v_n_283_: *mut crate::leanh::LeanObject,
    mut v_inst_284_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_288_: u8 = 0;
    v___f_285_ = crate::leanh::lean_alloc_closure(
        l_Nat_decidableBallLE___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_285_, 0, v_inst_284_);
    v___x_286_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_287_ = lean_nat_add(v_n_283_, v___x_286_);
    v___x_288_ = l_Nat_decidableBallLT___redArg(v___x_287_, v___f_285_);
    crate::leanh::lean_dec(v___x_287_);
    return v___x_288_;
}
pub unsafe fn l_Nat_decidableBallLE___redArg___boxed(
    mut v_n_289_: *mut crate::leanh::LeanObject,
    mut v_inst_290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_291_: u8 = 0;
    let mut v_r_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_291_ = l_Nat_decidableBallLE___redArg(v_n_289_, v_inst_290_);
    crate::leanh::lean_dec(v_n_289_);
    v_r_292_ = crate::leanh::lean_box((v_res_291_) as usize);
    return v_r_292_;
}
pub unsafe fn l_Nat_decidableBallLE(
    mut v_n_293_: *mut crate::leanh::LeanObject,
    mut v_P_294_: *mut crate::leanh::LeanObject,
    mut v_inst_295_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_296_: u8 = 0;
    v___x_296_ = l_Nat_decidableBallLE___redArg(v_n_293_, v_inst_295_);
    return v___x_296_;
}
pub unsafe fn l_Nat_decidableBallLE___boxed(
    mut v_n_297_: *mut crate::leanh::LeanObject,
    mut v_P_298_: *mut crate::leanh::LeanObject,
    mut v_inst_299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_300_: u8 = 0;
    let mut v_r_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_300_ = l_Nat_decidableBallLE(v_n_297_, v_P_298_, v_inst_299_);
    crate::leanh::lean_dec(v_n_297_);
    v_r_301_ = crate::leanh::lean_box((v_res_300_) as usize);
    return v_r_301_;
}
pub unsafe fn l_Nat_decidableExistsLT___redArg(
    mut v_h_302_: *mut crate::leanh::LeanObject,
    mut v_x_303_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_305_: u8 = 0;
    v_zero_304_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_305_ = lean_nat_dec_eq(v_x_303_, v_zero_304_);
    if v_isZero_305_ == 1 {
        let mut v___x_306_: u8 = 0;
        crate::leanh::lean_dec_ref(v_h_302_);
        v___x_306_ = 0;
        return v___x_306_;
    } else {
        let mut v_one_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_310_: u8 = 0;
        v_one_307_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_308_ = lean_nat_sub(v_x_303_, v_one_307_);
        crate::leanh::lean_inc_ref(v_h_302_);
        crate::leanh::lean_inc(v_n_308_);
        v___x_309_ = crate::leanh::lean_apply_1(v_h_302_, v_n_308_);
        v___x_310_ = l_Nat_decidableExistsLT___redArg(v_h_302_, v_n_308_);
        crate::leanh::lean_dec(v_n_308_);
        if v___x_310_ == 0 {
            let mut v___x_311_: u8 = 0;
            v___x_311_ = (crate::leanh::lean_unbox(v___x_309_) as u8);
            return v___x_311_;
        } else {
            return v___x_310_;
        }
    }
}
pub unsafe fn l_Nat_decidableExistsLT___redArg___boxed(
    mut v_h_312_: *mut crate::leanh::LeanObject,
    mut v_x_313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_314_: u8 = 0;
    let mut v_r_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_314_ = l_Nat_decidableExistsLT___redArg(v_h_312_, v_x_313_);
    crate::leanh::lean_dec(v_x_313_);
    v_r_315_ = crate::leanh::lean_box((v_res_314_) as usize);
    return v_r_315_;
}
pub unsafe fn l_Nat_decidableExistsLT(
    mut v_p_316_: *mut crate::leanh::LeanObject,
    mut v_h_317_: *mut crate::leanh::LeanObject,
    mut v_x_318_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_319_: u8 = 0;
    v___x_319_ = l_Nat_decidableExistsLT___redArg(v_h_317_, v_x_318_);
    return v___x_319_;
}
pub unsafe fn l_Nat_decidableExistsLT___boxed(
    mut v_p_320_: *mut crate::leanh::LeanObject,
    mut v_h_321_: *mut crate::leanh::LeanObject,
    mut v_x_322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_323_: u8 = 0;
    let mut v_r_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_323_ = l_Nat_decidableExistsLT(v_p_320_, v_h_321_, v_x_322_);
    crate::leanh::lean_dec(v_x_322_);
    v_r_324_ = crate::leanh::lean_box((v_res_323_) as usize);
    return v_r_324_;
}
pub unsafe fn l_Nat_decidableExistsLE___redArg(
    mut v_inst_325_: *mut crate::leanh::LeanObject,
    mut v_n_326_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_329_: u8 = 0;
    v___x_327_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_328_ = lean_nat_add(v_n_326_, v___x_327_);
    v___x_329_ = l_Nat_decidableExistsLT___redArg(v_inst_325_, v___x_328_);
    crate::leanh::lean_dec(v___x_328_);
    return v___x_329_;
}
pub unsafe fn l_Nat_decidableExistsLE___redArg___boxed(
    mut v_inst_330_: *mut crate::leanh::LeanObject,
    mut v_n_331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_332_: u8 = 0;
    let mut v_r_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_332_ = l_Nat_decidableExistsLE___redArg(v_inst_330_, v_n_331_);
    crate::leanh::lean_dec(v_n_331_);
    v_r_333_ = crate::leanh::lean_box((v_res_332_) as usize);
    return v_r_333_;
}
pub unsafe fn l_Nat_decidableExistsLE(
    mut v_p_334_: *mut crate::leanh::LeanObject,
    mut v_inst_335_: *mut crate::leanh::LeanObject,
    mut v_n_336_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_337_: u8 = 0;
    v___x_337_ = l_Nat_decidableExistsLE___redArg(v_inst_335_, v_n_336_);
    return v___x_337_;
}
pub unsafe fn l_Nat_decidableExistsLE___boxed(
    mut v_p_338_: *mut crate::leanh::LeanObject,
    mut v_inst_339_: *mut crate::leanh::LeanObject,
    mut v_n_340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_341_: u8 = 0;
    let mut v_r_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_341_ = l_Nat_decidableExistsLE(v_p_338_, v_inst_339_, v_n_340_);
    crate::leanh::lean_dec(v_n_340_);
    v_r_342_ = crate::leanh::lean_box((v_res_341_) as usize);
    return v_r_342_;
}
pub unsafe fn l_Nat_decidableExistsLT_x27___redArg___lam__0(
    mut v_I_343_: *mut crate::leanh::LeanObject,
    mut v_m_344_: *mut crate::leanh::LeanObject,
    mut v_h_345_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: u8 = 0;
    v___x_346_ = crate::leanh::lean_apply_2(v_I_343_, v_m_344_, crate::leanh::lean_box(0));
    v___x_347_ = (crate::leanh::lean_unbox(v___x_346_) as u8);
    return v___x_347_;
}
pub unsafe fn l_Nat_decidableExistsLT_x27___redArg___lam__0___boxed(
    mut v_I_348_: *mut crate::leanh::LeanObject,
    mut v_m_349_: *mut crate::leanh::LeanObject,
    mut v_h_350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_351_: u8 = 0;
    let mut v_r_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_351_ = l_Nat_decidableExistsLT_x27___redArg___lam__0(v_I_348_, v_m_349_, v_h_350_);
    v_r_352_ = crate::leanh::lean_box((v_res_351_) as usize);
    return v_r_352_;
}
pub unsafe fn l_Nat_decidableExistsLT_x27___redArg(
    mut v_k_353_: *mut crate::leanh::LeanObject,
    mut v_I_354_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_356_: u8 = 0;
    v_zero_355_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_356_ = lean_nat_dec_eq(v_k_353_, v_zero_355_);
    if v_isZero_356_ == 1 {
        let mut v___x_357_: u8 = 0;
        crate::leanh::lean_dec_ref(v_I_354_);
        v___x_357_ = 0;
        return v___x_357_;
    } else {
        let mut v___f_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_361_: u8 = 0;
        crate::leanh::lean_inc_ref(v_I_354_);
        v___f_358_ = crate::leanh::lean_alloc_closure(
            l_Nat_decidableExistsLT_x27___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_358_, 0, v_I_354_);
        v_one_359_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_360_ = lean_nat_sub(v_k_353_, v_one_359_);
        v___x_361_ = l_Nat_decidableExistsLT_x27___redArg(v_n_360_, v___f_358_);
        if v___x_361_ == 0 {
            let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_363_: u8 = 0;
            v___x_362_ = crate::leanh::lean_apply_2(v_I_354_, v_n_360_, crate::leanh::lean_box(0));
            v___x_363_ = (crate::leanh::lean_unbox(v___x_362_) as u8);
            return v___x_363_;
        } else {
            crate::leanh::lean_dec(v_n_360_);
            crate::leanh::lean_dec_ref(v_I_354_);
            return v___x_361_;
        }
    }
}
pub unsafe fn l_Nat_decidableExistsLT_x27___redArg___boxed(
    mut v_k_364_: *mut crate::leanh::LeanObject,
    mut v_I_365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_366_: u8 = 0;
    let mut v_r_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_366_ = l_Nat_decidableExistsLT_x27___redArg(v_k_364_, v_I_365_);
    crate::leanh::lean_dec(v_k_364_);
    v_r_367_ = crate::leanh::lean_box((v_res_366_) as usize);
    return v_r_367_;
}
pub unsafe fn l_Nat_decidableExistsLT_x27(
    mut v_k_368_: *mut crate::leanh::LeanObject,
    mut v_p_369_: *mut crate::leanh::LeanObject,
    mut v_I_370_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_371_: u8 = 0;
    v___x_371_ = l_Nat_decidableExistsLT_x27___redArg(v_k_368_, v_I_370_);
    return v___x_371_;
}
pub unsafe fn l_Nat_decidableExistsLT_x27___boxed(
    mut v_k_372_: *mut crate::leanh::LeanObject,
    mut v_p_373_: *mut crate::leanh::LeanObject,
    mut v_I_374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_375_: u8 = 0;
    let mut v_r_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_375_ = l_Nat_decidableExistsLT_x27(v_k_372_, v_p_373_, v_I_374_);
    crate::leanh::lean_dec(v_k_372_);
    v_r_376_ = crate::leanh::lean_box((v_res_375_) as usize);
    return v_r_376_;
}
pub unsafe fn l_Nat_decidableExistsLE_x27___redArg(
    mut v_k_377_: *mut crate::leanh::LeanObject,
    mut v_I_378_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: u8 = 0;
    v___f_379_ = crate::leanh::lean_alloc_closure(
        l_Nat_decidableExistsLT_x27___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_379_, 0, v_I_378_);
    v___x_380_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_381_ = lean_nat_add(v_k_377_, v___x_380_);
    v___x_382_ = l_Nat_decidableExistsLT_x27___redArg(v___x_381_, v___f_379_);
    crate::leanh::lean_dec(v___x_381_);
    return v___x_382_;
}
pub unsafe fn l_Nat_decidableExistsLE_x27___redArg___boxed(
    mut v_k_383_: *mut crate::leanh::LeanObject,
    mut v_I_384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_385_: u8 = 0;
    let mut v_r_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_385_ = l_Nat_decidableExistsLE_x27___redArg(v_k_383_, v_I_384_);
    crate::leanh::lean_dec(v_k_383_);
    v_r_386_ = crate::leanh::lean_box((v_res_385_) as usize);
    return v_r_386_;
}
pub unsafe fn l_Nat_decidableExistsLE_x27(
    mut v_k_387_: *mut crate::leanh::LeanObject,
    mut v_p_388_: *mut crate::leanh::LeanObject,
    mut v_I_389_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_390_: u8 = 0;
    v___x_390_ = l_Nat_decidableExistsLE_x27___redArg(v_k_387_, v_I_389_);
    return v___x_390_;
}
pub unsafe fn l_Nat_decidableExistsLE_x27___boxed(
    mut v_k_391_: *mut crate::leanh::LeanObject,
    mut v_p_392_: *mut crate::leanh::LeanObject,
    mut v_I_393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_394_: u8 = 0;
    let mut v_r_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_394_ = l_Nat_decidableExistsLE_x27(v_k_391_, v_p_392_, v_I_393_);
    crate::leanh::lean_dec(v_k_391_);
    v_r_395_ = crate::leanh::lean_box((v_res_394_) as usize);
    return v_r_395_;
}
pub unsafe fn l_Nat_decidableExistsFin___redArg___lam__0(
    mut v_n_396_: *mut crate::leanh::LeanObject,
    mut v_inst_397_: *mut crate::leanh::LeanObject,
    mut v_a_398_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_399_: u8 = 0;
    v___x_399_ = lean_nat_dec_lt(v_a_398_, v_n_396_);
    if v___x_399_ == 0 {
        let mut v___x_400_: u8 = 0;
        crate::leanh::lean_dec(v_a_398_);
        crate::leanh::lean_dec_ref(v_inst_397_);
        v___x_400_ = 1;
        return v___x_400_;
    } else {
        let mut v___x_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_402_: u8 = 0;
        v___x_401_ = crate::leanh::lean_apply_1(v_inst_397_, v_a_398_);
        v___x_402_ = (crate::leanh::lean_unbox(v___x_401_) as u8);
        return v___x_402_;
    }
}
pub unsafe fn l_Nat_decidableExistsFin___redArg___lam__0___boxed(
    mut v_n_403_: *mut crate::leanh::LeanObject,
    mut v_inst_404_: *mut crate::leanh::LeanObject,
    mut v_a_405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_406_: u8 = 0;
    let mut v_r_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_406_ = l_Nat_decidableExistsFin___redArg___lam__0(v_n_403_, v_inst_404_, v_a_405_);
    crate::leanh::lean_dec(v_n_403_);
    v_r_407_ = crate::leanh::lean_box((v_res_406_) as usize);
    return v_r_407_;
}
pub unsafe fn l_Nat_decidableExistsFin___redArg(
    mut v_n_408_: *mut crate::leanh::LeanObject,
    mut v_inst_409_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: u8 = 0;
    crate::leanh::lean_inc(v_n_408_);
    v___f_410_ = crate::leanh::lean_alloc_closure(
        l_Nat_decidableExistsFin___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_410_, 0, v_n_408_);
    crate::leanh::lean_closure_set(v___f_410_, 1, v_inst_409_);
    v___x_411_ = l_Nat_decidableExistsLT___redArg(v___f_410_, v_n_408_);
    crate::leanh::lean_dec(v_n_408_);
    return v___x_411_;
}
pub unsafe fn l_Nat_decidableExistsFin___redArg___boxed(
    mut v_n_412_: *mut crate::leanh::LeanObject,
    mut v_inst_413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_414_: u8 = 0;
    let mut v_r_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_414_ = l_Nat_decidableExistsFin___redArg(v_n_412_, v_inst_413_);
    v_r_415_ = crate::leanh::lean_box((v_res_414_) as usize);
    return v_r_415_;
}
pub unsafe fn l_Nat_decidableExistsFin(
    mut v_n_416_: *mut crate::leanh::LeanObject,
    mut v_P_417_: *mut crate::leanh::LeanObject,
    mut v_inst_418_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_419_: u8 = 0;
    v___x_419_ = l_Nat_decidableExistsFin___redArg(v_n_416_, v_inst_418_);
    return v___x_419_;
}
pub unsafe fn l_Nat_decidableExistsFin___boxed(
    mut v_n_420_: *mut crate::leanh::LeanObject,
    mut v_P_421_: *mut crate::leanh::LeanObject,
    mut v_inst_422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_423_: u8 = 0;
    let mut v_r_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_423_ = l_Nat_decidableExistsFin(v_n_420_, v_P_421_, v_inst_422_);
    v_r_424_ = crate::leanh::lean_box((v_res_423_) as usize);
    return v_r_424_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Nat_Lemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Nat_Bitwise_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Log2(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Log2(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_TacticsExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_PropLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Dvd(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Mod(builtin);
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
pub unsafe fn meta_initialize_Init_Data_Nat_Lemmas(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Nat_Lemmas(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Nat_Bitwise_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Log2(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Log2(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_TacticsExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Div_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_PropLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Dvd(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_MinMax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Mod(builtin);
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
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Nat_Lemmas(builtin);
}
