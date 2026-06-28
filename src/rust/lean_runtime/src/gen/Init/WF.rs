// Lean compiler output
// Module: Init.WF
// Imports: Init.BinderNameHint Init.Grind.Tactics Init.Data.Nat.Basic
use crate::r#gen::Init::BinderNameHint::{
    initialize_Init_BinderNameHint, runtime_initialize_Init_BinderNameHint,
};
use crate::r#gen::Init::Data::Nat::Basic::{
    initialize_Init_Data_Nat_Basic, l_Nat_recCompiled___redArg,
    runtime_initialize_Init_Data_Nat_Basic,
};
use crate::r#gen::Init::Grind::Tactics::{
    initialize_Init_Grind_Tactics, runtime_initialize_Init_Grind_Tactics,
};
use crate::lean_imports_rs::Init::Prelude::lean_nat_add;
pub static mut l_Nat_lt__wfRel: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_Nat_fix_go___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_WellFounded_Nat_fix_go___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_WellFounded_Nat_fix_go___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_WellFounded_Nat_fix_go___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_WellFounded_wrap___redArg(
    mut v_x_196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_196_);
    return v_x_196_;
}
pub unsafe fn l_WellFounded_wrap___redArg___boxed(
    mut v_x_197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_198_ = l_WellFounded_wrap___redArg(v_x_197_);
    crate::leanh::lean_dec(v_x_197_);
    return v_res_198_;
}
pub unsafe fn l_WellFounded_wrap(
    mut v_00_u03b1_199_: *mut crate::leanh::LeanObject,
    mut v_r_200_: *mut crate::leanh::LeanObject,
    mut v_h_201_: *mut crate::leanh::LeanObject,
    mut v_x_202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_202_);
    return v_x_202_;
}
pub unsafe fn l_WellFounded_wrap___boxed(
    mut v_00_u03b1_203_: *mut crate::leanh::LeanObject,
    mut v_r_204_: *mut crate::leanh::LeanObject,
    mut v_h_205_: *mut crate::leanh::LeanObject,
    mut v_x_206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_207_ = l_WellFounded_wrap(v_00_u03b1_203_, v_r_204_, v_h_205_, v_x_206_);
    crate::leanh::lean_dec(v_x_206_);
    return v_res_207_;
}
pub unsafe fn l_emptyWf(
    mut v_00_u03b1_208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_209_ = crate::leanh::lean_box(0);
    return v___x_209_;
}
pub unsafe fn l_invImage(
    mut v_00_u03b1_210_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_211_: *mut crate::leanh::LeanObject,
    mut v_f_212_: *mut crate::leanh::LeanObject,
    mut v_h_213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_214_ = crate::leanh::lean_box(0);
    return v___x_214_;
}
pub unsafe fn l_invImage___boxed(
    mut v_00_u03b1_215_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_216_: *mut crate::leanh::LeanObject,
    mut v_f_217_: *mut crate::leanh::LeanObject,
    mut v_h_218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_219_ = l_invImage(v_00_u03b1_215_, v_00_u03b2_216_, v_f_217_, v_h_218_);
    crate::leanh::lean_dec(v_f_217_);
    return v_res_219_;
}
pub unsafe fn _init_l_Nat_lt__wfRel() -> *mut crate::leanh::LeanObject {
    let mut v___x_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_220_ = crate::leanh::lean_box(0);
    return v___x_220_;
}
pub unsafe fn l_measure(
    mut v_00_u03b1_221_: *mut crate::leanh::LeanObject,
    mut v_f_222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_223_ = crate::leanh::lean_box(0);
    return v___x_223_;
}
pub unsafe fn l_measure___boxed(
    mut v_00_u03b1_224_: *mut crate::leanh::LeanObject,
    mut v_f_225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_226_ = l_measure(v_00_u03b1_224_, v_f_225_);
    crate::leanh::lean_dec_ref(v_f_225_);
    return v_res_226_;
}
pub unsafe fn l_sizeOfWFRel(
    mut v_00_u03b1_227_: *mut crate::leanh::LeanObject,
    mut v_inst_228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_229_ = crate::leanh::lean_box(0);
    return v___x_229_;
}
pub unsafe fn l_sizeOfWFRel___boxed(
    mut v_00_u03b1_230_: *mut crate::leanh::LeanObject,
    mut v_inst_231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_232_ = l_sizeOfWFRel(v_00_u03b1_230_, v_inst_231_);
    crate::leanh::lean_dec_ref(v_inst_231_);
    return v_res_232_;
}
pub unsafe fn l_Prod_Lex_instDecidableRelOfDecidableEq___redArg(
    mut v_00_u03b1eqDec_233_: *mut crate::leanh::LeanObject,
    mut v_rDec_234_: *mut crate::leanh::LeanObject,
    mut v_sDec_235_: *mut crate::leanh::LeanObject,
    mut v_x_236_: *mut crate::leanh::LeanObject,
    mut v_x_237_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_244_: u8 = 0;
    v_fst_238_ = crate::leanh::lean_ctor_get(v_x_236_, 0);
    crate::leanh::lean_inc_n(v_fst_238_, 2);
    v_snd_239_ = crate::leanh::lean_ctor_get(v_x_236_, 1);
    crate::leanh::lean_inc(v_snd_239_);
    crate::leanh::lean_dec_ref(v_x_236_);
    v_fst_240_ = crate::leanh::lean_ctor_get(v_x_237_, 0);
    crate::leanh::lean_inc_n(v_fst_240_, 2);
    v_snd_241_ = crate::leanh::lean_ctor_get(v_x_237_, 1);
    crate::leanh::lean_inc(v_snd_241_);
    crate::leanh::lean_dec_ref(v_x_237_);
    v___x_242_ = crate::leanh::lean_apply_2(v_00_u03b1eqDec_233_, v_fst_238_, v_fst_240_);
    v___x_243_ = crate::leanh::lean_apply_2(v_rDec_234_, v_fst_238_, v_fst_240_);
    v___x_244_ = (crate::leanh::lean_unbox(v___x_243_) as u8);
    if v___x_244_ == 0 {
        let mut v___x_245_: u8 = 0;
        v___x_245_ = (crate::leanh::lean_unbox(v___x_242_) as u8);
        if v___x_245_ == 0 {
            let mut v___x_246_: u8 = 0;
            crate::leanh::lean_dec(v_snd_241_);
            crate::leanh::lean_dec(v_snd_239_);
            crate::leanh::lean_dec_ref(v_sDec_235_);
            v___x_246_ = (crate::leanh::lean_unbox(v___x_242_) as u8);
            return v___x_246_;
        } else {
            let mut v___x_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_248_: u8 = 0;
            v___x_247_ = crate::leanh::lean_apply_2(v_sDec_235_, v_snd_239_, v_snd_241_);
            v___x_248_ = (crate::leanh::lean_unbox(v___x_247_) as u8);
            return v___x_248_;
        }
    } else {
        let mut v___x_249_: u8 = 0;
        crate::leanh::lean_dec(v_snd_241_);
        crate::leanh::lean_dec(v_snd_239_);
        crate::leanh::lean_dec_ref(v_sDec_235_);
        v___x_249_ = (crate::leanh::lean_unbox(v___x_243_) as u8);
        return v___x_249_;
    }
}
pub unsafe fn l_Prod_Lex_instDecidableRelOfDecidableEq___redArg___boxed(
    mut v_00_u03b1eqDec_250_: *mut crate::leanh::LeanObject,
    mut v_rDec_251_: *mut crate::leanh::LeanObject,
    mut v_sDec_252_: *mut crate::leanh::LeanObject,
    mut v_x_253_: *mut crate::leanh::LeanObject,
    mut v_x_254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_255_: u8 = 0;
    let mut v_r_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_255_ = l_Prod_Lex_instDecidableRelOfDecidableEq___redArg(
        v_00_u03b1eqDec_250_,
        v_rDec_251_,
        v_sDec_252_,
        v_x_253_,
        v_x_254_,
    );
    v_r_256_ = crate::leanh::lean_box((v_res_255_) as usize);
    return v_r_256_;
}
pub unsafe fn l_Prod_Lex_instDecidableRelOfDecidableEq(
    mut v_00_u03b1_257_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_258_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1eqDec_259_: *mut crate::leanh::LeanObject,
    mut v_r_260_: *mut crate::leanh::LeanObject,
    mut v_rDec_261_: *mut crate::leanh::LeanObject,
    mut v_s_262_: *mut crate::leanh::LeanObject,
    mut v_sDec_263_: *mut crate::leanh::LeanObject,
    mut v_x_264_: *mut crate::leanh::LeanObject,
    mut v_x_265_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_266_: u8 = 0;
    v___x_266_ = l_Prod_Lex_instDecidableRelOfDecidableEq___redArg(
        v_00_u03b1eqDec_259_,
        v_rDec_261_,
        v_sDec_263_,
        v_x_264_,
        v_x_265_,
    );
    return v___x_266_;
}
pub unsafe fn l_Prod_Lex_instDecidableRelOfDecidableEq___boxed(
    mut v_00_u03b1_267_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_268_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1eqDec_269_: *mut crate::leanh::LeanObject,
    mut v_r_270_: *mut crate::leanh::LeanObject,
    mut v_rDec_271_: *mut crate::leanh::LeanObject,
    mut v_s_272_: *mut crate::leanh::LeanObject,
    mut v_sDec_273_: *mut crate::leanh::LeanObject,
    mut v_x_274_: *mut crate::leanh::LeanObject,
    mut v_x_275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_276_: u8 = 0;
    let mut v_r_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_276_ = l_Prod_Lex_instDecidableRelOfDecidableEq(
        v_00_u03b1_267_,
        v_00_u03b2_268_,
        v_00_u03b1eqDec_269_,
        v_r_270_,
        v_rDec_271_,
        v_s_272_,
        v_sDec_273_,
        v_x_274_,
        v_x_275_,
    );
    v_r_277_ = crate::leanh::lean_box((v_res_276_) as usize);
    return v_r_277_;
}
pub unsafe fn l_Prod_lex(
    mut v_00_u03b1_278_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_279_: *mut crate::leanh::LeanObject,
    mut v_ha_280_: *mut crate::leanh::LeanObject,
    mut v_hb_281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_282_ = crate::leanh::lean_box(0);
    return v___x_282_;
}
pub unsafe fn l_Prod_instWellFoundedRelation(
    mut v_00_u03b1_283_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_284_: *mut crate::leanh::LeanObject,
    mut v_ha_285_: *mut crate::leanh::LeanObject,
    mut v_hb_286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_287_ = crate::leanh::lean_box(0);
    return v___x_287_;
}
pub unsafe fn l_Prod_rprod(
    mut v_00_u03b1_288_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_289_: *mut crate::leanh::LeanObject,
    mut v_ha_290_: *mut crate::leanh::LeanObject,
    mut v_hb_291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_292_ = crate::leanh::lean_box(0);
    return v___x_292_;
}
pub unsafe fn l_PSigma_lex(
    mut v_00_u03b1_293_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_294_: *mut crate::leanh::LeanObject,
    mut v_ha_295_: *mut crate::leanh::LeanObject,
    mut v_hb_296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_297_ = crate::leanh::lean_box(0);
    return v___x_297_;
}
pub unsafe fn l_PSigma_lex___boxed(
    mut v_00_u03b1_298_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_299_: *mut crate::leanh::LeanObject,
    mut v_ha_300_: *mut crate::leanh::LeanObject,
    mut v_hb_301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_302_ = l_PSigma_lex(v_00_u03b1_298_, v_00_u03b2_299_, v_ha_300_, v_hb_301_);
    crate::leanh::lean_dec_ref(v_hb_301_);
    return v_res_302_;
}
pub unsafe fn l_PSigma_instWellFoundedRelation(
    mut v_00_u03b1_303_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_304_: *mut crate::leanh::LeanObject,
    mut v_ha_305_: *mut crate::leanh::LeanObject,
    mut v_hb_306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_307_ = crate::leanh::lean_box(0);
    return v___x_307_;
}
pub unsafe fn l_PSigma_instWellFoundedRelation___boxed(
    mut v_00_u03b1_308_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_309_: *mut crate::leanh::LeanObject,
    mut v_ha_310_: *mut crate::leanh::LeanObject,
    mut v_hb_311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_312_ =
        l_PSigma_instWellFoundedRelation(v_00_u03b1_308_, v_00_u03b2_309_, v_ha_310_, v_hb_311_);
    crate::leanh::lean_dec_ref(v_hb_311_);
    return v_res_312_;
}
pub unsafe fn l_PSigma_skipLeft(
    mut v_00_u03b1_313_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_314_: *mut crate::leanh::LeanObject,
    mut v_hb_315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_316_ = crate::leanh::lean_box(0);
    return v___x_316_;
}
pub unsafe fn l_WellFounded_Nat_eager(
    mut v_n_317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_n_317_);
    return v_n_317_;
}
pub unsafe fn l_WellFounded_Nat_eager___boxed(
    mut v_n_318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_319_ = l_WellFounded_Nat_eager(v_n_318_);
    crate::leanh::lean_dec(v_n_318_);
    return v_res_319_;
}
pub unsafe fn l_WellFounded_Nat_fix_go___redArg___lam__0(
    mut v_x_320_: *mut crate::leanh::LeanObject,
    mut v_hfuel_321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    core::hint::unreachable_unchecked();
}
pub unsafe fn l_WellFounded_Nat_fix_go___redArg___lam__0___boxed(
    mut v_x_322_: *mut crate::leanh::LeanObject,
    mut v_hfuel_323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_324_ = l_WellFounded_Nat_fix_go___redArg___lam__0(v_x_322_, v_hfuel_323_);
    crate::leanh::lean_dec(v_x_322_);
    return v_res_324_;
}
pub unsafe fn l_WellFounded_Nat_fix_go___redArg___lam__1(
    mut v_ih_325_: *mut crate::leanh::LeanObject,
    mut v_y_326_: *mut crate::leanh::LeanObject,
    mut v_hy_327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_328_ = crate::leanh::lean_apply_2(v_ih_325_, v_y_326_, crate::leanh::lean_box(0));
    return v___x_328_;
}
pub unsafe fn l_WellFounded_Nat_fix_go___redArg___lam__2(
    mut v_F_329_: *mut crate::leanh::LeanObject,
    mut v_x_330_: *mut crate::leanh::LeanObject,
    mut v_ih_331_: *mut crate::leanh::LeanObject,
    mut v_x_332_: *mut crate::leanh::LeanObject,
    mut v_hfuel_333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_334_ = crate::leanh::lean_alloc_closure(
        l_WellFounded_Nat_fix_go___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_334_, 0, v_ih_331_);
    v___x_335_ = crate::leanh::lean_apply_2(v_F_329_, v_x_332_, v___f_334_);
    return v___x_335_;
}
pub unsafe fn l_WellFounded_Nat_fix_go___redArg___lam__2___boxed(
    mut v_F_336_: *mut crate::leanh::LeanObject,
    mut v_x_337_: *mut crate::leanh::LeanObject,
    mut v_ih_338_: *mut crate::leanh::LeanObject,
    mut v_x_339_: *mut crate::leanh::LeanObject,
    mut v_hfuel_340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_341_ = l_WellFounded_Nat_fix_go___redArg___lam__2(
        v_F_336_,
        v_x_337_,
        v_ih_338_,
        v_x_339_,
        v_hfuel_340_,
    );
    crate::leanh::lean_dec(v_x_337_);
    return v_res_341_;
}
pub unsafe fn l_WellFounded_Nat_fix_go___redArg(
    mut v_F_343_: *mut crate::leanh::LeanObject,
    mut v_fuel_344_: *mut crate::leanh::LeanObject,
    mut v_x_345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_10__overap_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_346_ = l_WellFounded_Nat_fix_go___redArg___closed__0;
    v___f_347_ = crate::leanh::lean_alloc_closure(
        l_WellFounded_Nat_fix_go___redArg___lam__2___boxed as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_347_, 0, v_F_343_);
    v___x_10__overap_348_ = l_Nat_recCompiled___redArg(v___f_346_, v___f_347_, v_fuel_344_);
    v___x_349_ =
        crate::leanh::lean_apply_2(v___x_10__overap_348_, v_x_345_, crate::leanh::lean_box(0));
    return v___x_349_;
}
pub unsafe fn l_WellFounded_Nat_fix_go___redArg___boxed(
    mut v_F_350_: *mut crate::leanh::LeanObject,
    mut v_fuel_351_: *mut crate::leanh::LeanObject,
    mut v_x_352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_353_ = l_WellFounded_Nat_fix_go___redArg(v_F_350_, v_fuel_351_, v_x_352_);
    crate::leanh::lean_dec(v_fuel_351_);
    return v_res_353_;
}
pub unsafe fn l_WellFounded_Nat_fix_go(
    mut v_00_u03b1_354_: *mut crate::leanh::LeanObject,
    mut v_motive_355_: *mut crate::leanh::LeanObject,
    mut v_h_356_: *mut crate::leanh::LeanObject,
    mut v_F_357_: *mut crate::leanh::LeanObject,
    mut v_fuel_358_: *mut crate::leanh::LeanObject,
    mut v_x_359_: *mut crate::leanh::LeanObject,
    mut v_a_360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_361_ = l_WellFounded_Nat_fix_go___redArg(v_F_357_, v_fuel_358_, v_x_359_);
    return v___x_361_;
}
pub unsafe fn l_WellFounded_Nat_fix_go___boxed(
    mut v_00_u03b1_362_: *mut crate::leanh::LeanObject,
    mut v_motive_363_: *mut crate::leanh::LeanObject,
    mut v_h_364_: *mut crate::leanh::LeanObject,
    mut v_F_365_: *mut crate::leanh::LeanObject,
    mut v_fuel_366_: *mut crate::leanh::LeanObject,
    mut v_x_367_: *mut crate::leanh::LeanObject,
    mut v_a_368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_369_ = l_WellFounded_Nat_fix_go(
        v_00_u03b1_362_,
        v_motive_363_,
        v_h_364_,
        v_F_365_,
        v_fuel_366_,
        v_x_367_,
        v_a_368_,
    );
    crate::leanh::lean_dec(v_fuel_366_);
    crate::leanh::lean_dec_ref(v_h_364_);
    return v_res_369_;
}
pub unsafe fn l_WellFounded_Nat_fix___redArg(
    mut v_h_370_: *mut crate::leanh::LeanObject,
    mut v_F_371_: *mut crate::leanh::LeanObject,
    mut v_x_372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_x_372_);
    v___x_373_ = crate::leanh::lean_apply_1(v_h_370_, v_x_372_);
    v___x_374_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_375_ = lean_nat_add(v___x_373_, v___x_374_);
    crate::leanh::lean_dec(v___x_373_);
    v___x_376_ = l_WellFounded_Nat_fix_go___redArg(v_F_371_, v___x_375_, v_x_372_);
    crate::leanh::lean_dec(v___x_375_);
    return v___x_376_;
}
pub unsafe fn l_WellFounded_Nat_fix(
    mut v_00_u03b1_377_: *mut crate::leanh::LeanObject,
    mut v_motive_378_: *mut crate::leanh::LeanObject,
    mut v_h_379_: *mut crate::leanh::LeanObject,
    mut v_F_380_: *mut crate::leanh::LeanObject,
    mut v_x_381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_382_ = l_WellFounded_Nat_fix___redArg(v_h_379_, v_F_380_, v_x_381_);
    return v___x_382_;
}
pub unsafe fn l_wfParam___redArg(
    mut v_a_383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_a_383_);
    return v_a_383_;
}
pub unsafe fn l_wfParam___redArg___boxed(
    mut v_a_384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_385_ = l_wfParam___redArg(v_a_384_);
    crate::leanh::lean_dec(v_a_384_);
    return v_res_385_;
}
pub unsafe fn l_wfParam(
    mut v_00_u03b1_386_: *mut crate::leanh::LeanObject,
    mut v_a_387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_a_387_);
    return v_a_387_;
}
pub unsafe fn l_wfParam___boxed(
    mut v_00_u03b1_388_: *mut crate::leanh::LeanObject,
    mut v_a_389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_390_ = l_wfParam(v_00_u03b1_388_, v_a_389_);
    crate::leanh::lean_dec(v_a_389_);
    return v_res_390_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_WF(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_BinderNameHint(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Nat_lt__wfRel = _init_l_Nat_lt__wfRel();
    crate::leanh::lean_mark_persistent(l_Nat_lt__wfRel);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_WF(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_WF(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_BinderNameHint(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_WF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_WF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_WF(builtin);
}
