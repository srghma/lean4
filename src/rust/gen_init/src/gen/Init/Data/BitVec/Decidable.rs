// Lean compiler output
// Module: Init.Data.BitVec.Decidable
// Imports: Init.Ext Init.Data.BitVec.Basic Init.PropLemmas Init.Classical Init.Data.BitVec.Bootstrap
use crate::r#gen::Init::Classical::{initialize_Init_Classical, runtime_initialize_Init_Classical};
use crate::r#gen::Init::Data::BitVec::Basic::{
    initialize_Init_Data_BitVec_Basic, l_BitVec_cons, runtime_initialize_Init_Data_BitVec_Basic,
};
use crate::r#gen::Init::Data::BitVec::Bootstrap::{
    initialize_Init_Data_BitVec_Bootstrap, runtime_initialize_Init_Data_BitVec_Bootstrap,
};
use crate::r#gen::Init::Data::Bool::l_Bool_instDecidableForallOfDecidablePred___redArg;
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::Prelude::l_BitVec_ofNat;
use crate::r#gen::Init::PropLemmas::{
    initialize_Init_PropLemmas, runtime_initialize_Init_PropLemmas,
};
use crate::ffi::{lean_nat_dec_eq, lean_nat_sub};
static mut l_BitVec_instDecidableForallBitVec___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_BitVec_instDecidableForallBitVec___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_BitVec_instDecidableForallBitVecZero___redArg(mut v_x_172_: u8) -> u8 {
    return v_x_172_;
}
pub unsafe fn l_BitVec_instDecidableForallBitVecZero___redArg___boxed(
    mut v_x_173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_18__boxed_174_: u8 = 0;
    let mut v_res_175_: u8 = 0;
    let mut v_r_176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_18__boxed_174_ = (crate::leanh::lean_unbox(v_x_173_) as u8);
    v_res_175_ = l_BitVec_instDecidableForallBitVecZero___redArg(v_x_18__boxed_174_);
    v_r_176_ = crate::leanh::lean_box((v_res_175_) as usize);
    return v_r_176_;
}
pub unsafe fn l_BitVec_instDecidableForallBitVecZero(
    mut v_P_177_: *mut crate::leanh::LeanObject,
    mut v_x_178_: u8,
) -> u8 {
    return v_x_178_;
}
pub unsafe fn l_BitVec_instDecidableForallBitVecZero___boxed(
    mut v_P_179_: *mut crate::leanh::LeanObject,
    mut v_x_180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_21__boxed_181_: u8 = 0;
    let mut v_res_182_: u8 = 0;
    let mut v_r_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_21__boxed_181_ = (crate::leanh::lean_unbox(v_x_180_) as u8);
    v_res_182_ = l_BitVec_instDecidableForallBitVecZero(v_P_179_, v_x_21__boxed_181_);
    v_r_183_ = crate::leanh::lean_box((v_res_182_) as usize);
    return v_r_183_;
}
pub unsafe fn l_BitVec_instDecidableForallBitVecSucc___redArg(mut v_inst_184_: u8) -> u8 {
    return v_inst_184_;
}
pub unsafe fn l_BitVec_instDecidableForallBitVecSucc___redArg___boxed(
    mut v_inst_185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inst_10__boxed_186_: u8 = 0;
    let mut v_res_187_: u8 = 0;
    let mut v_r_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_inst_10__boxed_186_ = (crate::leanh::lean_unbox(v_inst_185_) as u8);
    v_res_187_ = l_BitVec_instDecidableForallBitVecSucc___redArg(v_inst_10__boxed_186_);
    v_r_188_ = crate::leanh::lean_box((v_res_187_) as usize);
    return v_r_188_;
}
pub unsafe fn l_BitVec_instDecidableForallBitVecSucc(
    mut v_n_189_: *mut crate::leanh::LeanObject,
    mut v_P_190_: *mut crate::leanh::LeanObject,
    mut v_inst_191_: *mut crate::leanh::LeanObject,
    mut v_inst_192_: u8,
) -> u8 {
    return v_inst_192_;
}
pub unsafe fn l_BitVec_instDecidableForallBitVecSucc___boxed(
    mut v_n_193_: *mut crate::leanh::LeanObject,
    mut v_P_194_: *mut crate::leanh::LeanObject,
    mut v_inst_195_: *mut crate::leanh::LeanObject,
    mut v_inst_196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inst_14__boxed_197_: u8 = 0;
    let mut v_res_198_: u8 = 0;
    let mut v_r_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_inst_14__boxed_197_ = (crate::leanh::lean_unbox(v_inst_196_) as u8);
    v_res_198_ = l_BitVec_instDecidableForallBitVecSucc(
        v_n_193_,
        v_P_194_,
        v_inst_195_,
        v_inst_14__boxed_197_,
    );
    crate::leanh::lean_dec_ref(v_inst_195_);
    crate::leanh::lean_dec(v_n_193_);
    v_r_199_ = crate::leanh::lean_box((v_res_198_) as usize);
    return v_r_199_;
}
pub unsafe fn l_BitVec_instDecidableExistsBitVecZero___redArg(mut v_inst_200_: u8) -> u8 {
    return v_inst_200_;
}
pub unsafe fn l_BitVec_instDecidableExistsBitVecZero___redArg___boxed(
    mut v_inst_201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inst_27__boxed_202_: u8 = 0;
    let mut v_res_203_: u8 = 0;
    let mut v_r_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_inst_27__boxed_202_ = (crate::leanh::lean_unbox(v_inst_201_) as u8);
    v_res_203_ = l_BitVec_instDecidableExistsBitVecZero___redArg(v_inst_27__boxed_202_);
    v_r_204_ = crate::leanh::lean_box((v_res_203_) as usize);
    return v_r_204_;
}
pub unsafe fn l_BitVec_instDecidableExistsBitVecZero(
    mut v_P_205_: *mut crate::leanh::LeanObject,
    mut v_inst_206_: u8,
) -> u8 {
    return v_inst_206_;
}
pub unsafe fn l_BitVec_instDecidableExistsBitVecZero___boxed(
    mut v_P_207_: *mut crate::leanh::LeanObject,
    mut v_inst_208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inst_30__boxed_209_: u8 = 0;
    let mut v_res_210_: u8 = 0;
    let mut v_r_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_inst_30__boxed_209_ = (crate::leanh::lean_unbox(v_inst_208_) as u8);
    v_res_210_ = l_BitVec_instDecidableExistsBitVecZero(v_P_207_, v_inst_30__boxed_209_);
    v_r_211_ = crate::leanh::lean_box((v_res_210_) as usize);
    return v_r_211_;
}
pub unsafe fn l_BitVec_instDecidableExistsBitVecSucc___redArg(mut v_inst_212_: u8) -> u8 {
    if v_inst_212_ == 0 {
        let mut v___x_213_: u8 = 0;
        v___x_213_ = 1;
        return v___x_213_;
    } else {
        let mut v___x_214_: u8 = 0;
        v___x_214_ = 0;
        return v___x_214_;
    }
}
pub unsafe fn l_BitVec_instDecidableExistsBitVecSucc___redArg___boxed(
    mut v_inst_215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inst_21__boxed_216_: u8 = 0;
    let mut v_res_217_: u8 = 0;
    let mut v_r_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_inst_21__boxed_216_ = (crate::leanh::lean_unbox(v_inst_215_) as u8);
    v_res_217_ = l_BitVec_instDecidableExistsBitVecSucc___redArg(v_inst_21__boxed_216_);
    v_r_218_ = crate::leanh::lean_box((v_res_217_) as usize);
    return v_r_218_;
}
pub unsafe fn l_BitVec_instDecidableExistsBitVecSucc(
    mut v_n_219_: *mut crate::leanh::LeanObject,
    mut v_P_220_: *mut crate::leanh::LeanObject,
    mut v_inst_221_: *mut crate::leanh::LeanObject,
    mut v_inst_222_: u8,
) -> u8 {
    let mut v___x_223_: u8 = 0;
    v___x_223_ = l_BitVec_instDecidableExistsBitVecSucc___redArg(v_inst_222_);
    return v___x_223_;
}
pub unsafe fn l_BitVec_instDecidableExistsBitVecSucc___boxed(
    mut v_n_224_: *mut crate::leanh::LeanObject,
    mut v_P_225_: *mut crate::leanh::LeanObject,
    mut v_inst_226_: *mut crate::leanh::LeanObject,
    mut v_inst_227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inst_29__boxed_228_: u8 = 0;
    let mut v_res_229_: u8 = 0;
    let mut v_r_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_inst_29__boxed_228_ = (crate::leanh::lean_unbox(v_inst_227_) as u8);
    v_res_229_ = l_BitVec_instDecidableExistsBitVecSucc(
        v_n_224_,
        v_P_225_,
        v_inst_226_,
        v_inst_29__boxed_228_,
    );
    crate::leanh::lean_dec_ref(v_inst_226_);
    crate::leanh::lean_dec(v_n_224_);
    v_r_230_ = crate::leanh::lean_box((v_res_229_) as usize);
    return v_r_230_;
}
pub unsafe fn l_BitVec_instDecidableForallBitVec___redArg___lam__0(
    mut v_n_231_: *mut crate::leanh::LeanObject,
    mut v_a_232_: u8,
    mut v_x_233_: *mut crate::leanh::LeanObject,
    mut v_a_234_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_237_: u8 = 0;
    v___x_235_ = l_BitVec_cons(v_n_231_, v_a_232_, v_a_234_);
    v___x_236_ = crate::leanh::lean_apply_1(v_x_233_, v___x_235_);
    v___x_237_ = (crate::leanh::lean_unbox(v___x_236_) as u8);
    return v___x_237_;
}
pub unsafe fn l_BitVec_instDecidableForallBitVec___redArg___lam__0___boxed(
    mut v_n_238_: *mut crate::leanh::LeanObject,
    mut v_a_239_: *mut crate::leanh::LeanObject,
    mut v_x_240_: *mut crate::leanh::LeanObject,
    mut v_a_241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_242_: u8 = 0;
    let mut v_res_243_: u8 = 0;
    let mut v_r_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_242_ = (crate::leanh::lean_unbox(v_a_239_) as u8);
    v_res_243_ = l_BitVec_instDecidableForallBitVec___redArg___lam__0(
        v_n_238_,
        v_a_boxed_242_,
        v_x_240_,
        v_a_241_,
    );
    crate::leanh::lean_dec(v_a_241_);
    crate::leanh::lean_dec(v_n_238_);
    v_r_244_ = crate::leanh::lean_box((v_res_243_) as usize);
    return v_r_244_;
}
pub unsafe fn _init_l_BitVec_instDecidableForallBitVec___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v_zero_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_zero_245_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_246_ = l_BitVec_ofNat(v_zero_245_, v_zero_245_);
    return v___x_246_;
}
pub unsafe fn l_BitVec_instDecidableForallBitVec___redArg___lam__1___boxed(
    mut v_n_247_: *mut crate::leanh::LeanObject,
    mut v_x_248_: *mut crate::leanh::LeanObject,
    mut v_a_249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_250_: u8 = 0;
    let mut v_res_251_: u8 = 0;
    let mut v_r_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_250_ = (crate::leanh::lean_unbox(v_a_249_) as u8);
    v_res_251_ =
        l_BitVec_instDecidableForallBitVec___redArg___lam__1(v_n_247_, v_x_248_, v_a_boxed_250_);
    v_r_252_ = crate::leanh::lean_box((v_res_251_) as usize);
    return v_r_252_;
}
pub unsafe fn l_BitVec_instDecidableForallBitVec___redArg(
    mut v_x_253_: *mut crate::leanh::LeanObject,
    mut v_x_254_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_256_: u8 = 0;
    v_zero_255_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_256_ = lean_nat_dec_eq(v_x_253_, v_zero_255_);
    if v_isZero_256_ == 1 {
        let mut v___x_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_259_: u8 = 0;
        v___x_257_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_BitVec_instDecidableForallBitVec___redArg___closed__0),
            core::ptr::addr_of_mut!(l_BitVec_instDecidableForallBitVec___redArg___closed__0_once),
            _init_l_BitVec_instDecidableForallBitVec___redArg___closed__0,
        );
        v___x_258_ = crate::leanh::lean_apply_1(v_x_254_, v___x_257_);
        v___x_259_ = (crate::leanh::lean_unbox(v___x_258_) as u8);
        return v___x_259_;
    } else {
        let mut v_one_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_263_: u8 = 0;
        v_one_260_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_261_ = lean_nat_sub(v_x_253_, v_one_260_);
        v___f_262_ = crate::leanh::lean_alloc_closure(
            l_BitVec_instDecidableForallBitVec___redArg___lam__1___boxed as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_262_, 0, v_n_261_);
        crate::leanh::lean_closure_set(v___f_262_, 1, v_x_254_);
        v___x_263_ = l_Bool_instDecidableForallOfDecidablePred___redArg(v___f_262_);
        return v___x_263_;
    }
}
pub unsafe fn l_BitVec_instDecidableForallBitVec___redArg___lam__1(
    mut v_n_264_: *mut crate::leanh::LeanObject,
    mut v_x_265_: *mut crate::leanh::LeanObject,
    mut v_a_266_: u8,
) -> u8 {
    let mut v___x_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_269_: u8 = 0;
    v___x_267_ = crate::leanh::lean_box((v_a_266_) as usize);
    crate::leanh::lean_inc(v_n_264_);
    v___f_268_ = crate::leanh::lean_alloc_closure(
        l_BitVec_instDecidableForallBitVec___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_268_, 0, v_n_264_);
    crate::leanh::lean_closure_set(v___f_268_, 1, v___x_267_);
    crate::leanh::lean_closure_set(v___f_268_, 2, v_x_265_);
    v___x_269_ = l_BitVec_instDecidableForallBitVec___redArg(v_n_264_, v___f_268_);
    crate::leanh::lean_dec(v_n_264_);
    return v___x_269_;
}
pub unsafe fn l_BitVec_instDecidableForallBitVec___redArg___boxed(
    mut v_x_270_: *mut crate::leanh::LeanObject,
    mut v_x_271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_272_: u8 = 0;
    let mut v_r_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_272_ = l_BitVec_instDecidableForallBitVec___redArg(v_x_270_, v_x_271_);
    crate::leanh::lean_dec(v_x_270_);
    v_r_273_ = crate::leanh::lean_box((v_res_272_) as usize);
    return v_r_273_;
}
pub unsafe fn l_BitVec_instDecidableForallBitVec(
    mut v_x_274_: *mut crate::leanh::LeanObject,
    mut v_x_275_: *mut crate::leanh::LeanObject,
    mut v_x_276_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_277_: u8 = 0;
    v___x_277_ = l_BitVec_instDecidableForallBitVec___redArg(v_x_274_, v_x_276_);
    return v___x_277_;
}
pub unsafe fn l_BitVec_instDecidableForallBitVec___boxed(
    mut v_x_278_: *mut crate::leanh::LeanObject,
    mut v_x_279_: *mut crate::leanh::LeanObject,
    mut v_x_280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_281_: u8 = 0;
    let mut v_r_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_281_ = l_BitVec_instDecidableForallBitVec(v_x_278_, v_x_279_, v_x_280_);
    crate::leanh::lean_dec(v_x_278_);
    v_r_282_ = crate::leanh::lean_box((v_res_281_) as usize);
    return v_r_282_;
}
pub unsafe fn l_BitVec_instDecidableExistsBitVec___redArg___lam__0(
    mut v_n_283_: *mut crate::leanh::LeanObject,
    mut v_a_284_: u8,
    mut v_x_285_: *mut crate::leanh::LeanObject,
    mut v_isZero_286_: u8,
    mut v_a_287_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: u8 = 0;
    v___x_288_ = l_BitVec_cons(v_n_283_, v_a_284_, v_a_287_);
    v___x_289_ = crate::leanh::lean_apply_1(v_x_285_, v___x_288_);
    v___x_290_ = (crate::leanh::lean_unbox(v___x_289_) as u8);
    if v___x_290_ == 0 {
        let mut v___x_291_: u8 = 0;
        v___x_291_ = 1;
        return v___x_291_;
    } else {
        return v_isZero_286_;
    }
}
pub unsafe fn l_BitVec_instDecidableExistsBitVec___redArg___lam__0___boxed(
    mut v_n_292_: *mut crate::leanh::LeanObject,
    mut v_a_293_: *mut crate::leanh::LeanObject,
    mut v_x_294_: *mut crate::leanh::LeanObject,
    mut v_isZero_295_: *mut crate::leanh::LeanObject,
    mut v_a_296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_297_: u8 = 0;
    let mut v_isZero_boxed_298_: u8 = 0;
    let mut v_res_299_: u8 = 0;
    let mut v_r_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_297_ = (crate::leanh::lean_unbox(v_a_293_) as u8);
    v_isZero_boxed_298_ = (crate::leanh::lean_unbox(v_isZero_295_) as u8);
    v_res_299_ = l_BitVec_instDecidableExistsBitVec___redArg___lam__0(
        v_n_292_,
        v_a_boxed_297_,
        v_x_294_,
        v_isZero_boxed_298_,
        v_a_296_,
    );
    crate::leanh::lean_dec(v_a_296_);
    crate::leanh::lean_dec(v_n_292_);
    v_r_300_ = crate::leanh::lean_box((v_res_299_) as usize);
    return v_r_300_;
}
pub unsafe fn l_BitVec_instDecidableExistsBitVec___redArg___lam__1(
    mut v_n_301_: *mut crate::leanh::LeanObject,
    mut v_x_302_: *mut crate::leanh::LeanObject,
    mut v_isZero_303_: u8,
    mut v_a_304_: u8,
) -> u8 {
    let mut v___x_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_308_: u8 = 0;
    v___x_305_ = crate::leanh::lean_box((v_a_304_) as usize);
    v___x_306_ = crate::leanh::lean_box((v_isZero_303_) as usize);
    crate::leanh::lean_inc(v_n_301_);
    v___f_307_ = crate::leanh::lean_alloc_closure(
        l_BitVec_instDecidableExistsBitVec___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_307_, 0, v_n_301_);
    crate::leanh::lean_closure_set(v___f_307_, 1, v___x_305_);
    crate::leanh::lean_closure_set(v___f_307_, 2, v_x_302_);
    crate::leanh::lean_closure_set(v___f_307_, 3, v___x_306_);
    v___x_308_ = l_BitVec_instDecidableForallBitVec___redArg(v_n_301_, v___f_307_);
    crate::leanh::lean_dec(v_n_301_);
    return v___x_308_;
}
pub unsafe fn l_BitVec_instDecidableExistsBitVec___redArg___lam__1___boxed(
    mut v_n_309_: *mut crate::leanh::LeanObject,
    mut v_x_310_: *mut crate::leanh::LeanObject,
    mut v_isZero_311_: *mut crate::leanh::LeanObject,
    mut v_a_312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isZero_boxed_313_: u8 = 0;
    let mut v_a_boxed_314_: u8 = 0;
    let mut v_res_315_: u8 = 0;
    let mut v_r_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isZero_boxed_313_ = (crate::leanh::lean_unbox(v_isZero_311_) as u8);
    v_a_boxed_314_ = (crate::leanh::lean_unbox(v_a_312_) as u8);
    v_res_315_ = l_BitVec_instDecidableExistsBitVec___redArg___lam__1(
        v_n_309_,
        v_x_310_,
        v_isZero_boxed_313_,
        v_a_boxed_314_,
    );
    v_r_316_ = crate::leanh::lean_box((v_res_315_) as usize);
    return v_r_316_;
}
pub unsafe fn l_BitVec_instDecidableExistsBitVec___redArg(
    mut v_x_317_: *mut crate::leanh::LeanObject,
    mut v_x_318_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_320_: u8 = 0;
    v_zero_319_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_320_ = lean_nat_dec_eq(v_x_317_, v_zero_319_);
    if v_isZero_320_ == 1 {
        let mut v___x_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_323_: u8 = 0;
        v___x_321_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_BitVec_instDecidableForallBitVec___redArg___closed__0),
            core::ptr::addr_of_mut!(l_BitVec_instDecidableForallBitVec___redArg___closed__0_once),
            _init_l_BitVec_instDecidableForallBitVec___redArg___closed__0,
        );
        v___x_322_ = crate::leanh::lean_apply_1(v_x_318_, v___x_321_);
        v___x_323_ = (crate::leanh::lean_unbox(v___x_322_) as u8);
        return v___x_323_;
    } else {
        let mut v_one_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_328_: u8 = 0;
        let mut v___x_329_: u8 = 0;
        v_one_324_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_325_ = lean_nat_sub(v_x_317_, v_one_324_);
        v___x_326_ = crate::leanh::lean_box((v_isZero_320_) as usize);
        v___f_327_ = crate::leanh::lean_alloc_closure(
            l_BitVec_instDecidableExistsBitVec___redArg___lam__1___boxed as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_327_, 0, v_n_325_);
        crate::leanh::lean_closure_set(v___f_327_, 1, v_x_318_);
        crate::leanh::lean_closure_set(v___f_327_, 2, v___x_326_);
        v___x_328_ = l_Bool_instDecidableForallOfDecidablePred___redArg(v___f_327_);
        v___x_329_ = l_BitVec_instDecidableExistsBitVecSucc___redArg(v___x_328_);
        return v___x_329_;
    }
}
pub unsafe fn l_BitVec_instDecidableExistsBitVec___redArg___boxed(
    mut v_x_330_: *mut crate::leanh::LeanObject,
    mut v_x_331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_332_: u8 = 0;
    let mut v_r_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_332_ = l_BitVec_instDecidableExistsBitVec___redArg(v_x_330_, v_x_331_);
    crate::leanh::lean_dec(v_x_330_);
    v_r_333_ = crate::leanh::lean_box((v_res_332_) as usize);
    return v_r_333_;
}
pub unsafe fn l_BitVec_instDecidableExistsBitVec(
    mut v_x_334_: *mut crate::leanh::LeanObject,
    mut v_x_335_: *mut crate::leanh::LeanObject,
    mut v_x_336_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_337_: u8 = 0;
    v___x_337_ = l_BitVec_instDecidableExistsBitVec___redArg(v_x_334_, v_x_336_);
    return v___x_337_;
}
pub unsafe fn l_BitVec_instDecidableExistsBitVec___boxed(
    mut v_x_338_: *mut crate::leanh::LeanObject,
    mut v_x_339_: *mut crate::leanh::LeanObject,
    mut v_x_340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_341_: u8 = 0;
    let mut v_r_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_341_ = l_BitVec_instDecidableExistsBitVec(v_x_338_, v_x_339_, v_x_340_);
    crate::leanh::lean_dec(v_x_338_);
    v_r_342_ = crate::leanh::lean_box((v_res_341_) as usize);
    return v_r_342_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_BitVec_Decidable(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_PropLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_BitVec_Decidable(
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
pub unsafe fn initialize_Init_Data_BitVec_Decidable(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_PropLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Decidable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_BitVec_Decidable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_BitVec_Decidable(builtin);
}
