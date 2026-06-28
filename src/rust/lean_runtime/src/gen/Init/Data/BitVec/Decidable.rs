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
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_sub};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_1, lean_box, lean_closure_set,
    lean_dec, lean_dec_ref, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once,
    lean_unbox, lean_unsigned_to_nat,
};
static mut l_BitVec_instDecidableForallBitVec___redArg___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_BitVec_instDecidableForallBitVec___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_BitVec_instDecidableForallBitVecZero___redArg(mut v_x_172_: u8) -> u8 {
    return v_x_172_;
}
pub unsafe fn l_BitVec_instDecidableForallBitVecZero___redArg___boxed(
    mut v_x_173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_18__boxed_174_: u8 = 0;
    let mut v_res_175_: u8 = 0;
    let mut v_r_176_: *mut LeanObject = core::ptr::null_mut();
    v_x_18__boxed_174_ = (lean_unbox(v_x_173_) as u8);
    v_res_175_ = l_BitVec_instDecidableForallBitVecZero___redArg(v_x_18__boxed_174_);
    v_r_176_ = lean_box((v_res_175_) as usize);
    return v_r_176_;
}
pub unsafe fn l_BitVec_instDecidableForallBitVecZero(
    mut v_P_177_: *mut LeanObject,
    mut v_x_178_: u8,
) -> u8 {
    return v_x_178_;
}
pub unsafe fn l_BitVec_instDecidableForallBitVecZero___boxed(
    mut v_P_179_: *mut LeanObject,
    mut v_x_180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_21__boxed_181_: u8 = 0;
    let mut v_res_182_: u8 = 0;
    let mut v_r_183_: *mut LeanObject = core::ptr::null_mut();
    v_x_21__boxed_181_ = (lean_unbox(v_x_180_) as u8);
    v_res_182_ = l_BitVec_instDecidableForallBitVecZero(v_P_179_, v_x_21__boxed_181_);
    v_r_183_ = lean_box((v_res_182_) as usize);
    return v_r_183_;
}
pub unsafe fn l_BitVec_instDecidableForallBitVecSucc___redArg(mut v_inst_184_: u8) -> u8 {
    return v_inst_184_;
}
pub unsafe fn l_BitVec_instDecidableForallBitVecSucc___redArg___boxed(
    mut v_inst_185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_10__boxed_186_: u8 = 0;
    let mut v_res_187_: u8 = 0;
    let mut v_r_188_: *mut LeanObject = core::ptr::null_mut();
    v_inst_10__boxed_186_ = (lean_unbox(v_inst_185_) as u8);
    v_res_187_ = l_BitVec_instDecidableForallBitVecSucc___redArg(v_inst_10__boxed_186_);
    v_r_188_ = lean_box((v_res_187_) as usize);
    return v_r_188_;
}
pub unsafe fn l_BitVec_instDecidableForallBitVecSucc(
    mut v_n_189_: *mut LeanObject,
    mut v_P_190_: *mut LeanObject,
    mut v_inst_191_: *mut LeanObject,
    mut v_inst_192_: u8,
) -> u8 {
    return v_inst_192_;
}
pub unsafe fn l_BitVec_instDecidableForallBitVecSucc___boxed(
    mut v_n_193_: *mut LeanObject,
    mut v_P_194_: *mut LeanObject,
    mut v_inst_195_: *mut LeanObject,
    mut v_inst_196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_14__boxed_197_: u8 = 0;
    let mut v_res_198_: u8 = 0;
    let mut v_r_199_: *mut LeanObject = core::ptr::null_mut();
    v_inst_14__boxed_197_ = (lean_unbox(v_inst_196_) as u8);
    v_res_198_ = l_BitVec_instDecidableForallBitVecSucc(
        v_n_193_,
        v_P_194_,
        v_inst_195_,
        v_inst_14__boxed_197_,
    );
    lean_dec_ref(v_inst_195_);
    lean_dec(v_n_193_);
    v_r_199_ = lean_box((v_res_198_) as usize);
    return v_r_199_;
}
pub unsafe fn l_BitVec_instDecidableExistsBitVecZero___redArg(mut v_inst_200_: u8) -> u8 {
    return v_inst_200_;
}
pub unsafe fn l_BitVec_instDecidableExistsBitVecZero___redArg___boxed(
    mut v_inst_201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_27__boxed_202_: u8 = 0;
    let mut v_res_203_: u8 = 0;
    let mut v_r_204_: *mut LeanObject = core::ptr::null_mut();
    v_inst_27__boxed_202_ = (lean_unbox(v_inst_201_) as u8);
    v_res_203_ = l_BitVec_instDecidableExistsBitVecZero___redArg(v_inst_27__boxed_202_);
    v_r_204_ = lean_box((v_res_203_) as usize);
    return v_r_204_;
}
pub unsafe fn l_BitVec_instDecidableExistsBitVecZero(
    mut v_P_205_: *mut LeanObject,
    mut v_inst_206_: u8,
) -> u8 {
    return v_inst_206_;
}
pub unsafe fn l_BitVec_instDecidableExistsBitVecZero___boxed(
    mut v_P_207_: *mut LeanObject,
    mut v_inst_208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_30__boxed_209_: u8 = 0;
    let mut v_res_210_: u8 = 0;
    let mut v_r_211_: *mut LeanObject = core::ptr::null_mut();
    v_inst_30__boxed_209_ = (lean_unbox(v_inst_208_) as u8);
    v_res_210_ = l_BitVec_instDecidableExistsBitVecZero(v_P_207_, v_inst_30__boxed_209_);
    v_r_211_ = lean_box((v_res_210_) as usize);
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
    mut v_inst_215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_21__boxed_216_: u8 = 0;
    let mut v_res_217_: u8 = 0;
    let mut v_r_218_: *mut LeanObject = core::ptr::null_mut();
    v_inst_21__boxed_216_ = (lean_unbox(v_inst_215_) as u8);
    v_res_217_ = l_BitVec_instDecidableExistsBitVecSucc___redArg(v_inst_21__boxed_216_);
    v_r_218_ = lean_box((v_res_217_) as usize);
    return v_r_218_;
}
pub unsafe fn l_BitVec_instDecidableExistsBitVecSucc(
    mut v_n_219_: *mut LeanObject,
    mut v_P_220_: *mut LeanObject,
    mut v_inst_221_: *mut LeanObject,
    mut v_inst_222_: u8,
) -> u8 {
    let mut v___x_223_: u8 = 0;
    v___x_223_ = l_BitVec_instDecidableExistsBitVecSucc___redArg(v_inst_222_);
    return v___x_223_;
}
pub unsafe fn l_BitVec_instDecidableExistsBitVecSucc___boxed(
    mut v_n_224_: *mut LeanObject,
    mut v_P_225_: *mut LeanObject,
    mut v_inst_226_: *mut LeanObject,
    mut v_inst_227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_29__boxed_228_: u8 = 0;
    let mut v_res_229_: u8 = 0;
    let mut v_r_230_: *mut LeanObject = core::ptr::null_mut();
    v_inst_29__boxed_228_ = (lean_unbox(v_inst_227_) as u8);
    v_res_229_ = l_BitVec_instDecidableExistsBitVecSucc(
        v_n_224_,
        v_P_225_,
        v_inst_226_,
        v_inst_29__boxed_228_,
    );
    lean_dec_ref(v_inst_226_);
    lean_dec(v_n_224_);
    v_r_230_ = lean_box((v_res_229_) as usize);
    return v_r_230_;
}
pub unsafe fn l_BitVec_instDecidableForallBitVec___redArg___lam__0(
    mut v_n_231_: *mut LeanObject,
    mut v_a_232_: u8,
    mut v_x_233_: *mut LeanObject,
    mut v_a_234_: *mut LeanObject,
) -> u8 {
    let mut v___x_235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_237_: u8 = 0;
    v___x_235_ = l_BitVec_cons(v_n_231_, v_a_232_, v_a_234_);
    v___x_236_ = lean_apply_1(v_x_233_, v___x_235_);
    v___x_237_ = (lean_unbox(v___x_236_) as u8);
    return v___x_237_;
}
pub unsafe fn l_BitVec_instDecidableForallBitVec___redArg___lam__0___boxed(
    mut v_n_238_: *mut LeanObject,
    mut v_a_239_: *mut LeanObject,
    mut v_x_240_: *mut LeanObject,
    mut v_a_241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_242_: u8 = 0;
    let mut v_res_243_: u8 = 0;
    let mut v_r_244_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_242_ = (lean_unbox(v_a_239_) as u8);
    v_res_243_ = l_BitVec_instDecidableForallBitVec___redArg___lam__0(
        v_n_238_,
        v_a_boxed_242_,
        v_x_240_,
        v_a_241_,
    );
    lean_dec(v_a_241_);
    lean_dec(v_n_238_);
    v_r_244_ = lean_box((v_res_243_) as usize);
    return v_r_244_;
}
pub unsafe fn _init_l_BitVec_instDecidableForallBitVec___redArg___closed__0() -> *mut LeanObject {
    let mut v_zero_245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_246_: *mut LeanObject = core::ptr::null_mut();
    v_zero_245_ = lean_unsigned_to_nat(0);
    v___x_246_ = l_BitVec_ofNat(v_zero_245_, v_zero_245_);
    return v___x_246_;
}
pub unsafe fn l_BitVec_instDecidableForallBitVec___redArg___lam__1___boxed(
    mut v_n_247_: *mut LeanObject,
    mut v_x_248_: *mut LeanObject,
    mut v_a_249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_250_: u8 = 0;
    let mut v_res_251_: u8 = 0;
    let mut v_r_252_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_250_ = (lean_unbox(v_a_249_) as u8);
    v_res_251_ =
        l_BitVec_instDecidableForallBitVec___redArg___lam__1(v_n_247_, v_x_248_, v_a_boxed_250_);
    v_r_252_ = lean_box((v_res_251_) as usize);
    return v_r_252_;
}
pub unsafe fn l_BitVec_instDecidableForallBitVec___redArg(
    mut v_x_253_: *mut LeanObject,
    mut v_x_254_: *mut LeanObject,
) -> u8 {
    let mut v_zero_255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_256_: u8 = 0;
    v_zero_255_ = lean_unsigned_to_nat(0);
    v_isZero_256_ = lean_nat_dec_eq(v_x_253_, v_zero_255_);
    if v_isZero_256_ == 1 {
        let mut v___x_257_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_258_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_259_: u8 = 0;
        v___x_257_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_BitVec_instDecidableForallBitVec___redArg___closed__0),
            core::ptr::addr_of_mut!(l_BitVec_instDecidableForallBitVec___redArg___closed__0_once),
            _init_l_BitVec_instDecidableForallBitVec___redArg___closed__0,
        );
        v___x_258_ = lean_apply_1(v_x_254_, v___x_257_);
        v___x_259_ = (lean_unbox(v___x_258_) as u8);
        return v___x_259_;
    } else {
        let mut v_one_260_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_261_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_262_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_263_: u8 = 0;
        v_one_260_ = lean_unsigned_to_nat(1);
        v_n_261_ = lean_nat_sub(v_x_253_, v_one_260_);
        v___f_262_ = lean_alloc_closure(
            l_BitVec_instDecidableForallBitVec___redArg___lam__1___boxed as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_262_, 0, v_n_261_);
        lean_closure_set(v___f_262_, 1, v_x_254_);
        v___x_263_ = l_Bool_instDecidableForallOfDecidablePred___redArg(v___f_262_);
        return v___x_263_;
    }
}
pub unsafe fn l_BitVec_instDecidableForallBitVec___redArg___lam__1(
    mut v_n_264_: *mut LeanObject,
    mut v_x_265_: *mut LeanObject,
    mut v_a_266_: u8,
) -> u8 {
    let mut v___x_267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_269_: u8 = 0;
    v___x_267_ = lean_box((v_a_266_) as usize);
    lean_inc(v_n_264_);
    v___f_268_ = lean_alloc_closure(
        l_BitVec_instDecidableForallBitVec___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_268_, 0, v_n_264_);
    lean_closure_set(v___f_268_, 1, v___x_267_);
    lean_closure_set(v___f_268_, 2, v_x_265_);
    v___x_269_ = l_BitVec_instDecidableForallBitVec___redArg(v_n_264_, v___f_268_);
    lean_dec(v_n_264_);
    return v___x_269_;
}
pub unsafe fn l_BitVec_instDecidableForallBitVec___redArg___boxed(
    mut v_x_270_: *mut LeanObject,
    mut v_x_271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_272_: u8 = 0;
    let mut v_r_273_: *mut LeanObject = core::ptr::null_mut();
    v_res_272_ = l_BitVec_instDecidableForallBitVec___redArg(v_x_270_, v_x_271_);
    lean_dec(v_x_270_);
    v_r_273_ = lean_box((v_res_272_) as usize);
    return v_r_273_;
}
pub unsafe fn l_BitVec_instDecidableForallBitVec(
    mut v_x_274_: *mut LeanObject,
    mut v_x_275_: *mut LeanObject,
    mut v_x_276_: *mut LeanObject,
) -> u8 {
    let mut v___x_277_: u8 = 0;
    v___x_277_ = l_BitVec_instDecidableForallBitVec___redArg(v_x_274_, v_x_276_);
    return v___x_277_;
}
pub unsafe fn l_BitVec_instDecidableForallBitVec___boxed(
    mut v_x_278_: *mut LeanObject,
    mut v_x_279_: *mut LeanObject,
    mut v_x_280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_281_: u8 = 0;
    let mut v_r_282_: *mut LeanObject = core::ptr::null_mut();
    v_res_281_ = l_BitVec_instDecidableForallBitVec(v_x_278_, v_x_279_, v_x_280_);
    lean_dec(v_x_278_);
    v_r_282_ = lean_box((v_res_281_) as usize);
    return v_r_282_;
}
pub unsafe fn l_BitVec_instDecidableExistsBitVec___redArg___lam__0(
    mut v_n_283_: *mut LeanObject,
    mut v_a_284_: u8,
    mut v_x_285_: *mut LeanObject,
    mut v_isZero_286_: u8,
    mut v_a_287_: *mut LeanObject,
) -> u8 {
    let mut v___x_288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_290_: u8 = 0;
    v___x_288_ = l_BitVec_cons(v_n_283_, v_a_284_, v_a_287_);
    v___x_289_ = lean_apply_1(v_x_285_, v___x_288_);
    v___x_290_ = (lean_unbox(v___x_289_) as u8);
    if v___x_290_ == 0 {
        let mut v___x_291_: u8 = 0;
        v___x_291_ = 1;
        return v___x_291_;
    } else {
        return v_isZero_286_;
    }
}
pub unsafe fn l_BitVec_instDecidableExistsBitVec___redArg___lam__0___boxed(
    mut v_n_292_: *mut LeanObject,
    mut v_a_293_: *mut LeanObject,
    mut v_x_294_: *mut LeanObject,
    mut v_isZero_295_: *mut LeanObject,
    mut v_a_296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_297_: u8 = 0;
    let mut v_isZero_boxed_298_: u8 = 0;
    let mut v_res_299_: u8 = 0;
    let mut v_r_300_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_297_ = (lean_unbox(v_a_293_) as u8);
    v_isZero_boxed_298_ = (lean_unbox(v_isZero_295_) as u8);
    v_res_299_ = l_BitVec_instDecidableExistsBitVec___redArg___lam__0(
        v_n_292_,
        v_a_boxed_297_,
        v_x_294_,
        v_isZero_boxed_298_,
        v_a_296_,
    );
    lean_dec(v_a_296_);
    lean_dec(v_n_292_);
    v_r_300_ = lean_box((v_res_299_) as usize);
    return v_r_300_;
}
pub unsafe fn l_BitVec_instDecidableExistsBitVec___redArg___lam__1(
    mut v_n_301_: *mut LeanObject,
    mut v_x_302_: *mut LeanObject,
    mut v_isZero_303_: u8,
    mut v_a_304_: u8,
) -> u8 {
    let mut v___x_305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_308_: u8 = 0;
    v___x_305_ = lean_box((v_a_304_) as usize);
    v___x_306_ = lean_box((v_isZero_303_) as usize);
    lean_inc(v_n_301_);
    v___f_307_ = lean_alloc_closure(
        l_BitVec_instDecidableExistsBitVec___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_307_, 0, v_n_301_);
    lean_closure_set(v___f_307_, 1, v___x_305_);
    lean_closure_set(v___f_307_, 2, v_x_302_);
    lean_closure_set(v___f_307_, 3, v___x_306_);
    v___x_308_ = l_BitVec_instDecidableForallBitVec___redArg(v_n_301_, v___f_307_);
    lean_dec(v_n_301_);
    return v___x_308_;
}
pub unsafe fn l_BitVec_instDecidableExistsBitVec___redArg___lam__1___boxed(
    mut v_n_309_: *mut LeanObject,
    mut v_x_310_: *mut LeanObject,
    mut v_isZero_311_: *mut LeanObject,
    mut v_a_312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isZero_boxed_313_: u8 = 0;
    let mut v_a_boxed_314_: u8 = 0;
    let mut v_res_315_: u8 = 0;
    let mut v_r_316_: *mut LeanObject = core::ptr::null_mut();
    v_isZero_boxed_313_ = (lean_unbox(v_isZero_311_) as u8);
    v_a_boxed_314_ = (lean_unbox(v_a_312_) as u8);
    v_res_315_ = l_BitVec_instDecidableExistsBitVec___redArg___lam__1(
        v_n_309_,
        v_x_310_,
        v_isZero_boxed_313_,
        v_a_boxed_314_,
    );
    v_r_316_ = lean_box((v_res_315_) as usize);
    return v_r_316_;
}
pub unsafe fn l_BitVec_instDecidableExistsBitVec___redArg(
    mut v_x_317_: *mut LeanObject,
    mut v_x_318_: *mut LeanObject,
) -> u8 {
    let mut v_zero_319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_320_: u8 = 0;
    v_zero_319_ = lean_unsigned_to_nat(0);
    v_isZero_320_ = lean_nat_dec_eq(v_x_317_, v_zero_319_);
    if v_isZero_320_ == 1 {
        let mut v___x_321_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_323_: u8 = 0;
        v___x_321_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_BitVec_instDecidableForallBitVec___redArg___closed__0),
            core::ptr::addr_of_mut!(l_BitVec_instDecidableForallBitVec___redArg___closed__0_once),
            _init_l_BitVec_instDecidableForallBitVec___redArg___closed__0,
        );
        v___x_322_ = lean_apply_1(v_x_318_, v___x_321_);
        v___x_323_ = (lean_unbox(v___x_322_) as u8);
        return v___x_323_;
    } else {
        let mut v_one_324_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_325_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_326_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_327_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_328_: u8 = 0;
        let mut v___x_329_: u8 = 0;
        v_one_324_ = lean_unsigned_to_nat(1);
        v_n_325_ = lean_nat_sub(v_x_317_, v_one_324_);
        v___x_326_ = lean_box((v_isZero_320_) as usize);
        v___f_327_ = lean_alloc_closure(
            l_BitVec_instDecidableExistsBitVec___redArg___lam__1___boxed as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_327_, 0, v_n_325_);
        lean_closure_set(v___f_327_, 1, v_x_318_);
        lean_closure_set(v___f_327_, 2, v___x_326_);
        v___x_328_ = l_Bool_instDecidableForallOfDecidablePred___redArg(v___f_327_);
        v___x_329_ = l_BitVec_instDecidableExistsBitVecSucc___redArg(v___x_328_);
        return v___x_329_;
    }
}
pub unsafe fn l_BitVec_instDecidableExistsBitVec___redArg___boxed(
    mut v_x_330_: *mut LeanObject,
    mut v_x_331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_332_: u8 = 0;
    let mut v_r_333_: *mut LeanObject = core::ptr::null_mut();
    v_res_332_ = l_BitVec_instDecidableExistsBitVec___redArg(v_x_330_, v_x_331_);
    lean_dec(v_x_330_);
    v_r_333_ = lean_box((v_res_332_) as usize);
    return v_r_333_;
}
pub unsafe fn l_BitVec_instDecidableExistsBitVec(
    mut v_x_334_: *mut LeanObject,
    mut v_x_335_: *mut LeanObject,
    mut v_x_336_: *mut LeanObject,
) -> u8 {
    let mut v___x_337_: u8 = 0;
    v___x_337_ = l_BitVec_instDecidableExistsBitVec___redArg(v_x_334_, v_x_336_);
    return v___x_337_;
}
pub unsafe fn l_BitVec_instDecidableExistsBitVec___boxed(
    mut v_x_338_: *mut LeanObject,
    mut v_x_339_: *mut LeanObject,
    mut v_x_340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_341_: u8 = 0;
    let mut v_r_342_: *mut LeanObject = core::ptr::null_mut();
    v_res_341_ = l_BitVec_instDecidableExistsBitVec(v_x_338_, v_x_339_, v_x_340_);
    lean_dec(v_x_338_);
    v_r_342_ = lean_box((v_res_341_) as usize);
    return v_r_342_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_BitVec_Decidable(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_PropLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_BitVec_Decidable(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_BitVec_Decidable(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_PropLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Decidable(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_BitVec_Decidable(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_BitVec_Decidable(builtin);
}
